import V185TrunkScan23Chunk0423

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2506505 : List Nat := [1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_2506505 : Nat := 118140960795 + 2506505 * 2 ^ 59
def prefixEnd_2506505 : Nat := 4983230072969 + 3 ^ 40 * 2506505 * 2
def baseEnd_2506505 : Nat := 1287041827897821021360299

theorem tailTrace_2506505 : CollatzResearch.WordTrace tailWord_2506505 prefixEnd_2506505 1287041827897821021360299 := by
  unfold tailWord_2506505
  simp only [CollatzResearch.WordTrace]
  refine ⟨91419747784367936818160969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60946498522911957878773979 91419747784367936818160969)
  ·
    refine ⟨68564810838275952613620727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91419747784367936818160969 68564810838275952613620727)
    ·
      refine ⟨102847216257413928920431091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68564810838275952613620727 102847216257413928920431091)
      ·
        refine ⟨154270824386120893380646637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102847216257413928920431091 154270824386120893380646637)
        ·
          refine ⟨57851559144795335017742489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154270824386120893380646637 57851559144795335017742489)
          ·
            refine ⟨43388669358596501263306867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57851559144795335017742489 43388669358596501263306867)
            ·
              refine ⟨65083004037894751894960301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43388669358596501263306867 65083004037894751894960301)
              ·
                refine ⟨24406126514210531960610113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65083004037894751894960301 24406126514210531960610113)
                ·
                  refine ⟨18304594885657898970457585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24406126514210531960610113 18304594885657898970457585)
                  ·
                    refine ⟨13728446164243424227843189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18304594885657898970457585 13728446164243424227843189)
                    ·
                      refine ⟨1287041827897821021360299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13728446164243424227843189 1287041827897821021360299)
                      ·
                        rfl

theorem cell23_2506505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_2506505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506505 prefixEnd_2506505 := by exact prefixLift 2506505
  have htrace : WordTrace (prefixWord ++ tailWord_2506505) baseStart_2506505 baseEnd_2506505 := by
    simpa [prefixWord, tailWord_2506505, baseEnd_2506505] using wordTrace_append hprefix tailTrace_2506505
  have hstable : (prefixWord ++ tailWord_2506505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506505).length < 2 ^ (prefixWord ++ tailWord_2506505).sum := by decide
  have hdescent : baseEnd_2506505 < baseStart_2506505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506515 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 4]
def baseStart_2506515 : Nat := 118140960795 + 2506515 * 2 ^ 59
def prefixEnd_2506515 : Nat := 4983230072969 + 3 ^ 40 * 2506515 * 2
def baseEnd_2506515 : Nat := 1287046962704365982235253

theorem tailTrace_2506515 : CollatzResearch.WordTrace tailWord_2506515 prefixEnd_2506515 1287046962704365982235253 := by
  unfold tailWord_2506515
  simp only [CollatzResearch.WordTrace]
  refine ⟨91420112514331708526024999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60946741676221139017349999 91420112514331708526024999)
  ·
    refine ⟨137130168771497562789037499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91420112514331708526024999 137130168771497562789037499)
    ·
      refine ⟨205695253157246344183556249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137130168771497562789037499 205695253157246344183556249)
      ·
        refine ⟨154271439867934758137667187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205695253157246344183556249 154271439867934758137667187)
        ·
          refine ⟨231407159801902137206500781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154271439867934758137667187 231407159801902137206500781)
          ·
            refine ⟨86777684925713301452437793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231407159801902137206500781 86777684925713301452437793)
            ·
              refine ⟨65083263694284976089328345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86777684925713301452437793 65083263694284976089328345)
              ·
                refine ⟨48812447770713732066996259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65083263694284976089328345 48812447770713732066996259)
                ·
                  refine ⟨73218671656070598100494389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48812447770713732066996259 73218671656070598100494389)
                  ·
                    refine ⟨6864250467756618571921349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73218671656070598100494389 6864250467756618571921349)
                    ·
                      refine ⟨1287046962704365982235253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6864250467756618571921349 1287046962704365982235253)
                      ·
                        rfl

theorem cell23_2506515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 5, 4].length) (baseStart_2506515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506515 prefixEnd_2506515 := by exact prefixLift 2506515
  have htrace : WordTrace (prefixWord ++ tailWord_2506515) baseStart_2506515 baseEnd_2506515 := by
    simpa [prefixWord, tailWord_2506515, baseEnd_2506515] using wordTrace_append hprefix tailTrace_2506515
  have hstable : (prefixWord ++ tailWord_2506515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506515).length < 2 ^ (prefixWord ++ tailWord_2506515).sum := by decide
  have hdescent : baseEnd_2506515 < baseStart_2506515 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506516 : List Nat := [2, 4, 4, 1, 1, 1, 10]
def baseStart_2506516 : Nat := 118140960795 + 2506516 * 2 ^ 59
def prefixEnd_2506516 : Nat := 4983230072969 + 3 ^ 40 * 2506516 * 2
def baseEnd_2506516 : Nat := 15889475014629882448429

theorem tailTrace_2506516 : CollatzResearch.WordTrace tailWord_2506516 prefixEnd_2506516 15889475014629882448429 := by
  unfold tailWord_2506516
  simp only [CollatzResearch.WordTrace]
  refine ⟨45710074493664042848405701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60946765991552057131207601 45710074493664042848405701)
  ·
    refine ⟨8570638967562008034076069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45710074493664042848405701 8570638967562008034076069)
    ·
      refine ⟨1606994806417876506389263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8570638967562008034076069 1606994806417876506389263)
      ·
        refine ⟨2410492209626814759583895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606994806417876506389263 2410492209626814759583895)
        ·
          refine ⟨3615738314440222139375843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410492209626814759583895 3615738314440222139375843)
          ·
            refine ⟨5423607471660333209063765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615738314440222139375843 5423607471660333209063765)
            ·
              refine ⟨15889475014629882448429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5423607471660333209063765 15889475014629882448429)
              ·
                rfl

theorem cell23_2506516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 10].length) (baseStart_2506516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506516 prefixEnd_2506516 := by exact prefixLift 2506516
  have htrace : WordTrace (prefixWord ++ tailWord_2506516) baseStart_2506516 baseEnd_2506516 := by
    simpa [prefixWord, tailWord_2506516, baseEnd_2506516] using wordTrace_append hprefix tailTrace_2506516
  have hstable : (prefixWord ++ tailWord_2506516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506516).length < 2 ^ (prefixWord ++ tailWord_2506516).sum := by decide
  have hdescent : baseEnd_2506516 < baseStart_2506516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506575 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 6]
def baseStart_2506575 : Nat := 118140960795 + 2506575 * 2 ^ 59
def prefixEnd_2506575 : Nat := 4983230072969 + 3 ^ 40 * 2506575 * 2
def baseEnd_2506575 : Nat := 1287077771543635747484977

theorem tailTrace_2506575 : CollatzResearch.WordTrace tailWord_2506575 prefixEnd_2506575 1287077771543635747484977 := by
  unfold tailWord_2506575
  simp only [CollatzResearch.WordTrace]
  refine ⟨91422300894114338773209179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60948200596076225848806119 91422300894114338773209179)
  ·
    refine ⟨137133451341171508159813769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91422300894114338773209179 137133451341171508159813769)
    ·
      refine ⟨102850088505878631119860327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137133451341171508159813769 102850088505878631119860327)
      ·
        refine ⟨154275132758817946679790491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102850088505878631119860327 154275132758817946679790491)
        ·
          refine ⟨231412699138226920019685737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154275132758817946679790491 231412699138226920019685737)
          ·
            refine ⟨173559524353670190014764303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231412699138226920019685737 173559524353670190014764303)
            ·
              refine ⟨260339286530505285022146455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173559524353670190014764303 260339286530505285022146455)
              ·
                refine ⟨390508929795757927533219683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260339286530505285022146455 390508929795757927533219683)
                ·
                  refine ⟨585763394693636891299829525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 390508929795757927533219683 585763394693636891299829525)
                  ·
                    refine ⟨27457659126264229279679509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 585763394693636891299829525 27457659126264229279679509)
                    ·
                      refine ⟨1287077771543635747484977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27457659126264229279679509 1287077771543635747484977)
                      ·
                        rfl

theorem cell23_2506575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_2506575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506575 prefixEnd_2506575 := by exact prefixLift 2506575
  have htrace : WordTrace (prefixWord ++ tailWord_2506575) baseStart_2506575 baseEnd_2506575 := by
    simpa [prefixWord, tailWord_2506575, baseEnd_2506575] using wordTrace_append hprefix tailTrace_2506575
  have hstable : (prefixWord ++ tailWord_2506575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506575).length < 2 ^ (prefixWord ++ tailWord_2506575).sum := by decide
  have hdescent : baseEnd_2506575 < baseStart_2506575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506696 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 6]
def baseStart_2506696 : Nat := 118140960795 + 2506696 * 2 ^ 59
def prefixEnd_2506696 : Nat := 4983230072969 + 3 ^ 40 * 2506696 * 2
def baseEnd_2506696 : Nat := 143015544744758863785769

theorem tailTrace_2506696 : CollatzResearch.WordTrace tailWord_2506696 prefixEnd_2506696 143015544744758863785769 := by
  unfold tailWord_2506696
  simp only [CollatzResearch.WordTrace]
  refine ⟨45713357063337988219181971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60951142751117317625575961 45713357063337988219181971)
  ·
    refine ⟨68570035595006982328772957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45713357063337988219181971 68570035595006982328772957)
    ·
      refine ⟨25713763348127618373289859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68570035595006982328772957 25713763348127618373289859)
      ·
        refine ⟨38570645022191427559934789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25713763348127618373289859 38570645022191427559934789)
        ·
          refine ⟨7231995941660892667487773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38570645022191427559934789 7231995941660892667487773)
          ·
            refine ⟨2711998478122834750307915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7231995941660892667487773 2711998478122834750307915)
            ·
              refine ⟨4067997717184252125461873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711998478122834750307915 4067997717184252125461873)
              ·
                refine ⟨3050998287888189094096405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067997717184252125461873 3050998287888189094096405)
                ·
                  refine ⟨143015544744758863785769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3050998287888189094096405 143015544744758863785769)
                  ·
                    rfl

theorem cell23_2506696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 6].length) (baseStart_2506696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506696 prefixEnd_2506696 := by exact prefixLift 2506696
  have htrace : WordTrace (prefixWord ++ tailWord_2506696) baseStart_2506696 baseEnd_2506696 := by
    simpa [prefixWord, tailWord_2506696, baseEnd_2506696] using wordTrace_append hprefix tailTrace_2506696
  have hstable : (prefixWord ++ tailWord_2506696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506696).length < 2 ^ (prefixWord ++ tailWord_2506696).sum := by decide
  have hdescent : baseEnd_2506696 < baseStart_2506696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506749 : List Nat := [1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 5]
def baseStart_2506749 : Nat := 118140960795 + 2506749 * 2 ^ 59
def prefixEnd_2506749 : Nat := 4983230072969 + 3 ^ 40 * 2506749 * 2
def baseEnd_2506749 : Nat := 1287167117177518066709177

theorem tailTrace_2506749 : CollatzResearch.WordTrace tailWord_2506749 prefixEnd_2506749 1287167117177518066709177 := by
  unfold tailWord_2506749
  simp only [CollatzResearch.WordTrace]
  refine ⟨91428647195483966490043301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60952431463655977660028867 91428647195483966490043301)
  ·
    refine ⟨17142871349153243716883119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91428647195483966490043301 17142871349153243716883119)
    ·
      refine ⟨25714307023729865575324679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17142871349153243716883119 25714307023729865575324679)
      ·
        refine ⟨38571460535594798362987019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25714307023729865575324679 38571460535594798362987019)
        ·
          refine ⟨57857190803392197544480529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38571460535594798362987019 57857190803392197544480529)
          ·
            refine ⟨43392893102544148158360397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57857190803392197544480529 43392893102544148158360397)
            ·
              refine ⟨16272334913454055559385149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43392893102544148158360397 16272334913454055559385149)
              ·
                refine ⟨6102125592545270834769431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16272334913454055559385149 6102125592545270834769431)
                ·
                  refine ⟨9153188388817906252154147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6102125592545270834769431 9153188388817906252154147)
                  ·
                    refine ⟨13729782583226859378231221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9153188388817906252154147 13729782583226859378231221)
                    ·
                      refine ⟨1287167117177518066709177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13729782583226859378231221 1287167117177518066709177)
                      ·
                        rfl

theorem cell23_2506749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 3, 1, 1, 5].length) (baseStart_2506749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506749 prefixEnd_2506749 := by exact prefixLift 2506749
  have htrace : WordTrace (prefixWord ++ tailWord_2506749) baseStart_2506749 baseEnd_2506749 := by
    simpa [prefixWord, tailWord_2506749, baseEnd_2506749] using wordTrace_append hprefix tailTrace_2506749
  have hstable : (prefixWord ++ tailWord_2506749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506749).length < 2 ^ (prefixWord ++ tailWord_2506749).sum := by decide
  have hdescent : baseEnd_2506749 < baseStart_2506749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506750 : List Nat := [4, 2, 2, 2, 1, 2, 1, 2, 2, 3, 2]
def baseStart_2506750 : Nat := 118140960795 + 2506750 * 2 ^ 59
def prefixEnd_2506750 : Nat := 4983230072969 + 3 ^ 40 * 2506750 * 2
def baseEnd_2506750 : Nat := 1287167630658172562796673

theorem tailTrace_2506750 : CollatzResearch.WordTrace tailWord_2506750 prefixEnd_2506750 1287167630658172562796673 := by
  unfold tailWord_2506750
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428585458560042957603713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60952455778986895773886469 11428585458560042957603713)
  ·
    refine ⟨8571439093920032218202785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11428585458560042957603713 8571439093920032218202785)
    ·
      refine ⟨6428579320440024163652089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8571439093920032218202785 6428579320440024163652089)
      ·
        refine ⟨4821434490330018122739067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6428579320440024163652089 4821434490330018122739067)
        ·
          refine ⟨7232151735495027184108601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821434490330018122739067 7232151735495027184108601)
          ·
            refine ⟨5424113801621270388081451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7232151735495027184108601 5424113801621270388081451)
            ·
              refine ⟨8136170702431905582122177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5424113801621270388081451 8136170702431905582122177)
              ·
                refine ⟨6102128026823929186591633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8136170702431905582122177 6102128026823929186591633)
                ·
                  refine ⟨4576596020117946889943725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6102128026823929186591633 4576596020117946889943725)
                  ·
                    refine ⟨1716223507544230083728897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4576596020117946889943725 1716223507544230083728897)
                    ·
                      refine ⟨1287167630658172562796673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1716223507544230083728897 1287167630658172562796673)
                      ·
                        rfl

theorem cell23_2506750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_2506750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506750 prefixEnd_2506750 := by exact prefixLift 2506750
  have htrace : WordTrace (prefixWord ++ tailWord_2506750) baseStart_2506750 baseEnd_2506750 := by
    simpa [prefixWord, tailWord_2506750, baseEnd_2506750] using wordTrace_append hprefix tailTrace_2506750
  have hstable : (prefixWord ++ tailWord_2506750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506750).length < 2 ^ (prefixWord ++ tailWord_2506750).sum := by decide
  have hdescent : baseEnd_2506750 < baseStart_2506750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506759 : List Nat := [1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 6]
def baseStart_2506759 : Nat := 118140960795 + 2506759 * 2 ^ 59
def prefixEnd_2506759 : Nat := 4983230072969 + 3 ^ 40 * 2506759 * 2
def baseEnd_2506759 : Nat := 1287172251984063027584131

theorem tailTrace_2506759 : CollatzResearch.WordTrace tailWord_2506759 prefixEnd_2506759 1287172251984063027584131 := by
  unfold tailWord_2506759
  simp only [CollatzResearch.WordTrace]
  refine ⟨91429011925447738197907331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60952674616965158798604887 91429011925447738197907331)
  ·
    refine ⟨137143517888171607296860997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91429011925447738197907331 137143517888171607296860997)
    ·
      refine ⟨25714409604032176368161437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137143517888171607296860997 25714409604032176368161437)
      ·
        refine ⟨9642903601512066138060539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25714409604032176368161437 9642903601512066138060539)
        ·
          refine ⟨14464355402268099207090809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9642903601512066138060539 14464355402268099207090809)
          ·
            refine ⟨10848266551701074405318107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14464355402268099207090809 10848266551701074405318107)
            ·
              refine ⟨16272399827551611607977161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10848266551701074405318107 16272399827551611607977161)
              ·
                refine ⟨12204299870663708705982871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16272399827551611607977161 12204299870663708705982871)
                ·
                  refine ⟨18306449805995563058974307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12204299870663708705982871 18306449805995563058974307)
                  ·
                    refine ⟨27459674708993344588461461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18306449805995563058974307 27459674708993344588461461)
                    ·
                      refine ⟨1287172251984063027584131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27459674708993344588461461 1287172251984063027584131)
                      ·
                        rfl

theorem cell23_2506759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_2506759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506759 prefixEnd_2506759 := by exact prefixLift 2506759
  have htrace : WordTrace (prefixWord ++ tailWord_2506759) baseStart_2506759 baseEnd_2506759 := by
    simpa [prefixWord, tailWord_2506759, baseEnd_2506759] using wordTrace_append hprefix tailTrace_2506759
  have hstable : (prefixWord ++ tailWord_2506759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506759).length < 2 ^ (prefixWord ++ tailWord_2506759).sum := by decide
  have hdescent : baseEnd_2506759 < baseStart_2506759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506766 : List Nat := [4, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3]
def baseStart_2506766 : Nat := 118140960795 + 2506766 * 2 ^ 59
def prefixEnd_2506766 : Nat := 4983230072969 + 3 ^ 40 * 2506766 * 2
def baseEnd_2506766 : Nat := 1287175846348644500196599

theorem tailTrace_2506766 : CollatzResearch.WordTrace tailWord_2506766 prefixEnd_2506766 1287175846348644500196599 := by
  unfold tailWord_2506766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428658404552797299176519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60952844824281585595608101 11428658404552797299176519)
  ·
    refine ⟨17142987606829195948764779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11428658404552797299176519 17142987606829195948764779)
    ·
      refine ⟨25714481410243793923147169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17142987606829195948764779 25714481410243793923147169)
      ·
        refine ⟨19285861057682845442360377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25714481410243793923147169 19285861057682845442360377)
        ·
          refine ⟨14464395793262134081770283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19285861057682845442360377 14464395793262134081770283)
          ·
            refine ⟨21696593689893201122655425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14464395793262134081770283 21696593689893201122655425)
            ·
              refine ⟨16272445267419900841991569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21696593689893201122655425 16272445267419900841991569)
              ·
                refine ⟨12204333950564925631493677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16272445267419900841991569 12204333950564925631493677)
                ·
                  refine ⟨4576625231461847111810129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12204333950564925631493677 4576625231461847111810129)
                  ·
                    refine ⟨3432468923596385333857597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4576625231461847111810129 3432468923596385333857597)
                    ·
                      refine ⟨1287175846348644500196599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3432468923596385333857597 1287175846348644500196599)
                      ·
                        rfl

theorem cell23_2506766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_2506766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506766 prefixEnd_2506766 := by exact prefixLift 2506766
  have htrace : WordTrace (prefixWord ++ tailWord_2506766) baseStart_2506766 baseEnd_2506766 := by
    simpa [prefixWord, tailWord_2506766, baseEnd_2506766] using wordTrace_append hprefix tailTrace_2506766
  have hstable : (prefixWord ++ tailWord_2506766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506766).length < 2 ^ (prefixWord ++ tailWord_2506766).sum := by decide
  have hdescent : baseEnd_2506766 < baseStart_2506766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506773 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 2, 4]
def baseStart_2506773 : Nat := 118140960795 + 2506773 * 2 ^ 59
def prefixEnd_2506773 : Nat := 4983230072969 + 3 ^ 40 * 2506773 * 2
def baseEnd_2506773 : Nat := 429059813571075324269689

theorem tailTrace_2506773 : CollatzResearch.WordTrace tailWord_2506773 prefixEnd_2506773 429059813571075324269689 := by
  unfold tailWord_2506773
  simp only [CollatzResearch.WordTrace]
  refine ⟨91429522547397018588916973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60953015031598012392611315 91429522547397018588916973)
  ·
    refine ⟨34286070955273881970843865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91429522547397018588916973 34286070955273881970843865)
    ·
      refine ⟨25714553216455411478132899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34286070955273881970843865 25714553216455411478132899)
      ·
        refine ⟨38571829824683117217199349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25714553216455411478132899 38571829824683117217199349)
        ·
          refine ⟨3616109046064042239112439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38571829824683117217199349 3616109046064042239112439)
          ·
            refine ⟨5424163569096063358668659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616109046064042239112439 5424163569096063358668659)
            ·
              refine ⟨8136245353644095038002989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5424163569096063358668659 8136245353644095038002989)
              ·
                refine ⟨3051092007616535639251121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8136245353644095038002989 3051092007616535639251121)
                ·
                  refine ⟨2288319005712401729438341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051092007616535639251121 2288319005712401729438341)
                  ·
                    refine ⟨429059813571075324269689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2288319005712401729438341 429059813571075324269689)
                    ·
                      rfl

theorem cell23_2506773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_2506773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506773 prefixEnd_2506773 := by exact prefixLift 2506773
  have htrace : WordTrace (prefixWord ++ tailWord_2506773) baseStart_2506773 baseEnd_2506773 := by
    simpa [prefixWord, tailWord_2506773, baseEnd_2506773] using wordTrace_append hprefix tailTrace_2506773
  have hstable : (prefixWord ++ tailWord_2506773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506773).length < 2 ^ (prefixWord ++ tailWord_2506773).sum := by decide
  have hdescent : baseEnd_2506773 < baseStart_2506773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506796 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 3]
def baseStart_2506796 : Nat := 118140960795 + 2506796 * 2 ^ 59
def prefixEnd_2506796 : Nat := 4983230072969 + 3 ^ 40 * 2506796 * 2
def baseEnd_2506796 : Nat := 1287191250768279382821461

theorem tailTrace_2506796 : CollatzResearch.WordTrace tailWord_2506796 prefixEnd_2506796 1287191250768279382821461 := by
  unfold tailWord_2506796
  simp only [CollatzResearch.WordTrace]
  refine ⟨45715180713156846758502121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60953574284209129011336161 45715180713156846758502121)
  ·
    refine ⟨34286385534867635068876591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45715180713156846758502121 34286385534867635068876591)
    ·
      refine ⟨51429578302301452603314887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34286385534867635068876591 51429578302301452603314887)
      ·
        refine ⟨77144367453452178904972331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51429578302301452603314887 77144367453452178904972331)
        ·
          refine ⟨115716551180178268357458497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77144367453452178904972331 115716551180178268357458497)
          ·
            refine ⟨86787413385133701268093873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115716551180178268357458497 86787413385133701268093873)
            ·
              refine ⟨65090560038850275951070405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86787413385133701268093873 65090560038850275951070405)
              ·
                refine ⟨12204480007284426740825701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65090560038850275951070405 12204480007284426740825701)
                ·
                  refine ⟨2288340001365830013904819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12204480007284426740825701 2288340001365830013904819)
                  ·
                    refine ⟨3432510002048745020857229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2288340001365830013904819 3432510002048745020857229)
                    ·
                      refine ⟨1287191250768279382821461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3432510002048745020857229 1287191250768279382821461)
                      ·
                        rfl

theorem cell23_2506796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 3].length) (baseStart_2506796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506796 prefixEnd_2506796 := by exact prefixLift 2506796
  have htrace : WordTrace (prefixWord ++ tailWord_2506796) baseStart_2506796 baseEnd_2506796 := by
    simpa [prefixWord, tailWord_2506796, baseEnd_2506796] using wordTrace_append hprefix tailTrace_2506796
  have hstable : (prefixWord ++ tailWord_2506796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506796).length < 2 ^ (prefixWord ++ tailWord_2506796).sum := by decide
  have hdescent : baseEnd_2506796 < baseStart_2506796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506814 : List Nat := [4, 2, 1, 3, 2, 1, 1, 4, 1, 2, 2]
def baseStart_2506814 : Nat := 118140960795 + 2506814 * 2 ^ 59
def prefixEnd_2506814 : Nat := 4983230072969 + 3 ^ 40 * 2506814 * 2
def baseEnd_2506814 : Nat := 1287200493420060312396379

theorem tailTrace_2506814 : CollatzResearch.WordTrace tailWord_2506814 prefixEnd_2506814 1287200493420060312396379 := by
  unfold tailWord_2506814
  simp only [CollatzResearch.WordTrace]
  refine ⟨11428877242531060323894937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60954011960165655060772997 11428877242531060323894937)
  ·
    refine ⟨8571657931898295242921203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11428877242531060323894937 8571657931898295242921203)
    ·
      refine ⟨12857486897847442864381805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8571657931898295242921203 12857486897847442864381805)
      ·
        refine ⟨4821557586692791074143177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12857486897847442864381805 4821557586692791074143177)
        ·
          refine ⟨3616168190019593305607383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4821557586692791074143177 3616168190019593305607383)
          ·
            refine ⟨5424252285029389958411075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616168190019593305607383 5424252285029389958411075)
            ·
              refine ⟨8136378427544084937616613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5424252285029389958411075 8136378427544084937616613)
              ·
                refine ⟨1525570955164515925803115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8136378427544084937616613 1525570955164515925803115)
                ·
                  refine ⟨2288356432746773888704673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525570955164515925803115 2288356432746773888704673)
                  ·
                    refine ⟨1716267324560080416528505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2288356432746773888704673 1716267324560080416528505)
                    ·
                      refine ⟨1287200493420060312396379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1716267324560080416528505 1287200493420060312396379)
                      ·
                        rfl

theorem cell23_2506814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 4, 1, 2, 2].length) (baseStart_2506814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506814 prefixEnd_2506814 := by exact prefixLift 2506814
  have htrace : WordTrace (prefixWord ++ tailWord_2506814) baseStart_2506814 baseEnd_2506814 := by
    simpa [prefixWord, tailWord_2506814, baseEnd_2506814] using wordTrace_append hprefix tailTrace_2506814
  have hstable : (prefixWord ++ tailWord_2506814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506814).length < 2 ^ (prefixWord ++ tailWord_2506814).sum := by decide
  have hdescent : baseEnd_2506814 < baseStart_2506814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506839 : List Nat := [1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 5]
def baseStart_2506839 : Nat := 118140960795 + 2506839 * 2 ^ 59
def prefixEnd_2506839 : Nat := 4983230072969 + 3 ^ 40 * 2506839 * 2
def baseEnd_2506839 : Nat := 1287213330436422714583763

theorem tailTrace_2506839 : CollatzResearch.WordTrace tailWord_2506839 prefixEnd_2506839 1287213330436422714583763 := by
  unfold tailWord_2506839
  simp only [CollatzResearch.WordTrace]
  refine ⟨91431929765157911860819571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60954619843438607907213047 91431929765157911860819571)
  ·
    refine ⟨137147894647736867791229357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91431929765157911860819571 137147894647736867791229357)
    ·
      refine ⟨51430460492901325421711009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137147894647736867791229357 51430460492901325421711009)
      ·
        refine ⟨38572845369675994066283257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51430460492901325421711009 38572845369675994066283257)
        ·
          refine ⟨28929634027256995549712443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38572845369675994066283257 28929634027256995549712443)
          ·
            refine ⟨43394451040885493324568665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28929634027256995549712443 43394451040885493324568665)
            ·
              refine ⟨32545838280664119993426499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43394451040885493324568665 32545838280664119993426499)
              ·
                refine ⟨48818757420996179990139749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32545838280664119993426499 48818757420996179990139749)
                ·
                  refine ⟨9153517016436783748151203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48818757420996179990139749 9153517016436783748151203)
                  ·
                    refine ⟨13730275524655175622226805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9153517016436783748151203 13730275524655175622226805)
                    ·
                      refine ⟨1287213330436422714583763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13730275524655175622226805 1287213330436422714583763)
                      ·
                        rfl

theorem cell23_2506839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_2506839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506839 prefixEnd_2506839 := by exact prefixLift 2506839
  have htrace : WordTrace (prefixWord ++ tailWord_2506839) baseStart_2506839 baseEnd_2506839 := by
    simpa [prefixWord, tailWord_2506839, baseEnd_2506839] using wordTrace_append hprefix tailTrace_2506839
  have hstable : (prefixWord ++ tailWord_2506839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506839).length < 2 ^ (prefixWord ++ tailWord_2506839).sum := by decide
  have hdescent : baseEnd_2506839 < baseStart_2506839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506849 : List Nat := [1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_2506849 : Nat := 118140960795 + 2506849 * 2 ^ 59
def prefixEnd_2506849 : Nat := 4983230072969 + 3 ^ 40 * 2506849 * 2
def baseEnd_2506849 : Nat := 1287218465242967675458717

theorem tailTrace_2506849 : CollatzResearch.WordTrace tailWord_2506849 prefixEnd_2506849 1287218465242967675458717 := by
  unfold tailWord_2506849
  simp only [CollatzResearch.WordTrace]
  refine ⟨91432294495121683568683601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60954862996747789045789067 91432294495121683568683601)
  ·
    refine ⟨68574220871341262676512701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91432294495121683568683601 68574220871341262676512701)
    ·
      refine ⟨25715332826752973503692263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68574220871341262676512701 25715332826752973503692263)
      ·
        refine ⟨38572999240129460255538395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25715332826752973503692263 38572999240129460255538395)
        ·
          refine ⟨57859498860194190383307593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38572999240129460255538395 57859498860194190383307593)
          ·
            refine ⟨43394624145145642787480695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57859498860194190383307593 43394624145145642787480695)
            ·
              refine ⟨65091936217718464181221043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43394624145145642787480695 65091936217718464181221043)
              ·
                refine ⟨97637904326577696271831565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65091936217718464181221043 97637904326577696271831565)
                ·
                  refine ⟨36614214122466636101936837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97637904326577696271831565 36614214122466636101936837)
                  ·
                    refine ⟨6865165147962494269113157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36614214122466636101936837 6865165147962494269113157)
                    ·
                      refine ⟨1287218465242967675458717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6865165147962494269113157 1287218465242967675458717)
                      ·
                        rfl

theorem cell23_2506849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_2506849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506849 prefixEnd_2506849 := by exact prefixLift 2506849
  have htrace : WordTrace (prefixWord ++ tailWord_2506849) baseStart_2506849 baseEnd_2506849 := by
    simpa [prefixWord, tailWord_2506849, baseEnd_2506849] using wordTrace_append hprefix tailTrace_2506849
  have hstable : (prefixWord ++ tailWord_2506849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506849).length < 2 ^ (prefixWord ++ tailWord_2506849).sum := by decide
  have hdescent : baseEnd_2506849 < baseStart_2506849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506853 : List Nat := [1, 3, 1, 3, 2, 2, 2, 2, 1, 4, 2]
def baseStart_2506853 : Nat := 118140960795 + 2506853 * 2 ^ 59
def prefixEnd_2506853 : Nat := 4983230072969 + 3 ^ 40 * 2506853 * 2
def baseEnd_2506853 : Nat := 1287220519165585659808699

theorem tailTrace_2506853 : CollatzResearch.WordTrace tailWord_2506853 prefixEnd_2506853 1287220519165585659808699 := by
  unfold tailWord_2506853
  simp only [CollatzResearch.WordTrace]
  refine ⟨91432440387107192251829213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60954960258071461501219475 91432440387107192251829213)
  ·
    refine ⟨34287165145165197094435955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91432440387107192251829213 34287165145165197094435955)
    ·
      refine ⟨51430747717747795641653933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34287165145165197094435955 51430747717747795641653933)
      ·
        refine ⟨19286530394155423365620225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51430747717747795641653933 19286530394155423365620225)
        ·
          refine ⟨14464897795616567524215169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19286530394155423365620225 14464897795616567524215169)
          ·
            refine ⟨10848673346712425643161377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14464897795616567524215169 10848673346712425643161377)
            ·
              refine ⟨8136505010034319232371033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10848673346712425643161377 8136505010034319232371033)
              ·
                refine ⟨6102378757525739424278275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8136505010034319232371033 6102378757525739424278275)
                ·
                  refine ⟨9153568136288609136417413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6102378757525739424278275 9153568136288609136417413)
                  ·
                    refine ⟨1716294025554114213078265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9153568136288609136417413 1716294025554114213078265)
                    ·
                      refine ⟨1287220519165585659808699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1716294025554114213078265 1287220519165585659808699)
                      ·
                        rfl

theorem cell23_2506853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_2506853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506853 prefixEnd_2506853 := by exact prefixLift 2506853
  have htrace : WordTrace (prefixWord ++ tailWord_2506853) baseStart_2506853 baseEnd_2506853 := by
    simpa [prefixWord, tailWord_2506853, baseEnd_2506853] using wordTrace_append hprefix tailTrace_2506853
  have hstable : (prefixWord ++ tailWord_2506853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506853).length < 2 ^ (prefixWord ++ tailWord_2506853).sum := by decide
  have hdescent : baseEnd_2506853 < baseStart_2506853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506866 : List Nat := [3, 2, 1, 2, 2, 2, 1, 2, 2, 2, 4]
def baseStart_2506866 : Nat := 118140960795 + 2506866 * 2 ^ 59
def prefixEnd_2506866 : Nat := 4983230072969 + 3 ^ 40 * 2506866 * 2
def baseEnd_2506866 : Nat := 1287227194414094108946139

theorem tailTrace_2506866 : CollatzResearch.WordTrace tailWord_2506866 prefixEnd_2506866 1287227194414094108946139 := by
  unfold tailWord_2506866
  simp only [CollatzResearch.WordTrace]
  refine ⟨22858228634015023868013113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60955276357373396981368301 22858228634015023868013113)
  ·
    refine ⟨17143671475511267901009835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22858228634015023868013113 17143671475511267901009835)
    ·
      refine ⟨25715507213266901851514753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17143671475511267901009835 25715507213266901851514753)
      ·
        refine ⟨19286630409950176388636065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25715507213266901851514753 19286630409950176388636065)
        ·
          refine ⟨14464972807462632291477049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19286630409950176388636065 14464972807462632291477049)
          ·
            refine ⟨10848729605596974218607787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14464972807462632291477049 10848729605596974218607787)
            ·
              refine ⟨16273094408395461327911681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10848729605596974218607787 16273094408395461327911681)
              ·
                refine ⟨12204820806296595995933761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16273094408395461327911681 12204820806296595995933761)
                ·
                  refine ⟨9153615604722446996950321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12204820806296595995933761 9153615604722446996950321)
                  ·
                    refine ⟨6865211703541835247712741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9153615604722446996950321 6865211703541835247712741)
                    ·
                      refine ⟨1287227194414094108946139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6865211703541835247712741 1287227194414094108946139)
                      ·
                        rfl

theorem cell23_2506866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_2506866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506866 prefixEnd_2506866 := by exact prefixLift 2506866
  have htrace : WordTrace (prefixWord ++ tailWord_2506866) baseStart_2506866 baseEnd_2506866 := by
    simpa [prefixWord, tailWord_2506866, baseEnd_2506866] using wordTrace_append hprefix tailTrace_2506866
  have hstable : (prefixWord ++ tailWord_2506866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506866).length < 2 ^ (prefixWord ++ tailWord_2506866).sum := by decide
  have hdescent : baseEnd_2506866 < baseStart_2506866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506876 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 7]
def baseStart_2506876 : Nat := 118140960795 + 2506876 * 2 ^ 59
def prefixEnd_2506876 : Nat := 4983230072969 + 3 ^ 40 * 2506876 * 2
def baseEnd_2506876 : Nat := 143025814357848785535677

theorem tailTrace_2506876 : CollatzResearch.WordTrace tailWord_2506876 prefixEnd_2506876 143025814357848785535677 := by
  unfold tailWord_2506876
  simp only [CollatzResearch.WordTrace]
  refine ⟨45716639633011933589958241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60955519510682578119944321 45716639633011933589958241)
  ·
    refine ⟨34287479724758950192468681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45716639633011933589958241 34287479724758950192468681)
    ·
      refine ⟨25715609793569212644351511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34287479724758950192468681 25715609793569212644351511)
      ·
        refine ⟨38573414690353818966527267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25715609793569212644351511 38573414690353818966527267)
        ·
          refine ⟨57860122035530728449790901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38573414690353818966527267 57860122035530728449790901)
          ·
            refine ⟨5424386440831005792167897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57860122035530728449790901 5424386440831005792167897)
            ·
              refine ⟨4068289830623254344125923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5424386440831005792167897 4068289830623254344125923)
              ·
                refine ⟨6102434745934881516188885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4068289830623254344125923 6102434745934881516188885)
                ·
                  refine ⟨143025814357848785535677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6102434745934881516188885 143025814357848785535677)
                  ·
                    rfl

theorem cell23_2506876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_2506876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506876 prefixEnd_2506876 := by exact prefixLift 2506876
  have htrace : WordTrace (prefixWord ++ tailWord_2506876) baseStart_2506876 baseEnd_2506876 := by
    simpa [prefixWord, tailWord_2506876, baseEnd_2506876] using wordTrace_append hprefix tailTrace_2506876
  have hstable : (prefixWord ++ tailWord_2506876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506876).length < 2 ^ (prefixWord ++ tailWord_2506876).sum := by decide
  have hdescent : baseEnd_2506876 < baseStart_2506876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506889 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 3, 7]
def baseStart_2506889 : Nat := 118140960795 + 2506889 * 2 ^ 59
def prefixEnd_2506889 : Nat := 4983230072969 + 3 ^ 40 * 2506889 * 2
def baseEnd_2506889 : Nat := 429079668156382506319511

theorem tailTrace_2506889 : CollatzResearch.WordTrace tailWord_2506889 prefixEnd_2506889 429079668156382506319511 := by
  unfold tailWord_2506889
  simp only [CollatzResearch.WordTrace]
  refine ⟨91433753414976770400139721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60955835609984513600093147 91433753414976770400139721)
  ·
    refine ⟨68575315061232577800104791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91433753414976770400139721 68575315061232577800104791)
    ·
      refine ⟨102862972591848866700157187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68575315061232577800104791 102862972591848866700157187)
      ·
        refine ⟨154294458887773300050235781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102862972591848866700157187 154294458887773300050235781)
        ·
          refine ⟨28930211041457493759419209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154294458887773300050235781 28930211041457493759419209)
          ·
            refine ⟨21697658281093120319564407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28930211041457493759419209 21697658281093120319564407)
            ·
              refine ⟨32546487421639680479346611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21697658281093120319564407 32546487421639680479346611)
              ·
                refine ⟨48819731132459520719019917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32546487421639680479346611 48819731132459520719019917)
                ·
                  refine ⟨18307399174672320269632469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48819731132459520719019917 18307399174672320269632469)
                  ·
                    refine ⟨429079668156382506319511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18307399174672320269632469 429079668156382506319511)
                    ·
                      rfl

theorem cell23_2506889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_2506889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506889 prefixEnd_2506889 := by exact prefixLift 2506889
  have htrace : WordTrace (prefixWord ++ tailWord_2506889) baseStart_2506889 baseEnd_2506889 := by
    simpa [prefixWord, tailWord_2506889, baseEnd_2506889] using wordTrace_append hprefix tailTrace_2506889
  have hstable : (prefixWord ++ tailWord_2506889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506889).length < 2 ^ (prefixWord ++ tailWord_2506889).sum := by decide
  have hdescent : baseEnd_2506889 < baseStart_2506889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506899 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 5]
def baseStart_2506899 : Nat := 118140960795 + 2506899 * 2 ^ 59
def prefixEnd_2506899 : Nat := 4983230072969 + 3 ^ 40 * 2506899 * 2
def baseEnd_2506899 : Nat := 1287244139275692479833487

theorem tailTrace_2506899 : CollatzResearch.WordTrace tailWord_2506899 prefixEnd_2506899 1287244139275692479833487 := by
  unfold tailWord_2506899
  simp only [CollatzResearch.WordTrace]
  refine ⟨91434118144940542108003751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60956078763293694738669167 91434118144940542108003751)
  ·
    refine ⟨137151177217410813162005627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91434118144940542108003751 137151177217410813162005627)
    ·
      refine ⟨205726765826116219743008441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137151177217410813162005627 205726765826116219743008441)
      ·
        refine ⟨154295074369587164807256331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205726765826116219743008441 154295074369587164807256331)
        ·
          refine ⟨231442611554380747210884497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154295074369587164807256331 231442611554380747210884497)
          ·
            refine ⟨173581958665785560408163373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231442611554380747210884497 173581958665785560408163373)
            ·
              refine ⟨65093234499669585153061265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173581958665785560408163373 65093234499669585153061265)
              ·
                refine ⟨48819925874752188864795949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65093234499669585153061265 48819925874752188864795949)
                ·
                  refine ⟨18307472203032070824298481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48819925874752188864795949 18307472203032070824298481)
                  ·
                    refine ⟨13730604152274053118223861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18307472203032070824298481 13730604152274053118223861)
                    ·
                      refine ⟨1287244139275692479833487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13730604152274053118223861 1287244139275692479833487)
                      ·
                        rfl

theorem cell23_2506899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 3, 2, 5].length) (baseStart_2506899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506899 prefixEnd_2506899 := by exact prefixLift 2506899
  have htrace : WordTrace (prefixWord ++ tailWord_2506899) baseStart_2506899 baseEnd_2506899 := by
    simpa [prefixWord, tailWord_2506899, baseEnd_2506899] using wordTrace_append hprefix tailTrace_2506899
  have hstable : (prefixWord ++ tailWord_2506899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506899).length < 2 ^ (prefixWord ++ tailWord_2506899).sum := by decide
  have hdescent : baseEnd_2506899 < baseStart_2506899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506978 : List Nat := [3, 3, 4, 1, 2, 1, 2, 2, 5]
def baseStart_2506978 : Nat := 118140960795 + 2506978 * 2 ^ 59
def prefixEnd_2506978 : Nat := 4983230072969 + 3 ^ 40 * 2506978 * 2
def baseEnd_2506978 : Nat := 143031633805266407860625

theorem tailTrace_2506978 : CollatzResearch.WordTrace tailWord_2506978 prefixEnd_2506978 143031633805266407860625 := by
  unfold tailWord_2506978
  simp only [CollatzResearch.WordTrace]
  refine ⟨22859249877913584650032397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60957999674436225733419725 22859249877913584650032397)
  ·
    refine ⟨8572218704217594243762149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22859249877913584650032397 8572218704217594243762149)
    ·
      refine ⟨1607291007040798920705403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8572218704217594243762149 1607291007040798920705403)
      ·
        refine ⟨2410936510561198381058105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607291007040798920705403 2410936510561198381058105)
        ·
          refine ⟨1808202382920898785793579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2410936510561198381058105 1808202382920898785793579)
          ·
            refine ⟨2712303574381348178690369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808202382920898785793579 2712303574381348178690369)
            ·
              refine ⟨2034227680786011134017777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712303574381348178690369 2034227680786011134017777)
              ·
                refine ⟨1525670760589508350513333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2034227680786011134017777 1525670760589508350513333)
                ·
                  refine ⟨143031633805266407860625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1525670760589508350513333 143031633805266407860625)
                  ·
                    rfl

theorem cell23_2506978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_2506978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506978 prefixEnd_2506978 := by exact prefixLift 2506978
  have htrace : WordTrace (prefixWord ++ tailWord_2506978) baseStart_2506978 baseEnd_2506978 := by
    simpa [prefixWord, tailWord_2506978, baseEnd_2506978] using wordTrace_append hprefix tailTrace_2506978
  have hstable : (prefixWord ++ tailWord_2506978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506978).length < 2 ^ (prefixWord ++ tailWord_2506978).sum := by decide
  have hdescent : baseEnd_2506978 < baseStart_2506978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506983 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 6]
def baseStart_2506983 : Nat := 118140960795 + 2506983 * 2 ^ 59
def prefixEnd_2506983 : Nat := 4983230072969 + 3 ^ 40 * 2506983 * 2
def baseEnd_2506983 : Nat := 143031919072296683464789

theorem tailTrace_2506983 : CollatzResearch.WordTrace tailWord_2506983 prefixEnd_2506983 143031919072296683464789 := by
  unfold tailWord_2506983
  simp only [CollatzResearch.WordTrace]
  refine ⟨91437181876636224454061603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60958121251090816302707735 91437181876636224454061603)
  ·
    refine ⟨137155772814954336681092405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91437181876636224454061603 137155772814954336681092405)
    ·
      refine ⟨12858353701401969063852413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137155772814954336681092405 12858353701401969063852413)
      ·
        refine ⟨4821882638025738398944655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12858353701401969063852413 4821882638025738398944655)
        ·
          refine ⟨7232823957038607598416983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821882638025738398944655 7232823957038607598416983)
          ·
            refine ⟨10849235935557911397625475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7232823957038607598416983 10849235935557911397625475)
            ·
              refine ⟨16273853903336867096438213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10849235935557911397625475 16273853903336867096438213)
              ·
                refine ⟨3051347606875662580582165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16273853903336867096438213 3051347606875662580582165)
                ·
                  refine ⟨143031919072296683464789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3051347606875662580582165 143031919072296683464789)
                  ·
                    rfl

theorem cell23_2506983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 6].length) (baseStart_2506983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506983 prefixEnd_2506983 := by exact prefixLift 2506983
  have htrace : WordTrace (prefixWord ++ tailWord_2506983) baseStart_2506983 baseEnd_2506983 := by
    simpa [prefixWord, tailWord_2506983, baseEnd_2506983] using wordTrace_append hprefix tailTrace_2506983
  have hstable : (prefixWord ++ tailWord_2506983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506983).length < 2 ^ (prefixWord ++ tailWord_2506983).sum := by decide
  have hdescent : baseEnd_2506983 < baseStart_2506983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2506986 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6]
def baseStart_2506986 : Nat := 118140960795 + 2506986 * 2 ^ 59
def prefixEnd_2506986 : Nat := 4983230072969 + 3 ^ 40 * 2506986 * 2
def baseEnd_2506986 : Nat := 1287288812092633639445587

theorem tailTrace_2506986 : CollatzResearch.WordTrace tailWord_2506986 prefixEnd_2506986 1287288812092633639445587 := by
  unfold tailWord_2506986
  simp only [CollatzResearch.WordTrace]
  refine ⟨22859322823906338991605203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60958194197083570644280541 22859322823906338991605203)
  ·
    refine ⟨34288984235859508487407805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22859322823906338991605203 34288984235859508487407805)
    ·
      refine ⟨12858369088447315682777927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34288984235859508487407805 12858369088447315682777927)
      ·
        refine ⟨19287553632670973524166891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12858369088447315682777927 19287553632670973524166891)
        ·
          refine ⟨28931330449006460286250337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19287553632670973524166891 28931330449006460286250337)
          ·
            refine ⟨21698497836754845214687753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28931330449006460286250337 21698497836754845214687753)
            ·
              refine ⟨16273873377566133911015815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21698497836754845214687753 16273873377566133911015815)
              ·
                refine ⟨24410810066349200866523723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16273873377566133911015815 24410810066349200866523723)
                ·
                  refine ⟨36616215099523801299785585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24410810066349200866523723 36616215099523801299785585)
                  ·
                    refine ⟨27462161324642850974839189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36616215099523801299785585 27462161324642850974839189)
                    ·
                      refine ⟨1287288812092633639445587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27462161324642850974839189 1287288812092633639445587)
                      ·
                        rfl

theorem cell23_2506986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6].length) (baseStart_2506986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2506986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2506986 prefixEnd_2506986 := by exact prefixLift 2506986
  have htrace : WordTrace (prefixWord ++ tailWord_2506986) baseStart_2506986 baseEnd_2506986 := by
    simpa [prefixWord, tailWord_2506986, baseEnd_2506986] using wordTrace_append hprefix tailTrace_2506986
  have hstable : (prefixWord ++ tailWord_2506986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2506986).length < 2 ^ (prefixWord ++ tailWord_2506986).sum := by decide
  have hdescent : baseEnd_2506986 < baseStart_2506986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2506986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507043 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 4, 4]
def baseStart_2507043 : Nat := 118140960795 + 2507043 * 2 ^ 59
def prefixEnd_2507043 : Nat := 4983230072969 + 3 ^ 40 * 2507043 * 2
def baseEnd_2507043 : Nat := 429106026829979972144275

theorem tailTrace_2507043 : CollatzResearch.WordTrace tailWord_2507043 prefixEnd_2507043 429106026829979972144275 := by
  unfold tailWord_2507043
  simp only [CollatzResearch.WordTrace]
  refine ⟨91439370256418854701245783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60959580170945903134163855 91439370256418854701245783)
  ·
    refine ⟨137159055384628282051868675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91439370256418854701245783 137159055384628282051868675)
    ·
      refine ⟨205738583076942423077803013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137159055384628282051868675 205738583076942423077803013)
      ·
        refine ⟨38575984326926704327088065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205738583076942423077803013 38575984326926704327088065)
        ·
          refine ⟨28931988245195028245316049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38575984326926704327088065 28931988245195028245316049)
          ·
            refine ⟨21698991183896271183987037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28931988245195028245316049 21698991183896271183987037)
            ·
              refine ⟨8137121693961101693995139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21698991183896271183987037 8137121693961101693995139)
              ·
                refine ⟨12205682540941652540992709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8137121693961101693995139 12205682540941652540992709)
                ·
                  refine ⟨2288565476426559851436133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12205682540941652540992709 2288565476426559851436133)
                  ·
                    refine ⟨429106026829979972144275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2288565476426559851436133 429106026829979972144275)
                    ·
                      rfl

theorem cell23_2507043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 4, 4].length) (baseStart_2507043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507043 prefixEnd_2507043 := by exact prefixLift 2507043
  have htrace : WordTrace (prefixWord ++ tailWord_2507043) baseStart_2507043 baseEnd_2507043 := by
    simpa [prefixWord, tailWord_2507043, baseEnd_2507043] using wordTrace_append hprefix tailTrace_2507043
  have hstable : (prefixWord ++ tailWord_2507043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507043).length < 2 ^ (prefixWord ++ tailWord_2507043).sum := by decide
  have hdescent : baseEnd_2507043 < baseStart_2507043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507060 : List Nat := [2, 5, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_2507060 : Nat := 118140960795 + 2507060 * 2 ^ 59
def prefixEnd_2507060 : Nat := 4983230072969 + 3 ^ 40 * 2507060 * 2
def baseEnd_2507060 : Nat := 429108936553688783306749

theorem tailTrace_2507060 : CollatzResearch.WordTrace tailWord_2507060 prefixEnd_2507060 429108936553688783306749 := by
  unfold tailWord_2507060
  simp only [CollatzResearch.WordTrace]
  refine ⟨45719995148678633302307317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60959993531571511069743089 45719995148678633302307317)
  ·
    refine ⟨4286249545188621872091311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45719995148678633302307317 4286249545188621872091311)
    ·
      refine ⟨6429374317782932808136967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4286249545188621872091311 6429374317782932808136967)
      ·
        refine ⟨9644061476674399212205451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6429374317782932808136967 9644061476674399212205451)
        ·
          refine ⟨14466092215011598818308177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9644061476674399212205451 14466092215011598818308177)
          ·
            refine ⟨10849569161258699113731133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14466092215011598818308177 10849569161258699113731133)
            ·
              refine ⟨4068588435472012167649175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10849569161258699113731133 4068588435472012167649175)
              ·
                refine ⟨6102882653208018251473763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4068588435472012167649175 6102882653208018251473763)
                ·
                  refine ⟨9154323979812027377210645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6102882653208018251473763 9154323979812027377210645)
                  ·
                    refine ⟨429108936553688783306749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9154323979812027377210645 429108936553688783306749)
                    ·
                      rfl

theorem cell23_2507060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_2507060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507060 prefixEnd_2507060 := by exact prefixLift 2507060
  have htrace : WordTrace (prefixWord ++ tailWord_2507060) baseStart_2507060 baseEnd_2507060 := by
    simpa [prefixWord, tailWord_2507060, baseEnd_2507060] using wordTrace_append hprefix tailTrace_2507060
  have hstable : (prefixWord ++ tailWord_2507060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507060).length < 2 ^ (prefixWord ++ tailWord_2507060).sum := by decide
  have hdescent : baseEnd_2507060 < baseStart_2507060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507117 : List Nat := [1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 3]
def baseStart_2507117 : Nat := 118140960795 + 2507117 * 2 ^ 59
def prefixEnd_2507117 : Nat := 4983230072969 + 3 ^ 40 * 2507117 * 2
def baseEnd_2507117 : Nat := 1287356078058372626907485

theorem tailTrace_2507117 : CollatzResearch.WordTrace tailWord_2507117 prefixEnd_2507117 1287356078058372626907485 := by
  unfold tailWord_2507117
  simp only [CollatzResearch.WordTrace]
  refine ⟨91442069258150765339439605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60961379505433843559626403 91442069258150765339439605)
  ·
    refine ⟨8572693992951634250572463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91442069258150765339439605 8572693992951634250572463)
    ·
      refine ⟨12859040989427451375858695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8572693992951634250572463 12859040989427451375858695)
      ·
        refine ⟨19288561484141177063788043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12859040989427451375858695 19288561484141177063788043)
        ·
          refine ⟨28932842226211765595682065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19288561484141177063788043 28932842226211765595682065)
          ·
            refine ⟨21699631669658824196761549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28932842226211765595682065 21699631669658824196761549)
            ·
              refine ⟨8137361876122059073785581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21699631669658824196761549 8137361876122059073785581)
              ·
                refine ⟨3051510703545772152669593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8137361876122059073785581 3051510703545772152669593)
                ·
                  refine ⟨2288633027659329114502195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051510703545772152669593 2288633027659329114502195)
                  ·
                    refine ⟨3432949541488993671753293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2288633027659329114502195 3432949541488993671753293)
                    ·
                      refine ⟨1287356078058372626907485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3432949541488993671753293 1287356078058372626907485)
                      ·
                        rfl

theorem cell23_2507117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_2507117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507117 prefixEnd_2507117 := by exact prefixLift 2507117
  have htrace : WordTrace (prefixWord ++ tailWord_2507117) baseStart_2507117 baseEnd_2507117 := by
    simpa [prefixWord, tailWord_2507117, baseEnd_2507117] using wordTrace_append hprefix tailTrace_2507117
  have hstable : (prefixWord ++ tailWord_2507117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507117).length < 2 ^ (prefixWord ++ tailWord_2507117).sum := by decide
  have hdescent : baseEnd_2507117 < baseStart_2507117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507143 : List Nat := [1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 5]
def baseStart_2507143 : Nat := 118140960795 + 2507143 * 2 ^ 59
def prefixEnd_2507143 : Nat := 4983230072969 + 3 ^ 40 * 2507143 * 2
def baseEnd_2507143 : Nat := 1287369428555389525182365

theorem tailTrace_2507143 : CollatzResearch.WordTrace tailWord_2507143 prefixEnd_2507143 1287369428555389525182365 := by
  unfold tailWord_2507143
  simp only [CollatzResearch.WordTrace]
  refine ⟨91443017556056571779886083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60962011704037714519924055 91443017556056571779886083)
  ·
    refine ⟨137164526334084857669829125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91443017556056571779886083 137164526334084857669829125)
    ·
      refine ⟨25718348687640910813092961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137164526334084857669829125 25718348687640910813092961)
      ·
        refine ⟨19288761515730683109819721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25718348687640910813092961 19288761515730683109819721)
        ·
          refine ⟨14466571136798012332364791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19288761515730683109819721 14466571136798012332364791)
          ·
            refine ⟨21699856705197018498547187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14466571136798012332364791 21699856705197018498547187)
            ·
              refine ⟨32549785057795527747820781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21699856705197018498547187 32549785057795527747820781)
              ·
                refine ⟨12206169396673322905432793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32549785057795527747820781 12206169396673322905432793)
                ·
                  refine ⟨9154627047504992179074595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12206169396673322905432793 9154627047504992179074595)
                  ·
                    refine ⟨13731940571257488268611893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9154627047504992179074595 13731940571257488268611893)
                    ·
                      refine ⟨1287369428555389525182365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13731940571257488268611893 1287369428555389525182365)
                      ·
                        rfl

theorem cell23_2507143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_2507143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507143 prefixEnd_2507143 := by exact prefixLift 2507143
  have htrace : WordTrace (prefixWord ++ tailWord_2507143) baseStart_2507143 baseEnd_2507143 := by
    simpa [prefixWord, tailWord_2507143, baseEnd_2507143] using wordTrace_append hprefix tailTrace_2507143
  have hstable : (prefixWord ++ tailWord_2507143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507143).length < 2 ^ (prefixWord ++ tailWord_2507143).sum := by decide
  have hdescent : baseEnd_2507143 < baseStart_2507143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507144 : List Nat := [2, 1, 3, 3, 1, 1, 5, 1, 1, 3, 2]
def baseStart_2507144 : Nat := 118140960795 + 2507144 * 2 ^ 59
def prefixEnd_2507144 : Nat := 4983230072969 + 3 ^ 40 * 2507144 * 2
def baseEnd_2507144 : Nat := 1287369942036044021269861

theorem tailTrace_2507144 : CollatzResearch.WordTrace tailWord_2507144 prefixEnd_2507144 1287369942036044021269861 := by
  unfold tailWord_2507144
  simp only [CollatzResearch.WordTrace]
  refine ⟨45721527014526474475336243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60962036019368632633781657 45721527014526474475336243)
  ·
    refine ⟨68582290521789711713004365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45721527014526474475336243 68582290521789711713004365)
    ·
      refine ⟨25718358945671141892376637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68582290521789711713004365 25718358945671141892376637)
      ·
        refine ⟨9644384604626678209641239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25718358945671141892376637 9644384604626678209641239)
        ·
          refine ⟨14466576906940017314461859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9644384604626678209641239 14466576906940017314461859)
          ·
            refine ⟨21699865360410025971692789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14466576906940017314461859 21699865360410025971692789)
            ·
              refine ⟨2034362377538439934846199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21699865360410025971692789 2034362377538439934846199)
              ·
                refine ⟨3051543566307659902269299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034362377538439934846199 3051543566307659902269299)
                ·
                  refine ⟨4577315349461489853403949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051543566307659902269299 4577315349461489853403949)
                  ·
                    refine ⟨1716493256048058695026481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4577315349461489853403949 1716493256048058695026481)
                    ·
                      refine ⟨1287369942036044021269861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1716493256048058695026481 1287369942036044021269861)
                      ·
                        rfl

theorem cell23_2507144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_2507144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507144 prefixEnd_2507144 := by exact prefixLift 2507144
  have htrace : WordTrace (prefixWord ++ tailWord_2507144) baseStart_2507144 baseEnd_2507144 := by
    simpa [prefixWord, tailWord_2507144, baseEnd_2507144] using wordTrace_append hprefix tailTrace_2507144
  have hstable : (prefixWord ++ tailWord_2507144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507144).length < 2 ^ (prefixWord ++ tailWord_2507144).sum := by decide
  have hdescent : baseEnd_2507144 < baseStart_2507144 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507160 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2507160 : Nat := 118140960795 + 2507160 * 2 ^ 59
def prefixEnd_2507160 : Nat := 4983230072969 + 3 ^ 40 * 2507160 * 2
def baseEnd_2507160 : Nat := 1287378157726515958669787

theorem tailTrace_2507160 : CollatzResearch.WordTrace tailWord_2507160 prefixEnd_2507160 1287378157726515958669787 := by
  unfold tailWord_2507160
  simp only [CollatzResearch.WordTrace]
  refine ⟨45721818798497491841627467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60962425064663322455503289 45721818798497491841627467)
  ·
    refine ⟨68582728197746237762441201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45721818798497491841627467 68582728197746237762441201)
    ·
      refine ⟨51437046148309678321830901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68582728197746237762441201 51437046148309678321830901)
      ·
        refine ⟨4822223076404032342671647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51437046148309678321830901 4822223076404032342671647)
        ·
          refine ⟨7233334614606048514007471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4822223076404032342671647 7233334614606048514007471)
          ·
            refine ⟨10850001921909072771011207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7233334614606048514007471 10850001921909072771011207)
            ·
              refine ⟨16275002882863609156516811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10850001921909072771011207 16275002882863609156516811)
              ·
                refine ⟨24412504324295413734775217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16275002882863609156516811 24412504324295413734775217)
                ·
                  refine ⟨18309378243221560301081413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24412504324295413734775217 18309378243221560301081413)
                  ·
                    refine ⟨3433008420604042556452765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18309378243221560301081413 3433008420604042556452765)
                    ·
                      refine ⟨1287378157726515958669787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3433008420604042556452765 1287378157726515958669787)
                      ·
                        rfl

theorem cell23_2507160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2507160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507160 prefixEnd_2507160 := by exact prefixLift 2507160
  have htrace : WordTrace (prefixWord ++ tailWord_2507160) baseStart_2507160 baseEnd_2507160 := by
    simpa [prefixWord, tailWord_2507160, baseEnd_2507160] using wordTrace_append hprefix tailTrace_2507160
  have hstable : (prefixWord ++ tailWord_2507160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507160).length < 2 ^ (prefixWord ++ tailWord_2507160).sum := by decide
  have hdescent : baseEnd_2507160 < baseStart_2507160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507170 : List Nat := [3, 3, 1, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_2507170 : Nat := 118140960795 + 2507170 * 2 ^ 59
def prefixEnd_2507170 : Nat := 4983230072969 + 3 ^ 40 * 2507170 * 2
def baseEnd_2507170 : Nat := 1287383292533060919544741

theorem tailTrace_2507170 : CollatzResearch.WordTrace tailWord_2507170 prefixEnd_2507170 1287383292533060919544741 := by
  unfold tailWord_2507170
  simp only [CollatzResearch.WordTrace]
  refine ⟨22861000581739688847779741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60962668217972503594079309 22861000581739688847779741)
  ·
    refine ⟨8572875218152383317917403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22861000581739688847779741 8572875218152383317917403)
    ·
      refine ⟨12859312827228574976876105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8572875218152383317917403 12859312827228574976876105)
      ·
        refine ⟨9644484620421431232657079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12859312827228574976876105 9644484620421431232657079)
        ·
          refine ⟨14466726930632146848985619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9644484620421431232657079 14466726930632146848985619)
          ·
            refine ⟨21700090395948220273478429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14466726930632146848985619 21700090395948220273478429)
            ·
              refine ⟨8137533898480582602554411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21700090395948220273478429 8137533898480582602554411)
              ·
                refine ⟨12206300847720873903831617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8137533898480582602554411 12206300847720873903831617)
                ·
                  refine ⟨9154725635790655427873713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12206300847720873903831617 9154725635790655427873713)
                  ·
                    refine ⟨6866044226842991570905285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9154725635790655427873713 6866044226842991570905285)
                    ·
                      refine ⟨1287383292533060919544741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6866044226842991570905285 1287383292533060919544741)
                      ·
                        rfl

theorem cell23_2507170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_2507170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507170 prefixEnd_2507170 := by exact prefixLift 2507170
  have htrace : WordTrace (prefixWord ++ tailWord_2507170) baseStart_2507170 baseEnd_2507170 := by
    simpa [prefixWord, tailWord_2507170, baseEnd_2507170] using wordTrace_append hprefix tailTrace_2507170
  have hstable : (prefixWord ++ tailWord_2507170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507170).length < 2 ^ (prefixWord ++ tailWord_2507170).sum := by decide
  have hdescent : baseEnd_2507170 < baseStart_2507170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507197 : List Nat := [1, 4, 1, 2, 2, 3, 2, 3, 5]
def baseStart_2507197 : Nat := 118140960795 + 2507197 * 2 ^ 59
def prefixEnd_2507197 : Nat := 4983230072969 + 3 ^ 40 * 2507197 * 2
def baseEnd_2507197 : Nat := 143044128501192479323013

theorem tailTrace_2507197 : CollatzResearch.WordTrace tailWord_2507197 prefixEnd_2507197 143044128501192479323013 := by
  unfold tailWord_2507197
  simp only [CollatzResearch.WordTrace]
  refine ⟨91444987097860939002351845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60963324731907292668234563 91444987097860939002351845)
  ·
    refine ⟨17145935080848926062940971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91444987097860939002351845 17145935080848926062940971)
    ·
      refine ⟨25718902621273389094411457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17145935080848926062940971 25718902621273389094411457)
      ·
        refine ⟨19289176965955041820808593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25718902621273389094411457 19289176965955041820808593)
        ·
          refine ⟨14466882724466281365606445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19289176965955041820808593 14466882724466281365606445)
          ·
            refine ⟨5425081021674855512102417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14466882724466281365606445 5425081021674855512102417)
            ·
              refine ⟨4068810766256141634076813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5425081021674855512102417 4068810766256141634076813)
              ·
                refine ⟨1525804037346053112778805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4068810766256141634076813 1525804037346053112778805)
                ·
                  refine ⟨143044128501192479323013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1525804037346053112778805 143044128501192479323013)
                  ·
                    rfl

theorem cell23_2507197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 3, 5].length) (baseStart_2507197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507197 prefixEnd_2507197 := by exact prefixLift 2507197
  have htrace : WordTrace (prefixWord ++ tailWord_2507197) baseStart_2507197 baseEnd_2507197 := by
    simpa [prefixWord, tailWord_2507197, baseEnd_2507197] using wordTrace_append hprefix tailTrace_2507197
  have hstable : (prefixWord ++ tailWord_2507197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507197).length < 2 ^ (prefixWord ++ tailWord_2507197).sum := by decide
  have hdescent : baseEnd_2507197 < baseStart_2507197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507243 : List Nat := [1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 4]
def baseStart_2507243 : Nat := 118140960795 + 2507243 * 2 ^ 59
def prefixEnd_2507243 : Nat := 4983230072969 + 3 ^ 40 * 2507243 * 2
def baseEnd_2507243 : Nat := 1287420776620839133931905

theorem tailTrace_2507243 : CollatzResearch.WordTrace tailWord_2507243 prefixEnd_2507243 1287420776620839133931905 := by
  unfold tailWord_2507243
  simp only [CollatzResearch.WordTrace]
  refine ⟨91446664855694288858526383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60964443237129525905684255 91446664855694288858526383)
  ·
    refine ⟨137169997283541433287789575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91446664855694288858526383 137169997283541433287789575)
    ·
      refine ⟨205754995925312149931684363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137169997283541433287789575 205754995925312149931684363)
      ·
        refine ⟨308632493887968224897526545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205754995925312149931684363 308632493887968224897526545)
        ·
          refine ⟨231474370415976168673144909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308632493887968224897526545 231474370415976168673144909)
          ·
            refine ⟨86802888905991063252429341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231474370415976168673144909 86802888905991063252429341)
            ·
              refine ⟨32551083339746648719661003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86802888905991063252429341 32551083339746648719661003)
              ·
                refine ⟨48826625009619973079491505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32551083339746648719661003 48826625009619973079491505)
                ·
                  refine ⟨36619968757214979809618629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48826625009619973079491505 36619968757214979809618629)
                  ·
                    refine ⟨6866244141977808714303493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36619968757214979809618629 6866244141977808714303493)
                    ·
                      refine ⟨1287420776620839133931905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6866244141977808714303493 1287420776620839133931905)
                      ·
                        rfl

theorem cell23_2507243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 4].length) (baseStart_2507243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507243 prefixEnd_2507243 := by exact prefixLift 2507243
  have htrace : WordTrace (prefixWord ++ tailWord_2507243) baseStart_2507243 baseEnd_2507243 := by
    simpa [prefixWord, tailWord_2507243, baseEnd_2507243] using wordTrace_append hprefix tailTrace_2507243
  have hstable : (prefixWord ++ tailWord_2507243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507243).length < 2 ^ (prefixWord ++ tailWord_2507243).sum := by decide
  have hdescent : baseEnd_2507243 < baseStart_2507243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507273 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 6]
def baseStart_2507273 : Nat := 118140960795 + 2507273 * 2 ^ 59
def prefixEnd_2507273 : Nat := 4983230072969 + 3 ^ 40 * 2507273 * 2
def baseEnd_2507273 : Nat := 1287436181040474016556767

theorem tailTrace_2507273 : CollatzResearch.WordTrace tailWord_2507273 prefixEnd_2507273 1287436181040474016556767 := by
  unfold tailWord_2507273
  simp only [CollatzResearch.WordTrace]
  refine ⟨91447759045585603982118473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60965172697057069321412315 91447759045585603982118473)
  ·
    refine ⟨68585819284189202986588855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91447759045585603982118473 68585819284189202986588855)
    ·
      refine ⟨102878728926283804479883283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68585819284189202986588855 102878728926283804479883283)
      ·
        refine ⟨154318093389425706719824925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102878728926283804479883283 154318093389425706719824925)
        ·
          refine ⟨57869285021034640019934347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154318093389425706719824925 57869285021034640019934347)
          ·
            refine ⟨86803927531551960029901521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57869285021034640019934347 86803927531551960029901521)
            ·
              refine ⟨65102945648663970022426141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86803927531551960029901521 65102945648663970022426141)
              ·
                refine ⟨24413604618248988758409803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65102945648663970022426141 24413604618248988758409803)
                ·
                  refine ⟨36620406927373483137614705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24413604618248988758409803 36620406927373483137614705)
                  ·
                    refine ⟨27465305195530112353211029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36620406927373483137614705 27465305195530112353211029)
                    ·
                      refine ⟨1287436181040474016556767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27465305195530112353211029 1287436181040474016556767)
                      ·
                        rfl

theorem cell23_2507273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 2, 6].length) (baseStart_2507273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507273 prefixEnd_2507273 := by exact prefixLift 2507273
  have htrace : WordTrace (prefixWord ++ tailWord_2507273) baseStart_2507273 baseEnd_2507273 := by
    simpa [prefixWord, tailWord_2507273, baseEnd_2507273] using wordTrace_append hprefix tailTrace_2507273
  have hstable : (prefixWord ++ tailWord_2507273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507273).length < 2 ^ (prefixWord ++ tailWord_2507273).sum := by decide
  have hdescent : baseEnd_2507273 < baseStart_2507273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507297 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 3]
def baseStart_2507297 : Nat := 118140960795 + 2507297 * 2 ^ 59
def prefixEnd_2507297 : Nat := 4983230072969 + 3 ^ 40 * 2507297 * 2
def baseEnd_2507297 : Nat := 1287448504576181922656657

theorem tailTrace_2507297 : CollatzResearch.WordTrace tailWord_2507297 prefixEnd_2507297 1287448504576181922656657 := by
  unfold tailWord_2507297
  simp only [CollatzResearch.WordTrace]
  refine ⟨91448634397498656080992145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60965756264999104053994763 91448634397498656080992145)
  ·
    refine ⟨68586475798123992060744109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91448634397498656080992145 68586475798123992060744109)
    ·
      refine ⟨25719928424296497022779041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68586475798123992060744109 25719928424296497022779041)
      ·
        refine ⟨19289946318222372767084281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25719928424296497022779041 19289946318222372767084281)
        ·
          refine ⟨14467459738666779575313211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19289946318222372767084281 14467459738666779575313211)
          ·
            refine ⟨21701189608000169362969817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14467459738666779575313211 21701189608000169362969817)
            ·
              refine ⟨16275892206000127022227363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21701189608000169362969817 16275892206000127022227363)
              ·
                refine ⟨24413838309000190533341045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16275892206000127022227363 24413838309000190533341045)
                ·
                  refine ⟨2288797341468767862500723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24413838309000190533341045 2288797341468767862500723)
                  ·
                    refine ⟨3433196012203151793751085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2288797341468767862500723 3433196012203151793751085)
                    ·
                      refine ⟨1287448504576181922656657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3433196012203151793751085 1287448504576181922656657)
                      ·
                        rfl

theorem cell23_2507297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_2507297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507297 prefixEnd_2507297 := by exact prefixLift 2507297
  have htrace : WordTrace (prefixWord ++ tailWord_2507297) baseStart_2507297 baseEnd_2507297 := by
    simpa [prefixWord, tailWord_2507297, baseEnd_2507297] using wordTrace_append hprefix tailTrace_2507297
  have hstable : (prefixWord ++ tailWord_2507297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507297).length < 2 ^ (prefixWord ++ tailWord_2507297).sum := by decide
  have hdescent : baseEnd_2507297 < baseStart_2507297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507324 : List Nat := [2, 2, 2, 2, 3, 1, 2, 2, 2, 3, 2]
def baseStart_2507324 : Nat := 118140960795 + 2507324 * 2 ^ 59
def prefixEnd_2507324 : Nat := 4983230072969 + 3 ^ 40 * 2507324 * 2
def baseEnd_2507324 : Nat := 1287462368553853317019033

theorem tailTrace_2507324 : CollatzResearch.WordTrace tailWord_2507324 prefixEnd_2507324 1287462368553853317019033 := by
  unfold tailWord_2507324
  simp only [CollatzResearch.WordTrace]
  refine ⟨45724809584200419846112513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60966412778933893128150017 45724809584200419846112513)
  ·
    refine ⟨34293607188150314884584385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45724809584200419846112513 34293607188150314884584385)
    ·
      refine ⟨25720205391112736163438289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34293607188150314884584385 25720205391112736163438289)
      ·
        refine ⟨19290154043334552122578717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25720205391112736163438289 19290154043334552122578717)
        ·
          refine ⟨7233807766250457045967019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19290154043334552122578717 7233807766250457045967019)
          ·
            refine ⟨10850711649375685568950529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7233807766250457045967019 10850711649375685568950529)
            ·
              refine ⟨8138033737031764176712897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10850711649375685568950529 8138033737031764176712897)
              ·
                refine ⟨6103525302773823132534673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8138033737031764176712897 6103525302773823132534673)
                ·
                  refine ⟨4577643977080367349401005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6103525302773823132534673 4577643977080367349401005)
                  ·
                    refine ⟨1716616491405137756025377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4577643977080367349401005 1716616491405137756025377)
                    ·
                      refine ⟨1287462368553853317019033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1716616491405137756025377 1287462368553853317019033)
                      ·
                        rfl

theorem cell23_2507324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 2, 2, 2, 3, 2].length) (baseStart_2507324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507324 prefixEnd_2507324 := by exact prefixLift 2507324
  have htrace : WordTrace (prefixWord ++ tailWord_2507324) baseStart_2507324 baseEnd_2507324 := by
    simpa [prefixWord, tailWord_2507324, baseEnd_2507324] using wordTrace_append hprefix tailTrace_2507324
  have hstable : (prefixWord ++ tailWord_2507324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507324).length < 2 ^ (prefixWord ++ tailWord_2507324).sum := by decide
  have hdescent : baseEnd_2507324 < baseStart_2507324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507334 : List Nat := [6, 1, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_2507334 : Nat := 118140960795 + 2507334 * 2 ^ 59
def prefixEnd_2507334 : Nat := 4983230072969 + 3 ^ 40 * 2507334 * 2
def baseEnd_2507334 : Nat := 429155834453466092631329

theorem tailTrace_2507334 : CollatzResearch.WordTrace tailWord_2507334 prefixEnd_2507334 429155834453466092631329 := by
  unfold tailWord_2507334
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857811996823894106252783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60966655932243074266726037 2857811996823894106252783)
  ·
    refine ⟨4286717995235841159379175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2857811996823894106252783 4286717995235841159379175)
    ·
      refine ⟨6430076992853761739068763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4286717995235841159379175 6430076992853761739068763)
      ·
        refine ⟨9645115489280642608603145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6430076992853761739068763 9645115489280642608603145)
        ·
          refine ⟨7233836616960481956452359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9645115489280642608603145 7233836616960481956452359)
          ·
            refine ⟨10850754925440722934678539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7233836616960481956452359 10850754925440722934678539)
            ·
              refine ⟨16276132388161084402017809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10850754925440722934678539 16276132388161084402017809)
              ·
                refine ⟨12207099291120813301513357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16276132388161084402017809 12207099291120813301513357)
                ·
                  refine ⟨4577662234170304988067509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12207099291120813301513357 4577662234170304988067509)
                  ·
                    refine ⟨429155834453466092631329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4577662234170304988067509 429155834453466092631329)
                    ·
                      rfl

theorem cell23_2507334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_2507334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507334 prefixEnd_2507334 := by exact prefixLift 2507334
  have htrace : WordTrace (prefixWord ++ tailWord_2507334) baseStart_2507334 baseEnd_2507334 := by
    simpa [prefixWord, tailWord_2507334, baseEnd_2507334] using wordTrace_append hprefix tailTrace_2507334
  have hstable : (prefixWord ++ tailWord_2507334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507334).length < 2 ^ (prefixWord ++ tailWord_2507334).sum := by decide
  have hdescent : baseEnd_2507334 < baseStart_2507334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507340 : List Nat := [2, 2, 1, 3, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2507340 : Nat := 118140960795 + 2507340 * 2 ^ 59
def prefixEnd_2507340 : Nat := 4983230072969 + 3 ^ 40 * 2507340 * 2
def baseEnd_2507340 : Nat := 1287470584244325254418959

theorem tailTrace_2507340 : CollatzResearch.WordTrace tailWord_2507340 prefixEnd_2507340 1287470584244325254418959 := by
  unfold tailWord_2507340
  simp only [CollatzResearch.WordTrace]
  refine ⟨45725101368171437212403737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60966801824228582949871649 45725101368171437212403737)
  ·
    refine ⟨34293826026128577909302803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45725101368171437212403737 34293826026128577909302803)
    ·
      refine ⟨51440739039192866863954205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34293826026128577909302803 51440739039192866863954205)
      ·
        refine ⟨19290277139697325073982827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51440739039192866863954205 19290277139697325073982827)
        ·
          refine ⟨28935415709545987610974241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19290277139697325073982827 28935415709545987610974241)
          ·
            refine ⟨21701561782159490708230681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28935415709545987610974241 21701561782159490708230681)
            ·
              refine ⟨16276171336619618031173011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21701561782159490708230681 16276171336619618031173011)
              ·
                refine ⟨24414257004929427046759517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16276171336619618031173011 24414257004929427046759517)
                ·
                  refine ⟨9155346376848535142534819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24414257004929427046759517 9155346376848535142534819)
                  ·
                    refine ⟨13733019565272802713802229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9155346376848535142534819 13733019565272802713802229)
                    ·
                      refine ⟨1287470584244325254418959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13733019565272802713802229 1287470584244325254418959)
                      ·
                        rfl

theorem cell23_2507340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2507340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507340 prefixEnd_2507340 := by exact prefixLift 2507340
  have htrace : WordTrace (prefixWord ++ tailWord_2507340) baseStart_2507340 baseEnd_2507340 := by
    simpa [prefixWord, tailWord_2507340, baseEnd_2507340] using wordTrace_append hprefix tailTrace_2507340
  have hstable : (prefixWord ++ tailWord_2507340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507340).length < 2 ^ (prefixWord ++ tailWord_2507340).sum := by decide
  have hdescent : baseEnd_2507340 < baseStart_2507340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507368 : List Nat := [2, 1, 4, 3, 3, 1, 2, 1, 1, 5]
def baseStart_2507368 : Nat := 118140960795 + 2507368 * 2 ^ 59
def prefixEnd_2507368 : Nat := 4983230072969 + 3 ^ 40 * 2507368 * 2
def baseEnd_2507368 : Nat := 429161653900883714956277

theorem tailTrace_2507368 : CollatzResearch.WordTrace tailWord_2507368 prefixEnd_2507368 429161653900883714956277 := by
  unfold tailWord_2507368
  simp only [CollatzResearch.WordTrace]
  refine ⟨45725611990120717603413379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60967482653494290137884505 45725611990120717603413379)
  ·
    refine ⟨68588417985181076405120069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45725611990120717603413379 68588417985181076405120069)
    ·
      refine ⟨12860328372221451825960013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68588417985181076405120069 12860328372221451825960013)
      ·
        refine ⟨4822623139583044434735005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12860328372221451825960013 4822623139583044434735005)
        ·
          refine ⟨1808483677343641663025627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4822623139583044434735005 1808483677343641663025627)
          ·
            refine ⟨2712725516015462494538441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808483677343641663025627 2712725516015462494538441)
            ·
              refine ⟨2034544137011596870903831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2712725516015462494538441 2034544137011596870903831)
              ·
                refine ⟨3051816205517395306355747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034544137011596870903831 3051816205517395306355747)
                ·
                  refine ⟨4577724308276092959533621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3051816205517395306355747 4577724308276092959533621)
                  ·
                    refine ⟨429161653900883714956277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4577724308276092959533621 429161653900883714956277)
                    ·
                      rfl

theorem cell23_2507368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_2507368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507368 prefixEnd_2507368 := by exact prefixLift 2507368
  have htrace : WordTrace (prefixWord ++ tailWord_2507368) baseStart_2507368 baseEnd_2507368 := by
    simpa [prefixWord, tailWord_2507368, baseEnd_2507368] using wordTrace_append hprefix tailTrace_2507368
  have hstable : (prefixWord ++ tailWord_2507368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507368).length < 2 ^ (prefixWord ++ tailWord_2507368).sum := by decide
  have hdescent : baseEnd_2507368 < baseStart_2507368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507497 : List Nat := [1, 2, 1, 1, 1, 2, 6, 2, 2, 5]
def baseStart_2507497 : Nat := 118140960795 + 2507497 * 2 ^ 59
def prefixEnd_2507497 : Nat := 4983230072969 + 3 ^ 40 * 2507497 * 2
def baseEnd_2507497 : Nat := 429183733569027046718579

theorem tailTrace_2507497 : CollatzResearch.WordTrace tailWord_2507497 prefixEnd_2507497 429183733569027046718579 := by
  unfold tailWord_2507497
  simp only [CollatzResearch.WordTrace]
  refine ⟨91455928996774090238272745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60970619331182726825515163 91455928996774090238272745)
  ·
    refine ⟨68591946747580567678704559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91455928996774090238272745 68591946747580567678704559)
    ·
      refine ⟨102887920121370851518056839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68591946747580567678704559 102887920121370851518056839)
      ·
        refine ⟨154331880182056277277085259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102887920121370851518056839 154331880182056277277085259)
        ·
          refine ⟨231497820273084415915627889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154331880182056277277085259 231497820273084415915627889)
          ·
            refine ⟨173623365204813311936720917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231497820273084415915627889 173623365204813311936720917)
            ·
              refine ⟨8138595243975623997033793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173623365204813311936720917 8138595243975623997033793)
              ·
                refine ⟨6103946432981717997775345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8138595243975623997033793 6103946432981717997775345)
                ·
                  refine ⟨4577959824736288498331509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6103946432981717997775345 4577959824736288498331509)
                  ·
                    refine ⟨429183733569027046718579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4577959824736288498331509 429183733569027046718579)
                    ·
                      rfl

theorem cell23_2507497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 5].length) (baseStart_2507497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507497 prefixEnd_2507497 := by exact prefixLift 2507497
  have htrace : WordTrace (prefixWord ++ tailWord_2507497) baseStart_2507497 baseEnd_2507497 := by
    simpa [prefixWord, tailWord_2507497, baseEnd_2507497] using wordTrace_append hprefix tailTrace_2507497
  have hstable : (prefixWord ++ tailWord_2507497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507497).length < 2 ^ (prefixWord ++ tailWord_2507497).sum := by decide
  have hdescent : baseEnd_2507497 < baseStart_2507497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507508 : List Nat := [2, 6, 1, 1, 2, 1, 1, 1, 2, 2, 4]
def baseStart_2507508 : Nat := 118140960795 + 2507508 * 2 ^ 59
def prefixEnd_2507508 : Nat := 4983230072969 + 3 ^ 40 * 2507508 * 2
def baseEnd_2507508 : Nat := 1287556848994280597118187

theorem tailTrace_2507508 : CollatzResearch.WordTrace tailWord_2507508 prefixEnd_2507508 1287556848994280597118187 := by
  unfold tailWord_2507508
  simp only [CollatzResearch.WordTrace]
  refine ⟨45728165099867119558461589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60970886799822826077948785 45728165099867119558461589)
  ·
    refine ⟨2143507739056271229302887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45728165099867119558461589 2143507739056271229302887)
    ·
      refine ⟨3215261608584406843954331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2143507739056271229302887 3215261608584406843954331)
      ·
        refine ⟨4822892412876610265931497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3215261608584406843954331 4822892412876610265931497)
        ·
          refine ⟨3617169309657457699448623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4822892412876610265931497 3617169309657457699448623)
          ·
            refine ⟨5425753964486186549172935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617169309657457699448623 5425753964486186549172935)
            ·
              refine ⟨8138630946729279823759403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5425753964486186549172935 8138630946729279823759403)
              ·
                refine ⟨12207946420093919735639105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8138630946729279823759403 12207946420093919735639105)
                ·
                  refine ⟨9155959815070439801729329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12207946420093919735639105 9155959815070439801729329)
                  ·
                    refine ⟨6866969861302829851296997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9155959815070439801729329 6866969861302829851296997)
                    ·
                      refine ⟨1287556848994280597118187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6866969861302829851296997 1287556848994280597118187)
                      ·
                        rfl

theorem cell23_2507508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_2507508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507508 prefixEnd_2507508 := by exact prefixLift 2507508
  have htrace : WordTrace (prefixWord ++ tailWord_2507508) baseStart_2507508 baseEnd_2507508 := by
    simpa [prefixWord, tailWord_2507508, baseEnd_2507508] using wordTrace_append hprefix tailTrace_2507508
  have hstable : (prefixWord ++ tailWord_2507508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507508).length < 2 ^ (prefixWord ++ tailWord_2507508).sum := by decide
  have hdescent : baseEnd_2507508 < baseStart_2507508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507517 : List Nat := [1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 4]
def baseStart_2507517 : Nat := 118140960795 + 2507517 * 2 ^ 59
def prefixEnd_2507517 : Nat := 4983230072969 + 3 ^ 40 * 2507517 * 2
def baseEnd_2507517 : Nat := 1287561470320171061905645

theorem tailTrace_2507517 : CollatzResearch.WordTrace tailWord_2507517 prefixEnd_2507517 1287561470320171061905645 := by
  unfold tailWord_2507517
  simp only [CollatzResearch.WordTrace]
  refine ⟨91456658456701633654000805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60971105637801089102667203 91456658456701633654000805)
  ·
    refine ⟨17148123460631556310125151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91456658456701633654000805 17148123460631556310125151)
    ·
      refine ⟨25722185190947334465187727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17148123460631556310125151 25722185190947334465187727)
      ·
        refine ⟨38583277786421001697781591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25722185190947334465187727 38583277786421001697781591)
        ·
          refine ⟨57874916679631502546672387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38583277786421001697781591 57874916679631502546672387)
          ·
            refine ⟨86812375019447253820008581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57874916679631502546672387 86812375019447253820008581)
            ·
              refine ⟨16277320316146360091251609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86812375019447253820008581 16277320316146360091251609)
              ·
                refine ⟨12207990237109770068438707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16277320316146360091251609 12207990237109770068438707)
                ·
                  refine ⟨18311985355664655102658061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12207990237109770068438707 18311985355664655102658061)
                  ·
                    refine ⟨6866994508374245663496773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18311985355664655102658061 6866994508374245663496773)
                    ·
                      refine ⟨1287561470320171061905645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6866994508374245663496773 1287561470320171061905645)
                      ·
                        rfl

theorem cell23_2507517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_2507517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507517 prefixEnd_2507517 := by exact prefixLift 2507517
  have htrace : WordTrace (prefixWord ++ tailWord_2507517) baseStart_2507517 baseEnd_2507517 := by
    simpa [prefixWord, tailWord_2507517, baseEnd_2507517] using wordTrace_append hprefix tailTrace_2507517
  have hstable : (prefixWord ++ tailWord_2507517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507517).length < 2 ^ (prefixWord ++ tailWord_2507517).sum := by decide
  have hdescent : baseEnd_2507517 < baseStart_2507517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507534 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2]
def baseStart_2507534 : Nat := 118140960795 + 2507534 * 2 ^ 59
def prefixEnd_2507534 : Nat := 4983230072969 + 3 ^ 40 * 2507534 * 2
def baseEnd_2507534 : Nat := 1287570199491297495393067

theorem tailTrace_2507534 : CollatzResearch.WordTrace tailWord_2507534 prefixEnd_2507534 1287570199491297495393067 := by
  unfold tailWord_2507534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11432159812205005694671207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60971518998426697038246437 11432159812205005694671207)
  ·
    refine ⟨17148239718307508542006811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11432159812205005694671207 17148239718307508542006811)
    ·
      refine ⟨25722359577461262813010217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17148239718307508542006811 25722359577461262813010217)
      ·
        refine ⟨19291769683095947109757663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25722359577461262813010217 19291769683095947109757663)
        ·
          refine ⟨28937654524643920664636495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19291769683095947109757663 28937654524643920664636495)
          ·
            refine ⟨43406481786965880996954743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28937654524643920664636495 43406481786965880996954743)
            ·
              refine ⟨65109722680448821495432115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43406481786965880996954743 65109722680448821495432115)
              ·
                refine ⟨97664584020673232243148173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65109722680448821495432115 97664584020673232243148173)
                ·
                  refine ⟨36624219007752462091180565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97664584020673232243148173 36624219007752462091180565)
                  ·
                    refine ⟨1716760265988396660524089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36624219007752462091180565 1716760265988396660524089)
                    ·
                      refine ⟨1287570199491297495393067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1716760265988396660524089 1287570199491297495393067)
                      ·
                        rfl

theorem cell23_2507534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_2507534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507534 prefixEnd_2507534 := by exact prefixLift 2507534
  have htrace : WordTrace (prefixWord ++ tailWord_2507534) baseStart_2507534 baseEnd_2507534 := by
    simpa [prefixWord, tailWord_2507534, baseEnd_2507534] using wordTrace_append hprefix tailTrace_2507534
  have hstable : (prefixWord ++ tailWord_2507534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507534).length < 2 ^ (prefixWord ++ tailWord_2507534).sum := by decide
  have hdescent : baseEnd_2507534 < baseStart_2507534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507557 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 8]
def baseStart_2507557 : Nat := 118140960795 + 2507557 * 2 ^ 59
def prefixEnd_2507557 : Nat := 4983230072969 + 3 ^ 40 * 2507557 * 2
def baseEnd_2507557 : Nat := 143064667727372322822829

theorem tailTrace_2507557 : CollatzResearch.WordTrace tailWord_2507557 prefixEnd_2507557 143064667727372322822829 := by
  unfold tailWord_2507557
  simp only [CollatzResearch.WordTrace]
  refine ⟨91458117376556720485456925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60972078251037813656971283 91458117376556720485456925)
  ·
    refine ⟨34296794016208770182046347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91458117376556720485456925 34296794016208770182046347)
    ·
      refine ⟨51445191024313155273069521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34296794016208770182046347 51445191024313155273069521)
      ·
        refine ⟨38583893268234866454802141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51445191024313155273069521 38583893268234866454802141)
        ·
          refine ⟨14468959975588074920550803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38583893268234866454802141 14468959975588074920550803)
          ·
            refine ⟨21703439963382112380826205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14468959975588074920550803 21703439963382112380826205)
            ·
              refine ⟨8138789986268292142809827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21703439963382112380826205 8138789986268292142809827)
              ·
                refine ⟨12208184979402438214214741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8138789986268292142809827 12208184979402438214214741)
                ·
                  refine ⟨143064667727372322822829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12208184979402438214214741 143064667727372322822829)
                  ·
                    rfl

theorem cell23_2507557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 8].length) (baseStart_2507557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507557 prefixEnd_2507557 := by exact prefixLift 2507557
  have htrace : WordTrace (prefixWord ++ tailWord_2507557) baseStart_2507557 baseEnd_2507557 := by
    simpa [prefixWord, tailWord_2507557, baseEnd_2507557] using wordTrace_append hprefix tailTrace_2507557
  have hstable : (prefixWord ++ tailWord_2507557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507557).length < 2 ^ (prefixWord ++ tailWord_2507557).sum := by decide
  have hdescent : baseEnd_2507557 < baseStart_2507557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507567 : List Nat := [1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 3]
def baseStart_2507567 : Nat := 118140960795 + 2507567 * 2 ^ 59
def prefixEnd_2507567 : Nat := 4983230072969 + 3 ^ 40 * 2507567 * 2
def baseEnd_2507567 : Nat := 1287587144352895866280415

theorem tailTrace_2507567 : CollatzResearch.WordTrace tailWord_2507567 prefixEnd_2507567 1287587144352895866280415 := by
  unfold tailWord_2507567
  simp only [CollatzResearch.WordTrace]
  refine ⟨91458482106520492193320955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60972321404346994795547303 91458482106520492193320955)
  ·
    refine ⟨137187723159780738289981433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91458482106520492193320955 137187723159780738289981433)
    ·
      refine ⟨102890792369835553717486075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137187723159780738289981433 102890792369835553717486075)
      ·
        refine ⟨154336188554753330576229113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102890792369835553717486075 154336188554753330576229113)
        ·
          refine ⟨115752141416064997932171835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154336188554753330576229113 115752141416064997932171835)
          ·
            refine ⟨173628212124097496898257753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115752141416064997932171835 173628212124097496898257753)
            ·
              refine ⟨130221159093073122673693315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173628212124097496898257753 130221159093073122673693315)
              ·
                refine ⟨195331738639609684010539973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130221159093073122673693315 195331738639609684010539973)
                ·
                  refine ⟨36624700994926815751976245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195331738639609684010539973 36624700994926815751976245)
                  ·
                    refine ⟨3433565718274388976747773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36624700994926815751976245 3433565718274388976747773)
                    ·
                      refine ⟨1287587144352895866280415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3433565718274388976747773 1287587144352895866280415)
                      ·
                        rfl

theorem cell23_2507567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 5, 3].length) (baseStart_2507567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507567 prefixEnd_2507567 := by exact prefixLift 2507567
  have htrace : WordTrace (prefixWord ++ tailWord_2507567) baseStart_2507567 baseEnd_2507567 := by
    simpa [prefixWord, tailWord_2507567, baseEnd_2507567] using wordTrace_append hprefix tailTrace_2507567
  have hstable : (prefixWord ++ tailWord_2507567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507567).length < 2 ^ (prefixWord ++ tailWord_2507567).sum := by decide
  have hdescent : baseEnd_2507567 < baseStart_2507567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507617 : List Nat := [1, 2, 3, 1, 1, 1, 2, 1, 5, 6]
def baseStart_2507617 : Nat := 118140960795 + 2507617 * 2 ^ 59
def prefixEnd_2507617 : Nat := 4983230072969 + 3 ^ 40 * 2507617 * 2
def baseEnd_2507617 : Nat := 429204272795206890218395

theorem tailTrace_2507617 : CollatzResearch.WordTrace tailWord_2507617 prefixEnd_2507617 429204272795206890218395 := by
  unfold tailWord_2507617
  simp only [CollatzResearch.WordTrace]
  refine ⟨91460305756339350732641105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60973537170892900488427403 91460305756339350732641105)
  ·
    refine ⟨68595229317254513049480829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91460305756339350732641105 68595229317254513049480829)
    ·
      refine ⟨25723210993970442393555311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68595229317254513049480829 25723210993970442393555311)
      ·
        refine ⟨38584816490955663590332967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25723210993970442393555311 38584816490955663590332967)
        ·
          refine ⟨57877224736433495385499451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38584816490955663590332967 57877224736433495385499451)
          ·
            refine ⟨86815837104650243078249177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57877224736433495385499451 86815837104650243078249177)
            ·
              refine ⟨65111877828487682308686883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86815837104650243078249177 65111877828487682308686883)
              ·
                refine ⟨97667816742731523463030325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65111877828487682308686883 97667816742731523463030325)
                ·
                  refine ⟨9156357819631080324659093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97667816742731523463030325 9156357819631080324659093)
                  ·
                    refine ⟨429204272795206890218395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9156357819631080324659093 429204272795206890218395)
                    ·
                      rfl

theorem cell23_2507617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_2507617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507617 prefixEnd_2507617 := by exact prefixLift 2507617
  have htrace : WordTrace (prefixWord ++ tailWord_2507617) baseStart_2507617 baseEnd_2507617 := by
    simpa [prefixWord, tailWord_2507617, baseEnd_2507617] using wordTrace_append hprefix tailTrace_2507617
  have hstable : (prefixWord ++ tailWord_2507617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507617).length < 2 ^ (prefixWord ++ tailWord_2507617).sum := by decide
  have hdescent : baseEnd_2507617 < baseStart_2507617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507638 : List Nat := [5, 1, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_2507638 : Nat := 118140960795 + 2507638 * 2 ^ 59
def prefixEnd_2507638 : Nat := 4983230072969 + 3 ^ 40 * 2507638 * 2
def baseEnd_2507638 : Nat := 429207867159788362830863

theorem tailTrace_2507638 : CollatzResearch.WordTrace tailWord_2507638 prefixEnd_2507638 429207867159788362830863 := by
  unfold tailWord_2507638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5716316980578954457447223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 60974047792842180879437045 5716316980578954457447223)
  ·
    refine ⟨8574475470868431686170835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5716316980578954457447223 8574475470868431686170835)
    ·
      refine ⟨12861713206302647529256253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8574475470868431686170835 12861713206302647529256253)
      ·
        refine ⟨4823142452363492823471095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12861713206302647529256253 4823142452363492823471095)
        ·
          refine ⟨7234713678545239235206643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823142452363492823471095 7234713678545239235206643)
          ·
            refine ⟨10852070517817858852809965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7234713678545239235206643 10852070517817858852809965)
            ·
              refine ⟨4069526444181697069803737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10852070517817858852809965 4069526444181697069803737)
              ·
                refine ⟨3052144833136272802352803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069526444181697069803737 3052144833136272802352803)
                ·
                  refine ⟨4578217249704409203529205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052144833136272802352803 4578217249704409203529205)
                  ·
                    refine ⟨429207867159788362830863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4578217249704409203529205 429207867159788362830863)
                    ·
                      rfl

theorem cell23_2507638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_2507638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507638 prefixEnd_2507638 := by exact prefixLift 2507638
  have htrace : WordTrace (prefixWord ++ tailWord_2507638) baseStart_2507638 baseEnd_2507638 := by
    simpa [prefixWord, tailWord_2507638, baseEnd_2507638] using wordTrace_append hprefix tailTrace_2507638
  have hstable : (prefixWord ++ tailWord_2507638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507638).length < 2 ^ (prefixWord ++ tailWord_2507638).sum := by decide
  have hdescent : baseEnd_2507638 < baseStart_2507638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507641 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 4]
def baseStart_2507641 : Nat := 118140960795 + 2507641 * 2 ^ 59
def prefixEnd_2507641 : Nat := 4983230072969 + 3 ^ 40 * 2507641 * 2
def baseEnd_2507641 : Nat := 1287625141921328576755075

theorem tailTrace_2507641 : CollatzResearch.WordTrace tailWord_2507641 prefixEnd_2507641 1287625141921328576755075 := by
  unfold tailWord_2507641
  simp only [CollatzResearch.WordTrace]
  refine ⟨91461181108252402831514777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60974120738834935221009851 91461181108252402831514777)
  ·
    refine ⟨68595885831189302123636083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91461181108252402831514777 68595885831189302123636083)
    ·
      refine ⟨102893828746783953185454125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68595885831189302123636083 102893828746783953185454125)
      ·
        refine ⟨38585185780043982444545297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102893828746783953185454125 38585185780043982444545297)
        ·
          refine ⟨28938889335032986833408973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38585185780043982444545297 28938889335032986833408973)
          ·
            refine ⟨10852083500637370062528365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28938889335032986833408973 10852083500637370062528365)
            ·
              refine ⟨4069531312739013773448137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10852083500637370062528365 4069531312739013773448137)
              ·
                refine ⟨3052148484554260330086103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069531312739013773448137 3052148484554260330086103)
                ·
                  refine ⟨4578222726831390495129155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052148484554260330086103 4578222726831390495129155)
                  ·
                    refine ⟨6867334090247085742693733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4578222726831390495129155 6867334090247085742693733)
                    ·
                      refine ⟨1287625141921328576755075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6867334090247085742693733 1287625141921328576755075)
                      ·
                        rfl

theorem cell23_2507641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 1, 1, 4].length) (baseStart_2507641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507641 prefixEnd_2507641 := by exact prefixLift 2507641
  have htrace : WordTrace (prefixWord ++ tailWord_2507641) baseStart_2507641 baseEnd_2507641 := by
    simpa [prefixWord, tailWord_2507641, baseEnd_2507641] using wordTrace_append hprefix tailTrace_2507641
  have hstable : (prefixWord ++ tailWord_2507641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507641).length < 2 ^ (prefixWord ++ tailWord_2507641).sum := by decide
  have hdescent : baseEnd_2507641 < baseStart_2507641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507647 : List Nat := [1, 1, 2, 2, 1, 1, 6, 9]
def baseStart_2507647 : Nat := 118140960795 + 2507647 * 2 ^ 59
def prefixEnd_2507647 : Nat := 4983230072969 + 3 ^ 40 * 2507647 * 2
def baseEnd_2507647 : Nat := 47689934177972427899261

theorem tailTrace_2507647 : CollatzResearch.WordTrace tailWord_2507647 prefixEnd_2507647 47689934177972427899261 := by
  unfold tailWord_2507647
  simp only [CollatzResearch.WordTrace]
  refine ⟨91461399946230665856233195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60974266630820443904155463 91461399946230665856233195)
  ·
    refine ⟨137192099919345998784349793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91461399946230665856233195 137192099919345998784349793)
    ·
      refine ⟨102894074939509499088262345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137192099919345998784349793 102894074939509499088262345)
      ·
        refine ⟨77170556204632124316196759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102894074939509499088262345 77170556204632124316196759)
        ·
          refine ⟨115755834306948186474295139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77170556204632124316196759 115755834306948186474295139)
          ·
            refine ⟨173633751460422279711442709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115755834306948186474295139 173633751460422279711442709)
            ·
              refine ⟨8139082099707294361473877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173633751460422279711442709 8139082099707294361473877)
              ·
                refine ⟨47689934177972427899261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8139082099707294361473877 47689934177972427899261)
                ·
                  rfl

theorem cell23_2507647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 9].length) (baseStart_2507647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507647 prefixEnd_2507647 := by exact prefixLift 2507647
  have htrace : WordTrace (prefixWord ++ tailWord_2507647) baseStart_2507647 baseEnd_2507647 := by
    simpa [prefixWord, tailWord_2507647, baseEnd_2507647] using wordTrace_append hprefix tailTrace_2507647
  have hstable : (prefixWord ++ tailWord_2507647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507647).length < 2 ^ (prefixWord ++ tailWord_2507647).sum := by decide
  have hdescent : baseEnd_2507647 < baseStart_2507647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507667 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6]
def baseStart_2507667 : Nat := 118140960795 + 2507667 * 2 ^ 59
def prefixEnd_2507667 : Nat := 4983230072969 + 3 ^ 40 * 2507667 * 2
def baseEnd_2507667 : Nat := 1287638492418345475029955

theorem tailTrace_2507667 : CollatzResearch.WordTrace tailWord_2507667 prefixEnd_2507667 1287638492418345475029955 := by
  unfold tailWord_2507667
  simp only [CollatzResearch.WordTrace]
  refine ⟨91462129406158209271961255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60974752937438806181307503 91462129406158209271961255)
  ·
    refine ⟨137193194109237313907941883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91462129406158209271961255 137193194109237313907941883)
    ·
      refine ⟨205789791163855970861912825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137193194109237313907941883 205789791163855970861912825)
      ·
        refine ⟨154342343372891978146434619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205789791163855970861912825 154342343372891978146434619)
        ·
          refine ⟨231513515059337967219651929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154342343372891978146434619 231513515059337967219651929)
          ·
            refine ⟨173635136294503475414738947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231513515059337967219651929 173635136294503475414738947)
            ·
              refine ⟨260452704441755213122108421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173635136294503475414738947 260452704441755213122108421)
              ·
                refine ⟨48834882082829102460395329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260452704441755213122108421 48834882082829102460395329)
                ·
                  refine ⟨36626161562121826845296497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48834882082829102460395329 36626161562121826845296497)
                  ·
                    refine ⟨27469621171591370133972373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36626161562121826845296497 27469621171591370133972373)
                    ·
                      refine ⟨1287638492418345475029955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27469621171591370133972373 1287638492418345475029955)
                      ·
                        rfl

theorem cell23_2507667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 6].length) (baseStart_2507667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507667 prefixEnd_2507667 := by exact prefixLift 2507667
  have htrace : WordTrace (prefixWord ++ tailWord_2507667) baseStart_2507667 baseEnd_2507667 := by
    simpa [prefixWord, tailWord_2507667, baseEnd_2507667] using wordTrace_append hprefix tailTrace_2507667
  have hstable : (prefixWord ++ tailWord_2507667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507667).length < 2 ^ (prefixWord ++ tailWord_2507667).sum := by decide
  have hdescent : baseEnd_2507667 < baseStart_2507667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507668 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_2507668 : Nat := 118140960795 + 2507668 * 2 ^ 59
def prefixEnd_2507668 : Nat := 4983230072969 + 3 ^ 40 * 2507668 * 2
def baseEnd_2507668 : Nat := 429213001966333323705817

theorem tailTrace_2507668 : CollatzResearch.WordTrace tailWord_2507668 prefixEnd_2507668 429213001966333323705817 := by
  unfold tailWord_2507668
  simp only [CollatzResearch.WordTrace]
  refine ⟨45731082939577293221373829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60974777252769724295165105 45731082939577293221373829)
  ·
    refine ⟨8574578051170742479007593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45731082939577293221373829 8574578051170742479007593)
    ·
      refine ⟨6430933538378056859255695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8574578051170742479007593 6430933538378056859255695)
      ·
        refine ⟨9646400307567085288883543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6430933538378056859255695 9646400307567085288883543)
        ·
          refine ⟨14469600461350627933325315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9646400307567085288883543 14469600461350627933325315)
          ·
            refine ⟨21704400692025941899987973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14469600461350627933325315 21704400692025941899987973)
            ·
              refine ⟨4069575129754864106247745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21704400692025941899987973 4069575129754864106247745)
              ·
                refine ⟨3052181347316148079685809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069575129754864106247745 3052181347316148079685809)
                ·
                  refine ⟨2289136010487111059764357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3052181347316148079685809 2289136010487111059764357)
                  ·
                    refine ⟨429213001966333323705817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2289136010487111059764357 429213001966333323705817)
                    ·
                      rfl

theorem cell23_2507668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_2507668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507668 prefixEnd_2507668 := by exact prefixLift 2507668
  have htrace : WordTrace (prefixWord ++ tailWord_2507668) baseStart_2507668 baseEnd_2507668 := by
    simpa [prefixWord, tailWord_2507668, baseEnd_2507668] using wordTrace_append hprefix tailTrace_2507668
  have hstable : (prefixWord ++ tailWord_2507668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507668).length < 2 ^ (prefixWord ++ tailWord_2507668).sum := by decide
  have hdescent : baseEnd_2507668 < baseStart_2507668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507681 : List Nat := [1, 2, 3, 4, 1, 3, 1, 8]
def baseStart_2507681 : Nat := 118140960795 + 2507681 * 2 ^ 59
def prefixEnd_2507681 : Nat := 4983230072969 + 3 ^ 40 * 2507681 * 2
def baseEnd_2507681 : Nat := 47690580783241052602033

theorem tailTrace_2507681 : CollatzResearch.WordTrace tailWord_2507681 prefixEnd_2507681 47690580783241052602033 := by
  unfold tailWord_2507681
  simp only [CollatzResearch.WordTrace]
  refine ⟨91462640028107489662970897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60975093352071659775313931 91462640028107489662970897)
  ·
    refine ⟨68596980021080617247228173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91462640028107489662970897 68596980021080617247228173)
    ·
      refine ⟨25723867507905231467710565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68596980021080617247228173 25723867507905231467710565)
      ·
        refine ⟨4823225157732230900195731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25723867507905231467710565 4823225157732230900195731)
        ·
          refine ⟨7234837736598346350293597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823225157732230900195731 7234837736598346350293597)
          ·
            refine ⟨2713064151224379881360099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7234837736598346350293597 2713064151224379881360099)
            ·
              refine ⟨4069596226836569822040149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2713064151224379881360099 4069596226836569822040149)
              ·
                refine ⟨47690580783241052602033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4069596226836569822040149 47690580783241052602033)
                ·
                  rfl

theorem cell23_2507681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 1, 8].length) (baseStart_2507681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507681 prefixEnd_2507681 := by exact prefixLift 2507681
  have htrace : WordTrace (prefixWord ++ tailWord_2507681) baseStart_2507681 baseEnd_2507681 := by
    simpa [prefixWord, tailWord_2507681, baseEnd_2507681] using wordTrace_append hprefix tailTrace_2507681
  have hstable : (prefixWord ++ tailWord_2507681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507681).length < 2 ^ (prefixWord ++ tailWord_2507681).sum := by decide
  have hdescent : baseEnd_2507681 < baseStart_2507681 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507724 : List Nat := [2, 2, 1, 4, 1, 1, 1, 1, 4, 6]
def baseStart_2507724 : Nat := 118140960795 + 2507724 * 2 ^ 59
def prefixEnd_2507724 : Nat := 4983230072969 + 3 ^ 40 * 2507724 * 2
def baseEnd_2507724 : Nat := 429222586938550584005731

theorem tailTrace_2507724 : CollatzResearch.WordTrace tailWord_2507724 prefixEnd_2507724 429222586938550584005731 := by
  unfold tailWord_2507724
  simp only [CollatzResearch.WordTrace]
  refine ⟨45732104183475854003393113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60976138911301138671190817 45732104183475854003393113)
  ·
    refine ⟨34299078137606890502544835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45732104183475854003393113 34299078137606890502544835)
    ·
      refine ⟨51448617206410335753817253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34299078137606890502544835 51448617206410335753817253)
      ·
        refine ⟨9646615726201937953840735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51448617206410335753817253 9646615726201937953840735)
        ·
          refine ⟨14469923589302906930761103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9646615726201937953840735 14469923589302906930761103)
          ·
            refine ⟨21704885383954360396141655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14469923589302906930761103 21704885383954360396141655)
            ·
              refine ⟨32557328075931540594212483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21704885383954360396141655 32557328075931540594212483)
              ·
                refine ⟨48835992113897310891318725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32557328075931540594212483 48835992113897310891318725)
                ·
                  refine ⟨9156748521355745792122261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48835992113897310891318725 9156748521355745792122261)
                  ·
                    refine ⟨429222586938550584005731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9156748521355745792122261 429222586938550584005731)
                    ·
                      rfl

theorem cell23_2507724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 1, 4, 6].length) (baseStart_2507724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507724 prefixEnd_2507724 := by exact prefixLift 2507724
  have htrace : WordTrace (prefixWord ++ tailWord_2507724) baseStart_2507724 baseEnd_2507724 := by
    simpa [prefixWord, tailWord_2507724, baseEnd_2507724] using wordTrace_append hprefix tailTrace_2507724
  have hstable : (prefixWord ++ tailWord_2507724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507724).length < 2 ^ (prefixWord ++ tailWord_2507724).sum := by decide
  have hdescent : baseEnd_2507724 < baseStart_2507724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507741 : List Nat := [1, 4, 3, 1, 2, 1, 2, 1, 2, 6]
def baseStart_2507741 : Nat := 118140960795 + 2507741 * 2 ^ 59
def prefixEnd_2507741 : Nat := 4983230072969 + 3 ^ 40 * 2507741 * 2
def baseEnd_2507741 : Nat := 429225496662259395168205

theorem tailTrace_2507741 : CollatzResearch.WordTrace tailWord_2507741 prefixEnd_2507741 429225496662259395168205 := by
  unfold tailWord_2507741
  simp only [CollatzResearch.WordTrace]
  refine ⟨91464828407890119910155077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60976552271926746606770051 91464828407890119910155077)
  ·
    refine ⟨17149655326479397483154077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91464828407890119910155077 17149655326479397483154077)
    ·
      refine ⟨6431120747429774056182779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17149655326479397483154077 6431120747429774056182779)
      ·
        refine ⟨9646681121144661084274169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6431120747429774056182779 9646681121144661084274169)
        ·
          refine ⟨7235010840858495813205627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9646681121144661084274169 7235010840858495813205627)
          ·
            refine ⟨10852516261287743719808441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7235010840858495813205627 10852516261287743719808441)
            ·
              refine ⟨8139387195965807789856331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10852516261287743719808441 8139387195965807789856331)
              ·
                refine ⟨12209080793948711684784497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8139387195965807789856331 12209080793948711684784497)
                ·
                  refine ⟨9156810595461533763588373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12209080793948711684784497 9156810595461533763588373)
                  ·
                    refine ⟨429225496662259395168205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9156810595461533763588373 429225496662259395168205)
                    ·
                      rfl

theorem cell23_2507741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_2507741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507741 prefixEnd_2507741 := by exact prefixLift 2507741
  have htrace : WordTrace (prefixWord ++ tailWord_2507741) baseStart_2507741 baseEnd_2507741 := by
    simpa [prefixWord, tailWord_2507741, baseEnd_2507741] using wordTrace_append hprefix tailTrace_2507741
  have hstable : (prefixWord ++ tailWord_2507741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507741).length < 2 ^ (prefixWord ++ tailWord_2507741).sum := by decide
  have hdescent : baseEnd_2507741 < baseStart_2507741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507799 : List Nat := [1, 1, 3, 5, 1, 3, 2, 1, 2, 2, 2]
def baseStart_2507799 : Nat := 118140960795 + 2507799 * 2 ^ 59
def prefixEnd_2507799 : Nat := 4983230072969 + 3 ^ 40 * 2507799 * 2
def baseEnd_2507799 : Nat := 1287706271864738958579349

theorem tailTrace_2507799 : CollatzResearch.WordTrace tailWord_2507799 prefixEnd_2507799 1287706271864738958579349 := by
  unfold tailWord_2507799
  simp only [CollatzResearch.WordTrace]
  refine ⟨91466943841679995815766451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60977962561119997210510967 91466943841679995815766451)
  ·
    refine ⟨137200415762519993723649677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91466943841679995815766451 137200415762519993723649677)
    ·
      refine ⟨51450155910944997646368629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137200415762519993723649677 51450155910944997646368629)
      ·
        refine ⟨4823452116651093529347059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51450155910944997646368629 4823452116651093529347059)
        ·
          refine ⟨7235178174976640294020589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823452116651093529347059 7235178174976640294020589)
          ·
            refine ⟨2713191815616240110257721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7235178174976640294020589 2713191815616240110257721)
            ·
              refine ⟨2034893861712180082693291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2713191815616240110257721 2034893861712180082693291)
              ·
                refine ⟨3052340792568270124039937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034893861712180082693291 3052340792568270124039937)
                ·
                  refine ⟨2289255594426202593029953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3052340792568270124039937 2289255594426202593029953)
                  ·
                    refine ⟨1716941695819651944772465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2289255594426202593029953 1716941695819651944772465)
                    ·
                      refine ⟨1287706271864738958579349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1716941695819651944772465 1287706271864738958579349)
                      ·
                        rfl

theorem cell23_2507799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_2507799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507799 prefixEnd_2507799 := by exact prefixLift 2507799
  have htrace : WordTrace (prefixWord ++ tailWord_2507799) baseStart_2507799 baseEnd_2507799 := by
    simpa [prefixWord, tailWord_2507799, baseEnd_2507799] using wordTrace_append hprefix tailTrace_2507799
  have hstable : (prefixWord ++ tailWord_2507799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507799).length < 2 ^ (prefixWord ++ tailWord_2507799).sum := by decide
  have hdescent : baseEnd_2507799 < baseStart_2507799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507828 : List Nat := [2, 5, 1, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_2507828 : Nat := 118140960795 + 2507828 * 2 ^ 59
def prefixEnd_2507828 : Nat := 4983230072969 + 3 ^ 40 * 2507828 * 2
def baseEnd_2507828 : Nat := 1287721162803719345116715

theorem tailTrace_2507828 : CollatzResearch.WordTrace tailWord_2507828 prefixEnd_2507828 1287721162803719345116715 := by
  unfold tailWord_2507828
  simp only [CollatzResearch.WordTrace]
  refine ⟨45734000779287466884286069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60978667705716622512381425 45734000779287466884286069)
  ·
    refine ⟨4287562573058200020401819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45734000779287466884286069 4287562573058200020401819)
    ·
      refine ⟨6431343859587300030602729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4287562573058200020401819 6431343859587300030602729)
      ·
        refine ⟨4823507894690475022952047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6431343859587300030602729 4823507894690475022952047)
        ·
          refine ⟨7235261842035712534428071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823507894690475022952047 7235261842035712534428071)
          ·
            refine ⟨10852892763053568801642107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7235261842035712534428071 10852892763053568801642107)
            ·
              refine ⟨16279339144580353202463161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10852892763053568801642107 16279339144580353202463161)
              ·
                refine ⟨12209504358435264901847371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16279339144580353202463161 12209504358435264901847371)
                ·
                  refine ⟨18314256537652897352771057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12209504358435264901847371 18314256537652897352771057)
                  ·
                    refine ⟨13735692403239673014578293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18314256537652897352771057 13735692403239673014578293)
                    ·
                      refine ⟨1287721162803719345116715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13735692403239673014578293 1287721162803719345116715)
                      ·
                        rfl

theorem cell23_2507828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_2507828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507828 prefixEnd_2507828 := by exact prefixLift 2507828
  have htrace : WordTrace (prefixWord ++ tailWord_2507828) baseStart_2507828 baseEnd_2507828 := by
    simpa [prefixWord, tailWord_2507828, baseEnd_2507828] using wordTrace_append hprefix tailTrace_2507828
  have hstable : (prefixWord ++ tailWord_2507828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507828).length < 2 ^ (prefixWord ++ tailWord_2507828).sum := by decide
  have hdescent : baseEnd_2507828 < baseStart_2507828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507861 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 6]
def baseStart_2507861 : Nat := 118140960795 + 2507861 * 2 ^ 59
def prefixEnd_2507861 : Nat := 4983230072969 + 3 ^ 40 * 2507861 * 2
def baseEnd_2507861 : Nat := 143082011962813079556007

theorem tailTrace_2507861 : CollatzResearch.WordTrace tailWord_2507861 prefixEnd_2507861 143082011962813079556007 := by
  unfold tailWord_2507861
  simp only [CollatzResearch.WordTrace]
  refine ⟨91469205167455380404523437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60979470111636920269682291 91469205167455380404523437)
  ·
    refine ⟨34300951937795767651696289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91469205167455380404523437 34300951937795767651696289)
    ·
      refine ⟨25725713953346825738772217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34300951937795767651696289 25725713953346825738772217)
      ·
        refine ⟨19294285465010119304079163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25725713953346825738772217 19294285465010119304079163)
        ·
          refine ⟨28941428197515178956118745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19294285465010119304079163 28941428197515178956118745)
          ·
            refine ⟨21706071148136384217089059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28941428197515178956118745 21706071148136384217089059)
            ·
              refine ⟨32559106722204576325633589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21706071148136384217089059 32559106722204576325633589)
              ·
                refine ⟨3052416255206679030528149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32559106722204576325633589 3052416255206679030528149)
                ·
                  refine ⟨143082011962813079556007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3052416255206679030528149 143082011962813079556007)
                  ·
                    rfl

theorem cell23_2507861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 6].length) (baseStart_2507861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507861 prefixEnd_2507861 := by exact prefixLift 2507861
  have htrace : WordTrace (prefixWord ++ tailWord_2507861) baseStart_2507861 baseEnd_2507861 := by
    simpa [prefixWord, tailWord_2507861, baseEnd_2507861] using wordTrace_append hprefix tailTrace_2507861
  have hstable : (prefixWord ++ tailWord_2507861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507861).length < 2 ^ (prefixWord ++ tailWord_2507861).sum := by decide
  have hdescent : baseEnd_2507861 < baseStart_2507861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507882 : List Nat := [3, 1, 3, 2, 2, 2, 2, 3, 1, 4]
def baseStart_2507882 : Nat := 118140960795 + 2507882 * 2 ^ 59
def prefixEnd_2507882 : Nat := 4983230072969 + 3 ^ 40 * 2507882 * 2
def baseEnd_2507882 : Nat := 429249630253020711280489

theorem tailTrace_2507882 : CollatzResearch.WordTrace tailWord_2507882 prefixEnd_2507882 429249630253020711280489 := by
  unfold tailWord_2507882
  simp only [CollatzResearch.WordTrace]
  refine ⟨22867492775094825247759475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60979980733586200660691933 22867492775094825247759475)
  ·
    refine ⟨34301239162642237871639213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22867492775094825247759475 34301239162642237871639213)
    ·
      refine ⟨12862964685990839201864705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34301239162642237871639213 12862964685990839201864705)
      ·
        refine ⟨9647223514493129401398529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12862964685990839201864705 9647223514493129401398529)
        ·
          refine ⟨7235417635869847051048897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9647223514493129401398529 7235417635869847051048897)
          ·
            refine ⟨5426563226902385288286673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7235417635869847051048897 5426563226902385288286673)
            ·
              refine ⟨4069922420176788966215005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5426563226902385288286673 4069922420176788966215005)
              ·
                refine ⟨1526220907566295862330627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4069922420176788966215005 1526220907566295862330627)
                ·
                  refine ⟨2289331361349443793495941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526220907566295862330627 2289331361349443793495941)
                  ·
                    refine ⟨429249630253020711280489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2289331361349443793495941 429249630253020711280489)
                    ·
                      rfl

theorem cell23_2507882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_2507882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507882 prefixEnd_2507882 := by exact prefixLift 2507882
  have htrace : WordTrace (prefixWord ++ tailWord_2507882) baseStart_2507882 baseEnd_2507882 := by
    simpa [prefixWord, tailWord_2507882, baseEnd_2507882] using wordTrace_append hprefix tailTrace_2507882
  have hstable : (prefixWord ++ tailWord_2507882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507882).length < 2 ^ (prefixWord ++ tailWord_2507882).sum := by decide
  have hdescent : baseEnd_2507882 < baseStart_2507882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507888 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 5, 1, 3]
def baseStart_2507888 : Nat := 118140960795 + 2507888 * 2 ^ 59
def prefixEnd_2507888 : Nat := 4983230072969 + 3 ^ 40 * 2507888 * 2
def baseEnd_2507888 : Nat := 1287751971642989110366439

theorem tailTrace_2507888 : CollatzResearch.WordTrace tailWord_2507888 prefixEnd_2507888 1287751971642989110366439 := by
  unfold tailWord_2507888
  simp only [CollatzResearch.WordTrace]
  refine ⟨45735094969178782007878159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60980126625571709343837545 45735094969178782007878159)
  ·
    refine ⟨68602642453768173011817239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45735094969178782007878159 68602642453768173011817239)
    ·
      refine ⟨102903963680652259517725859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68602642453768173011817239 102903963680652259517725859)
      ·
        refine ⟨154355945520978389276588789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102903963680652259517725859 154355945520978389276588789)
        ·
          refine ⟨14470869892591723994680199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154355945520978389276588789 14470869892591723994680199)
          ·
            refine ⟨21706304838887585992020299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14470869892591723994680199 21706304838887585992020299)
            ·
              refine ⟨32559457258331378988030449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21706304838887585992020299 32559457258331378988030449)
              ·
                refine ⟨24419592943748534241022837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32559457258331378988030449 24419592943748534241022837)
                ·
                  refine ⟨2289336838476425085095891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24419592943748534241022837 2289336838476425085095891)
                  ·
                    refine ⟨3434005257714637627643837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2289336838476425085095891 3434005257714637627643837)
                    ·
                      refine ⟨1287751971642989110366439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3434005257714637627643837 1287751971642989110366439)
                      ·
                        rfl

theorem cell23_2507888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 5, 1, 3].length) (baseStart_2507888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507888 prefixEnd_2507888 := by exact prefixLift 2507888
  have htrace : WordTrace (prefixWord ++ tailWord_2507888) baseStart_2507888 baseEnd_2507888 := by
    simpa [prefixWord, tailWord_2507888, baseEnd_2507888] using wordTrace_append hprefix tailTrace_2507888
  have hstable : (prefixWord ++ tailWord_2507888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507888).length < 2 ^ (prefixWord ++ tailWord_2507888).sum := by decide
  have hdescent : baseEnd_2507888 < baseStart_2507888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507905 : List Nat := [1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 3]
def baseStart_2507905 : Nat := 118140960795 + 2507905 * 2 ^ 59
def prefixEnd_2507905 : Nat := 4983230072969 + 3 ^ 40 * 2507905 * 2
def baseEnd_2507905 : Nat := 1287760700814115543853861

theorem tailTrace_2507905 : CollatzResearch.WordTrace tailWord_2507905 prefixEnd_2507905 1287760700814115543853861 := by
  unfold tailWord_2507905
  simp only [CollatzResearch.WordTrace]
  refine ⟨91470809979295975919125169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60980539986197317279416779 91470809979295975919125169)
  ·
    refine ⟨68603107484471981939343877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91470809979295975919125169 68603107484471981939343877)
    ·
      refine ⟨12863082653338496613626977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68603107484471981939343877 12863082653338496613626977)
      ·
        refine ⟨9647311990003872460220233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12863082653338496613626977 9647311990003872460220233)
        ·
          refine ⟨7235483992502904345165175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9647311990003872460220233 7235483992502904345165175)
          ·
            refine ⟨10853225988754356517747763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7235483992502904345165175 10853225988754356517747763)
            ·
              refine ⟨16279838983131534776621645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10853225988754356517747763 16279838983131534776621645)
              ·
                refine ⟨6104939618674325541233117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16279838983131534776621645 6104939618674325541233117)
                ·
                  refine ⟨2289352357002872077962419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6104939618674325541233117 2289352357002872077962419)
                  ·
                    refine ⟨3434028535504308116943629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2289352357002872077962419 3434028535504308116943629)
                    ·
                      refine ⟨1287760700814115543853861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3434028535504308116943629 1287760700814115543853861)
                      ·
                        rfl

theorem cell23_2507905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 3, 3, 1, 3].length) (baseStart_2507905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507905 prefixEnd_2507905 := by exact prefixLift 2507905
  have htrace : WordTrace (prefixWord ++ tailWord_2507905) baseStart_2507905 baseEnd_2507905 := by
    simpa [prefixWord, tailWord_2507905, baseEnd_2507905] using wordTrace_append hprefix tailTrace_2507905
  have hstable : (prefixWord ++ tailWord_2507905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507905).length < 2 ^ (prefixWord ++ tailWord_2507905).sum := by decide
  have hdescent : baseEnd_2507905 < baseStart_2507905 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507968 : List Nat := [2, 1, 1, 2, 6, 1, 2, 8]
def baseStart_2507968 : Nat := 118140960795 + 2507968 * 2 ^ 59
def prefixEnd_2507968 : Nat := 4983230072969 + 3 ^ 40 * 2507968 * 2
def baseEnd_2507968 : Nat := 47696038892420325828373

theorem tailTrace_2507968 : CollatzResearch.WordTrace tailWord_2507968 prefixEnd_2507968 47696038892420325828373 := by
  unfold tailWord_2507968
  simp only [CollatzResearch.WordTrace]
  refine ⟨45736553889033868839334279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60982071852045158452445705 45736553889033868839334279)
  ·
    refine ⟨68604830833550803259001419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45736553889033868839334279 68604830833550803259001419)
    ·
      refine ⟨102907246250326204888502129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68604830833550803259001419 102907246250326204888502129)
      ·
        refine ⟨77180434687744653666376597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102907246250326204888502129 77180434687744653666376597)
        ·
          refine ⟨3617832875988030640611403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77180434687744653666376597 3617832875988030640611403)
          ·
            refine ⟨5426749313982045960917105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617832875988030640611403 5426749313982045960917105)
            ·
              refine ⟨4070061985486534470687829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5426749313982045960917105 4070061985486534470687829)
              ·
                refine ⟨47696038892420325828373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4070061985486534470687829 47696038892420325828373)
                ·
                  rfl

theorem cell23_2507968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 2, 8].length) (baseStart_2507968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507968 prefixEnd_2507968 := by exact prefixLift 2507968
  have htrace : WordTrace (prefixWord ++ tailWord_2507968) baseStart_2507968 baseEnd_2507968 := by
    simpa [prefixWord, tailWord_2507968, baseEnd_2507968] using wordTrace_append hprefix tailTrace_2507968
  have hstable : (prefixWord ++ tailWord_2507968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507968).length < 2 ^ (prefixWord ++ tailWord_2507968).sum := by decide
  have hdescent : baseEnd_2507968 < baseStart_2507968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507972 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_2507972 : Nat := 118140960795 + 2507972 * 2 ^ 59
def prefixEnd_2507972 : Nat := 4983230072969 + 3 ^ 40 * 2507972 * 2
def baseEnd_2507972 : Nat := 429265034672655593905351

theorem tailTrace_2507972 : CollatzResearch.WordTrace tailWord_2507972 prefixEnd_2507972 429265034672655593905351 := by
  unfold tailWord_2507972
  simp only [CollatzResearch.WordTrace]
  refine ⟨45736626835026623180907085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60982169113368830907876113 45736626835026623180907085)
  ·
    refine ⟨17151235063134983692840157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45736626835026623180907085 17151235063134983692840157)
    ·
      refine ⟨6431713148675618884815059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17151235063134983692840157 6431713148675618884815059)
      ·
        refine ⟨9647569723013428327222589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6431713148675618884815059 9647569723013428327222589)
        ·
          refine ⟨3617838646130035622708471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9647569723013428327222589 3617838646130035622708471)
          ·
            refine ⟨5426757969195053434062707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617838646130035622708471 5426757969195053434062707)
            ·
              refine ⟨8140136953792580151094061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5426757969195053434062707 8140136953792580151094061)
              ·
                refine ⟨3052551357672217556660273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8140136953792580151094061 3052551357672217556660273)
                ·
                  refine ⟨2289413518254163167495205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3052551357672217556660273 2289413518254163167495205)
                  ·
                    refine ⟨429265034672655593905351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2289413518254163167495205 429265034672655593905351)
                    ·
                      rfl

theorem cell23_2507972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_2507972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507972 prefixEnd_2507972 := by exact prefixLift 2507972
  have htrace : WordTrace (prefixWord ++ tailWord_2507972) baseStart_2507972 baseEnd_2507972 := by
    simpa [prefixWord, tailWord_2507972, baseEnd_2507972] using wordTrace_append hprefix tailTrace_2507972
  have hstable : (prefixWord ++ tailWord_2507972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507972).length < 2 ^ (prefixWord ++ tailWord_2507972).sum := by decide
  have hdescent : baseEnd_2507972 < baseStart_2507972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2507991 : List Nat := [1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 5]
def baseStart_2507991 : Nat := 118140960795 + 2507991 * 2 ^ 59
def prefixEnd_2507991 : Nat := 4983230072969 + 3 ^ 40 * 2507991 * 2
def baseEnd_2507991 : Nat := 1287804860150402207378465

theorem tailTrace_2507991 : CollatzResearch.WordTrace tailWord_2507991 prefixEnd_2507991 1287804860150402207378465 := by
  unfold tailWord_2507991
  simp only [CollatzResearch.WordTrace]
  refine ⟨91473946656984412606755827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60982631104656275071170551 91473946656984412606755827)
  ·
    refine ⟨137210919985476618910133741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91473946656984412606755827 137210919985476618910133741)
    ·
      refine ⟨51454094994553732091300153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137210919985476618910133741 51454094994553732091300153)
      ·
        refine ⟨38590571245915299068475115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51454094994553732091300153 38590571245915299068475115)
        ·
          refine ⟨57885856868872948602712673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38590571245915299068475115 57885856868872948602712673)
          ·
            refine ⟨43414392651654711452034505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57885856868872948602712673 43414392651654711452034505)
            ·
              refine ⟨32560794488741033589025879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43414392651654711452034505 32560794488741033589025879)
              ·
                refine ⟨48841191733111550383538819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32560794488741033589025879 48841191733111550383538819)
                ·
                  refine ⟨73261787599667325575308229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48841191733111550383538819 73261787599667325575308229)
                  ·
                    refine ⟨13736585174937623545370293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73261787599667325575308229 13736585174937623545370293)
                    ·
                      refine ⟨1287804860150402207378465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13736585174937623545370293 1287804860150402207378465)
                      ·
                        rfl

theorem cell23_2507991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 4, 5].length) (baseStart_2507991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2507991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2507991 prefixEnd_2507991 := by exact prefixLift 2507991
  have htrace : WordTrace (prefixWord ++ tailWord_2507991) baseStart_2507991 baseEnd_2507991 := by
    simpa [prefixWord, tailWord_2507991, baseEnd_2507991] using wordTrace_append hprefix tailTrace_2507991
  have hstable : (prefixWord ++ tailWord_2507991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2507991).length < 2 ^ (prefixWord ++ tailWord_2507991).sum := by decide
  have hdescent : baseEnd_2507991 < baseStart_2507991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2507991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508012 : List Nat := [2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 3]
def baseStart_2508012 : Nat := 118140960795 + 2508012 * 2 ^ 59
def prefixEnd_2508012 : Nat := 4983230072969 + 3 ^ 40 * 2508012 * 2
def baseEnd_2508012 : Nat := 1287815643244146625215869

theorem tailTrace_2508012 : CollatzResearch.WordTrace tailWord_2508012 prefixEnd_2508012 1287815643244146625215869 := by
  unfold tailWord_2508012
  simp only [CollatzResearch.WordTrace]
  refine ⟨45737356294954166596635145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60983141726605555462180193 45737356294954166596635145)
  ·
    refine ⟨34303017221215624947476359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45737356294954166596635145 34303017221215624947476359)
    ·
      refine ⟨51454525831823437421214539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34303017221215624947476359 51454525831823437421214539)
      ·
        refine ⟨77181788747735156131821809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51454525831823437421214539 77181788747735156131821809)
        ·
          refine ⟨57886341560801367098866357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77181788747735156131821809 57886341560801367098866357)
          ·
            refine ⟨5426844521325128165518721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57886341560801367098866357 5426844521325128165518721)
            ·
              refine ⟨4070133390993846124139041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5426844521325128165518721 4070133390993846124139041)
              ·
                refine ⟨3052600043245384593104281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4070133390993846124139041 3052600043245384593104281)
                ·
                  refine ⟨2289450032434038444828211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3052600043245384593104281 2289450032434038444828211)
                  ·
                    refine ⟨3434175048651057667242317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2289450032434038444828211 3434175048651057667242317)
                    ·
                      refine ⟨1287815643244146625215869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3434175048651057667242317 1287815643244146625215869)
                      ·
                        rfl

theorem cell23_2508012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 3].length) (baseStart_2508012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508012 prefixEnd_2508012 := by exact prefixLift 2508012
  have htrace : WordTrace (prefixWord ++ tailWord_2508012) baseStart_2508012 baseEnd_2508012 := by
    simpa [prefixWord, tailWord_2508012, baseEnd_2508012] using wordTrace_append hprefix tailTrace_2508012
  have hstable : (prefixWord ++ tailWord_2508012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508012).length < 2 ^ (prefixWord ++ tailWord_2508012).sum := by decide
  have hdescent : baseEnd_2508012 < baseStart_2508012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508013 : List Nat := [1, 5, 1, 2, 2, 3, 2, 2, 1, 2, 2]
def baseStart_2508013 : Nat := 118140960795 + 2508013 * 2 ^ 59
def prefixEnd_2508013 : Nat := 4983230072969 + 3 ^ 40 * 2508013 * 2
def baseEnd_2508013 : Nat := 1287816156724801121303365

theorem tailTrace_2508013 : CollatzResearch.WordTrace tailWord_2508013 prefixEnd_2508013 1287816156724801121303365 := by
  unfold tailWord_2508013
  simp only [CollatzResearch.WordTrace]
  refine ⟨91474749062904710364056693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60983166041936473576037795 91474749062904710364056693)
  ·
    refine ⟨8575757724647316596630315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91474749062904710364056693 8575757724647316596630315)
    ·
      refine ⟨12863636586970974894945473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8575757724647316596630315 12863636586970974894945473)
      ·
        refine ⟨9647727440228231171209105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12863636586970974894945473 9647727440228231171209105)
        ·
          refine ⟨7235795580171173378406829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9647727440228231171209105 7235795580171173378406829)
          ·
            refine ⟨2713423342564190016902561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7235795580171173378406829 2713423342564190016902561)
            ·
              refine ⟨2035067506923142512676921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2713423342564190016902561 2035067506923142512676921)
              ·
                refine ⟨1526300630192356884507691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035067506923142512676921 1526300630192356884507691)
                ·
                  refine ⟨2289450945288535326761537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526300630192356884507691 2289450945288535326761537)
                  ·
                    refine ⟨1717088208966401495071153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2289450945288535326761537 1717088208966401495071153)
                    ·
                      refine ⟨1287816156724801121303365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717088208966401495071153 1287816156724801121303365)
                      ·
                        rfl

theorem cell23_2508013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 2, 1, 2, 2].length) (baseStart_2508013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508013 prefixEnd_2508013 := by exact prefixLift 2508013
  have htrace : WordTrace (prefixWord ++ tailWord_2508013) baseStart_2508013 baseEnd_2508013 := by
    simpa [prefixWord, tailWord_2508013, baseEnd_2508013] using wordTrace_append hprefix tailTrace_2508013
  have hstable : (prefixWord ++ tailWord_2508013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508013).length < 2 ^ (prefixWord ++ tailWord_2508013).sum := by decide
  have hdescent : baseEnd_2508013 < baseStart_2508013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508035 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 1, 4, 2]
def baseStart_2508035 : Nat := 118140960795 + 2508035 * 2 ^ 59
def prefixEnd_2508035 : Nat := 4983230072969 + 3 ^ 40 * 2508035 * 2
def baseEnd_2508035 : Nat := 1287827453299200035228263

theorem tailTrace_2508035 : CollatzResearch.WordTrace tailWord_2508035 prefixEnd_2508035 1287827453299200035228263 := by
  unfold tailWord_2508035
  simp only [CollatzResearch.WordTrace]
  refine ⟨91475551468825008121357559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60983700979216672080905039 91475551468825008121357559)
  ·
    refine ⟨137213327203237512182036339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91475551468825008121357559 137213327203237512182036339)
    ·
      refine ⟨205819990804856268273054509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137213327203237512182036339 205819990804856268273054509)
      ·
        refine ⟨77182496551821100602395441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205819990804856268273054509 77182496551821100602395441)
        ·
          refine ⟨57886872413865825451796581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77182496551821100602395441 57886872413865825451796581)
          ·
            refine ⟨10853788577599842272211859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57886872413865825451796581 10853788577599842272211859)
            ·
              refine ⟨16280682866399763408317789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10853788577599842272211859 16280682866399763408317789)
              ·
                refine ⟨6105256074899911278119171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16280682866399763408317789 6105256074899911278119171)
                ·
                  refine ⟨9157884112349866917178757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6105256074899911278119171 9157884112349866917178757)
                  ·
                    refine ⟨1717103271065600046971017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9157884112349866917178757 1717103271065600046971017)
                    ·
                      refine ⟨1287827453299200035228263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717103271065600046971017 1287827453299200035228263)
                      ·
                        rfl

theorem cell23_2508035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 4, 2].length) (baseStart_2508035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508035 prefixEnd_2508035 := by exact prefixLift 2508035
  have htrace : WordTrace (prefixWord ++ tailWord_2508035) baseStart_2508035 baseEnd_2508035 := by
    simpa [prefixWord, tailWord_2508035, baseEnd_2508035] using wordTrace_append hprefix tailTrace_2508035
  have hstable : (prefixWord ++ tailWord_2508035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508035).length < 2 ^ (prefixWord ++ tailWord_2508035).sum := by decide
  have hdescent : baseEnd_2508035 < baseStart_2508035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508051 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 7]
def baseStart_2508051 : Nat := 118140960795 + 2508051 * 2 ^ 59
def prefixEnd_2508051 : Nat := 4983230072969 + 3 ^ 40 * 2508051 * 2
def baseEnd_2508051 : Nat := 1287835668989671972628189

theorem tailTrace_2508051 : CollatzResearch.WordTrace tailWord_2508051 prefixEnd_2508051 1287835668989671972628189 := by
  unfold tailWord_2508051
  simp only [CollatzResearch.WordTrace]
  refine ⟨91476135036767042853940007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60984090024511361902626671 91476135036767042853940007)
  ·
    refine ⟨137214202555150564280910011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91476135036767042853940007 137214202555150564280910011)
    ·
      refine ⟨205821303832725846421365017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137214202555150564280910011 205821303832725846421365017)
      ·
        refine ⟨154365977874544384816023763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205821303832725846421365017 154365977874544384816023763)
        ·
          refine ⟨231548966811816577224035645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154365977874544384816023763 231548966811816577224035645)
          ·
            refine ⟨86830862554431216459013367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231548966811816577224035645 86830862554431216459013367)
            ·
              refine ⟨130246293831646824688520051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86830862554431216459013367 130246293831646824688520051)
              ·
                refine ⟨195369440747470237032780077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130246293831646824688520051 195369440747470237032780077)
                ·
                  refine ⟨73263540280301338887292529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195369440747470237032780077 73263540280301338887292529)
                  ·
                    refine ⟨54947655210226004165469397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 73263540280301338887292529 54947655210226004165469397)
                    ·
                      refine ⟨1287835668989671972628189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54947655210226004165469397 1287835668989671972628189)
                      ·
                        rfl

theorem cell23_2508051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 7].length) (baseStart_2508051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508051 prefixEnd_2508051 := by exact prefixLift 2508051
  have htrace : WordTrace (prefixWord ++ tailWord_2508051) baseStart_2508051 baseEnd_2508051 := by
    simpa [prefixWord, tailWord_2508051, baseEnd_2508051] using wordTrace_append hprefix tailTrace_2508051
  have hstable : (prefixWord ++ tailWord_2508051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508051).length < 2 ^ (prefixWord ++ tailWord_2508051).sum := by decide
  have hdescent : baseEnd_2508051 < baseStart_2508051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508069 : List Nat := [1, 3, 1, 2, 4, 1, 3, 2, 2, 2, 2]
def baseStart_2508069 : Nat := 118140960795 + 2508069 * 2 ^ 59
def prefixEnd_2508069 : Nat := 4983230072969 + 3 ^ 40 * 2508069 * 2
def baseEnd_2508069 : Nat := 1287844911641452902203107

theorem tailTrace_2508069 : CollatzResearch.WordTrace tailWord_2508069 prefixEnd_2508069 1287844911641452902203107 := by
  unfold tailWord_2508069
  simp only [CollatzResearch.WordTrace]
  refine ⟨91476791550701831928095261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60984527700467887952063507 91476791550701831928095261)
  ·
    refine ⟨34303796831513186973035723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91476791550701831928095261 34303796831513186973035723)
    ·
      refine ⟨51455695247269780459553585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34303796831513186973035723 51455695247269780459553585)
      ·
        refine ⟨38591771435452335344665189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51455695247269780459553585 38591771435452335344665189)
        ·
          refine ⟨7235957144147312877124723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38591771435452335344665189 7235957144147312877124723)
          ·
            refine ⟨10853935716220969315687085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7235957144147312877124723 10853935716220969315687085)
            ·
              refine ⟨4070225893582863493382657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10853935716220969315687085 4070225893582863493382657)
              ·
                refine ⟨3052669420187147620036993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4070225893582863493382657 3052669420187147620036993)
                ·
                  refine ⟨2289502065140360715027745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3052669420187147620036993 2289502065140360715027745)
                  ·
                    refine ⟨1717126548855270536270809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2289502065140360715027745 1717126548855270536270809)
                    ·
                      refine ⟨1287844911641452902203107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717126548855270536270809 1287844911641452902203107)
                      ·
                        rfl

theorem cell23_2508069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_2508069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508069 prefixEnd_2508069 := by exact prefixLift 2508069
  have htrace : WordTrace (prefixWord ++ tailWord_2508069) baseStart_2508069 baseEnd_2508069 := by
    simpa [prefixWord, tailWord_2508069, baseEnd_2508069] using wordTrace_append hprefix tailTrace_2508069
  have hstable : (prefixWord ++ tailWord_2508069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508069).length < 2 ^ (prefixWord ++ tailWord_2508069).sum := by decide
  have hdescent : baseEnd_2508069 < baseStart_2508069 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508085 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 3]
def baseStart_2508085 : Nat := 118140960795 + 2508085 * 2 ^ 59
def prefixEnd_2508085 : Nat := 4983230072969 + 3 ^ 40 * 2508085 * 2
def baseEnd_2508085 : Nat := 1287853127331924839603033

theorem tailTrace_2508085 : CollatzResearch.WordTrace tailWord_2508085 prefixEnd_2508085 1287853127331924839603033 := by
  unfold tailWord_2508085
  simp only [CollatzResearch.WordTrace]
  refine ⟨91477375118643866660677709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60984916745762577773785139 91477375118643866660677709)
  ·
    refine ⟨34304015669491449997754141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91477375118643866660677709 34304015669491449997754141)
    ·
      refine ⟨12864005876059293749157803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34304015669491449997754141 12864005876059293749157803)
      ·
        refine ⟨19296008814088940623736705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12864005876059293749157803 19296008814088940623736705)
        ·
          refine ⟨14472006610566705467802529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19296008814088940623736705 14472006610566705467802529)
          ·
            refine ⟨10854004957925029100851897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14472006610566705467802529 10854004957925029100851897)
            ·
              refine ⟨8140503718443771825638923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10854004957925029100851897 8140503718443771825638923)
              ·
                refine ⟨12210755577665657738458385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8140503718443771825638923 12210755577665657738458385)
                ·
                  refine ⟨9158066683249243303843789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12210755577665657738458385 9158066683249243303843789)
                  ·
                    refine ⟨3434275006218466238941421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9158066683249243303843789 3434275006218466238941421)
                    ·
                      refine ⟨1287853127331924839603033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3434275006218466238941421 1287853127331924839603033)
                      ·
                        rfl

theorem cell23_2508085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 3, 3].length) (baseStart_2508085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508085 prefixEnd_2508085 := by exact prefixLift 2508085
  have htrace : WordTrace (prefixWord ++ tailWord_2508085) baseStart_2508085 baseEnd_2508085 := by
    simpa [prefixWord, tailWord_2508085, baseEnd_2508085] using wordTrace_append hprefix tailTrace_2508085
  have hstable : (prefixWord ++ tailWord_2508085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508085).length < 2 ^ (prefixWord ++ tailWord_2508085).sum := by decide
  have hdescent : baseEnd_2508085 < baseStart_2508085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508192 : List Nat := [2, 1, 1, 4, 1, 2, 2, 3, 3, 1, 3]
def baseStart_2508192 : Nat := 118140960795 + 2508192 * 2 ^ 59
def prefixEnd_2508192 : Nat := 4983230072969 + 3 ^ 40 * 2508192 * 2
def baseEnd_2508192 : Nat := 1287908069761955920965041

theorem tailTrace_2508192 : CollatzResearch.WordTrace tailWord_2508192 prefixEnd_2508192 1287908069761955920965041 := by
  unfold tailWord_2508192
  simp only [CollatzResearch.WordTrace]
  refine ⟨45740638864628111967411415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60987518486170815956548553 45740638864628111967411415)
  ·
    refine ⟨68610958296942167951117123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45740638864628111967411415 68610958296942167951117123)
    ·
      refine ⟨102916437445413251926675685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68610958296942167951117123 102916437445413251926675685)
      ·
        refine ⟨19296832021014984736251691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102916437445413251926675685 19296832021014984736251691)
        ·
          refine ⟨28945248031522477104377537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19296832021014984736251691 28945248031522477104377537)
          ·
            refine ⟨21708936023641857828283153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28945248031522477104377537 21708936023641857828283153)
            ·
              refine ⟨16281702017731393371212365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21708936023641857828283153 16281702017731393371212365)
              ·
                refine ⟨6105638256649272514204637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16281702017731393371212365 6105638256649272514204637)
                ·
                  refine ⟨2289614346243477192826739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6105638256649272514204637 2289614346243477192826739)
                  ·
                    refine ⟨3434421519365215789240109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2289614346243477192826739 3434421519365215789240109)
                    ·
                      refine ⟨1287908069761955920965041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3434421519365215789240109 1287908069761955920965041)
                      ·
                        rfl

theorem cell23_2508192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 3, 3, 1, 3].length) (baseStart_2508192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508192 prefixEnd_2508192 := by exact prefixLift 2508192
  have htrace : WordTrace (prefixWord ++ tailWord_2508192) baseStart_2508192 baseEnd_2508192 := by
    simpa [prefixWord, tailWord_2508192, baseEnd_2508192] using wordTrace_append hprefix tailTrace_2508192
  have hstable : (prefixWord ++ tailWord_2508192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508192).length < 2 ^ (prefixWord ++ tailWord_2508192).sum := by decide
  have hdescent : baseEnd_2508192 < baseStart_2508192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508215 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 4]
def baseStart_2508215 : Nat := 118140960795 + 2508215 * 2 ^ 59
def prefixEnd_2508215 : Nat := 4983230072969 + 3 ^ 40 * 2508215 * 2
def baseEnd_2508215 : Nat := 1287919879817009330977435

theorem tailTrace_2508215 : CollatzResearch.WordTrace tailWord_2508215 prefixEnd_2508215 1287919879817009330977435 := by
  unfold tailWord_2508215
  simp only [CollatzResearch.WordTrace]
  refine ⟨91482116608172898862910099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60988077738781932575273399 91482116608172898862910099)
  ·
    refine ⟨137223174912259348294365149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91482116608172898862910099 137223174912259348294365149)
    ·
      refine ⟨51458690592097255610386931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137223174912259348294365149 51458690592097255610386931)
      ·
        refine ⟨77188035888145883415580397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51458690592097255610386931 77188035888145883415580397)
        ·
          refine ⟨28945513458054706280842649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77188035888145883415580397 28945513458054706280842649)
          ·
            refine ⟨21709135093541029710631987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28945513458054706280842649 21709135093541029710631987)
            ·
              refine ⟨32563702640311544565947981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21709135093541029710631987 32563702640311544565947981)
              ·
                refine ⟨12211388490116829212230493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32563702640311544565947981 12211388490116829212230493)
                ·
                  refine ⟨4579270683793810954586435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12211388490116829212230493 4579270683793810954586435)
                  ·
                    refine ⟨6868906025690716431879653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4579270683793810954586435 6868906025690716431879653)
                    ·
                      refine ⟨1287919879817009330977435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6868906025690716431879653 1287919879817009330977435)
                      ·
                        rfl

theorem cell23_2508215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 3, 1, 4].length) (baseStart_2508215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508215 prefixEnd_2508215 := by exact prefixLift 2508215
  have htrace : WordTrace (prefixWord ++ tailWord_2508215) baseStart_2508215 baseEnd_2508215 := by
    simpa [prefixWord, tailWord_2508215, baseEnd_2508215] using wordTrace_append hprefix tailTrace_2508215
  have hstable : (prefixWord ++ tailWord_2508215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508215).length < 2 ^ (prefixWord ++ tailWord_2508215).sum := by decide
  have hdescent : baseEnd_2508215 < baseStart_2508215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508232 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 1, 1, 4]
def baseStart_2508232 : Nat := 118140960795 + 2508232 * 2 ^ 59
def prefixEnd_2508232 : Nat := 4983230072969 + 3 ^ 40 * 2508232 * 2
def baseEnd_2508232 : Nat := 1287928608988135764464857

theorem tailTrace_2508232 : CollatzResearch.WordTrace tailWord_2508232 prefixEnd_2508232 1287928608988135764464857 := by
  unfold tailWord_2508232
  simp only [CollatzResearch.WordTrace]
  refine ⟨45741368324555655383139475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60988491099407540510852633 45741368324555655383139475)
  ·
    refine ⟨68612052486833483074709213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45741368324555655383139475 68612052486833483074709213)
    ·
      refine ⟨25729519682562556153015955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68612052486833483074709213 25729519682562556153015955)
      ·
        refine ⟨38594279523843834229523933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25729519682562556153015955 38594279523843834229523933)
        ·
          refine ⟨14472854821441437836071475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38594279523843834229523933 14472854821441437836071475)
          ·
            refine ⟨21709282232162156754107213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14472854821441437836071475 21709282232162156754107213)
            ·
              refine ⟨8140980837060808782790205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21709282232162156754107213 8140980837060808782790205)
              ·
                refine ⟨3052867813897803293546327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8140980837060808782790205 3052867813897803293546327)
                ·
                  refine ⟨4579301720846704940319491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052867813897803293546327 4579301720846704940319491)
                  ·
                    refine ⟨6868952581270057410479237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4579301720846704940319491 6868952581270057410479237)
                    ·
                      refine ⟨1287928608988135764464857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6868952581270057410479237 1287928608988135764464857)
                      ·
                        rfl

theorem cell23_2508232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 1, 1, 4].length) (baseStart_2508232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508232 prefixEnd_2508232 := by exact prefixLift 2508232
  have htrace : WordTrace (prefixWord ++ tailWord_2508232) baseStart_2508232 baseEnd_2508232 := by
    simpa [prefixWord, tailWord_2508232, baseEnd_2508232] using wordTrace_append hprefix tailTrace_2508232
  have hstable : (prefixWord ++ tailWord_2508232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508232).length < 2 ^ (prefixWord ++ tailWord_2508232).sum := by decide
  have hdescent : baseEnd_2508232 < baseStart_2508232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508245 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_2508245 : Nat := 118140960795 + 2508245 * 2 ^ 59
def prefixEnd_2508245 : Nat := 4983230072969 + 3 ^ 40 * 2508245 * 2
def baseEnd_2508245 : Nat := 1287935284236644213602297

theorem tailTrace_2508245 : CollatzResearch.WordTrace tailWord_2508245 prefixEnd_2508245 1287935284236644213602297 := by
  unfold tailWord_2508245
  simp only [CollatzResearch.WordTrace]
  refine ⟨91483210798064213986502189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60988807198709475991001459 91483210798064213986502189)
  ·
    refine ⟨34306204049274080244938321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91483210798064213986502189 34306204049274080244938321)
    ·
      refine ⟨25729653036955560183703741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34306204049274080244938321 25729653036955560183703741)
      ·
        refine ⟨9648619888858335068888903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25729653036955560183703741 9648619888858335068888903)
        ·
          refine ⟨14472929833287502603333355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9648619888858335068888903 14472929833287502603333355)
          ·
            refine ⟨21709394749931253905000033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14472929833287502603333355 21709394749931253905000033)
            ·
              refine ⟨16282046062448440428750025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21709394749931253905000033 16282046062448440428750025)
              ·
                refine ⟨12211534546836330321562519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16282046062448440428750025 12211534546836330321562519)
                ·
                  refine ⟨18317301820254495482343779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12211534546836330321562519 18317301820254495482343779)
                  ·
                    refine ⟨27475952730381743223515669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18317301820254495482343779 27475952730381743223515669)
                    ·
                      refine ⟨1287935284236644213602297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27475952730381743223515669 1287935284236644213602297)
                      ·
                        rfl

theorem cell23_2508245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_2508245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508245 prefixEnd_2508245 := by exact prefixLift 2508245
  have htrace : WordTrace (prefixWord ++ tailWord_2508245) baseStart_2508245 baseEnd_2508245 := by
    simpa [prefixWord, tailWord_2508245, baseEnd_2508245] using wordTrace_append hprefix tailTrace_2508245
  have hstable : (prefixWord ++ tailWord_2508245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508245).length < 2 ^ (prefixWord ++ tailWord_2508245).sum := by decide
  have hdescent : baseEnd_2508245 < baseStart_2508245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508249 : List Nat := [1, 2, 1, 2, 4, 2, 1, 3, 3, 2, 2]
def baseStart_2508249 : Nat := 118140960795 + 2508249 * 2 ^ 59
def prefixEnd_2508249 : Nat := 4983230072969 + 3 ^ 40 * 2508249 * 2
def baseEnd_2508249 : Nat := 1287937338159262197952279

theorem tailTrace_2508249 : CollatzResearch.WordTrace tailWord_2508249 prefixEnd_2508249 1287937338159262197952279 := by
  unfold tailWord_2508249
  simp only [CollatzResearch.WordTrace]
  refine ⟨91483356690049722669647801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60988904460033148446431867 91483356690049722669647801)
  ·
    refine ⟨68612517517537292002235851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91483356690049722669647801 68612517517537292002235851)
    ·
      refine ⟨102918776276305938003353777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68612517517537292002235851 102918776276305938003353777)
      ·
        refine ⟨77189082207229453502515333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102918776276305938003353777 77189082207229453502515333)
        ·
          refine ⟨14472952913855522531721625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77189082207229453502515333 14472952913855522531721625)
          ·
            refine ⟨10854714685391641898791219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14472952913855522531721625 10854714685391641898791219)
            ·
              refine ⟨16282072028087462848186829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10854714685391641898791219 16282072028087462848186829)
              ·
                refine ⟨6105777010532798568070061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16282072028087462848186829 6105777010532798568070061)
                ·
                  refine ⟨2289666378949799463026273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6105777010532798568070061 2289666378949799463026273)
                  ·
                    refine ⟨1717249784212349597269705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2289666378949799463026273 1717249784212349597269705)
                    ·
                      refine ⟨1287937338159262197952279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717249784212349597269705 1287937338159262197952279)
                      ·
                        rfl

theorem cell23_2508249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 3, 2, 2].length) (baseStart_2508249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508249 prefixEnd_2508249 := by exact prefixLift 2508249
  have htrace : WordTrace (prefixWord ++ tailWord_2508249) baseStart_2508249 baseEnd_2508249 := by
    simpa [prefixWord, tailWord_2508249, baseEnd_2508249] using wordTrace_append hprefix tailTrace_2508249
  have hstable : (prefixWord ++ tailWord_2508249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508249).length < 2 ^ (prefixWord ++ tailWord_2508249).sum := by decide
  have hdescent : baseEnd_2508249 < baseStart_2508249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508272 : List Nat := [2, 1, 1, 1, 3, 6, 2, 7]
def baseStart_2508272 : Nat := 118140960795 + 2508272 * 2 ^ 59
def prefixEnd_2508272 : Nat := 4983230072969 + 3 ^ 40 * 2508272 * 2
def baseEnd_2508272 : Nat := 47701820304233911406099

theorem tailTrace_2508272 : CollatzResearch.WordTrace tailWord_2508272 prefixEnd_2508272 47701820304233911406099 := by
  unfold tailWord_2508272
  simp only [CollatzResearch.WordTrace]
  refine ⟨45742097784483198798867535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60989463712644265065156713 45742097784483198798867535)
  ·
    refine ⟨68613146676724798198301303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45742097784483198798867535 68613146676724798198301303)
    ·
      refine ⟨102919720015087197297451955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68613146676724798198301303 102919720015087197297451955)
      ·
        refine ⟨154379580022630795946177933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102919720015087197297451955 154379580022630795946177933)
        ·
          refine ⟨57892342508486548479816725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154379580022630795946177933 57892342508486548479816725)
          ·
            refine ⟨2713703555085306959991409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57892342508486548479816725 2713703555085306959991409)
            ·
              refine ⟨2035277666313980219993557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2713703555085306959991409 2035277666313980219993557)
              ·
                refine ⟨47701820304233911406099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2035277666313980219993557 47701820304233911406099)
                ·
                  rfl

theorem cell23_2508272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 2, 7].length) (baseStart_2508272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508272 prefixEnd_2508272 := by exact prefixLift 2508272
  have htrace : WordTrace (prefixWord ++ tailWord_2508272) baseStart_2508272 baseEnd_2508272 := by
    simpa [prefixWord, tailWord_2508272, baseEnd_2508272] using wordTrace_append hprefix tailTrace_2508272
  have hstable : (prefixWord ++ tailWord_2508272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508272).length < 2 ^ (prefixWord ++ tailWord_2508272).sum := by decide
  have hdescent : baseEnd_2508272 < baseStart_2508272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508282 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3]
def baseStart_2508282 : Nat := 118140960795 + 2508282 * 2 ^ 59
def prefixEnd_2508282 : Nat := 4983230072969 + 3 ^ 40 * 2508282 * 2
def baseEnd_2508282 : Nat := 1287954283020860568839627

theorem tailTrace_2508282 : CollatzResearch.WordTrace tailWord_2508282 prefixEnd_2508282 1287954283020860568839627 := by
  unfold tailWord_2508282
  simp only [CollatzResearch.WordTrace]
  refine ⟨22871140074732542326399775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60989706865953446203732733 22871140074732542326399775)
  ·
    refine ⟨34306710112098813489599663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22871140074732542326399775 34306710112098813489599663)
    ·
      refine ⟨51460065168148220234399495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34306710112098813489599663 51460065168148220234399495)
      ·
        refine ⟨77190097752222330351599243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51460065168148220234399495 77190097752222330351599243)
        ·
          refine ⟨115785146628333495527398865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77190097752222330351599243 115785146628333495527398865)
          ·
            refine ⟨86838859971250121645549149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115785146628333495527398865 86838859971250121645549149)
            ·
              refine ⟨32564572489218795617080931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86838859971250121645549149 32564572489218795617080931)
              ·
                refine ⟨48846858733828193425621397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32564572489218795617080931 48846858733828193425621397)
                ·
                  refine ⟨2289696503148196566826003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48846858733828193425621397 2289696503148196566826003)
                  ·
                    refine ⟨3434544754722294850239005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2289696503148196566826003 3434544754722294850239005)
                    ·
                      refine ⟨1287954283020860568839627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3434544754722294850239005 1287954283020860568839627)
                      ·
                        rfl

theorem cell23_2508282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 6, 1, 3].length) (baseStart_2508282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508282 prefixEnd_2508282 := by exact prefixLift 2508282
  have htrace : WordTrace (prefixWord ++ tailWord_2508282) baseStart_2508282 baseEnd_2508282 := by
    simpa [prefixWord, tailWord_2508282, baseEnd_2508282] using wordTrace_append hprefix tailTrace_2508282
  have hstable : (prefixWord ++ tailWord_2508282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508282).length < 2 ^ (prefixWord ++ tailWord_2508282).sum := by decide
  have hdescent : baseEnd_2508282 < baseStart_2508282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508286 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 1, 1, 5]
def baseStart_2508286 : Nat := 118140960795 + 2508286 * 2 ^ 59
def prefixEnd_2508286 : Nat := 4983230072969 + 3 ^ 40 * 2508286 * 2
def baseEnd_2508286 : Nat := 1287956336943478553189609

theorem tailTrace_2508286 : CollatzResearch.WordTrace tailWord_2508286 prefixEnd_2508286 1287956336943478553189609 := by
  unfold tailWord_2508286
  simp only [CollatzResearch.WordTrace]
  refine ⟨11435588273864459748593089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 60989804127277118659163141 11435588273864459748593089)
  ·
    refine ⟨8576691205398344811444817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11435588273864459748593089 8576691205398344811444817)
    ·
      refine ⟨6432518404048758608583613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8576691205398344811444817 6432518404048758608583613)
      ·
        refine ⟨2412194401518284478218855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6432518404048758608583613 2412194401518284478218855)
        ·
          refine ⟨3618291602277426717328283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412194401518284478218855 3618291602277426717328283)
          ·
            refine ⟨5427437403416140075992425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618291602277426717328283 5427437403416140075992425)
            ·
              refine ⟨4070578052562105056994319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5427437403416140075992425 4070578052562105056994319)
              ·
                refine ⟨6105867078843157585491479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070578052562105056994319 6105867078843157585491479)
                ·
                  refine ⟨9158800618264736378237219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6105867078843157585491479 9158800618264736378237219)
                  ·
                    refine ⟨13738200927397104567355829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9158800618264736378237219 13738200927397104567355829)
                    ·
                      refine ⟨1287956336943478553189609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13738200927397104567355829 1287956336943478553189609)
                      ·
                        rfl

theorem cell23_2508286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_2508286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508286 prefixEnd_2508286 := by exact prefixLift 2508286
  have htrace : WordTrace (prefixWord ++ tailWord_2508286) baseStart_2508286 baseEnd_2508286 := by
    simpa [prefixWord, tailWord_2508286, baseEnd_2508286] using wordTrace_append hprefix tailTrace_2508286
  have hstable : (prefixWord ++ tailWord_2508286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508286).length < 2 ^ (prefixWord ++ tailWord_2508286).sum := by decide
  have hdescent : baseEnd_2508286 < baseStart_2508286 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508294 : List Nat := [6, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_2508294 : Nat := 118140960795 + 2508294 * 2 ^ 59
def prefixEnd_2508294 : Nat := 4983230072969 + 3 ^ 40 * 2508294 * 2
def baseEnd_2508294 : Nat := 1287960444788714521889573

theorem tailTrace_2508294 : CollatzResearch.WordTrace tailWord_2508294 prefixEnd_2508294 1287960444788714521889573 := by
  unfold tailWord_2508294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2858906186715209229844873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 60989998649924463570023957 2858906186715209229844873)
  ·
    refine ⟨2144179640036406922383655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2858906186715209229844873 2144179640036406922383655)
    ·
      refine ⟨3216269460054610383575483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144179640036406922383655 3216269460054610383575483)
      ·
        refine ⟨4824404190081915575363225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3216269460054610383575483 4824404190081915575363225)
        ·
          refine ⟨3618303142561436681522419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4824404190081915575363225 3618303142561436681522419)
          ·
            refine ⟨5427454713842155022283629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618303142561436681522419 5427454713842155022283629)
            ·
              refine ⟨2035295517690808133356361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5427454713842155022283629 2035295517690808133356361)
              ·
                refine ⟨1526471638268106100017271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035295517690808133356361 1526471638268106100017271)
                ·
                  refine ⟨2289707457402159150025907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526471638268106100017271 2289707457402159150025907)
                  ·
                    refine ⟨3434561186103238725038861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2289707457402159150025907 3434561186103238725038861)
                    ·
                      refine ⟨1287960444788714521889573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3434561186103238725038861 1287960444788714521889573)
                      ·
                        rfl

theorem cell23_2508294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_2508294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508294 prefixEnd_2508294 := by exact prefixLift 2508294
  have htrace : WordTrace (prefixWord ++ tailWord_2508294) baseStart_2508294 baseEnd_2508294 := by
    simpa [prefixWord, tailWord_2508294, baseEnd_2508294] using wordTrace_append hprefix tailTrace_2508294
  have hstable : (prefixWord ++ tailWord_2508294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508294).length < 2 ^ (prefixWord ++ tailWord_2508294).sum := by decide
  have hdescent : baseEnd_2508294 < baseStart_2508294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508300 : List Nat := [2, 2, 1, 2, 5, 1, 3, 2, 1, 2, 2]
def baseStart_2508300 : Nat := 118140960795 + 2508300 * 2 ^ 59
def prefixEnd_2508300 : Nat := 4983230072969 + 3 ^ 40 * 2508300 * 2
def baseEnd_2508300 : Nat := 1287963525672641498414545

theorem tailTrace_2508300 : CollatzResearch.WordTrace tailWord_2508300 prefixEnd_2508300 1287963525672641498414545 := by
  unfold tailWord_2508300
  simp only [CollatzResearch.WordTrace]
  refine ⟨45742608406432479189877177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60990144541909972253169569 45742608406432479189877177)
  ·
    refine ⟨34306956304824359392407883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45742608406432479189877177 34306956304824359392407883)
    ·
      refine ⟨51460434457236539088611825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34306956304824359392407883 51460434457236539088611825)
      ·
        refine ⟨38595325842927404316458869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51460434457236539088611825 38595325842927404316458869)
        ·
          refine ⟨3618311797774444154668019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38595325842927404316458869 3618311797774444154668019)
          ·
            refine ⟨5427467696661666232002029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3618311797774444154668019 5427467696661666232002029)
            ·
              refine ⟨2035300386248124837000761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5427467696661666232002029 2035300386248124837000761)
              ·
                refine ⟨1526475289686093627750571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035300386248124837000761 1526475289686093627750571)
                ·
                  refine ⟨2289712934529140441625857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526475289686093627750571 2289712934529140441625857)
                  ·
                    refine ⟨1717284700896855331219393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2289712934529140441625857 1717284700896855331219393)
                    ·
                      refine ⟨1287963525672641498414545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717284700896855331219393 1287963525672641498414545)
                      ·
                        rfl

theorem cell23_2508300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 2, 1, 2, 2].length) (baseStart_2508300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508300 prefixEnd_2508300 := by exact prefixLift 2508300
  have htrace : WordTrace (prefixWord ++ tailWord_2508300) baseStart_2508300 baseEnd_2508300 := by
    simpa [prefixWord, tailWord_2508300, baseEnd_2508300] using wordTrace_append hprefix tailTrace_2508300
  have hstable : (prefixWord ++ tailWord_2508300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508300).length < 2 ^ (prefixWord ++ tailWord_2508300).sum := by decide
  have hdescent : baseEnd_2508300 < baseStart_2508300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508305 : List Nat := [1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 4]
def baseStart_2508305 : Nat := 118140960795 + 2508305 * 2 ^ 59
def prefixEnd_2508305 : Nat := 4983230072969 + 3 ^ 40 * 2508305 * 2
def baseEnd_2508305 : Nat := 1287966093075913978852021

theorem tailTrace_2508305 : CollatzResearch.WordTrace tailWord_2508305 prefixEnd_2508305 1287966093075913978852021 := by
  unfold tailWord_2508305
  simp only [CollatzResearch.WordTrace]
  refine ⟨91485399177846844233686369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60990266118564562822457579 91485399177846844233686369)
  ·
    refine ⟨68614049383385133175264777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91485399177846844233686369 68614049383385133175264777)
    ·
      refine ⟨51460537037538849881448583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68614049383385133175264777 51460537037538849881448583)
      ·
        refine ⟨77190805556308274822172875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51460537037538849881448583 77190805556308274822172875)
        ·
          refine ⟨115786208334462412233259313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77190805556308274822172875 115786208334462412233259313)
          ·
            refine ⟨86839656250846809174944485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115786208334462412233259313 86839656250846809174944485)
            ·
              refine ⟨16282435547033776720302091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86839656250846809174944485 16282435547033776720302091)
              ·
                refine ⟨24423653320550665080453137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16282435547033776720302091 24423653320550665080453137)
                ·
                  refine ⟨18317739990412998810339853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24423653320550665080453137 18317739990412998810339853)
                  ·
                    refine ⟨6869152496404874553877445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18317739990412998810339853 6869152496404874553877445)
                    ·
                      refine ⟨1287966093075913978852021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6869152496404874553877445 1287966093075913978852021)
                      ·
                        rfl

theorem cell23_2508305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_2508305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508305 prefixEnd_2508305 := by exact prefixLift 2508305
  have htrace : WordTrace (prefixWord ++ tailWord_2508305) baseStart_2508305 baseEnd_2508305 := by
    simpa [prefixWord, tailWord_2508305, baseEnd_2508305] using wordTrace_append hprefix tailTrace_2508305
  have hstable : (prefixWord ++ tailWord_2508305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508305).length < 2 ^ (prefixWord ++ tailWord_2508305).sum := by decide
  have hdescent : baseEnd_2508305 < baseStart_2508305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508339 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 1, 4, 2]
def baseStart_2508339 : Nat := 118140960795 + 2508339 * 2 ^ 59
def prefixEnd_2508339 : Nat := 4983230072969 + 3 ^ 40 * 2508339 * 2
def baseEnd_2508339 : Nat := 1287983551418166845826865

theorem tailTrace_2508339 : CollatzResearch.WordTrace tailWord_2508339 prefixEnd_2508339 1287983551418166845826865 := by
  unfold tailWord_2508339
  simp only [CollatzResearch.WordTrace]
  refine ⟨91486639259723668040424071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60991092839815778693616047 91486639259723668040424071)
  ·
    refine ⟨137229958889585502060636107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91486639259723668040424071 137229958889585502060636107)
    ·
      refine ⟨205844938334378253090954161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137229958889585502060636107 205844938334378253090954161)
      ·
        refine ⟨154383703750783689818215621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205844938334378253090954161 154383703750783689818215621)
        ·
          refine ⟨28946944453271941840915429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154383703750783689818215621 28946944453271941840915429)
          ·
            refine ⟨5427552084988489095171643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28946944453271941840915429 5427552084988489095171643)
            ·
              refine ⟨8141328127482733642757465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5427552084988489095171643 8141328127482733642757465)
              ·
                refine ⟨6105996095612050232068099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8141328127482733642757465 6105996095612050232068099)
                ·
                  refine ⟨9158994143418075348102149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6105996095612050232068099 9158994143418075348102149)
                  ·
                    refine ⟨1717311401890889127769153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9158994143418075348102149 1717311401890889127769153)
                    ·
                      refine ⟨1287983551418166845826865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717311401890889127769153 1287983551418166845826865)
                      ·
                        rfl

theorem cell23_2508339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 4, 2].length) (baseStart_2508339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508339 prefixEnd_2508339 := by exact prefixLift 2508339
  have htrace : WordTrace (prefixWord ++ tailWord_2508339) baseStart_2508339 baseEnd_2508339 := by
    simpa [prefixWord, tailWord_2508339, baseEnd_2508339] using wordTrace_append hprefix tailTrace_2508339
  have hstable : (prefixWord ++ tailWord_2508339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508339).length < 2 ^ (prefixWord ++ tailWord_2508339).sum := by decide
  have hdescent : baseEnd_2508339 < baseStart_2508339 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508412 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 4, 1, 4]
def baseStart_2508412 : Nat := 118140960795 + 2508412 * 2 ^ 59
def prefixEnd_2508412 : Nat := 4983230072969 + 3 ^ 40 * 2508412 * 2
def baseEnd_2508412 : Nat := 1288021035505945060214029

theorem tailTrace_2508412 : CollatzResearch.WordTrace tailWord_2508412 prefixEnd_2508412 1288021035505945060214029 := by
  unfold tailWord_2508412
  simp only [CollatzResearch.WordTrace]
  refine ⟨45744650894229600753915745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60992867858972801005220993 45744650894229600753915745)
  ·
    refine ⟨34308488170672200565436809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45744650894229600753915745 34308488170672200565436809)
    ·
      refine ⟨25731366128004150424077607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34308488170672200565436809 25731366128004150424077607)
      ·
        refine ⟨38597049192006225636116411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25731366128004150424077607 38597049192006225636116411)
        ·
          refine ⟨57895573788009338454174617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38597049192006225636116411 57895573788009338454174617)
          ·
            refine ⟨43421680341007003840630963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57895573788009338454174617 43421680341007003840630963)
            ·
              refine ⟨65132520511510505760946445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43421680341007003840630963 65132520511510505760946445)
              ·
                refine ⟨24424695191816439660354917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65132520511510505760946445 24424695191816439660354917)
                ·
                  refine ⟨4579630348465582436316547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24424695191816439660354917 4579630348465582436316547)
                  ·
                    refine ⟨6869445522698373654474821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4579630348465582436316547 6869445522698373654474821)
                    ·
                      refine ⟨1288021035505945060214029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6869445522698373654474821 1288021035505945060214029)
                      ·
                        rfl

theorem cell23_2508412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_2508412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508412 prefixEnd_2508412 := by exact prefixLift 2508412
  have htrace : WordTrace (prefixWord ++ tailWord_2508412) baseStart_2508412 baseEnd_2508412 := by
    simpa [prefixWord, tailWord_2508412, baseEnd_2508412] using wordTrace_append hprefix tailTrace_2508412
  have hstable : (prefixWord ++ tailWord_2508412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508412).length < 2 ^ (prefixWord ++ tailWord_2508412).sum := by decide
  have hdescent : baseEnd_2508412 < baseStart_2508412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508435 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 12]
def baseStart_2508435 : Nat := 118140960795 + 2508435 * 2 ^ 59
def prefixEnd_2508435 : Nat := 4983230072969 + 3 ^ 40 * 2508435 * 2
def baseEnd_2508435 : Nat := 143114760617888718914047

theorem tailTrace_2508435 : CollatzResearch.WordTrace tailWord_2508435 prefixEnd_2508435 143114760617888718914047 := by
  unfold tailWord_2508435
  simp only [CollatzResearch.WordTrace]
  refine ⟨91490140667375876435918759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60993427111583917623945839 91490140667375876435918759)
  ·
    refine ⟨137235211001063814653878139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91490140667375876435918759 137235211001063814653878139)
    ·
      refine ⟨205852816501595721980817209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137235211001063814653878139 205852816501595721980817209)
      ·
        refine ⟨154389612376196791485612907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205852816501595721980817209 154389612376196791485612907)
        ·
          refine ⟨231584418564295187228419361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154389612376196791485612907 231584418564295187228419361)
          ·
            refine ⟨173688313923221390421314521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231584418564295187228419361 173688313923221390421314521)
            ·
              refine ⟨130266235442416042815985891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173688313923221390421314521 130266235442416042815985891)
              ·
                refine ⟨195399353163624064223978837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130266235442416042815985891 195399353163624064223978837)
                ·
                  refine ⟨143114760617888718914047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 195399353163624064223978837 143114760617888718914047)
                  ·
                    rfl

theorem cell23_2508435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 12].length) (baseStart_2508435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508435 prefixEnd_2508435 := by exact prefixLift 2508435
  have htrace : WordTrace (prefixWord ++ tailWord_2508435) baseStart_2508435 baseEnd_2508435 := by
    simpa [prefixWord, tailWord_2508435, baseEnd_2508435] using wordTrace_append hprefix tailTrace_2508435
  have hstable : (prefixWord ++ tailWord_2508435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508435).length < 2 ^ (prefixWord ++ tailWord_2508435).sum := by decide
  have hdescent : baseEnd_2508435 < baseStart_2508435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508439 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 3, 4]
def baseStart_2508439 : Nat := 118140960795 + 2508439 * 2 ^ 59
def prefixEnd_2508439 : Nat := 4983230072969 + 3 ^ 40 * 2508439 * 2
def baseEnd_2508439 : Nat := 429344966494538818192135

theorem tailTrace_2508439 : CollatzResearch.WordTrace tailWord_2508439 prefixEnd_2508439 429344966494538818192135 := by
  unfold tailWord_2508439
  simp only [CollatzResearch.WordTrace]
  refine ⟨91490286559361385119064371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60993524372907590079376247 91490286559361385119064371)
  ·
    refine ⟨137235429839042077678596557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91490286559361385119064371 137235429839042077678596557)
    ·
      refine ⟨51463286189640779129473709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137235429839042077678596557 51463286189640779129473709)
      ·
        refine ⟨19298732321115292173552641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51463286189640779129473709 19298732321115292173552641)
        ·
          refine ⟨14474049240836469130164481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19298732321115292173552641 14474049240836469130164481)
          ·
            refine ⟨10855536930627351847623361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14474049240836469130164481 10855536930627351847623361)
            ·
              refine ⟨8141652697970513885717521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10855536930627351847623361 8141652697970513885717521)
              ·
                refine ⟨6106239523477885414288141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8141652697970513885717521 6106239523477885414288141)
                ·
                  refine ⟨2289839821304207030358053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6106239523477885414288141 2289839821304207030358053)
                  ·
                    refine ⟨429344966494538818192135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2289839821304207030358053 429344966494538818192135)
                    ·
                      rfl

theorem cell23_2508439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 4].length) (baseStart_2508439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508439 prefixEnd_2508439 := by exact prefixLift 2508439
  have htrace : WordTrace (prefixWord ++ tailWord_2508439) baseStart_2508439 baseEnd_2508439 := by
    simpa [prefixWord, tailWord_2508439, baseEnd_2508439] using wordTrace_append hprefix tailTrace_2508439
  have hstable : (prefixWord ++ tailWord_2508439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508439).length < 2 ^ (prefixWord ++ tailWord_2508439).sum := by decide
  have hdescent : baseEnd_2508439 < baseStart_2508439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508449 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 3]
def baseStart_2508449 : Nat := 118140960795 + 2508449 * 2 ^ 59
def prefixEnd_2508449 : Nat := 4983230072969 + 3 ^ 40 * 2508449 * 2
def baseEnd_2508449 : Nat := 1288040034290161415451359

theorem tailTrace_2508449 : CollatzResearch.WordTrace tailWord_2508449 prefixEnd_2508449 1288040034290161415451359 := by
  unfold tailWord_2508449
  simp only [CollatzResearch.WordTrace]
  refine ⟨91490651289325156826928401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60993767526216771217952267 91490651289325156826928401)
  ·
    refine ⟨68617988466993867620196301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91490651289325156826928401 68617988466993867620196301)
    ·
      refine ⟨25731745675122700357573613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68617988466993867620196301 25731745675122700357573613)
      ·
        refine ⟨9649404628171012634090105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25731745675122700357573613 9649404628171012634090105)
        ·
          refine ⟨7237053471128259475567579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9649404628171012634090105 7237053471128259475567579)
          ·
            refine ⟨10855580206692389213351369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7237053471128259475567579 10855580206692389213351369)
            ·
              refine ⟨8141685155019291910013527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10855580206692389213351369 8141685155019291910013527)
              ·
                refine ⟨12212527732528937865020291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8141685155019291910013527 12212527732528937865020291)
                ·
                  refine ⟨18318791598793406797530437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12212527732528937865020291 18318791598793406797530437)
                  ·
                    refine ⟨3434773424773763774536957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18318791598793406797530437 3434773424773763774536957)
                    ·
                      refine ⟨1288040034290161415451359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3434773424773763774536957 1288040034290161415451359)
                      ·
                        rfl

theorem cell23_2508449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_2508449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508449 prefixEnd_2508449 := by exact prefixLift 2508449
  have htrace : WordTrace (prefixWord ++ tailWord_2508449) baseStart_2508449 baseEnd_2508449 := by
    simpa [prefixWord, tailWord_2508449, baseEnd_2508449] using wordTrace_append hprefix tailTrace_2508449
  have hstable : (prefixWord ++ tailWord_2508449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508449).length < 2 ^ (prefixWord ++ tailWord_2508449).sum := by decide
  have hdescent : baseEnd_2508449 < baseStart_2508449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508452 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 8]
def baseStart_2508452 : Nat := 118140960795 + 2508452 * 2 ^ 59
def prefixEnd_2508452 : Nat := 4983230072969 + 3 ^ 40 * 2508452 * 2
def baseEnd_2508452 : Nat := 143115730525791655968205

theorem tailTrace_2508452 : CollatzResearch.WordTrace tailWord_2508452 prefixEnd_2508452 143115730525791655968205 := by
  unfold tailWord_2508452
  simp only [CollatzResearch.WordTrace]
  refine ⟨45745380354157144169643805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60993840472209525559525073 45745380354157144169643805)
  ·
    refine ⟨17154517632808929063616427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45745380354157144169643805 17154517632808929063616427)
    ·
      refine ⟨25731776449213393595424641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17154517632808929063616427 25731776449213393595424641)
      ·
        refine ⟨19298832336910045196568481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25731776449213393595424641 19298832336910045196568481)
        ·
          refine ⟨14474124252682533897426361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19298832336910045196568481 14474124252682533897426361)
          ·
            refine ⟨10855593189511900423069771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14474124252682533897426361 10855593189511900423069771)
            ·
              refine ⟨16283389784267850634604657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10855593189511900423069771 16283389784267850634604657)
              ·
                refine ⟨12212542338200887975953493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16283389784267850634604657 12212542338200887975953493)
                ·
                  refine ⟨143115730525791655968205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12212542338200887975953493 143115730525791655968205)
                  ·
                    rfl

theorem cell23_2508452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_2508452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508452 prefixEnd_2508452 := by exact prefixLift 2508452
  have htrace : WordTrace (prefixWord ++ tailWord_2508452) baseStart_2508452 baseEnd_2508452 := by
    simpa [prefixWord, tailWord_2508452, baseEnd_2508452] using wordTrace_append hprefix tailTrace_2508452
  have hstable : (prefixWord ++ tailWord_2508452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508452).length < 2 ^ (prefixWord ++ tailWord_2508452).sum := by decide
  have hdescent : baseEnd_2508452 < baseStart_2508452 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508506 : List Nat := [3, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2]
def baseStart_2508506 : Nat := 118140960795 + 2508506 * 2 ^ 59
def prefixEnd_2508506 : Nat := 4983230072969 + 3 ^ 40 * 2508506 * 2
def baseEnd_2508506 : Nat := 1288069302687467692438597

theorem tailTrace_2508506 : CollatzResearch.WordTrace tailWord_2508506 prefixEnd_2508506 1288069302687467692438597 := by
  unfold tailWord_2508506
  simp only [CollatzResearch.WordTrace]
  refine ⟨22873182562529663890438343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60995153500079103707835581 22873182562529663890438343)
  ·
    refine ⟨34309773843794495835657515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22873182562529663890438343 34309773843794495835657515)
    ·
      refine ⟨51464660765691743753486273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34309773843794495835657515 51464660765691743753486273)
      ·
        refine ⟨38598495574268807815114705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51464660765691743753486273 38598495574268807815114705)
        ·
          refine ⟨28948871680701605861336029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38598495574268807815114705 28948871680701605861336029)
          ·
            refine ⟨10855826880263102198001011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28948871680701605861336029 10855826880263102198001011)
            ·
              refine ⟨16283740320394653297001517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10855826880263102198001011 16283740320394653297001517)
              ·
                refine ⟨6106402620147994986375569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16283740320394653297001517 6106402620147994986375569)
                ·
                  refine ⟨4579801965110996239781677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6106402620147994986375569 4579801965110996239781677)
                  ·
                    refine ⟨1717425736916623589918129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4579801965110996239781677 1717425736916623589918129)
                    ·
                      refine ⟨1288069302687467692438597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717425736916623589918129 1288069302687467692438597)
                      ·
                        rfl

theorem cell23_2508506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2].length) (baseStart_2508506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508506 prefixEnd_2508506 := by exact prefixLift 2508506
  have htrace : WordTrace (prefixWord ++ tailWord_2508506) baseStart_2508506 baseEnd_2508506 := by
    simpa [prefixWord, tailWord_2508506, baseEnd_2508506] using wordTrace_append hprefix tailTrace_2508506
  have hstable : (prefixWord ++ tailWord_2508506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508506).length < 2 ^ (prefixWord ++ tailWord_2508506).sum := by decide
  have hdescent : baseEnd_2508506 < baseStart_2508506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508512 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 3, 6]
def baseStart_2508512 : Nat := 118140960795 + 2508512 * 2 ^ 59
def prefixEnd_2508512 : Nat := 4983230072969 + 3 ^ 40 * 2508512 * 2
def baseEnd_2508512 : Nat := 429357461190464889654523

theorem tailTrace_2508512 : CollatzResearch.WordTrace tailWord_2508512 prefixEnd_2508512 429357461190464889654523 := by
  unfold tailWord_2508512
  simp only [CollatzResearch.WordTrace]
  refine ⟨45746474544048459293235895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60995299392064612390981193 45746474544048459293235895)
  ·
    refine ⟨68619711816072688939853843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45746474544048459293235895 68619711816072688939853843)
    ·
      refine ⟨102929567724109033409780765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68619711816072688939853843 102929567724109033409780765)
      ·
        refine ⟨38598587896540887528667787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102929567724109033409780765 38598587896540887528667787)
        ·
          refine ⟨57897881844811331293001681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38598587896540887528667787 57897881844811331293001681)
          ·
            refine ⟨43423411383608498469751261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57897881844811331293001681 43423411383608498469751261)
            ·
              refine ⟨16283779268853186926156723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43423411383608498469751261 16283779268853186926156723)
              ·
                refine ⟨24425668903279780389235085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16283779268853186926156723 24425668903279780389235085)
                ·
                  refine ⟨9159625838729917645963157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24425668903279780389235085 9159625838729917645963157)
                  ·
                    refine ⟨429357461190464889654523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9159625838729917645963157 429357461190464889654523)
                    ·
                      rfl

theorem cell23_2508512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_2508512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508512 prefixEnd_2508512 := by exact prefixLift 2508512
  have htrace : WordTrace (prefixWord ++ tailWord_2508512) baseStart_2508512 baseEnd_2508512 := by
    simpa [prefixWord, tailWord_2508512, baseEnd_2508512] using wordTrace_append hprefix tailTrace_2508512
  have hstable : (prefixWord ++ tailWord_2508512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508512).length < 2 ^ (prefixWord ++ tailWord_2508512).sum := by decide
  have hdescent : baseEnd_2508512 < baseStart_2508512 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508516 : List Nat := [2, 3, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_2508516 : Nat := 118140960795 + 2508516 * 2 ^ 59
def prefixEnd_2508516 : Nat := 4983230072969 + 3 ^ 40 * 2508516 * 2
def baseEnd_2508516 : Nat := 429358145831337551104517

theorem tailTrace_2508516 : CollatzResearch.WordTrace tailWord_2508516 prefixEnd_2508516 429358145831337551104517 := by
  unfold tailWord_2508516
  simp only [CollatzResearch.WordTrace]
  refine ⟨45746547490041213634808701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60995396653388284846411601 45746547490041213634808701)
  ·
    refine ⟨17154955308765455113053263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45746547490041213634808701 17154955308765455113053263)
    ·
      refine ⟨25732432963148182669579895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17154955308765455113053263 25732432963148182669579895)
      ·
        refine ⟨38598649444722274004369843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25732432963148182669579895 38598649444722274004369843)
        ·
          refine ⟨57897974167083411006554765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38598649444722274004369843 57897974167083411006554765)
          ·
            refine ⟨21711740312656279127458037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57897974167083411006554765 21711740312656279127458037)
            ·
              refine ⟨2035475654311526168199191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21711740312656279127458037 2035475654311526168199191)
              ·
                refine ⟨3053213481467289252298787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035475654311526168199191 3053213481467289252298787)
                ·
                  refine ⟨4579820222200933878448181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053213481467289252298787 4579820222200933878448181)
                  ·
                    refine ⟨429358145831337551104517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4579820222200933878448181 429358145831337551104517)
                    ·
                      rfl

theorem cell23_2508516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_2508516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508516 prefixEnd_2508516 := by exact prefixLift 2508516
  have htrace : WordTrace (prefixWord ++ tailWord_2508516) baseStart_2508516 baseEnd_2508516 := by
    simpa [prefixWord, tailWord_2508516, baseEnd_2508516] using wordTrace_append hprefix tailTrace_2508516
  have hstable : (prefixWord ++ tailWord_2508516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508516).length < 2 ^ (prefixWord ++ tailWord_2508516).sum := by decide
  have hdescent : baseEnd_2508516 < baseStart_2508516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508546 : List Nat := [3, 4, 1, 1, 1, 1, 4, 1, 1, 6]
def baseStart_2508546 : Nat := 118140960795 + 2508546 * 2 ^ 59
def prefixEnd_2508546 : Nat := 4983230072969 + 3 ^ 40 * 2508546 * 2
def baseEnd_2508546 : Nat := 429363280637882511979471

theorem tailTrace_2508546 : CollatzResearch.WordTrace tailWord_2508546 prefixEnd_2508546 429363280637882511979471 := by
  unfold tailWord_2508546
  simp only [CollatzResearch.WordTrace]
  refine ⟨22873547292493435598302373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60996126113315828262139661 22873547292493435598302373)
  ·
    refine ⟨4288790117342519174681695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22873547292493435598302373 4288790117342519174681695)
    ·
      refine ⟨6433185176013778762022543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4288790117342519174681695 6433185176013778762022543)
      ·
        refine ⟨9649777764020668143033815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6433185176013778762022543 9649777764020668143033815)
        ·
          refine ⟨14474666646031002214550723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9649777764020668143033815 14474666646031002214550723)
          ·
            refine ⟨21711999969046503321826085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14474666646031002214550723 21711999969046503321826085)
            ·
              refine ⟨4070999994196219372842391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21711999969046503321826085 4070999994196219372842391)
              ·
                refine ⟨6106499991294329059263587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4070999994196219372842391 6106499991294329059263587)
                ·
                  refine ⟨9159749986941493588895381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6106499991294329059263587 9159749986941493588895381)
                  ·
                    refine ⟨429363280637882511979471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9159749986941493588895381 429363280637882511979471)
                    ·
                      rfl

theorem cell23_2508546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_2508546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508546 prefixEnd_2508546 := by exact prefixLift 2508546
  have htrace : WordTrace (prefixWord ++ tailWord_2508546) baseStart_2508546 baseEnd_2508546 := by
    simpa [prefixWord, tailWord_2508546, baseEnd_2508546] using wordTrace_append hprefix tailTrace_2508546
  have hstable : (prefixWord ++ tailWord_2508546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508546).length < 2 ^ (prefixWord ++ tailWord_2508546).sum := by decide
  have hdescent : baseEnd_2508546 < baseStart_2508546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508570 : List Nat := [3, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2]
def baseStart_2508570 : Nat := 118140960795 + 2508570 * 2 ^ 59
def prefixEnd_2508570 : Nat := 4983230072969 + 3 ^ 40 * 2508570 * 2
def baseEnd_2508570 : Nat := 1288102165449355442038303

theorem tailTrace_2508570 : CollatzResearch.WordTrace tailWord_2508570 prefixEnd_2508570 1288102165449355442038303 := by
  unfold tailWord_2508570
  simp only [CollatzResearch.WordTrace]
  refine ⟨22873766130471698623020791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 60996709681257862994722109 22873766130471698623020791)
  ·
    refine ⟨34310649195707547934531187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22873766130471698623020791 34310649195707547934531187)
    ·
      refine ⟨51465973793561321901796781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34310649195707547934531187 51465973793561321901796781)
      ·
        refine ⟨19299740172585495713173793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51465973793561321901796781 19299740172585495713173793)
        ·
          refine ⟨14474805129439121784880345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19299740172585495713173793 14474805129439121784880345)
          ·
            refine ⟨10856103847079341338660259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14474805129439121784880345 10856103847079341338660259)
            ·
              refine ⟨16284155770619012007990389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10856103847079341338660259 16284155770619012007990389)
              ·
                refine ⟨1526639603495532375749099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16284155770619012007990389 1526639603495532375749099)
                ·
                  refine ⟨2289959405243298563623649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526639603495532375749099 2289959405243298563623649)
                  ·
                    refine ⟨1717469553932473922717737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2289959405243298563623649 1717469553932473922717737)
                    ·
                      refine ⟨1288102165449355442038303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717469553932473922717737 1288102165449355442038303)
                      ·
                        rfl

theorem cell23_2508570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 5, 1, 2, 2].length) (baseStart_2508570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508570 prefixEnd_2508570 := by exact prefixLift 2508570
  have htrace : WordTrace (prefixWord ++ tailWord_2508570) baseStart_2508570 baseEnd_2508570 := by
    simpa [prefixWord, tailWord_2508570, baseEnd_2508570] using wordTrace_append hprefix tailTrace_2508570
  have hstable : (prefixWord ++ tailWord_2508570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508570).length < 2 ^ (prefixWord ++ tailWord_2508570).sum := by decide
  have hdescent : baseEnd_2508570 < baseStart_2508570 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508613 : List Nat := [1, 3, 1, 1, 1, 2, 6, 2, 1, 3, 2]
def baseStart_2508613 : Nat := 118140960795 + 2508613 * 2 ^ 59
def prefixEnd_2508613 : Nat := 4983230072969 + 3 ^ 40 * 2508613 * 2
def baseEnd_2508613 : Nat := 1288124245117498773800605

theorem tailTrace_2508613 : CollatzResearch.WordTrace tailWord_2508613 prefixEnd_2508613 1288124245117498773800605 := by
  unfold tailWord_2508613
  simp only [CollatzResearch.WordTrace]
  refine ⟨91496632860731012835898493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60997755240487341890598995 91496632860731012835898493)
  ·
    refine ⟨34311237322774129813461935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91496632860731012835898493 34311237322774129813461935)
    ·
      refine ⟨51466855984161194720192903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34311237322774129813461935 51466855984161194720192903)
      ·
        refine ⟨77200283976241792080289355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51466855984161194720192903 77200283976241792080289355)
        ·
          refine ⟨115800425964362688120434033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77200283976241792080289355 115800425964362688120434033)
          ·
            refine ⟨86850319473272016090325525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115800425964362688120434033 86850319473272016090325525)
            ·
              refine ⟨4071108725309625754234009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86850319473272016090325525 4071108725309625754234009)
              ·
                refine ⟨3053331543982219315675507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4071108725309625754234009 3053331543982219315675507)
                ·
                  refine ⟨4579997315973328973513261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053331543982219315675507 4579997315973328973513261)
                  ·
                    refine ⟨1717498993489998365067473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4579997315973328973513261 1717498993489998365067473)
                    ·
                      refine ⟨1288124245117498773800605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717498993489998365067473 1288124245117498773800605)
                      ·
                        rfl

theorem cell23_2508613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 1, 3, 2].length) (baseStart_2508613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508613 prefixEnd_2508613 := by exact prefixLift 2508613
  have htrace : WordTrace (prefixWord ++ tailWord_2508613) baseStart_2508613 baseEnd_2508613 := by
    simpa [prefixWord, tailWord_2508613, baseEnd_2508613] using wordTrace_append hprefix tailTrace_2508613
  have hstable : (prefixWord ++ tailWord_2508613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508613).length < 2 ^ (prefixWord ++ tailWord_2508613).sum := by decide
  have hdescent : baseEnd_2508613 < baseStart_2508613 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508629 : List Nat := [1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_2508629 : Nat := 118140960795 + 2508629 * 2 ^ 59
def prefixEnd_2508629 : Nat := 4983230072969 + 3 ^ 40 * 2508629 * 2
def baseEnd_2508629 : Nat := 1288132460807970711200531

theorem tailTrace_2508629 : CollatzResearch.WordTrace tailWord_2508629 prefixEnd_2508629 1288132460807970711200531 := by
  unfold tailWord_2508629
  simp only [CollatzResearch.WordTrace]
  refine ⟨91497216428673047568480941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60998144285782031712320627 91497216428673047568480941)
  ·
    refine ⟨34311456160752392838180353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91497216428673047568480941 34311456160752392838180353)
    ·
      refine ⟨25733592120564294628635265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34311456160752392838180353 25733592120564294628635265)
      ·
        refine ⟨19300194090423220971476449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25733592120564294628635265 19300194090423220971476449)
        ·
          refine ⟨14475145567817415728607337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19300194090423220971476449 14475145567817415728607337)
          ·
            refine ⟨10856359175863061796455503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14475145567817415728607337 10856359175863061796455503)
            ·
              refine ⟨16284538763794592694683255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10856359175863061796455503 16284538763794592694683255)
              ·
                refine ⟨24426808145691889042024883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16284538763794592694683255 24426808145691889042024883)
                ·
                  refine ⟨36640212218537833563037325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24426808145691889042024883 36640212218537833563037325)
                  ·
                    refine ⟨13740079581951687586138997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36640212218537833563037325 13740079581951687586138997)
                    ·
                      refine ⟨1288132460807970711200531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13740079581951687586138997 1288132460807970711200531)
                      ·
                        rfl

theorem cell23_2508629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_2508629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508629 prefixEnd_2508629 := by exact prefixLift 2508629
  have htrace : WordTrace (prefixWord ++ tailWord_2508629) baseStart_2508629 baseEnd_2508629 := by
    simpa [prefixWord, tailWord_2508629, baseEnd_2508629] using wordTrace_append hprefix tailTrace_2508629
  have hstable : (prefixWord ++ tailWord_2508629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508629).length < 2 ^ (prefixWord ++ tailWord_2508629).sum := by decide
  have hdescent : baseEnd_2508629 < baseStart_2508629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508659 : List Nat := [1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 3]
def baseStart_2508659 : Nat := 118140960795 + 2508659 * 2 ^ 59
def prefixEnd_2508659 : Nat := 4983230072969 + 3 ^ 40 * 2508659 * 2
def baseEnd_2508659 : Nat := 1288147865227605593825393

theorem tailTrace_2508659 : CollatzResearch.WordTrace tailWord_2508659 prefixEnd_2508659 1288147865227605593825393 := by
  unfold tailWord_2508659
  simp only [CollatzResearch.WordTrace]
  refine ⟨91498310618564362692073031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60998873745709575128048687 91498310618564362692073031)
  ·
    refine ⟨137247465927846544038109547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91498310618564362692073031 137247465927846544038109547)
    ·
      refine ⟨205871198891769816057164321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137247465927846544038109547 205871198891769816057164321)
      ·
        refine ⟨154403399168827362042873241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205871198891769816057164321 154403399168827362042873241)
        ·
          refine ⟨115802549376620521532154931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154403399168827362042873241 115802549376620521532154931)
          ·
            refine ⟨173703824064930782298232397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115802549376620521532154931 173703824064930782298232397)
            ·
              refine ⟨65138934024349043361837149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173703824064930782298232397 65138934024349043361837149)
              ·
                refine ⟨24427100259130891260688931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65138934024349043361837149 24427100259130891260688931)
                ·
                  refine ⟨36640650388696336891033397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24427100259130891260688931 36640650388696336891033397)
                  ·
                    refine ⟨3435060973940281583534381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36640650388696336891033397 3435060973940281583534381)
                    ·
                      refine ⟨1288147865227605593825393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3435060973940281583534381 1288147865227605593825393)
                      ·
                        rfl

theorem cell23_2508659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 5, 3].length) (baseStart_2508659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508659 prefixEnd_2508659 := by exact prefixLift 2508659
  have htrace : WordTrace (prefixWord ++ tailWord_2508659) baseStart_2508659 baseEnd_2508659 := by
    simpa [prefixWord, tailWord_2508659, baseEnd_2508659] using wordTrace_append hprefix tailTrace_2508659
  have hstable : (prefixWord ++ tailWord_2508659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508659).length < 2 ^ (prefixWord ++ tailWord_2508659).sum := by decide
  have hdescent : baseEnd_2508659 < baseStart_2508659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508689 : List Nat := [1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 5]
def baseStart_2508689 : Nat := 118140960795 + 2508689 * 2 ^ 59
def prefixEnd_2508689 : Nat := 4983230072969 + 3 ^ 40 * 2508689 * 2
def baseEnd_2508689 : Nat := 1288163269647240476450255

theorem tailTrace_2508689 : CollatzResearch.WordTrace tailWord_2508689 prefixEnd_2508689 1288163269647240476450255 := by
  unfold tailWord_2508689
  simp only [CollatzResearch.WordTrace]
  refine ⟨91499404808455677815665121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 60999603205637118543776747 91499404808455677815665121)
  ·
    refine ⟨68624553606341758361748841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91499404808455677815665121 68624553606341758361748841)
    ·
      refine ⟨51468415204756318771311631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68624553606341758361748841 51468415204756318771311631)
      ·
        refine ⟨77202622807134478156967447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51468415204756318771311631 77202622807134478156967447)
        ·
          refine ⟨115803934210701717235451171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77202622807134478156967447 115803934210701717235451171)
          ·
            refine ⟨173705901316052575853176757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115803934210701717235451171 173705901316052575853176757)
            ·
              refine ⟨16284928248379928986235321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173705901316052575853176757 16284928248379928986235321)
              ·
                refine ⟨12213696186284946739676491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16284928248379928986235321 12213696186284946739676491)
                ·
                  refine ⟨18320544279427420109514737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12213696186284946739676491 18320544279427420109514737)
                  ·
                    refine ⟨13740408209570565082136053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18320544279427420109514737 13740408209570565082136053)
                    ·
                      refine ⟨1288163269647240476450255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13740408209570565082136053 1288163269647240476450255)
                      ·
                        rfl

theorem cell23_2508689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_2508689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508689 prefixEnd_2508689 := by exact prefixLift 2508689
  have htrace : WordTrace (prefixWord ++ tailWord_2508689) baseStart_2508689 baseEnd_2508689 := by
    simpa [prefixWord, tailWord_2508689, baseEnd_2508689] using wordTrace_append hprefix tailTrace_2508689
  have hstable : (prefixWord ++ tailWord_2508689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508689).length < 2 ^ (prefixWord ++ tailWord_2508689).sum := by decide
  have hdescent : baseEnd_2508689 < baseStart_2508689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508700 : List Nat := [2, 2, 3, 3, 1, 1, 4, 2, 5]
def baseStart_2508700 : Nat := 118140960795 + 2508700 * 2 ^ 59
def prefixEnd_2508700 : Nat := 4983230072969 + 3 ^ 40 * 2508700 * 2
def baseEnd_2508700 : Nat := 143129879770493325934745

theorem tailTrace_2508700 : CollatzResearch.WordTrace tailWord_2508700 prefixEnd_2508700 143129879770493325934745 := by
  unfold tailWord_2508700
  simp only [CollatzResearch.WordTrace]
  refine ⟨45749903005707913347157777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 60999870674277217796210369 45749903005707913347157777)
  ·
    refine ⟨34312427254280935010368333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45749903005707913347157777 34312427254280935010368333)
    ·
      refine ⟨12867160220355350628888125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34312427254280935010368333 12867160220355350628888125)
      ·
        refine ⟨4825185082633256485833047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12867160220355350628888125 4825185082633256485833047)
        ·
          refine ⟨7237777623949884728749571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4825185082633256485833047 7237777623949884728749571)
          ·
            refine ⟨10856666435924827093124357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7237777623949884728749571 10856666435924827093124357)
            ·
              refine ⟨2035624956735905079960817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10856666435924827093124357 2035624956735905079960817)
              ·
                refine ⟨1526718717551928809970613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035624956735905079960817 1526718717551928809970613)
                ·
                  refine ⟨143129879770493325934745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1526718717551928809970613 143129879770493325934745)
                  ·
                    rfl

theorem cell23_2508700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_2508700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508700 prefixEnd_2508700 := by exact prefixLift 2508700
  have htrace : WordTrace (prefixWord ++ tailWord_2508700) baseStart_2508700 baseEnd_2508700 := by
    simpa [prefixWord, tailWord_2508700, baseEnd_2508700] using wordTrace_append hprefix tailTrace_2508700
  have hstable : (prefixWord ++ tailWord_2508700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508700).length < 2 ^ (prefixWord ++ tailWord_2508700).sum := by decide
  have hdescent : baseEnd_2508700 < baseStart_2508700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508733 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 4]
def baseStart_2508733 : Nat := 118140960795 + 2508733 * 2 ^ 59
def prefixEnd_2508733 : Nat := 4983230072969 + 3 ^ 40 * 2508733 * 2
def baseEnd_2508733 : Nat := 1288185862796038304300053

theorem tailTrace_2508733 : CollatzResearch.WordTrace tailWord_2508733 prefixEnd_2508733 1288185862796038304300053 := by
  unfold tailWord_2508733
  simp only [CollatzResearch.WordTrace]
  refine ⟨91501009620296273330266853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61000673080197515553511235 91501009620296273330266853)
  ·
    refine ⟨17156439303805551249425035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91501009620296273330266853 17156439303805551249425035)
    ·
      refine ⟨25734658955708326874137553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17156439303805551249425035 25734658955708326874137553)
      ·
        refine ⟨19300994216781245155603165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25734658955708326874137553 19300994216781245155603165)
        ·
          refine ⟨7237872831292966933351187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19300994216781245155603165 7237872831292966933351187)
          ·
            refine ⟨10856809246939450400026781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7237872831292966933351187 10856809246939450400026781)
            ·
              refine ⟨4071303467602293900010043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10856809246939450400026781 4071303467602293900010043)
              ·
                refine ⟨6106955201403440850015065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4071303467602293900010043 6106955201403440850015065)
                ·
                  refine ⟨4580216401052580637511299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6106955201403440850015065 4580216401052580637511299)
                  ·
                    refine ⟨6870324601578870956266949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4580216401052580637511299 6870324601578870956266949)
                    ·
                      refine ⟨1288185862796038304300053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6870324601578870956266949 1288185862796038304300053)
                      ·
                        rfl

theorem cell23_2508733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_2508733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508733 prefixEnd_2508733 := by exact prefixLift 2508733
  have htrace : WordTrace (prefixWord ++ tailWord_2508733) baseStart_2508733 baseEnd_2508733 := by
    simpa [prefixWord, tailWord_2508733, baseEnd_2508733] using wordTrace_append hprefix tailTrace_2508733
  have hstable : (prefixWord ++ tailWord_2508733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508733).length < 2 ^ (prefixWord ++ tailWord_2508733).sum := by decide
  have hdescent : baseEnd_2508733 < baseStart_2508733 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508736 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 3]
def baseStart_2508736 : Nat := 118140960795 + 2508736 * 2 ^ 59
def prefixEnd_2508736 : Nat := 4983230072969 + 3 ^ 40 * 2508736 * 2
def baseEnd_2508736 : Nat := 1288187403238001792562539

theorem tailTrace_2508736 : CollatzResearch.WordTrace tailWord_2508736 prefixEnd_2508736 1288187403238001792562539 := by
  unfold tailWord_2508736
  simp only [CollatzResearch.WordTrace]
  refine ⟨45750559519642702421313031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61000746026190269895084041 45750559519642702421313031)
  ·
    refine ⟨68625839279464053631969547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45750559519642702421313031 68625839279464053631969547)
    ·
      refine ⟨102938758919196080447954321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68625839279464053631969547 102938758919196080447954321)
      ·
        refine ⟨77204069189397060335965741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102938758919196080447954321 77204069189397060335965741)
        ·
          refine ⟨28951525946023897625987153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77204069189397060335965741 28951525946023897625987153)
          ·
            refine ⟨21713644459517923219490365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28951525946023897625987153 21713644459517923219490365)
            ·
              refine ⟨8142616672319221207308887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21713644459517923219490365 8142616672319221207308887)
              ·
                refine ⟨12213925008478831810963331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8142616672319221207308887 12213925008478831810963331)
                ·
                  refine ⟨18320887512718247716444997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12213925008478831810963331 18320887512718247716444997)
                  ·
                    refine ⟨3435166408634671446833437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18320887512718247716444997 3435166408634671446833437)
                    ·
                      refine ⟨1288187403238001792562539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3435166408634671446833437 1288187403238001792562539)
                      ·
                        rfl

theorem cell23_2508736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 3].length) (baseStart_2508736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508736 prefixEnd_2508736 := by exact prefixLift 2508736
  have htrace : WordTrace (prefixWord ++ tailWord_2508736) baseStart_2508736 baseEnd_2508736 := by
    simpa [prefixWord, tailWord_2508736, baseEnd_2508736] using wordTrace_append hprefix tailTrace_2508736
  have hstable : (prefixWord ++ tailWord_2508736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508736).length < 2 ^ (prefixWord ++ tailWord_2508736).sum := by decide
  have hdescent : baseEnd_2508736 < baseStart_2508736 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508756 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 8]
def baseStart_2508756 : Nat := 118140960795 + 2508756 * 2 ^ 59
def prefixEnd_2508756 : Nat := 4983230072969 + 3 ^ 40 * 2508756 * 2
def baseEnd_2508756 : Nat := 143133074761232412701383

theorem tailTrace_2508756 : CollatzResearch.WordTrace tailWord_2508756 prefixEnd_2508756 143133074761232412701383 := by
  unfold tailWord_2508756
  simp only [CollatzResearch.WordTrace]
  refine ⟨45750924249606474129177061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61001232332808632172236081 45750924249606474129177061)
  ·
    refine ⟨8578298296801213899220699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45750924249606474129177061 8578298296801213899220699)
    ·
      refine ⟨12867447445201820848831049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8578298296801213899220699 12867447445201820848831049)
      ·
        refine ⟨9650585583901365636623287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12867447445201820848831049 9650585583901365636623287)
        ·
          refine ⟨14475878375852048454934931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9650585583901365636623287 14475878375852048454934931)
          ·
            refine ⟨21713817563778072682402397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14475878375852048454934931 21713817563778072682402397)
            ·
              refine ⟨8142681586416777255900899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21713817563778072682402397 8142681586416777255900899)
              ·
                refine ⟨12214022379625165883851349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8142681586416777255900899 12214022379625165883851349)
                ·
                  refine ⟨143133074761232412701383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12214022379625165883851349 143133074761232412701383)
                  ·
                    rfl

theorem cell23_2508756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_2508756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508756 prefixEnd_2508756 := by exact prefixLift 2508756
  have htrace : WordTrace (prefixWord ++ tailWord_2508756) baseStart_2508756 baseEnd_2508756 := by
    simpa [prefixWord, tailWord_2508756, baseEnd_2508756] using wordTrace_append hprefix tailTrace_2508756
  have hstable : (prefixWord ++ tailWord_2508756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508756).length < 2 ^ (prefixWord ++ tailWord_2508756).sum := by decide
  have hdescent : baseEnd_2508756 < baseStart_2508756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508759 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 8]
def baseStart_2508759 : Nat := 118140960795 + 2508759 * 2 ^ 59
def prefixEnd_2508759 : Nat := 4983230072969 + 3 ^ 40 * 2508759 * 2
def baseEnd_2508759 : Nat := 1288199213293055202574933

theorem tailTrace_2508759 : CollatzResearch.WordTrace tailWord_2508759 prefixEnd_2508759 1288199213293055202574933 := by
  unfold tailWord_2508759
  simp only [CollatzResearch.WordTrace]
  refine ⟨91501957918202079770713331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61001305278801386513808887 91501957918202079770713331)
  ·
    refine ⟨137252936877303119656069997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91501957918202079770713331 137252936877303119656069997)
    ·
      refine ⟨51469851328988669871026249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137252936877303119656069997 51469851328988669871026249)
      ·
        refine ⟨38602388496741502403269687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51469851328988669871026249 38602388496741502403269687)
        ·
          refine ⟨57903582745112253604904531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38602388496741502403269687 57903582745112253604904531)
          ·
            refine ⟨86855374117668380407356797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57903582745112253604904531 86855374117668380407356797)
            ·
              refine ⟨32570765294125642652758799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86855374117668380407356797 32570765294125642652758799)
              ·
                refine ⟨48856147941188463979138199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32570765294125642652758799 48856147941188463979138199)
                ·
                  refine ⟨73284221911782695968707299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48856147941188463979138199 73284221911782695968707299)
                  ·
                    refine ⟨109926332867674043953060949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73284221911782695968707299 109926332867674043953060949)
                    ·
                      refine ⟨1288199213293055202574933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 109926332867674043953060949 1288199213293055202574933)
                      ·
                        rfl

theorem cell23_2508759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 8].length) (baseStart_2508759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508759 prefixEnd_2508759 := by exact prefixLift 2508759
  have htrace : WordTrace (prefixWord ++ tailWord_2508759) baseStart_2508759 baseEnd_2508759 := by
    simpa [prefixWord, tailWord_2508759, baseEnd_2508759] using wordTrace_append hprefix tailTrace_2508759
  have hstable : (prefixWord ++ tailWord_2508759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508759).length < 2 ^ (prefixWord ++ tailWord_2508759).sum := by decide
  have hdescent : baseEnd_2508759 < baseStart_2508759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508779 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 7]
def baseStart_2508779 : Nat := 118140960795 + 2508779 * 2 ^ 59
def prefixEnd_2508779 : Nat := 4983230072969 + 3 ^ 40 * 2508779 * 2
def baseEnd_2508779 : Nat := 1288209482906145124324841

theorem tailTrace_2508779 : CollatzResearch.WordTrace tailWord_2508779 prefixEnd_2508779 1288209482906145124324841 := by
  unfold tailWord_2508779
  simp only [CollatzResearch.WordTrace]
  refine ⟨91502687378129623186441391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61001791585419748790960927 91502687378129623186441391)
  ·
    refine ⟨137254031067194434779662087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91502687378129623186441391 137254031067194434779662087)
    ·
      refine ⟨205881046600791652169493131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137254031067194434779662087 205881046600791652169493131)
      ·
        refine ⟨308821569901187478254239697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205881046600791652169493131 308821569901187478254239697)
        ·
          refine ⟨231616177425890608690679773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308821569901187478254239697 231616177425890608690679773)
          ·
            refine ⟨86856066534708978259004915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231616177425890608690679773 86856066534708978259004915)
            ·
              refine ⟨130284099802063467388507373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86856066534708978259004915 130284099802063467388507373)
              ·
                refine ⟨48856537425773800270690265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130284099802063467388507373 48856537425773800270690265)
                ·
                  refine ⟨36642403069330350203017699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48856537425773800270690265 36642403069330350203017699)
                  ·
                    refine ⟨54963604603995525304526549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36642403069330350203017699 54963604603995525304526549)
                    ·
                      refine ⟨1288209482906145124324841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54963604603995525304526549 1288209482906145124324841)
                      ·
                        rfl

theorem cell23_2508779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_2508779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508779 prefixEnd_2508779 := by exact prefixLift 2508779
  have htrace : WordTrace (prefixWord ++ tailWord_2508779) baseStart_2508779 baseEnd_2508779 := by
    simpa [prefixWord, tailWord_2508779, baseEnd_2508779] using wordTrace_append hprefix tailTrace_2508779
  have hstable : (prefixWord ++ tailWord_2508779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508779).length < 2 ^ (prefixWord ++ tailWord_2508779).sum := by decide
  have hdescent : baseEnd_2508779 < baseStart_2508779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508783 : List Nat := [1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 3]
def baseStart_2508783 : Nat := 118140960795 + 2508783 * 2 ^ 59
def prefixEnd_2508783 : Nat := 4983230072969 + 3 ^ 40 * 2508783 * 2
def baseEnd_2508783 : Nat := 1288211536828763108674823

theorem tailTrace_2508783 : CollatzResearch.WordTrace tailWord_2508783 prefixEnd_2508783 1288211536828763108674823 := by
  unfold tailWord_2508783
  simp only [CollatzResearch.WordTrace]
  refine ⟨91502833270115131869587003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61001888846743421246391335 91502833270115131869587003)
  ·
    refine ⟨137254249905172697804380505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91502833270115131869587003 137254249905172697804380505)
    ·
      refine ⟨102940687428879523353285379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137254249905172697804380505 102940687428879523353285379)
      ·
        refine ⟨154411031143319285029928069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102940687428879523353285379 154411031143319285029928069)
        ·
          refine ⟨28952068339372365943111513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154411031143319285029928069 28952068339372365943111513)
          ·
            refine ⟨21714051254529274457333635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28952068339372365943111513 21714051254529274457333635)
            ·
              refine ⟨32571076881793911686000453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21714051254529274457333635 32571076881793911686000453)
              ·
                refine ⟨6107076915336358441125085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32571076881793911686000453 6107076915336358441125085)
                ·
                  refine ⟨2290153843251134415421907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6107076915336358441125085 2290153843251134415421907)
                  ·
                    refine ⟨3435230764876701623132861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2290153843251134415421907 3435230764876701623132861)
                    ·
                      refine ⟨1288211536828763108674823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3435230764876701623132861 1288211536828763108674823)
                      ·
                        rfl

theorem cell23_2508783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 4, 3, 1, 3].length) (baseStart_2508783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508783 prefixEnd_2508783 := by exact prefixLift 2508783
  have htrace : WordTrace (prefixWord ++ tailWord_2508783) baseStart_2508783 baseEnd_2508783 := by
    simpa [prefixWord, tailWord_2508783, baseEnd_2508783] using wordTrace_append hprefix tailTrace_2508783
  have hstable : (prefixWord ++ tailWord_2508783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508783).length < 2 ^ (prefixWord ++ tailWord_2508783).sum := by decide
  have hdescent : baseEnd_2508783 < baseStart_2508783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508793 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 1, 5, 2]
def baseStart_2508793 : Nat := 118140960795 + 2508793 * 2 ^ 59
def prefixEnd_2508793 : Nat := 4983230072969 + 3 ^ 40 * 2508793 * 2
def baseEnd_2508793 : Nat := 1288216671635308069549777

theorem tailTrace_2508793 : CollatzResearch.WordTrace tailWord_2508793 prefixEnd_2508793 1288216671635308069549777 := by
  unfold tailWord_2508793
  simp only [CollatzResearch.WordTrace]
  refine ⟨91503198000078903577451033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61002132000052602384967355 91503198000078903577451033)
  ·
    refine ⟨68627398500059177683088275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91503198000078903577451033 68627398500059177683088275)
    ·
      refine ⟨102941097750088766524632413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68627398500059177683088275 102941097750088766524632413)
      ·
        refine ⟨38602911656283287446737155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102941097750088766524632413 38602911656283287446737155)
        ·
          refine ⟨57904367484424931170105733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38602911656283287446737155 57904367484424931170105733)
          ·
            refine ⟨10857068903329674594394825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57904367484424931170105733 10857068903329674594394825)
            ·
              refine ⟨8142801677497255945796119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10857068903329674594394825 8142801677497255945796119)
              ·
                refine ⟨12214202516245883918694179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8142801677497255945796119 12214202516245883918694179)
                ·
                  refine ⟨18321303774368825878041269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12214202516245883918694179 18321303774368825878041269)
                  ·
                    refine ⟨1717622228847077426066369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18321303774368825878041269 1717622228847077426066369)
                    ·
                      refine ⟨1288216671635308069549777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717622228847077426066369 1288216671635308069549777)
                      ·
                        rfl

theorem cell23_2508793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 5, 2].length) (baseStart_2508793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508793 prefixEnd_2508793 := by exact prefixLift 2508793
  have htrace : WordTrace (prefixWord ++ tailWord_2508793) baseStart_2508793 baseEnd_2508793 := by
    simpa [prefixWord, tailWord_2508793, baseEnd_2508793] using wordTrace_append hprefix tailTrace_2508793
  have hstable : (prefixWord ++ tailWord_2508793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508793).length < 2 ^ (prefixWord ++ tailWord_2508793).sum := by decide
  have hdescent : baseEnd_2508793 < baseStart_2508793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508800 : List Nat := [2, 1, 1, 2, 1, 1, 1, 9, 1, 1, 3]
def baseStart_2508800 : Nat := 118140960795 + 2508800 * 2 ^ 59
def prefixEnd_2508800 : Nat := 4983230072969 + 3 ^ 40 * 2508800 * 2
def baseEnd_2508800 : Nat := 1288220265999889542162245

theorem tailTrace_2508800 : CollatzResearch.WordTrace tailWord_2508800 prefixEnd_2508800 1288220265999889542162245 := by
  unfold tailWord_2508800
  simp only [CollatzResearch.WordTrace]
  refine ⟨45751726655526771886477927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61002302207369029181970569 45751726655526771886477927)
  ·
    refine ⟨68627589983290157829716891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45751726655526771886477927 68627589983290157829716891)
    ·
      refine ⟨102941384974935236744575337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68627589983290157829716891 102941384974935236744575337)
      ·
        refine ⟨77206038731201427558431503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102941384974935236744575337 77206038731201427558431503)
        ·
          refine ⟨115809058096802141337647255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77206038731201427558431503 115809058096802141337647255)
          ·
            refine ⟨173713587145203212006470883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115809058096802141337647255 173713587145203212006470883)
            ·
              refine ⟨260570380717804818009706325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173713587145203212006470883 260570380717804818009706325)
              ·
                refine ⟨1526779574518387605525623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 260570380717804818009706325 1526779574518387605525623)
                ·
                  refine ⟨2290169361777581408288435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526779574518387605525623 2290169361777581408288435)
                  ·
                    refine ⟨3435254042666372112432653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2290169361777581408288435 3435254042666372112432653)
                    ·
                      refine ⟨1288220265999889542162245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3435254042666372112432653 1288220265999889542162245)
                      ·
                        rfl

theorem cell23_2508800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 9, 1, 1, 3].length) (baseStart_2508800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508800 prefixEnd_2508800 := by exact prefixLift 2508800
  have htrace : WordTrace (prefixWord ++ tailWord_2508800) baseStart_2508800 baseEnd_2508800 := by
    simpa [prefixWord, tailWord_2508800, baseEnd_2508800] using wordTrace_append hprefix tailTrace_2508800
  have hstable : (prefixWord ++ tailWord_2508800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508800).length < 2 ^ (prefixWord ++ tailWord_2508800).sum := by decide
  have hdescent : baseEnd_2508800 < baseStart_2508800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508843 : List Nat := [1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 3]
def baseStart_2508843 : Nat := 118140960795 + 2508843 * 2 ^ 59
def prefixEnd_2508843 : Nat := 4983230072969 + 3 ^ 40 * 2508843 * 2
def baseEnd_2508843 : Nat := 1288242345668032873924547

theorem tailTrace_2508843 : CollatzResearch.WordTrace tailWord_2508843 prefixEnd_2508843 1288242345668032873924547 := by
  unfold tailWord_2508843
  simp only [CollatzResearch.WordTrace]
  refine ⟨91505021649897762116771183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61003347766598508077847455 91505021649897762116771183)
  ·
    refine ⟨137257532474846643175156775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91505021649897762116771183 137257532474846643175156775)
    ·
      refine ⟨205886298712269964762735163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137257532474846643175156775 205886298712269964762735163)
      ·
        refine ⟨308829448068404947144102745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205886298712269964762735163 308829448068404947144102745)
        ·
          refine ⟨231622086051303710358077059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308829448068404947144102745 231622086051303710358077059)
          ·
            refine ⟨347433129076955565537115589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231622086051303710358077059 347433129076955565537115589)
            ·
              refine ⟨65143711701929168538209173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 347433129076955565537115589 65143711701929168538209173)
              ·
                refine ⟨3053611486027929775228555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 65143711701929168538209173 3053611486027929775228555)
                ·
                  refine ⟨4580417229041894662842833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053611486027929775228555 4580417229041894662842833)
                  ·
                    refine ⟨3435312921781420997132125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4580417229041894662842833 3435312921781420997132125)
                    ·
                      refine ⟨1288242345668032873924547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3435312921781420997132125 1288242345668032873924547)
                      ·
                        rfl

theorem cell23_2508843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 6, 1, 2, 3].length) (baseStart_2508843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508843 prefixEnd_2508843 := by exact prefixLift 2508843
  have htrace : WordTrace (prefixWord ++ tailWord_2508843) baseStart_2508843 baseEnd_2508843 := by
    simpa [prefixWord, tailWord_2508843, baseEnd_2508843] using wordTrace_append hprefix tailTrace_2508843
  have hstable : (prefixWord ++ tailWord_2508843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508843).length < 2 ^ (prefixWord ++ tailWord_2508843).sum := by decide
  have hdescent : baseEnd_2508843 < baseStart_2508843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508857 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 1, 1, 4]
def baseStart_2508857 : Nat := 118140960795 + 2508857 * 2 ^ 59
def prefixEnd_2508857 : Nat := 4983230072969 + 3 ^ 40 * 2508857 * 2
def baseEnd_2508857 : Nat := 1288249534397195819149483

theorem tailTrace_2508857 : CollatzResearch.WordTrace tailWord_2508857 prefixEnd_2508857 1288249534397195819149483 := by
  unfold tailWord_2508857
  simp only [CollatzResearch.WordTrace]
  refine ⟨91505532271847042507780825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61003688181231361671853883 91505532271847042507780825)
  ·
    refine ⟨68629149203885281880835619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91505532271847042507780825 68629149203885281880835619)
    ·
      refine ⟨102943723805827922821253429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68629149203885281880835619 102943723805827922821253429)
      ·
        refine ⟨9650974106796367764492509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102943723805827922821253429 9650974106796367764492509)
        ·
          refine ⟨3619115290048637911684691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9650974106796367764492509 3619115290048637911684691)
          ·
            refine ⟨5428672935072956867527037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619115290048637911684691 5428672935072956867527037)
            ·
              refine ⟨2035752350652358825322639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5428672935072956867527037 2035752350652358825322639)
              ·
                refine ⟨3053628525978538237983959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2035752350652358825322639 3053628525978538237983959)
                ·
                  refine ⟨4580442788967807356975939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053628525978538237983959 4580442788967807356975939)
                  ·
                    refine ⟨6870664183451711035463909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4580442788967807356975939 6870664183451711035463909)
                    ·
                      refine ⟨1288249534397195819149483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6870664183451711035463909 1288249534397195819149483)
                      ·
                        rfl

theorem cell23_2508857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_2508857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508857 prefixEnd_2508857 := by exact prefixLift 2508857
  have htrace : WordTrace (prefixWord ++ tailWord_2508857) baseStart_2508857 baseEnd_2508857 := by
    simpa [prefixWord, tailWord_2508857, baseEnd_2508857] using wordTrace_append hprefix tailTrace_2508857
  have hstable : (prefixWord ++ tailWord_2508857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508857).length < 2 ^ (prefixWord ++ tailWord_2508857).sum := by decide
  have hdescent : baseEnd_2508857 < baseStart_2508857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508870 : List Nat := [6, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2508870 : Nat := 118140960795 + 2508870 * 2 ^ 59
def prefixEnd_2508870 : Nat := 4983230072969 + 3 ^ 40 * 2508870 * 2
def baseEnd_2508870 : Nat := 1288256209645704268286923

theorem tailTrace_2508870 : CollatzResearch.WordTrace tailWord_2508870 prefixEnd_2508870 1288256209645704268286923 := by
  unfold tailWord_2508870
  simp only [CollatzResearch.WordTrace]
  refine ⟨2859562700649998304000127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61004004280533297152002709 2859562700649998304000127)
  ·
    refine ⟨4289344050974997456000191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2859562700649998304000127 4289344050974997456000191)
    ·
      refine ⟨6434016076462496184000287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4289344050974997456000191 6434016076462496184000287)
      ·
        refine ⟨9651024114693744276000431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6434016076462496184000287 9651024114693744276000431)
        ·
          refine ⟨14476536172040616414000647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9651024114693744276000431 14476536172040616414000647)
          ·
            refine ⟨21714804258060924621000971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14476536172040616414000647 21714804258060924621000971)
            ·
              refine ⟨32572206387091386931501457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21714804258060924621000971 32572206387091386931501457)
              ·
                refine ⟨24429154790318540198626093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32572206387091386931501457 24429154790318540198626093)
                ·
                  refine ⟨9160933046369452574484785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24429154790318540198626093 9160933046369452574484785)
                  ·
                    refine ⟨6870699784777089430863589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9160933046369452574484785 6870699784777089430863589)
                    ·
                      refine ⟨1288256209645704268286923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6870699784777089430863589 1288256209645704268286923)
                      ·
                        rfl

theorem cell23_2508870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2508870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508870 prefixEnd_2508870 := by exact prefixLift 2508870
  have htrace : WordTrace (prefixWord ++ tailWord_2508870) baseStart_2508870 baseEnd_2508870 := by
    simpa [prefixWord, tailWord_2508870, baseEnd_2508870] using wordTrace_append hprefix tailTrace_2508870
  have hstable : (prefixWord ++ tailWord_2508870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508870).length < 2 ^ (prefixWord ++ tailWord_2508870).sum := by decide
  have hdescent : baseEnd_2508870 < baseStart_2508870 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508876 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 2, 7]
def baseStart_2508876 : Nat := 118140960795 + 2508876 * 2 ^ 59
def prefixEnd_2508876 : Nat := 4983230072969 + 3 ^ 40 * 2508876 * 2
def baseEnd_2508876 : Nat := 429419763509877081603965

theorem tailTrace_2508876 : CollatzResearch.WordTrace tailWord_2508876 prefixEnd_2508876 429419763509877081603965 := by
  unfold tailWord_2508876
  simp only [CollatzResearch.WordTrace]
  refine ⟨45753112629389104376361241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61004150172518805835148321 45753112629389104376361241)
  ·
    refine ⟨34314834472041828282270931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45753112629389104376361241 34314834472041828282270931)
    ·
      refine ⟨51472251708062742423406397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34314834472041828282270931 51472251708062742423406397)
      ·
        refine ⟨19302094390523528408777399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51472251708062742423406397 19302094390523528408777399)
        ·
          refine ⟨28953141585785292613166099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19302094390523528408777399 28953141585785292613166099)
          ·
            refine ⟨43429712378677938919749149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28953141585785292613166099 43429712378677938919749149)
            ·
              refine ⟨16286142142004227094905931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43429712378677938919749149 16286142142004227094905931)
              ·
                refine ⟨24429213213006340642358897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16286142142004227094905931 24429213213006340642358897)
                ·
                  refine ⟨18321909909754755481769173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24429213213006340642358897 18321909909754755481769173)
                  ·
                    refine ⟨429419763509877081603965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18321909909754755481769173 429419763509877081603965)
                    ·
                      rfl

theorem cell23_2508876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_2508876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508876 prefixEnd_2508876 := by exact prefixLift 2508876
  have htrace : WordTrace (prefixWord ++ tailWord_2508876) baseStart_2508876 baseEnd_2508876 := by
    simpa [prefixWord, tailWord_2508876, baseEnd_2508876] using wordTrace_append hprefix tailTrace_2508876
  have hstable : (prefixWord ++ tailWord_2508876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508876).length < 2 ^ (prefixWord ++ tailWord_2508876).sum := by decide
  have hdescent : baseEnd_2508876 < baseStart_2508876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508890 : List Nat := [3, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3]
def baseStart_2508890 : Nat := 118140960795 + 2508890 * 2 ^ 59
def prefixEnd_2508890 : Nat := 4983230072969 + 3 ^ 40 * 2508890 * 2
def baseEnd_2508890 : Nat := 1288266479258794190036831

theorem tailTrace_2508890 : CollatzResearch.WordTrace tailWord_2508890 prefixEnd_2508890 1288266479258794190036831 := by
  unfold tailWord_2508890
  simp only [CollatzResearch.WordTrace]
  refine ⟨22876683970181872285933031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61004490587151659429154749 22876683970181872285933031)
  ·
    refine ⟨34315025955272808428899547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22876683970181872285933031 34315025955272808428899547)
    ·
      refine ⟨51472538932909212643349321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34315025955272808428899547 51472538932909212643349321)
      ·
        refine ⟨38604404199681909482511991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51472538932909212643349321 38604404199681909482511991)
        ·
          refine ⟨57906606299522864223767987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38604404199681909482511991 57906606299522864223767987)
          ·
            refine ⟨86859909449284296335651981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57906606299522864223767987 86859909449284296335651981)
            ·
              refine ⟨32572466043481611125869493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86859909449284296335651981 32572466043481611125869493)
              ·
                refine ⟨3053668691576401043050265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32572466043481611125869493 3053668691576401043050265)
                ·
                  refine ⟨2290251518682300782287699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3053668691576401043050265 2290251518682300782287699)
                  ·
                    refine ⟨3435377278023451173431549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2290251518682300782287699 3435377278023451173431549)
                    ·
                      refine ⟨1288266479258794190036831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3435377278023451173431549 1288266479258794190036831)
                      ·
                        rfl

theorem cell23_2508890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 5, 2, 1, 3].length) (baseStart_2508890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508890 prefixEnd_2508890 := by exact prefixLift 2508890
  have htrace : WordTrace (prefixWord ++ tailWord_2508890) baseStart_2508890 baseEnd_2508890 := by
    simpa [prefixWord, tailWord_2508890, baseEnd_2508890] using wordTrace_append hprefix tailTrace_2508890
  have hstable : (prefixWord ++ tailWord_2508890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508890).length < 2 ^ (prefixWord ++ tailWord_2508890).sum := by decide
  have hdescent : baseEnd_2508890 < baseStart_2508890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508900 : List Nat := [2, 3, 1, 1, 2, 1, 4, 1, 3, 3, 2]
def baseStart_2508900 : Nat := 118140960795 + 2508900 * 2 ^ 59
def prefixEnd_2508900 : Nat := 4983230072969 + 3 ^ 40 * 2508900 * 2
def baseEnd_2508900 : Nat := 1288271614065339150911785

theorem tailTrace_2508900 : CollatzResearch.WordTrace tailWord_2508900 prefixEnd_2508900 1288271614065339150911785 := by
  unfold tailWord_2508900
  simp only [CollatzResearch.WordTrace]
  refine ⟨45753550305345630425798077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61004733740460840567730769 45753550305345630425798077)
  ·
    refine ⟨17157581364504611409674279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45753550305345630425798077 17157581364504611409674279)
    ·
      refine ⟨25736372046756917114511419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17157581364504611409674279 25736372046756917114511419)
      ·
        refine ⟨38604558070135375671767129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25736372046756917114511419 38604558070135375671767129)
        ·
          refine ⟨28953418552601531753825347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38604558070135375671767129 28953418552601531753825347)
          ·
            refine ⟨43430127828902297630738021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28953418552601531753825347 43430127828902297630738021)
            ·
              refine ⟨8143148967919180805763379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43430127828902297630738021 8143148967919180805763379)
              ·
                refine ⟨12214723451878771208645069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8143148967919180805763379 12214723451878771208645069)
                ·
                  refine ⟨4580521294454539203241901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12214723451878771208645069 4580521294454539203241901)
                  ·
                    refine ⟨1717695485420452201215713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4580521294454539203241901 1717695485420452201215713)
                    ·
                      refine ⟨1288271614065339150911785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717695485420452201215713 1288271614065339150911785)
                      ·
                        rfl

theorem cell23_2508900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 3, 3, 2].length) (baseStart_2508900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508900 prefixEnd_2508900 := by exact prefixLift 2508900
  have htrace : WordTrace (prefixWord ++ tailWord_2508900) baseStart_2508900 baseEnd_2508900 := by
    simpa [prefixWord, tailWord_2508900, baseEnd_2508900] using wordTrace_append hprefix tailTrace_2508900
  have hstable : (prefixWord ++ tailWord_2508900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508900).length < 2 ^ (prefixWord ++ tailWord_2508900).sum := by decide
  have hdescent : baseEnd_2508900 < baseStart_2508900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2508983 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 4, 5]
def baseStart_2508983 : Nat := 118140960795 + 2508983 * 2 ^ 59
def prefixEnd_2508983 : Nat := 4983230072969 + 3 ^ 40 * 2508983 * 2
def baseEnd_2508983 : Nat := 429438077653220775391301

theorem tailTrace_2508983 : CollatzResearch.WordTrace tailWord_2508983 prefixEnd_2508983 429438077653220775391301 := by
  unfold tailWord_2508983
  simp only [CollatzResearch.WordTrace]
  refine ⟨91510127869390566026867603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61006751912927044017911735 91510127869390566026867603)
  ·
    refine ⟨137265191804085849040301405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91510127869390566026867603 137265191804085849040301405)
    ·
      refine ⟨51474446926532193390113027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137265191804085849040301405 51474446926532193390113027)
      ·
        refine ⟨77211670389798290085169541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51474446926532193390113027 77211670389798290085169541)
        ·
          refine ⟨14477188198087179390969289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77211670389798290085169541 14477188198087179390969289)
          ·
            refine ⟨10857891148565384543226967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14477188198087179390969289 10857891148565384543226967)
            ·
              refine ⟨16286836722848076814840451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10857891148565384543226967 16286836722848076814840451)
              ·
                refine ⟨24430255084272115222260677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16286836722848076814840451 24430255084272115222260677)
                ·
                  refine ⟨4580672828301021604173877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24430255084272115222260677 4580672828301021604173877)
                  ·
                    refine ⟨429438077653220775391301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4580672828301021604173877 429438077653220775391301)
                    ·
                      rfl

theorem cell23_2508983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 4, 5].length) (baseStart_2508983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2508983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2508983 prefixEnd_2508983 := by exact prefixLift 2508983
  have htrace : WordTrace (prefixWord ++ tailWord_2508983) baseStart_2508983 baseEnd_2508983 := by
    simpa [prefixWord, tailWord_2508983, baseEnd_2508983] using wordTrace_append hprefix tailTrace_2508983
  have hstable : (prefixWord ++ tailWord_2508983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2508983).length < 2 ^ (prefixWord ++ tailWord_2508983).sum := by decide
  have hdescent : baseEnd_2508983 < baseStart_2508983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2508983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509003 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 4]
def baseStart_2509003 : Nat := 118140960795 + 2509003 * 2 ^ 59
def prefixEnd_2509003 : Nat := 4983230072969 + 3 ^ 40 * 2509003 * 2
def baseEnd_2509003 : Nat := 1288324502572752247923811

theorem tailTrace_2509003 : CollatzResearch.WordTrace tailWord_2509003 prefixEnd_2509003 1288324502572752247923811 := by
  unfold tailWord_2509003
  simp only [CollatzResearch.WordTrace]
  refine ⟨91510857329318109442595663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61007238219545406295063775 91510857329318109442595663)
  ·
    refine ⟨137266285993977164163893495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91510857329318109442595663 137266285993977164163893495)
    ·
      refine ⟨205899428990965746245840243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137266285993977164163893495 205899428990965746245840243)
      ·
        refine ⟨308849143486448619368760365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205899428990965746245840243 308849143486448619368760365)
        ·
          refine ⟨115818428807418232263285137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308849143486448619368760365 115818428807418232263285137)
          ·
            refine ⟨86863821605563674197463853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115818428807418232263285137 86863821605563674197463853)
            ·
              refine ⟨32573933102086377824048945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86863821605563674197463853 32573933102086377824048945)
              ·
                refine ⟨24430449826564783368036709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32573933102086377824048945 24430449826564783368036709)
                ·
                  refine ⟨4580709342480896881506883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24430449826564783368036709 4580709342480896881506883)
                  ·
                    refine ⟨6871064013721345322260325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4580709342480896881506883 6871064013721345322260325)
                    ·
                      refine ⟨1288324502572752247923811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6871064013721345322260325 1288324502572752247923811)
                      ·
                        rfl

theorem cell23_2509003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 4, 1, 4].length) (baseStart_2509003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509003 prefixEnd_2509003 := by exact prefixLift 2509003
  have htrace : WordTrace (prefixWord ++ tailWord_2509003) baseStart_2509003 baseEnd_2509003 := by
    simpa [prefixWord, tailWord_2509003, baseEnd_2509003] using wordTrace_append hprefix tailTrace_2509003
  have hstable : (prefixWord ++ tailWord_2509003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509003).length < 2 ^ (prefixWord ++ tailWord_2509003).sum := by decide
  have hdescent : baseEnd_2509003 < baseStart_2509003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509103 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 3, 6]
def baseStart_2509103 : Nat := 118140960795 + 2509103 * 2 ^ 59
def prefixEnd_2509103 : Nat := 4983230072969 + 3 ^ 40 * 2509103 * 2
def baseEnd_2509103 : Nat := 429458616879400618891117

theorem tailTrace_2509103 : CollatzResearch.WordTrace tailWord_2509103 prefixEnd_2509103 429458616879400618891117 := by
  unfold tailWord_2509103
  simp only [CollatzResearch.WordTrace]
  refine ⟨91514504628955826521235963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61009669752637217680823975 91514504628955826521235963)
  ·
    refine ⟨137271756943433739781853945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91514504628955826521235963 137271756943433739781853945)
    ·
      refine ⟨102953817707575304836390459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137271756943433739781853945 102953817707575304836390459)
      ·
        refine ⟨154430726561362957254585689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102953817707575304836390459 154430726561362957254585689)
        ·
          refine ⟨115823044921022217940939267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154430726561362957254585689 115823044921022217940939267)
          ·
            refine ⟨173734567381533326911408901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115823044921022217940939267 173734567381533326911408901)
            ·
              refine ⟨32575231384037498795889169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173734567381533326911408901 32575231384037498795889169)
              ·
                refine ⟨24431423538028124096916877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32575231384037498795889169 24431423538028124096916877)
                ·
                  refine ⟨9161783826760546536343829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24431423538028124096916877 9161783826760546536343829)
                  ·
                    refine ⟨429458616879400618891117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9161783826760546536343829 429458616879400618891117)
                    ·
                      rfl

theorem cell23_2509103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 3, 6].length) (baseStart_2509103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509103 prefixEnd_2509103 := by exact prefixLift 2509103
  have htrace : WordTrace (prefixWord ++ tailWord_2509103) baseStart_2509103 baseEnd_2509103 := by
    simpa [prefixWord, tailWord_2509103, baseEnd_2509103] using wordTrace_append hprefix tailTrace_2509103
  have hstable : (prefixWord ++ tailWord_2509103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509103).length < 2 ^ (prefixWord ++ tailWord_2509103).sum := by decide
  have hdescent : baseEnd_2509103 < baseStart_2509103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509127 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 4]
def baseStart_2509127 : Nat := 118140960795 + 2509127 * 2 ^ 59
def prefixEnd_2509127 : Nat := 4983230072969 + 3 ^ 40 * 2509127 * 2
def baseEnd_2509127 : Nat := 1288388174173909762773241

theorem tailTrace_2509127 : CollatzResearch.WordTrace tailWord_2509127 prefixEnd_2509127 1288388174173909762773241 := by
  unfold tailWord_2509127
  simp only [CollatzResearch.WordTrace]
  refine ⟨91515379980868878620109635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61010253320579252413406423 91515379980868878620109635)
  ·
    refine ⟨137273069971303317930164453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91515379980868878620109635 137273069971303317930164453)
    ·
      refine ⟨25738700619619372111905835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137273069971303317930164453 25738700619619372111905835)
      ·
        refine ⟨38608050929429058167858753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25738700619619372111905835 38608050929429058167858753)
        ·
          refine ⟨28956038197071793625894065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38608050929429058167858753 28956038197071793625894065)
          ·
            refine ⟨21717028647803845219420549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28956038197071793625894065 21717028647803845219420549)
            ·
              refine ⟨4071942871463220978641353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21717028647803845219420549 4071942871463220978641353)
              ·
                refine ⟨3053957153597415733981015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4071942871463220978641353 3053957153597415733981015)
                ·
                  refine ⟨4580935730396123600971523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3053957153597415733981015 4580935730396123600971523)
                  ·
                    refine ⟨6871403595594185401457285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4580935730396123600971523 6871403595594185401457285)
                    ·
                      refine ⟨1288388174173909762773241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6871403595594185401457285 1288388174173909762773241)
                      ·
                        rfl

theorem cell23_2509127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 1, 1, 4].length) (baseStart_2509127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509127 prefixEnd_2509127 := by exact prefixLift 2509127
  have htrace : WordTrace (prefixWord ++ tailWord_2509127) baseStart_2509127 baseEnd_2509127 := by
    simpa [prefixWord, tailWord_2509127, baseEnd_2509127] using wordTrace_append hprefix tailTrace_2509127
  have hstable : (prefixWord ++ tailWord_2509127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509127).length < 2 ^ (prefixWord ++ tailWord_2509127).sum := by decide
  have hdescent : baseEnd_2509127 < baseStart_2509127 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509163 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 1, 9]
def baseStart_2509163 : Nat := 118140960795 + 2509163 * 2 ^ 59
def prefixEnd_2509163 : Nat := 4983230072969 + 3 ^ 40 * 2509163 * 2
def baseEnd_2509163 : Nat := 429468886492490540641025

theorem tailTrace_2509163 : CollatzResearch.WordTrace tailWord_2509163 prefixEnd_2509163 429468886492490540641025 := by
  unfold tailWord_2509163
  simp only [CollatzResearch.WordTrace]
  refine ⟨91516693008738456768420143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61011128672492304512280095 91516693008738456768420143)
  ·
    refine ⟨137275039513107685152630215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91516693008738456768420143 137275039513107685152630215)
    ·
      refine ⟨205912559269661527728945323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137275039513107685152630215 205912559269661527728945323)
      ·
        refine ⟨308868838904492291593417985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205912559269661527728945323 308868838904492291593417985)
        ·
          refine ⟨231651629178369218695063489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308868838904492291593417985 231651629178369218695063489)
          ·
            refine ⟨173738721883776914021297617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231651629178369218695063489 173738721883776914021297617)
            ·
              refine ⟨130304041412832685515973213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173738721883776914021297617 130304041412832685515973213)
              ·
                refine ⟨48864015529812257068489955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130304041412832685515973213 48864015529812257068489955)
                ·
                  refine ⟨73296023294718385602734933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48864015529812257068489955 73296023294718385602734933)
                  ·
                    refine ⟨429468886492490540641025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73296023294718385602734933 429468886492490540641025)
                    ·
                      rfl

theorem cell23_2509163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 9].length) (baseStart_2509163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509163 prefixEnd_2509163 := by exact prefixLift 2509163
  have htrace : WordTrace (prefixWord ++ tailWord_2509163) baseStart_2509163 baseEnd_2509163 := by
    simpa [prefixWord, tailWord_2509163, baseEnd_2509163] using wordTrace_append hprefix tailTrace_2509163
  have hstable : (prefixWord ++ tailWord_2509163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509163).length < 2 ^ (prefixWord ++ tailWord_2509163).sum := by decide
  have hdescent : baseEnd_2509163 < baseStart_2509163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509206 : List Nat := [5, 3, 1, 2, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2509206 : Nat := 118140960795 + 2509206 * 2 ^ 59
def prefixEnd_2509206 : Nat := 4983230072969 + 3 ^ 40 * 2509206 * 2
def baseEnd_2509206 : Nat := 1288428739145614953685379

theorem tailTrace_2509206 : CollatzResearch.WordTrace tailWord_2509206 prefixEnd_2509206 1288428739145614953685379 := by
  unfold tailWord_2509206
  simp only [CollatzResearch.WordTrace]
  refine ⟨5719891334223917194514717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61012174231721783408156981 5719891334223917194514717)
  ·
    refine ⟨2144959250333968947943019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5719891334223917194514717 2144959250333968947943019)
    ·
      refine ⟨3217438875500953421914529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2144959250333968947943019 3217438875500953421914529)
      ·
        refine ⟨2413079156625715066435897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3217438875500953421914529 2413079156625715066435897)
        ·
          refine ⟨1809809367469286299826923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2413079156625715066435897 1809809367469286299826923)
          ·
            refine ⟨2714714051203929449740385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1809809367469286299826923 2714714051203929449740385)
            ·
              refine ⟨2036035538402947087305289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2714714051203929449740385 2036035538402947087305289)
              ·
                refine ⟨1527026653802210315478967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036035538402947087305289 1527026653802210315478967)
                ·
                  refine ⟨2290539980703315473218451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527026653802210315478967 2290539980703315473218451)
                  ·
                    refine ⟨3435809971054973209827677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2290539980703315473218451 3435809971054973209827677)
                    ·
                      refine ⟨1288428739145614953685379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3435809971054973209827677 1288428739145614953685379)
                      ·
                        rfl

theorem cell23_2509206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2509206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509206 prefixEnd_2509206 := by exact prefixLift 2509206
  have htrace : WordTrace (prefixWord ++ tailWord_2509206) baseStart_2509206 baseEnd_2509206 := by
    simpa [prefixWord, tailWord_2509206, baseEnd_2509206] using wordTrace_append hprefix tailTrace_2509206
  have hstable : (prefixWord ++ tailWord_2509206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509206).length < 2 ^ (prefixWord ++ tailWord_2509206).sum := by decide
  have hdescent : baseEnd_2509206 < baseStart_2509206 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509220 : List Nat := [2, 3, 1, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_2509220 : Nat := 118140960795 + 2509220 * 2 ^ 59
def prefixEnd_2509220 : Nat := 4983230072969 + 3 ^ 40 * 2509220 * 2
def baseEnd_2509220 : Nat := 1288435927874777898910313

theorem tailTrace_2509220 : CollatzResearch.WordTrace tailWord_2509220 prefixEnd_2509220 1288435927874777898910313 := by
  unfold tailWord_2509220
  simp only [CollatzResearch.WordTrace]
  refine ⟨45759385984765977751622557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61012514646354637002163409 45759385984765977751622557)
  ·
    refine ⟨17159769744287241656858459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45759385984765977751622557 17159769744287241656858459)
    ·
      refine ⟨25739654616430862485287689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17159769744287241656858459 25739654616430862485287689)
      ·
        refine ⟨19304740962323146863965767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25739654616430862485287689 19304740962323146863965767)
        ·
          refine ⟨28957111443484720295948651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19304740962323146863965767 28957111443484720295948651)
          ·
            refine ⟨43435667165227080443922977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28957111443484720295948651 43435667165227080443922977)
            ·
              refine ⟨32576750373920310332942233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43435667165227080443922977 32576750373920310332942233)
              ·
                refine ⟨24432562780440232749706675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32576750373920310332942233 24432562780440232749706675)
                ·
                  refine ⟨36648844170660349124560013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24432562780440232749706675 36648844170660349124560013)
                  ·
                    refine ⟨13743316563997630921710005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36648844170660349124560013 13743316563997630921710005)
                    ·
                      refine ⟨1288435927874777898910313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13743316563997630921710005 1288435927874777898910313)
                      ·
                        rfl

theorem cell23_2509220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_2509220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509220 prefixEnd_2509220 := by exact prefixLift 2509220
  have htrace : WordTrace (prefixWord ++ tailWord_2509220) baseStart_2509220 baseEnd_2509220 := by
    simpa [prefixWord, tailWord_2509220, baseEnd_2509220] using wordTrace_append hprefix tailTrace_2509220
  have hstable : (prefixWord ++ tailWord_2509220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509220).length < 2 ^ (prefixWord ++ tailWord_2509220).sum := by decide
  have hdescent : baseEnd_2509220 < baseStart_2509220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509234 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2]
def baseStart_2509234 : Nat := 118140960795 + 2509234 * 2 ^ 59
def prefixEnd_2509234 : Nat := 4983230072969 + 3 ^ 40 * 2509234 * 2
def baseEnd_2509234 : Nat := 1288443116603940844135249

theorem tailTrace_2509234 : CollatzResearch.WordTrace tailWord_2509234 prefixEnd_2509234 1288443116603940844135249 := by
  unfold tailWord_2509234
  simp only [CollatzResearch.WordTrace]
  refine ⟨22879820647870308973563689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61012855060987490596169837 22879820647870308973563689)
  ·
    refine ⟨17159865485902731730172767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22879820647870308973563689 17159865485902731730172767)
    ·
      refine ⟨25739798228854097595259151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17159865485902731730172767 25739798228854097595259151)
      ·
        refine ⟨38609697343281146392888727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25739798228854097595259151 38609697343281146392888727)
        ·
          refine ⟨57914546014921719589333091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38609697343281146392888727 57914546014921719589333091)
          ·
            refine ⟨86871819022382579383999637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57914546014921719589333091 86871819022382579383999637)
            ·
              refine ⟨4072116516674183408624983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86871819022382579383999637 4072116516674183408624983)
              ·
                refine ⟨6108174775011275112937475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4072116516674183408624983 6108174775011275112937475)
                ·
                  refine ⟨9162262162516912669406213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6108174775011275112937475 9162262162516912669406213)
                  ·
                    refine ⟨1717924155471921125513665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9162262162516912669406213 1717924155471921125513665)
                    ·
                      refine ⟨1288443116603940844135249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717924155471921125513665 1288443116603940844135249)
                      ·
                        rfl

theorem cell23_2509234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 1, 4, 2].length) (baseStart_2509234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509234 prefixEnd_2509234 := by exact prefixLift 2509234
  have htrace : WordTrace (prefixWord ++ tailWord_2509234) baseStart_2509234 baseEnd_2509234 := by
    simpa [prefixWord, tailWord_2509234, baseEnd_2509234] using wordTrace_append hprefix tailTrace_2509234
  have hstable : (prefixWord ++ tailWord_2509234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509234).length < 2 ^ (prefixWord ++ tailWord_2509234).sum := by decide
  have hdescent : baseEnd_2509234 < baseStart_2509234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509257 : List Nat := [1, 2, 1, 1, 2, 1, 5, 5, 5]
def baseStart_2509257 : Nat := 118140960795 + 2509257 * 2 ^ 59
def prefixEnd_2509257 : Nat := 4983230072969 + 3 ^ 40 * 2509257 * 2
def baseEnd_2509257 : Nat := 143161658517666028238627

theorem tailTrace_2509257 : CollatzResearch.WordTrace tailWord_2509257 prefixEnd_2509257 143161658517666028238627 := by
  unfold tailWord_2509257
  simp only [CollatzResearch.WordTrace]
  refine ⟨91520121470397910822342025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61013414313598607214894683 91520121470397910822342025)
  ·
    refine ⟨68640091102798433116756519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91520121470397910822342025 68640091102798433116756519)
    ·
      refine ⟨102960136654197649675134779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68640091102798433116756519 102960136654197649675134779)
      ·
        refine ⟨154440204981296474512702169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102960136654197649675134779 154440204981296474512702169)
        ·
          refine ⟨115830153735972355884526627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154440204981296474512702169 115830153735972355884526627)
          ·
            refine ⟨173745230603958533826789941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115830153735972355884526627 173745230603958533826789941)
            ·
              refine ⟨16288615369121112546261557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173745230603958533826789941 16288615369121112546261557)
              ·
                refine ⟨1527057690855104301212021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16288615369121112546261557 1527057690855104301212021)
                ·
                  refine ⟨143161658517666028238627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1527057690855104301212021 143161658517666028238627)
                  ·
                    rfl

theorem cell23_2509257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 5, 5].length) (baseStart_2509257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509257 prefixEnd_2509257 := by exact prefixLift 2509257
  have htrace : WordTrace (prefixWord ++ tailWord_2509257) baseStart_2509257 baseEnd_2509257 := by
    simpa [prefixWord, tailWord_2509257, baseEnd_2509257] using wordTrace_append hprefix tailTrace_2509257
  have hstable : (prefixWord ++ tailWord_2509257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509257).length < 2 ^ (prefixWord ++ tailWord_2509257).sum := by decide
  have hdescent : baseEnd_2509257 < baseStart_2509257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509268 : List Nat := [2, 4, 1, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_2509268 : Nat := 118140960795 + 2509268 * 2 ^ 59
def prefixEnd_2509268 : Nat := 4983230072969 + 3 ^ 40 * 2509268 * 2
def baseEnd_2509268 : Nat := 1288460574946193711110093

theorem tailTrace_2509268 : CollatzResearch.WordTrace tailWord_2509268 prefixEnd_2509268 1288460574946193711110093 := by
  unfold tailWord_2509268
  simp only [CollatzResearch.WordTrace]
  refine ⟨45760261336679029850496229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61013681782238706467328305 45760261336679029850496229)
  ·
    refine ⟨8580049000627318096968043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45760261336679029850496229 8580049000627318096968043)
    ·
      refine ⟨12870073500940977145452065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8580049000627318096968043 12870073500940977145452065)
      ·
        refine ⟨9652555125705732859089049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12870073500940977145452065 9652555125705732859089049)
        ·
          refine ⟨7239416344279299644316787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9652555125705732859089049 7239416344279299644316787)
          ·
            refine ⟨10859124516418949466475181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7239416344279299644316787 10859124516418949466475181)
            ·
              refine ⟨4072171693657106049928193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10859124516418949466475181 4072171693657106049928193)
              ·
                refine ⟨3054128770242829537446145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4072171693657106049928193 3054128770242829537446145)
                ·
                  refine ⟨2290596577682122153084609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3054128770242829537446145 2290596577682122153084609)
                  ·
                    refine ⟨1717947433261591614813457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2290596577682122153084609 1717947433261591614813457)
                    ·
                      refine ⟨1288460574946193711110093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717947433261591614813457 1288460574946193711110093)
                      ·
                        rfl

theorem cell23_2509268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_2509268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509268 prefixEnd_2509268 := by exact prefixLift 2509268
  have htrace : WordTrace (prefixWord ++ tailWord_2509268) baseStart_2509268 baseEnd_2509268 := by
    simpa [prefixWord, tailWord_2509268, baseEnd_2509268] using wordTrace_append hprefix tailTrace_2509268
  have hstable : (prefixWord ++ tailWord_2509268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509268).length < 2 ^ (prefixWord ++ tailWord_2509268).sum := by decide
  have hdescent : baseEnd_2509268 < baseStart_2509268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509280 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_2509280 : Nat := 118140960795 + 2509280 * 2 ^ 59
def prefixEnd_2509280 : Nat := 4983230072969 + 3 ^ 40 * 2509280 * 2
def baseEnd_2509280 : Nat := 1288466736714047664160037

theorem tailTrace_2509280 : CollatzResearch.WordTrace tailWord_2509280 prefixEnd_2509280 1288466736714047664160037 := by
  unfold tailWord_2509280
  simp only [CollatzResearch.WordTrace]
  refine ⟨45760480174657292875214647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61013973566209723833619529 45760480174657292875214647)
  ·
    refine ⟨68640720261985939312821971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45760480174657292875214647 68640720261985939312821971)
    ·
      refine ⟨102961080392978908969232957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68640720261985939312821971 102961080392978908969232957)
      ·
        refine ⟨38610405147367090863462359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102961080392978908969232957 38610405147367090863462359)
        ·
          refine ⟨57915607721050636295193539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38610405147367090863462359 57915607721050636295193539)
          ·
            refine ⟨86873411581575954442790309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57915607721050636295193539 86873411581575954442790309)
            ·
              refine ⟨16288764671545491458023183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86873411581575954442790309 16288764671545491458023183)
              ·
                refine ⟨24433147007318237187034775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16288764671545491458023183 24433147007318237187034775)
                ·
                  refine ⟨36649720510977355780552163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24433147007318237187034775 36649720510977355780552163)
                  ·
                    refine ⟨54974580766466033670828245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36649720510977355780552163 54974580766466033670828245)
                    ·
                      refine ⟨1288466736714047664160037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 54974580766466033670828245 1288466736714047664160037)
                      ·
                        rfl

theorem cell23_2509280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_2509280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509280 prefixEnd_2509280 := by exact prefixLift 2509280
  have htrace : WordTrace (prefixWord ++ tailWord_2509280) baseStart_2509280 baseEnd_2509280 := by
    simpa [prefixWord, tailWord_2509280, baseEnd_2509280] using wordTrace_append hprefix tailTrace_2509280
  have hstable : (prefixWord ++ tailWord_2509280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509280).length < 2 ^ (prefixWord ++ tailWord_2509280).sum := by decide
  have hdescent : baseEnd_2509280 < baseStart_2509280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509285 : List Nat := [1, 3, 1, 5, 2, 1, 3, 1, 2, 2, 2]
def baseStart_2509285 : Nat := 118140960795 + 2509285 * 2 ^ 59
def prefixEnd_2509285 : Nat := 4983230072969 + 3 ^ 40 * 2509285 * 2
def baseEnd_2509285 : Nat := 1288469304117320144597515

theorem tailTrace_2509285 : CollatzResearch.WordTrace tailWord_2509285 prefixEnd_2509285 1288469304117320144597515 := by
  unfold tailWord_2509285
  simp only [CollatzResearch.WordTrace]
  refine ⟨91521142714296471604361309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61014095142864314402907539 91521142714296471604361309)
  ·
    refine ⟨34320428517861176851635491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91521142714296471604361309 34320428517861176851635491)
    ·
      refine ⟨51480642776791765277453237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34320428517861176851635491 51480642776791765277453237)
      ·
        refine ⟨4826310260324227994761241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51480642776791765277453237 4826310260324227994761241)
        ·
          refine ⟨3619732695243170996070931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4826310260324227994761241 3619732695243170996070931)
          ·
            refine ⟨5429599042864756494106397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619732695243170996070931 5429599042864756494106397)
            ·
              refine ⟨2036099641074283685289899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5429599042864756494106397 2036099641074283685289899)
              ·
                refine ⟨3054149461611425527934849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036099641074283685289899 3054149461611425527934849)
                ·
                  refine ⟨2290612096208569145951137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3054149461611425527934849 2290612096208569145951137)
                  ·
                    refine ⟨1717959072156426859463353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2290612096208569145951137 1717959072156426859463353)
                    ·
                      refine ⟨1288469304117320144597515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1717959072156426859463353 1288469304117320144597515)
                      ·
                        rfl

theorem cell23_2509285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_2509285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509285 prefixEnd_2509285 := by exact prefixLift 2509285
  have htrace : WordTrace (prefixWord ++ tailWord_2509285) baseStart_2509285 baseEnd_2509285 := by
    simpa [prefixWord, tailWord_2509285, baseEnd_2509285] using wordTrace_append hprefix tailTrace_2509285
  have hstable : (prefixWord ++ tailWord_2509285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509285).length < 2 ^ (prefixWord ++ tailWord_2509285).sum := by decide
  have hdescent : baseEnd_2509285 < baseStart_2509285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509317 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 5, 4]
def baseStart_2509317 : Nat := 118140960795 + 2509317 * 2 ^ 59
def prefixEnd_2509317 : Nat := 4983230072969 + 3 ^ 40 * 2509317 * 2
def baseEnd_2509317 : Nat := 429495245166088006465789

theorem tailTrace_2509317 : CollatzResearch.WordTrace tailWord_2509317 prefixEnd_2509317 429495245166088006465789 := by
  unfold tailWord_2509317
  simp only [CollatzResearch.WordTrace]
  refine ⟨91522309850180541069526205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61014873233453694046350803 91522309850180541069526205)
  ·
    refine ⟨34320866193817702901072327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91522309850180541069526205 34320866193817702901072327)
    ·
      refine ⟨51481299290726554351608491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34320866193817702901072327 51481299290726554351608491)
      ·
        refine ⟨77221948936089831527412737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51481299290726554351608491 77221948936089831527412737)
        ·
          refine ⟨57916461702067373645559553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77221948936089831527412737 57916461702067373645559553)
          ·
            refine ⟨43437346276550530234169665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57916461702067373645559553 43437346276550530234169665)
            ·
              refine ⟨32578009707412897675627249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43437346276550530234169665 32578009707412897675627249)
              ·
                refine ⟨24433507280559673256720437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32578009707412897675627249 24433507280559673256720437)
                ·
                  refine ⟨2290641307552469367817541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24433507280559673256720437 2290641307552469367817541)
                  ·
                    refine ⟨429495245166088006465789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2290641307552469367817541 429495245166088006465789)
                    ·
                      rfl

theorem cell23_2509317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 5, 4].length) (baseStart_2509317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509317 prefixEnd_2509317 := by exact prefixLift 2509317
  have htrace : WordTrace (prefixWord ++ tailWord_2509317) baseStart_2509317 baseEnd_2509317 := by
    simpa [prefixWord, tailWord_2509317, baseEnd_2509317] using wordTrace_append hprefix tailTrace_2509317
  have hstable : (prefixWord ++ tailWord_2509317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509317).length < 2 ^ (prefixWord ++ tailWord_2509317).sum := by decide
  have hdescent : baseEnd_2509317 < baseStart_2509317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509324 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 2, 1, 4]
def baseStart_2509324 : Nat := 118140960795 + 2509324 * 2 ^ 59
def prefixEnd_2509324 : Nat := 4983230072969 + 3 ^ 40 * 2509324 * 2
def baseEnd_2509324 : Nat := 1288489329862845492009835

theorem tailTrace_2509324 : CollatzResearch.WordTrace tailWord_2509324 prefixEnd_2509324 1288489329862845492009835 := by
  unfold tailWord_2509324
  simp only [CollatzResearch.WordTrace]
  refine ⟨45761282580577590632515513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61015043440770120843354017 45761282580577590632515513)
  ·
    refine ⟨34320961935433192974386635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45761282580577590632515513 34320961935433192974386635)
    ·
      refine ⟨51481442903149789461579953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34320961935433192974386635 51481442903149789461579953)
      ·
        refine ⟨38611082177362342096184965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51481442903149789461579953 38611082177362342096184965)
        ·
          refine ⟨7239577908255439143034681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38611082177362342096184965 7239577908255439143034681)
          ·
            refine ⟨5429683431191579357276011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7239577908255439143034681 5429683431191579357276011)
            ·
              refine ⟨8144525146787369035914017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5429683431191579357276011 8144525146787369035914017)
              ·
                refine ⟨6108393860090526776935513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8144525146787369035914017 6108393860090526776935513)
                ·
                  refine ⟨4581295395067895082701635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6108393860090526776935513 4581295395067895082701635)
                  ·
                    refine ⟨6871943092601842624052453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4581295395067895082701635 6871943092601842624052453)
                    ·
                      refine ⟨1288489329862845492009835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6871943092601842624052453 1288489329862845492009835)
                      ·
                        rfl

theorem cell23_2509324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_2509324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509324 prefixEnd_2509324 := by exact prefixLift 2509324
  have htrace : WordTrace (prefixWord ++ tailWord_2509324) baseStart_2509324 baseEnd_2509324 := by
    simpa [prefixWord, tailWord_2509324, baseEnd_2509324] using wordTrace_append hprefix tailTrace_2509324
  have hstable : (prefixWord ++ tailWord_2509324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509324).length < 2 ^ (prefixWord ++ tailWord_2509324).sum := by decide
  have hdescent : baseEnd_2509324 < baseStart_2509324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509325 : List Nat := [1, 7, 1, 1, 1, 2, 3, 2, 5]
def baseStart_2509325 : Nat := 118140960795 + 2509325 * 2 ^ 59
def prefixEnd_2509325 : Nat := 4983230072969 + 3 ^ 40 * 2509325 * 2
def baseEnd_2509325 : Nat := 143165538149277776455259

theorem tailTrace_2509325 : CollatzResearch.WordTrace tailWord_2509325 prefixEnd_2509325 143165538149277776455259 := by
  unfold tailWord_2509325
  simp only [CollatzResearch.WordTrace]
  refine ⟨91522601634151558435817429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61015067756101038957211619 91522601634151558435817429)
  ·
    refine ⟨2145060975800427150839471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 91522601634151558435817429 2145060975800427150839471)
    ·
      refine ⟨3217591463700640726259207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2145060975800427150839471 3217591463700640726259207)
      ·
        refine ⟨4826387195550961089388811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217591463700640726259207 4826387195550961089388811)
        ·
          refine ⟨7239580793326441634083217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826387195550961089388811 7239580793326441634083217)
          ·
            refine ⟨5429685594994831225562413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7239580793326441634083217 5429685594994831225562413)
            ·
              refine ⟨2036132098123061709585905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5429685594994831225562413 2036132098123061709585905)
              ·
                refine ⟨1527099073592296282189429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036132098123061709585905 1527099073592296282189429)
                ·
                  refine ⟨143165538149277776455259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1527099073592296282189429 143165538149277776455259)
                  ·
                    rfl

theorem cell23_2509325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_2509325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509325 prefixEnd_2509325 := by exact prefixLift 2509325
  have htrace : WordTrace (prefixWord ++ tailWord_2509325) baseStart_2509325 baseEnd_2509325 := by
    simpa [prefixWord, tailWord_2509325, baseEnd_2509325] using wordTrace_append hprefix tailTrace_2509325
  have hstable : (prefixWord ++ tailWord_2509325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509325).length < 2 ^ (prefixWord ++ tailWord_2509325).sum := by decide
  have hdescent : baseEnd_2509325 < baseStart_2509325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509327 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 3]
def baseStart_2509327 : Nat := 118140960795 + 2509327 * 2 ^ 59
def prefixEnd_2509327 : Nat := 4983230072969 + 3 ^ 40 * 2509327 * 2
def baseEnd_2509327 : Nat := 1288490870304808980272321

theorem tailTrace_2509327 : CollatzResearch.WordTrace tailWord_2509327 prefixEnd_2509327 1288490870304808980272321 := by
  unfold tailWord_2509327
  simp only [CollatzResearch.WordTrace]
  refine ⟨91522674580144312777390235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61015116386762875184926823 91522674580144312777390235)
  ·
    refine ⟨137284011870216469166085353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91522674580144312777390235 137284011870216469166085353)
    ·
      refine ⟨102963008902662351874564015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137284011870216469166085353 102963008902662351874564015)
      ·
        refine ⟨154444513353993527811846023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102963008902662351874564015 154444513353993527811846023)
        ·
          refine ⟨231666770030990291717769035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154444513353993527811846023 231666770030990291717769035)
          ·
            refine ⟨347500155046485437576653553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231666770030990291717769035 347500155046485437576653553)
            ·
              refine ⟨260625116284864078182490165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347500155046485437576653553 260625116284864078182490165)
              ·
                refine ⟨24433604651706007329608453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 260625116284864078182490165 24433604651706007329608453)
                ·
                  refine ⟨4581300872194876374301585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24433604651706007329608453 4581300872194876374301585)
                  ·
                    refine ⟨3435975654146157280726189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4581300872194876374301585 3435975654146157280726189)
                    ·
                      refine ⟨1288490870304808980272321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3435975654146157280726189 1288490870304808980272321)
                      ·
                        rfl

theorem cell23_2509327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 2, 3].length) (baseStart_2509327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509327 prefixEnd_2509327 := by exact prefixLift 2509327
  have htrace : WordTrace (prefixWord ++ tailWord_2509327) baseStart_2509327 baseEnd_2509327 := by
    simpa [prefixWord, tailWord_2509327, baseEnd_2509327] using wordTrace_append hprefix tailTrace_2509327
  have hstable : (prefixWord ++ tailWord_2509327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509327).length < 2 ^ (prefixWord ++ tailWord_2509327).sum := by decide
  have hdescent : baseEnd_2509327 < baseStart_2509327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509427 : List Nat := [1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 4]
def baseStart_2509427 : Nat := 118140960795 + 2509427 * 2 ^ 59
def prefixEnd_2509427 : Nat := 4983230072969 + 3 ^ 40 * 2509427 * 2
def baseEnd_2509427 : Nat := 1288542218370258589021861

theorem tailTrace_2509427 : CollatzResearch.WordTrace tailWord_2509427 prefixEnd_2509427 1288542218370258589021861 := by
  unfold tailWord_2509427
  simp only [CollatzResearch.WordTrace]
  refine ⟨91526321879782029856030535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61017547919854686570687023 91526321879782029856030535)
  ·
    refine ⟨137289482819673044784045803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91526321879782029856030535 137289482819673044784045803)
    ·
      refine ⟨205934224229509567176068705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137289482819673044784045803 205934224229509567176068705)
      ·
        refine ⟨154450668172132175382051529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205934224229509567176068705 154450668172132175382051529)
        ·
          refine ⟨115838001129099131536538647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154450668172132175382051529 115838001129099131536538647)
          ·
            refine ⟨173757001693648697304807971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115838001129099131536538647 173757001693648697304807971)
            ·
              refine ⟨260635502540473045957211957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173757001693648697304807971 260635502540473045957211957)
              ·
                refine ⟨24434578363169348058488621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 260635502540473045957211957 24434578363169348058488621)
                ·
                  refine ⟨9162966886188505521933233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24434578363169348058488621 9162966886188505521933233)
                  ·
                    refine ⟨6872225164641379141449925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9162966886188505521933233 6872225164641379141449925)
                    ·
                      refine ⟨1288542218370258589021861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6872225164641379141449925 1288542218370258589021861)
                      ·
                        rfl

theorem cell23_2509427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 4].length) (baseStart_2509427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509427 prefixEnd_2509427 := by exact prefixLift 2509427
  have htrace : WordTrace (prefixWord ++ tailWord_2509427) baseStart_2509427 baseEnd_2509427 := by
    simpa [prefixWord, tailWord_2509427, baseEnd_2509427] using wordTrace_append hprefix tailTrace_2509427
  have hstable : (prefixWord ++ tailWord_2509427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509427).length < 2 ^ (prefixWord ++ tailWord_2509427).sum := by decide
  have hdescent : baseEnd_2509427 < baseStart_2509427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509431 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 1, 1, 4]
def baseStart_2509431 : Nat := 118140960795 + 2509431 * 2 ^ 59
def prefixEnd_2509431 : Nat := 4983230072969 + 3 ^ 40 * 2509431 * 2
def baseEnd_2509431 : Nat := 1288544272292876573371843

theorem tailTrace_2509431 : CollatzResearch.WordTrace tailWord_2509431 prefixEnd_2509431 1288544272292876573371843 := by
  unfold tailWord_2509431
  simp only [CollatzResearch.WordTrace]
  refine ⟨91526467771767538539176147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61017645181178359026117431 91526467771767538539176147)
  ·
    refine ⟨137289701657651307808764221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91526467771767538539176147 137289701657651307808764221)
    ·
      refine ⟨51483638121619240428286583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137289701657651307808764221 51483638121619240428286583)
      ·
        refine ⟨77225457182428860642429875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51483638121619240428286583 77225457182428860642429875)
        ·
          refine ⟨115838185773643290963644813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77225457182428860642429875 115838185773643290963644813)
          ·
            refine ⟨43439319665116234111366805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115838185773643290963644813 43439319665116234111366805)
            ·
              refine ⟨2036218109302323473970319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43439319665116234111366805 2036218109302323473970319)
              ·
                refine ⟨3054327163953485210955479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036218109302323473970319 3054327163953485210955479)
                ·
                  refine ⟨4581490745930227816433219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054327163953485210955479 4581490745930227816433219)
                  ·
                    refine ⟨6872236118895341724649829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4581490745930227816433219 6872236118895341724649829)
                    ·
                      refine ⟨1288544272292876573371843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6872236118895341724649829 1288544272292876573371843)
                      ·
                        rfl

theorem cell23_2509431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 1, 1, 4].length) (baseStart_2509431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509431 prefixEnd_2509431 := by exact prefixLift 2509431
  have htrace : WordTrace (prefixWord ++ tailWord_2509431) baseStart_2509431 baseEnd_2509431 := by
    simpa [prefixWord, tailWord_2509431, baseEnd_2509431] using wordTrace_append hprefix tailTrace_2509431
  have hstable : (prefixWord ++ tailWord_2509431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509431).length < 2 ^ (prefixWord ++ tailWord_2509431).sum := by decide
  have hdescent : baseEnd_2509431 < baseStart_2509431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509468 : List Nat := [2, 2, 3, 2, 2, 2, 2, 2, 1, 2, 3]
def baseStart_2509468 : Nat := 118140960795 + 2509468 * 2 ^ 59
def prefixEnd_2509468 : Nat := 4983230072969 + 3 ^ 40 * 2509468 * 2
def baseEnd_2509468 : Nat := 1288563271077092928609173

theorem tailTrace_2509468 : CollatzResearch.WordTrace tailWord_2509468 prefixEnd_2509468 1288563271077092928609173 := by
  unfold tailWord_2509468
  simp only [CollatzResearch.WordTrace]
  refine ⟨45763908636316746929136529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61018544848422329238848705 45763908636316746929136529)
  ·
    refine ⟨34322931477237560196852397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45763908636316746929136529 34322931477237560196852397)
    ·
      refine ⟨12871099303964085073819649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34322931477237560196852397 12871099303964085073819649)
      ·
        refine ⟨9653324477973063805364737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12871099303964085073819649 9653324477973063805364737)
        ·
          refine ⟨7239993358479797854023553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9653324477973063805364737 7239993358479797854023553)
          ·
            refine ⟨5429995018859848390517665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7239993358479797854023553 5429995018859848390517665)
            ·
              refine ⟨4072496264144886292888249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5429995018859848390517665 4072496264144886292888249)
              ·
                refine ⟨3054372198108664719666187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4072496264144886292888249 3054372198108664719666187)
                ·
                  refine ⟨4581558297162997079499281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054372198108664719666187 4581558297162997079499281)
                  ·
                    refine ⟨3436168722872247809624461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4581558297162997079499281 3436168722872247809624461)
                    ·
                      refine ⟨1288563271077092928609173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3436168722872247809624461 1288563271077092928609173)
                      ·
                        rfl

theorem cell23_2509468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 2, 1, 2, 3].length) (baseStart_2509468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509468 prefixEnd_2509468 := by exact prefixLift 2509468
  have htrace : WordTrace (prefixWord ++ tailWord_2509468) baseStart_2509468 baseEnd_2509468 := by
    simpa [prefixWord, tailWord_2509468, baseEnd_2509468] using wordTrace_append hprefix tailTrace_2509468
  have hstable : (prefixWord ++ tailWord_2509468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509468).length < 2 ^ (prefixWord ++ tailWord_2509468).sum := by decide
  have hdescent : baseEnd_2509468 < baseStart_2509468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509521 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 1, 4, 2]
def baseStart_2509521 : Nat := 118140960795 + 2509521 * 2 ^ 59
def prefixEnd_2509521 : Nat := 4983230072969 + 3 ^ 40 * 2509521 * 2
def baseEnd_2509521 : Nat := 1288590485551781221246429

theorem tailTrace_2509521 : CollatzResearch.WordTrace tailWord_2509521 prefixEnd_2509521 1288590485551781221246429 := by
  unfold tailWord_2509521
  simp only [CollatzResearch.WordTrace]
  refine ⟨91529750341441483909952417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61019833560960989273301611 91529750341441483909952417)
  ·
    refine ⟨68647312756081112932464313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91529750341441483909952417 68647312756081112932464313)
    ·
      refine ⟨51485484567060834699348235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68647312756081112932464313 51485484567060834699348235)
      ·
        refine ⟨77228226850591252049022353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51485484567060834699348235 77228226850591252049022353)
        ·
          refine ⟨57921170137943439036766765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77228226850591252049022353 57921170137943439036766765)
          ·
            refine ⟨21720438801728789638787537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57921170137943439036766765 21720438801728789638787537)
            ·
              refine ⟨16290329101296592229090653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21720438801728789638787537 16290329101296592229090653)
              ·
                refine ⟨6108873412986222085908995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16290329101296592229090653 6108873412986222085908995)
                ·
                  refine ⟨9163310119479333128863493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6108873412986222085908995 9163310119479333128863493)
                  ·
                    refine ⟨1718120647402374961661905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9163310119479333128863493 1718120647402374961661905)
                    ·
                      refine ⟨1288590485551781221246429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718120647402374961661905 1288590485551781221246429)
                      ·
                        rfl

theorem cell23_2509521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 4, 2].length) (baseStart_2509521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509521 prefixEnd_2509521 := by exact prefixLift 2509521
  have htrace : WordTrace (prefixWord ++ tailWord_2509521) baseStart_2509521 baseEnd_2509521 := by
    simpa [prefixWord, tailWord_2509521, baseEnd_2509521] using wordTrace_append hprefix tailTrace_2509521
  have hstable : (prefixWord ++ tailWord_2509521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509521).length < 2 ^ (prefixWord ++ tailWord_2509521).sum := by decide
  have hdescent : baseEnd_2509521 < baseStart_2509521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509525 : List Nat := [1, 3, 2, 5, 1, 1, 1, 1, 3, 3, 2]
def baseStart_2509525 : Nat := 118140960795 + 2509525 * 2 ^ 59
def prefixEnd_2509525 : Nat := 4983230072969 + 3 ^ 40 * 2509525 * 2
def baseEnd_2509525 : Nat := 1288592539474399205596411

theorem tailTrace_2509525 : CollatzResearch.WordTrace tailWord_2509525 prefixEnd_2509525 1288592539474399205596411 := by
  unfold tailWord_2509525
  simp only [CollatzResearch.WordTrace]
  refine ⟨91529896233426992593098029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61019930822284661728732019 91529896233426992593098029)
  ·
    refine ⟨34323711087535122222411761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91529896233426992593098029 34323711087535122222411761)
    ·
      refine ⟨25742783315651341666808821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34323711087535122222411761 25742783315651341666808821)
      ·
        refine ⟨2413385935842313281263327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25742783315651341666808821 2413385935842313281263327)
        ·
          refine ⟨3620078903763469921894991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413385935842313281263327 3620078903763469921894991)
          ·
            refine ⟨5430118355645204882842487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620078903763469921894991 5430118355645204882842487)
            ·
              refine ⟨8145177533467807324263731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430118355645204882842487 8145177533467807324263731)
              ·
                refine ⟨12217766300201710986395597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8145177533467807324263731 12217766300201710986395597)
                ·
                  refine ⟨4581662362575641619898349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12217766300201710986395597 4581662362575641619898349)
                  ·
                    refine ⟨1718123385965865607461881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4581662362575641619898349 1718123385965865607461881)
                    ·
                      refine ⟨1288592539474399205596411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718123385965865607461881 1288592539474399205596411)
                      ·
                        rfl

theorem cell23_2509525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_2509525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509525 prefixEnd_2509525 := by exact prefixLift 2509525
  have htrace : WordTrace (prefixWord ++ tailWord_2509525) baseStart_2509525 baseEnd_2509525 := by
    simpa [prefixWord, tailWord_2509525, baseEnd_2509525] using wordTrace_append hprefix tailTrace_2509525
  have hstable : (prefixWord ++ tailWord_2509525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509525).length < 2 ^ (prefixWord ++ tailWord_2509525).sum := by decide
  have hdescent : baseEnd_2509525 < baseStart_2509525 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509591 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 1, 7]
def baseStart_2509591 : Nat := 118140960795 + 2509591 * 2 ^ 59
def prefixEnd_2509591 : Nat := 4983230072969 + 3 ^ 40 * 2509591 * 2
def baseEnd_2509591 : Nat := 429542143065865315790369

theorem tailTrace_2509591 : CollatzResearch.WordTrace tailWord_2509591 prefixEnd_2509591 429542143065865315790369 := by
  unfold tailWord_2509591
  simp only [CollatzResearch.WordTrace]
  refine ⟨91532303451187885865000627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61021535634125257243333751 91532303451187885865000627)
  ·
    refine ⟨137298455176781828797500941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91532303451187885865000627 137298455176781828797500941)
    ·
      refine ⟨51486920691293185799062853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137298455176781828797500941 51486920691293185799062853)
      ·
        refine ⟨9653797629617472337324285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51486920691293185799062853 9653797629617472337324285)
        ·
          refine ⟨3620174111106552126496607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9653797629617472337324285 3620174111106552126496607)
          ·
            refine ⟨5430261166659828189744911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620174111106552126496607 5430261166659828189744911)
            ·
              refine ⟨8145391749989742284617367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430261166659828189744911 8145391749989742284617367)
              ·
                refine ⟨12218087624984613426926051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8145391749989742284617367 12218087624984613426926051)
                ·
                  refine ⟨18327131437476920140389077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12218087624984613426926051 18327131437476920140389077)
                  ·
                    refine ⟨429542143065865315790369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18327131437476920140389077 429542143065865315790369)
                    ·
                      rfl

theorem cell23_2509591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 7].length) (baseStart_2509591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509591 prefixEnd_2509591 := by exact prefixLift 2509591
  have htrace : WordTrace (prefixWord ++ tailWord_2509591) baseStart_2509591 baseEnd_2509591 := by
    simpa [prefixWord, tailWord_2509591, baseEnd_2509591] using wordTrace_append hprefix tailTrace_2509591
  have hstable : (prefixWord ++ tailWord_2509591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509591).length < 2 ^ (prefixWord ++ tailWord_2509591).sum := by decide
  have hdescent : baseEnd_2509591 < baseStart_2509591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509611 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 2, 4, 2]
def baseStart_2509611 : Nat := 118140960795 + 2509611 * 2 ^ 59
def prefixEnd_2509611 : Nat := 4983230072969 + 3 ^ 40 * 2509611 * 2
def baseEnd_2509611 : Nat := 1288636698810685869121015

theorem tailTrace_2509611 : CollatzResearch.WordTrace tailWord_2509611 prefixEnd_2509611 1288636698810685869121015 := by
  unfold tailWord_2509611
  simp only [CollatzResearch.WordTrace]
  refine ⟨91533032911115429280728687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61022021940743619520485791 91533032911115429280728687)
  ·
    refine ⟨137299549366673143921093031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91533032911115429280728687 137299549366673143921093031)
    ·
      refine ⟨205949324050009715881639547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137299549366673143921093031 205949324050009715881639547)
      ·
        refine ⟨308923986075014573822459321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205949324050009715881639547 308923986075014573822459321)
        ·
          refine ⟨231692989556260930366844491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308923986075014573822459321 231692989556260930366844491)
          ·
            refine ⟨347539484334391395550266737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231692989556260930366844491 347539484334391395550266737)
            ·
              refine ⟨260654613250793546662700053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347539484334391395550266737 260654613250793546662700053)
              ·
                refine ⟨12218184996130947499814065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 260654613250793546662700053 12218184996130947499814065)
                ·
                  refine ⟨9163638747098210624860549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12218184996130947499814065 9163638747098210624860549)
                  ·
                    refine ⟨1718182265080914492161353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9163638747098210624860549 1718182265080914492161353)
                    ·
                      refine ⟨1288636698810685869121015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718182265080914492161353 1288636698810685869121015)
                      ·
                        rfl

theorem cell23_2509611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 2, 4, 2].length) (baseStart_2509611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509611 prefixEnd_2509611 := by exact prefixLift 2509611
  have htrace : WordTrace (prefixWord ++ tailWord_2509611) baseStart_2509611 baseEnd_2509611 := by
    simpa [prefixWord, tailWord_2509611, baseEnd_2509611] using wordTrace_append hprefix tailTrace_2509611
  have hstable : (prefixWord ++ tailWord_2509611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509611).length < 2 ^ (prefixWord ++ tailWord_2509611).sum := by decide
  have hdescent : baseEnd_2509611 < baseStart_2509611 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509624 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2509624 : Nat := 118140960795 + 2509624 * 2 ^ 59
def prefixEnd_2509624 : Nat := 4983230072969 + 3 ^ 40 * 2509624 * 2
def baseEnd_2509624 : Nat := 1288643374059194318258455

theorem tailTrace_2509624 : CollatzResearch.WordTrace tailWord_2509624 prefixEnd_2509624 1288643374059194318258455 := by
  unfold tailWord_2509624
  simp only [CollatzResearch.WordTrace]
  refine ⟨45766753530034166250475963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61022338040045555000634617 45766753530034166250475963)
  ·
    refine ⟨68650130295051249375713945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45766753530034166250475963 68650130295051249375713945)
    ·
      refine ⟨51487597721288437031785459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68650130295051249375713945 51487597721288437031785459)
      ·
        refine ⟨77231396581932655547678189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51487597721288437031785459 77231396581932655547678189)
        ·
          refine ⟨28961773718224745830379321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77231396581932655547678189 28961773718224745830379321)
          ·
            refine ⟨21721330288668559372784491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28961773718224745830379321 21721330288668559372784491)
            ·
              refine ⟨32581995433002839059176737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21721330288668559372784491 32581995433002839059176737)
              ·
                refine ⟨24436496574752129294382553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32581995433002839059176737 24436496574752129294382553)
                ·
                  refine ⟨18327372431064096970786915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24436496574752129294382553 18327372431064096970786915)
                  ·
                    refine ⟨27491058646596145456180373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18327372431064096970786915 27491058646596145456180373)
                    ·
                      refine ⟨1288643374059194318258455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27491058646596145456180373 1288643374059194318258455)
                      ·
                        rfl

theorem cell23_2509624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2509624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509624 prefixEnd_2509624 := by exact prefixLift 2509624
  have htrace : WordTrace (prefixWord ++ tailWord_2509624) baseStart_2509624 baseEnd_2509624 := by
    simpa [prefixWord, tailWord_2509624, baseEnd_2509624] using wordTrace_append hprefix tailTrace_2509624
  have hstable : (prefixWord ++ tailWord_2509624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509624).length < 2 ^ (prefixWord ++ tailWord_2509624).sum := by decide
  have hdescent : baseEnd_2509624 < baseStart_2509624 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509631 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 3]
def baseStart_2509631 : Nat := 118140960795 + 2509631 * 2 ^ 59
def prefixEnd_2509631 : Nat := 4983230072969 + 3 ^ 40 * 2509631 * 2
def baseEnd_2509631 : Nat := 1288646968423775790870923

theorem tailTrace_2509631 : CollatzResearch.WordTrace tailWord_2509631 prefixEnd_2509631 1288646968423775790870923 := by
  unfold tailWord_2509631
  simp only [CollatzResearch.WordTrace]
  refine ⟨91533762371042972696456747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61022508247361981797637831 91533762371042972696456747)
  ·
    refine ⟨137300643556564459044685121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91533762371042972696456747 137300643556564459044685121)
    ·
      refine ⟨102975482667423344283513841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137300643556564459044685121 102975482667423344283513841)
      ·
        refine ⟨77231612000567508212635381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102975482667423344283513841 77231612000567508212635381)
        ·
          refine ⟨7240463625053203894934567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77231612000567508212635381 7240463625053203894934567)
          ·
            refine ⟨10860695437579805842401851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7240463625053203894934567 10860695437579805842401851)
            ·
              refine ⟨16291043156369708763602777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10860695437579805842401851 16291043156369708763602777)
              ·
                refine ⟨12218282367277281572702083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16291043156369708763602777 12218282367277281572702083)
                ·
                  refine ⟨18327423550915922359053125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12218282367277281572702083 18327423550915922359053125)
                  ·
                    refine ⟨3436391915796735442322461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18327423550915922359053125 3436391915796735442322461)
                    ·
                      refine ⟨1288646968423775790870923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3436391915796735442322461 1288646968423775790870923)
                      ·
                        rfl

theorem cell23_2509631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 4, 3].length) (baseStart_2509631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509631 prefixEnd_2509631 := by exact prefixLift 2509631
  have htrace : WordTrace (prefixWord ++ tailWord_2509631) baseStart_2509631 baseEnd_2509631 := by
    simpa [prefixWord, tailWord_2509631, baseEnd_2509631] using wordTrace_append hprefix tailTrace_2509631
  have hstable : (prefixWord ++ tailWord_2509631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509631).length < 2 ^ (prefixWord ++ tailWord_2509631).sum := by decide
  have hdescent : baseEnd_2509631 < baseStart_2509631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509655 : List Nat := [1, 1, 3, 2, 4, 1, 3, 3, 1, 4]
def baseStart_2509655 : Nat := 118140960795 + 2509655 * 2 ^ 59
def prefixEnd_2509655 : Nat := 4983230072969 + 3 ^ 40 * 2509655 * 2
def baseEnd_2509655 : Nat := 429553097319827898990271

theorem tailTrace_2509655 : CollatzResearch.WordTrace tailWord_2509655 prefixEnd_2509655 429553097319827898990271 := by
  unfold tailWord_2509655
  simp only [CollatzResearch.WordTrace]
  refine ⟨91534637722956024795330419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61023091815304016530220279 91534637722956024795330419)
  ·
    refine ⟨137301956584434037192995629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91534637722956024795330419 137301956584434037192995629)
    ·
      refine ⟨51488233719162763947373361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137301956584434037192995629 51488233719162763947373361)
      ·
        refine ⟨38616175289372072960530021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51488233719162763947373361 38616175289372072960530021)
        ·
          refine ⟨7240532866757263680099379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38616175289372072960530021 7240532866757263680099379)
          ·
            refine ⟨10860799300135895520149069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7240532866757263680099379 10860799300135895520149069)
            ·
              refine ⟨4072799737550960820055901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10860799300135895520149069 4072799737550960820055901)
              ·
                refine ⟨1527299901581610307520963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4072799737550960820055901 1527299901581610307520963)
                ·
                  refine ⟨2290949852372415461281445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527299901581610307520963 2290949852372415461281445)
                  ·
                    refine ⟨429553097319827898990271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2290949852372415461281445 429553097319827898990271)
                    ·
                      rfl

theorem cell23_2509655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 4].length) (baseStart_2509655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509655 prefixEnd_2509655 := by exact prefixLift 2509655
  have htrace : WordTrace (prefixWord ++ tailWord_2509655) baseStart_2509655 baseEnd_2509655 := by
    simpa [prefixWord, tailWord_2509655, baseEnd_2509655] using wordTrace_append hprefix tailTrace_2509655
  have hstable : (prefixWord ++ tailWord_2509655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509655).length < 2 ^ (prefixWord ++ tailWord_2509655).sum := by decide
  have hdescent : baseEnd_2509655 < baseStart_2509655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509672 : List Nat := [2, 1, 4, 2, 1, 3, 3, 2, 1, 4]
def baseStart_2509672 : Nat := 118140960795 + 2509672 * 2 ^ 59
def prefixEnd_2509672 : Nat := 4983230072969 + 3 ^ 40 * 2509672 * 2
def baseEnd_2509672 : Nat := 429556007043536710152745

theorem tailTrace_2509672 : CollatzResearch.WordTrace tailWord_2509672 prefixEnd_2509672 429556007043536710152745 := by
  unfold tailWord_2509672
  simp only [CollatzResearch.WordTrace]
  refine ⟨45767628881947218349349635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61023505175929624465799513 45767628881947218349349635)
  ·
    refine ⟨68651443322920827524024453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45767628881947218349349635 68651443322920827524024453)
    ·
      refine ⟨12872145623047655160754585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68651443322920827524024453 12872145623047655160754585)
      ·
        refine ⟨9654109217285741370565939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12872145623047655160754585 9654109217285741370565939)
        ·
          refine ⟨14481163825928612055848909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9654109217285741370565939 14481163825928612055848909)
          ·
            refine ⟨5430436434723229520943341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14481163825928612055848909 5430436434723229520943341)
            ·
              refine ⟨2036413663021211070353753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5430436434723229520943341 2036413663021211070353753)
              ·
                refine ⟨1527310247265908302765315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036413663021211070353753 1527310247265908302765315)
                ·
                  refine ⟨2290965370898862454147973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527310247265908302765315 2290965370898862454147973)
                  ·
                    refine ⟨429556007043536710152745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2290965370898862454147973 429556007043536710152745)
                    ·
                      rfl

theorem cell23_2509672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_2509672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509672 prefixEnd_2509672 := by exact prefixLift 2509672
  have htrace : WordTrace (prefixWord ++ tailWord_2509672) baseStart_2509672 baseEnd_2509672 := by
    simpa [prefixWord, tailWord_2509672, baseEnd_2509672] using wordTrace_append hprefix tailTrace_2509672
  have hstable : (prefixWord ++ tailWord_2509672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509672).length < 2 ^ (prefixWord ++ tailWord_2509672).sum := by decide
  have hdescent : baseEnd_2509672 < baseStart_2509672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509685 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 6]
def baseStart_2509685 : Nat := 118140960795 + 2509685 * 2 ^ 59
def prefixEnd_2509685 : Nat := 4983230072969 + 3 ^ 40 * 2509685 * 2
def baseEnd_2509685 : Nat := 143186077375457619955075

theorem tailTrace_2509685 : CollatzResearch.WordTrace tailWord_2509685 prefixEnd_2509685 143186077375457619955075 := by
  unfold tailWord_2509685
  simp only [CollatzResearch.WordTrace]
  refine ⟨91535731912847339918922509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61023821275231559945948339 91535731912847339918922509)
  ·
    refine ⟨34325899467317752469595941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91535731912847339918922509 34325899467317752469595941)
    ·
      refine ⟨6436106150122078588049239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34325899467317752469595941 6436106150122078588049239)
      ·
        refine ⟨9654159225183117882073859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6436106150122078588049239 9654159225183117882073859)
        ·
          refine ⟨14481238837774676823110789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9654159225183117882073859 14481238837774676823110789)
          ·
            refine ⟨2715232282082751904333273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14481238837774676823110789 2715232282082751904333273)
            ·
              refine ⟨2036424211562063928249955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2715232282082751904333273 2036424211562063928249955)
              ·
                refine ⟨3054636317343095892374933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036424211562063928249955 3054636317343095892374933)
                ·
                  refine ⟨143186077375457619955075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3054636317343095892374933 143186077375457619955075)
                  ·
                    rfl

theorem cell23_2509685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 6].length) (baseStart_2509685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509685 prefixEnd_2509685 := by exact prefixLift 2509685
  have htrace : WordTrace (prefixWord ++ tailWord_2509685) baseStart_2509685 baseEnd_2509685 := by
    simpa [prefixWord, tailWord_2509685, baseEnd_2509685] using wordTrace_append hprefix tailTrace_2509685
  have hstable : (prefixWord ++ tailWord_2509685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509685).length < 2 ^ (prefixWord ++ tailWord_2509685).sum := by decide
  have hdescent : baseEnd_2509685 < baseStart_2509685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509705 : List Nat := [1, 2, 1, 1, 5, 3, 2, 1, 2, 3, 2]
def baseStart_2509705 : Nat := 118140960795 + 2509705 * 2 ^ 59
def prefixEnd_2509705 : Nat := 4983230072969 + 3 ^ 40 * 2509705 * 2
def baseEnd_2509705 : Nat := 1288684965992208501345583

theorem tailTrace_2509705 : CollatzResearch.WordTrace tailWord_2509705 prefixEnd_2509705 1288684965992208501345583 := by
  unfold tailWord_2509705
  simp only [CollatzResearch.WordTrace]
  refine ⟨91536461372774883334650569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61024307581849922223100379 91536461372774883334650569)
  ·
    refine ⟨68652346029581162500987927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91536461372774883334650569 68652346029581162500987927)
    ·
      refine ⟨102978519044371743751481891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68652346029581162500987927 102978519044371743751481891)
      ·
        refine ⟨154467778566557615627222837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102978519044371743751481891 154467778566557615627222837)
        ·
          refine ⟨14481354240614776465052141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154467778566557615627222837 14481354240614776465052141)
          ·
            refine ⟨5430507840230541174394553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14481354240614776465052141 5430507840230541174394553)
            ·
              refine ⟨4072880880172905880795915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5430507840230541174394553 4072880880172905880795915)
              ·
                refine ⟨6109321320259358821193873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4072880880172905880795915 6109321320259358821193873)
                ·
                  refine ⟨4581990990194519115895405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6109321320259358821193873 4581990990194519115895405)
                  ·
                    refine ⟨1718246621322944668460777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4581990990194519115895405 1718246621322944668460777)
                    ·
                      refine ⟨1288684965992208501345583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718246621322944668460777 1288684965992208501345583)
                      ·
                        rfl

theorem cell23_2509705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 2, 1, 2, 3, 2].length) (baseStart_2509705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509705 prefixEnd_2509705 := by exact prefixLift 2509705
  have htrace : WordTrace (prefixWord ++ tailWord_2509705) baseStart_2509705 baseEnd_2509705 := by
    simpa [prefixWord, tailWord_2509705, baseEnd_2509705] using wordTrace_append hprefix tailTrace_2509705
  have hstable : (prefixWord ++ tailWord_2509705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509705).length < 2 ^ (prefixWord ++ tailWord_2509705).sum := by decide
  have hdescent : baseEnd_2509705 < baseStart_2509705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509728 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 2, 4]
def baseStart_2509728 : Nat := 118140960795 + 2509728 * 2 ^ 59
def prefixEnd_2509728 : Nat := 4983230072969 + 3 ^ 40 * 2509728 * 2
def baseEnd_2509728 : Nat := 429565592015753970452659

theorem tailTrace_2509728 : CollatzResearch.WordTrace tailWord_2509728 prefixEnd_2509728 429565592015753970452659 := by
  unfold tailWord_2509728
  simp only [CollatzResearch.WordTrace]
  refine ⟨45768650125845779131368919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61024866834461038841825225 45768650125845779131368919)
  ·
    refine ⟨68652975188768668697053379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45768650125845779131368919 68652975188768668697053379)
    ·
      refine ⟨102979462783153003045580069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68652975188768668697053379 102979462783153003045580069)
      ·
        refine ⟨19308649271841188071046263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102979462783153003045580069 19308649271841188071046263)
        ·
          refine ⟨28962973907761782106569395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19308649271841188071046263 28962973907761782106569395)
          ·
            refine ⟨43444460861642673159854093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28962973907761782106569395 43444460861642673159854093)
            ·
              refine ⟨16291672823116002434945285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43444460861642673159854093 16291672823116002434945285)
              ·
                refine ⟨3054688654334250456552241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16291672823116002434945285 3054688654334250456552241)
                ·
                  refine ⟨2291016490750687842414181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3054688654334250456552241 2291016490750687842414181)
                  ·
                    refine ⟨429565592015753970452659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2291016490750687842414181 429565592015753970452659)
                    ·
                      rfl

theorem cell23_2509728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 2, 4].length) (baseStart_2509728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509728 prefixEnd_2509728 := by exact prefixLift 2509728
  have htrace : WordTrace (prefixWord ++ tailWord_2509728) baseStart_2509728 baseEnd_2509728 := by
    simpa [prefixWord, tailWord_2509728, baseEnd_2509728] using wordTrace_append hprefix tailTrace_2509728
  have hstable : (prefixWord ++ tailWord_2509728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509728).length < 2 ^ (prefixWord ++ tailWord_2509728).sum := by decide
  have hdescent : baseEnd_2509728 < baseStart_2509728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509729 : List Nat := [1, 2, 3, 4, 1, 1, 4, 2, 1, 1, 3]
def baseStart_2509729 : Nat := 118140960795 + 2509729 * 2 ^ 59
def prefixEnd_2509729 : Nat := 4983230072969 + 3 ^ 40 * 2509729 * 2
def baseEnd_2509729 : Nat := 1288697289527916407445473

theorem tailTrace_2509729 : CollatzResearch.WordTrace tailWord_2509729 prefixEnd_2509729 1288697289527916407445473 := by
  unfold tailWord_2509729
  simp only [CollatzResearch.WordTrace]
  refine ⟨91537336724687935433524241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61024891149791956955682827 91537336724687935433524241)
  ·
    refine ⟨68653002543515951575143181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91537336724687935433524241 68653002543515951575143181)
    ·
      refine ⟨25744875953818481840678693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68653002543515951575143181 25744875953818481840678693)
      ·
        refine ⟨4827164241340965345127255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25744875953818481840678693 4827164241340965345127255)
        ·
          refine ⟨7240746362011448017690883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827164241340965345127255 7240746362011448017690883)
          ·
            refine ⟨10861119543017172026536325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7240746362011448017690883 10861119543017172026536325)
            ·
              refine ⟨2036459914315719754975561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10861119543017172026536325 2036459914315719754975561)
              ·
                refine ⟨1527344935736789816231671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036459914315719754975561 1527344935736789816231671)
                ·
                  refine ⟨2291017403605184724347507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527344935736789816231671 2291017403605184724347507)
                  ·
                    refine ⟨3436526105407777086521261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2291017403605184724347507 3436526105407777086521261)
                    ·
                      refine ⟨1288697289527916407445473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3436526105407777086521261 1288697289527916407445473)
                      ·
                        rfl

theorem cell23_2509729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_2509729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509729 prefixEnd_2509729 := by exact prefixLift 2509729
  have htrace : WordTrace (prefixWord ++ tailWord_2509729) baseStart_2509729 baseEnd_2509729 := by
    simpa [prefixWord, tailWord_2509729, baseEnd_2509729] using wordTrace_append hprefix tailTrace_2509729
  have hstable : (prefixWord ++ tailWord_2509729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509729).length < 2 ^ (prefixWord ++ tailWord_2509729).sum := by decide
  have hdescent : baseEnd_2509729 < baseStart_2509729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509758 : List Nat := [4, 2, 1, 1, 1, 2, 5, 7]
def baseStart_2509758 : Nat := 118140960795 + 2509758 * 2 ^ 59
def prefixEnd_2509758 : Nat := 4983230072969 + 3 ^ 40 * 2509758 * 2
def baseEnd_2509758 : Nat := 47730080758033214591957

theorem tailTrace_2509758 : CollatzResearch.WordTrace tailWord_2509758 prefixEnd_2509758 47730080758033214591957 := by
  unfold tailWord_2509758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442299305197859173291241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61025596294388582257553285 11442299305197859173291241)
  ·
    refine ⟨8581724478898394379968431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11442299305197859173291241 8581724478898394379968431)
    ·
      refine ⟨12872586718347591569952647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8581724478898394379968431 12872586718347591569952647)
      ·
        refine ⟨19308880077521387354928971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12872586718347591569952647 19308880077521387354928971)
        ·
          refine ⟨28963320116282081032393457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19308880077521387354928971 28963320116282081032393457)
          ·
            refine ⟨21722490087211560774295093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28963320116282081032393457 21722490087211560774295093)
            ·
              refine ⟨2036483445676083822590165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21722490087211560774295093 2036483445676083822590165)
              ·
                refine ⟨47730080758033214591957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2036483445676083822590165 47730080758033214591957)
                ·
                  rfl

theorem cell23_2509758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_2509758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509758 prefixEnd_2509758 := by exact prefixLift 2509758
  have htrace : WordTrace (prefixWord ++ tailWord_2509758) baseStart_2509758 baseEnd_2509758 := by
    simpa [prefixWord, tailWord_2509758, baseEnd_2509758] using wordTrace_append hprefix tailTrace_2509758
  have hstable : (prefixWord ++ tailWord_2509758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509758).length < 2 ^ (prefixWord ++ tailWord_2509758).sum := by decide
  have hdescent : baseEnd_2509758 < baseStart_2509758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509766 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2509766 : Nat := 118140960795 + 2509766 * 2 ^ 59
def prefixEnd_2509766 : Nat := 4983230072969 + 3 ^ 40 * 2509766 * 2
def baseEnd_2509766 : Nat := 429572096104044254227601

theorem tailTrace_2509766 : CollatzResearch.WordTrace tailWord_2509766 prefixEnd_2509766 429572096104044254227601 := by
  unfold tailWord_2509766
  simp only [CollatzResearch.WordTrace]
  refine ⟨2860583944548559086019411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61025790817035927168414101 2860583944548559086019411)
  ·
    refine ⟨4290875916822838629029117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2860583944548559086019411 4290875916822838629029117)
    ·
      refine ⟨1609078468808564485885919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4290875916822838629029117 1609078468808564485885919)
      ·
        refine ⟨2413617703212846728828879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609078468808564485885919 2413617703212846728828879)
        ·
          refine ⟨3620426554819270093243319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413617703212846728828879 3620426554819270093243319)
          ·
            refine ⟨5430639832228905139864979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620426554819270093243319 5430639832228905139864979)
            ·
              refine ⟨8145959748343357709797469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430639832228905139864979 8145959748343357709797469)
              ·
                refine ⟨3054734905628759141174051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8145959748343357709797469 3054734905628759141174051)
                ·
                  refine ⟨4582102358443138711761077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054734905628759141174051 4582102358443138711761077)
                  ·
                    refine ⟨429572096104044254227601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4582102358443138711761077 429572096104044254227601)
                    ·
                      rfl

theorem cell23_2509766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2509766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509766 prefixEnd_2509766 := by exact prefixLift 2509766
  have htrace : WordTrace (prefixWord ++ tailWord_2509766) baseStart_2509766 baseEnd_2509766 := by
    simpa [prefixWord, tailWord_2509766, baseEnd_2509766] using wordTrace_append hprefix tailTrace_2509766
  have hstable : (prefixWord ++ tailWord_2509766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509766).length < 2 ^ (prefixWord ++ tailWord_2509766).sum := by decide
  have hdescent : baseEnd_2509766 < baseStart_2509766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509785 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 3]
def baseStart_2509785 : Nat := 118140960795 + 2509785 * 2 ^ 59
def prefixEnd_2509785 : Nat := 4983230072969 + 3 ^ 40 * 2509785 * 2
def baseEnd_2509785 : Nat := 1288726044444568188345215

theorem tailTrace_2509785 : CollatzResearch.WordTrace tailWord_2509785 prefixEnd_2509785 1288726044444568188345215 := by
  unfold tailWord_2509785
  simp only [CollatzResearch.WordTrace]
  refine ⟨91539379212485056997562809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61026252808323371331708539 91539379212485056997562809)
  ·
    refine ⟨68654534409363792748172107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91539379212485056997562809 68654534409363792748172107)
    ·
      refine ⟨102981801614045689122258161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68654534409363792748172107 102981801614045689122258161)
      ·
        refine ⟨77236351210534266841693621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102981801614045689122258161 77236351210534266841693621)
        ·
          refine ⟨7240907925987587516408777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77236351210534266841693621 7240907925987587516408777)
          ·
            refine ⟨5430680944490690637306583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7240907925987587516408777 5430680944490690637306583)
            ·
              refine ⟨8146021416736035955959875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430680944490690637306583 8146021416736035955959875)
              ·
                refine ⟨12219032125104053933939813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8146021416736035955959875 12219032125104053933939813)
                ·
                  refine ⟨2291068523457010112613715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12219032125104053933939813 2291068523457010112613715)
                  ·
                    refine ⟨3436602785185515168920573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2291068523457010112613715 3436602785185515168920573)
                    ·
                      refine ⟨1288726044444568188345215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3436602785185515168920573 1288726044444568188345215)
                      ·
                        rfl

theorem cell23_2509785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 4, 1, 3].length) (baseStart_2509785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509785 prefixEnd_2509785 := by exact prefixLift 2509785
  have htrace : WordTrace (prefixWord ++ tailWord_2509785) baseStart_2509785 baseEnd_2509785 := by
    simpa [prefixWord, tailWord_2509785, baseEnd_2509785] using wordTrace_append hprefix tailTrace_2509785
  have hstable : (prefixWord ++ tailWord_2509785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509785).length < 2 ^ (prefixWord ++ tailWord_2509785).sum := by decide
  have hdescent : baseEnd_2509785 < baseStart_2509785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509848 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 7]
def baseStart_2509848 : Nat := 118140960795 + 2509848 * 2 ^ 59
def prefixEnd_2509848 : Nat := 4983230072969 + 3 ^ 40 * 2509848 * 2
def baseEnd_2509848 : Nat := 143195377080644604650825

theorem tailTrace_2509848 : CollatzResearch.WordTrace tailWord_2509848 prefixEnd_2509848 143195377080644604650825 := by
  unfold tailWord_2509848
  simp only [CollatzResearch.WordTrace]
  refine ⟨45770838505628409378553099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61027784674171212504737465 45770838505628409378553099)
  ·
    refine ⟨68656257758442614067829649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45770838505628409378553099 68656257758442614067829649)
    ·
      refine ⟨51492193318831960550872237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68656257758442614067829649 51492193318831960550872237)
      ·
        refine ⟨19309572494561985206577089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51492193318831960550872237 19309572494561985206577089)
        ·
          refine ⟨14482179370921488904932817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19309572494561985206577089 14482179370921488904932817)
          ·
            refine ⟨10861634528191116678699613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14482179370921488904932817 10861634528191116678699613)
            ·
              refine ⟨4073112948071668754512355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10861634528191116678699613 4073112948071668754512355)
              ·
                refine ⟨6109669422107503131768533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073112948071668754512355 6109669422107503131768533)
                ·
                  refine ⟨143195377080644604650825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6109669422107503131768533 143195377080644604650825)
                  ·
                    rfl

theorem cell23_2509848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 7].length) (baseStart_2509848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509848 prefixEnd_2509848 := by exact prefixLift 2509848
  have htrace : WordTrace (prefixWord ++ tailWord_2509848) baseStart_2509848 baseEnd_2509848 := by
    simpa [prefixWord, tailWord_2509848, baseEnd_2509848] using wordTrace_append hprefix tailTrace_2509848
  have hstable : (prefixWord ++ tailWord_2509848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509848).length < 2 ^ (prefixWord ++ tailWord_2509848).sum := by decide
  have hdescent : baseEnd_2509848 < baseStart_2509848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509859 : List Nat := [1, 1, 1, 4, 3, 2, 4, 1, 2, 2, 2]
def baseStart_2509859 : Nat := 118140960795 + 2509859 * 2 ^ 59
def prefixEnd_2509859 : Nat := 4983230072969 + 3 ^ 40 * 2509859 * 2
def baseEnd_2509859 : Nat := 1288764042013000898819875

theorem tailTrace_2509859 : CollatzResearch.WordTrace tailWord_2509859 prefixEnd_2509859 1288764042013000898819875 := by
  unfold tailWord_2509859
  simp only [CollatzResearch.WordTrace]
  refine ⟨91542078214216967635756631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61028052142811311757171087 91542078214216967635756631)
  ·
    refine ⟨137313117321325451453634947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91542078214216967635756631 137313117321325451453634947)
    ·
      refine ⟨205969675981988177180452421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137313117321325451453634947 205969675981988177180452421)
      ·
        refine ⟨38619314246622783221334829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205969675981988177180452421 38619314246622783221334829)
        ·
          refine ⟨14482242842483543708000561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38619314246622783221334829 14482242842483543708000561)
          ·
            refine ⟨10861682131862657781000421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14482242842483543708000561 10861682131862657781000421)
            ·
              refine ⟨2036565399724248333937579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10861682131862657781000421 2036565399724248333937579)
              ·
                refine ⟨3054848099586372500906369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036565399724248333937579 3054848099586372500906369)
                ·
                  refine ⟨2291136074689779375679777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3054848099586372500906369 2291136074689779375679777)
                  ·
                    refine ⟨1718352056017334531759833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2291136074689779375679777 1718352056017334531759833)
                    ·
                      refine ⟨1288764042013000898819875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718352056017334531759833 1288764042013000898819875)
                      ·
                        rfl

theorem cell23_2509859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 1, 2, 2, 2].length) (baseStart_2509859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509859 prefixEnd_2509859 := by exact prefixLift 2509859
  have htrace : WordTrace (prefixWord ++ tailWord_2509859) baseStart_2509859 baseEnd_2509859 := by
    simpa [prefixWord, tailWord_2509859, baseEnd_2509859] using wordTrace_append hprefix tailTrace_2509859
  have hstable : (prefixWord ++ tailWord_2509859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509859).length < 2 ^ (prefixWord ++ tailWord_2509859).sum := by decide
  have hdescent : baseEnd_2509859 < baseStart_2509859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509925 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 3, 4]
def baseStart_2509925 : Nat := 118140960795 + 2509925 * 2 ^ 59
def prefixEnd_2509925 : Nat := 4983230072969 + 3 ^ 40 * 2509925 * 2
def baseEnd_2509925 : Nat := 429599310578732546864857

theorem tailTrace_2509925 : CollatzResearch.WordTrace tailWord_2509925 prefixEnd_2509925 429599310578732546864857 := by
  unfold tailWord_2509925
  simp only [CollatzResearch.WordTrace]
  refine ⟨91544485431977860907659229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61029656954651907271772819 91544485431977860907659229)
  ·
    refine ⟨34329182036991697840372211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91544485431977860907659229 34329182036991697840372211)
    ·
      refine ⟨51493773055487546760558317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34329182036991697840372211 51493773055487546760558317)
      ·
        refine ⟨19310164895807830035209369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51493773055487546760558317 19310164895807830035209369)
        ·
          refine ⟨14482623671855872526407027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19310164895807830035209369 14482623671855872526407027)
          ·
            refine ⟨21723935507783808789610541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14482623671855872526407027 21723935507783808789610541)
            ·
              refine ⟨8146475815418928296103953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21723935507783808789610541 8146475815418928296103953)
              ·
                refine ⟨6109856861564196222077965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8146475815418928296103953 6109856861564196222077965)
                ·
                  refine ⟨2291196323086573583279237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6109856861564196222077965 2291196323086573583279237)
                  ·
                    refine ⟨429599310578732546864857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2291196323086573583279237 429599310578732546864857)
                    ·
                      rfl

theorem cell23_2509925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 4].length) (baseStart_2509925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509925 prefixEnd_2509925 := by exact prefixLift 2509925
  have htrace : WordTrace (prefixWord ++ tailWord_2509925) baseStart_2509925 baseEnd_2509925 := by
    simpa [prefixWord, tailWord_2509925, baseEnd_2509925] using wordTrace_append hprefix tailTrace_2509925
  have hstable : (prefixWord ++ tailWord_2509925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509925).length < 2 ^ (prefixWord ++ tailWord_2509925).sum := by decide
  have hdescent : baseEnd_2509925 < baseStart_2509925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509938 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 8]
def baseStart_2509938 : Nat := 118140960795 + 2509938 * 2 ^ 59
def prefixEnd_2509938 : Nat := 4983230072969 + 3 ^ 40 * 2509938 * 2
def baseEnd_2509938 : Nat := 143200511887189565525779

theorem tailTrace_2509938 : CollatzResearch.WordTrace tailWord_2509938 prefixEnd_2509938 143200511887189565525779 := by
  unfold tailWord_2509938
  simp only [CollatzResearch.WordTrace]
  refine ⟨22886239895232691031970617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61029973053953842751921645 22886239895232691031970617)
  ·
    refine ⟨17164679921424518273977963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22886239895232691031970617 17164679921424518273977963)
    ·
      refine ⟨25747019882136777410966945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17164679921424518273977963 25747019882136777410966945)
      ·
        refine ⟨19310264911602583058225209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25747019882136777410966945 19310264911602583058225209)
        ·
          refine ⟨14482698683701937293668907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19310264911602583058225209 14482698683701937293668907)
          ·
            refine ⟨21724048025552905940503361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14482698683701937293668907 21724048025552905940503361)
            ·
              refine ⟨16293036019164679455377521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21724048025552905940503361 16293036019164679455377521)
              ·
                refine ⟨12219777014373509591533141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16293036019164679455377521 12219777014373509591533141)
                ·
                  refine ⟨143200511887189565525779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12219777014373509591533141 143200511887189565525779)
                  ·
                    rfl

theorem cell23_2509938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 8].length) (baseStart_2509938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509938 prefixEnd_2509938 := by exact prefixLift 2509938
  have htrace : WordTrace (prefixWord ++ tailWord_2509938) baseStart_2509938 baseEnd_2509938 := by
    simpa [prefixWord, tailWord_2509938, baseEnd_2509938] using wordTrace_append hprefix tailTrace_2509938
  have hstable : (prefixWord ++ tailWord_2509938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509938).length < 2 ^ (prefixWord ++ tailWord_2509938).sum := by decide
  have hdescent : baseEnd_2509938 < baseStart_2509938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509968 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 3, 5]
def baseStart_2509968 : Nat := 118140960795 + 2509968 * 2 ^ 59
def prefixEnd_2509968 : Nat := 4983230072969 + 3 ^ 40 * 2509968 * 2
def baseEnd_2509968 : Nat := 429606670468113657452291

theorem tailTrace_2509968 : CollatzResearch.WordTrace tailWord_2509968 prefixEnd_2509968 429606670468113657452291 := by
  unfold tailWord_2509968
  simp only [CollatzResearch.WordTrace]
  refine ⟨45773026885411039625737279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61030702513881386167649705 45773026885411039625737279)
  ·
    refine ⟨68659540328116559438605919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45773026885411039625737279 68659540328116559438605919)
    ·
      refine ⟨102989310492174839157908879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68659540328116559438605919 102989310492174839157908879)
      ·
        refine ⟨154483965738262258736863319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102989310492174839157908879 154483965738262258736863319)
        ·
          refine ⟨231725948607393388105294979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154483965738262258736863319 231725948607393388105294979)
          ·
            refine ⟨347588922911090082157942469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231725948607393388105294979 347588922911090082157942469)
            ·
              refine ⟨65172923045829390404614213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 347588922911090082157942469 65172923045829390404614213)
              ·
                refine ⟨12219923071093010700865165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65172923045829390404614213 12219923071093010700865165)
                ·
                  refine ⟨4582471151659879012824437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12219923071093010700865165 4582471151659879012824437)
                  ·
                    refine ⟨429606670468113657452291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4582471151659879012824437 429606670468113657452291)
                    ·
                      rfl

theorem cell23_2509968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_2509968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509968 prefixEnd_2509968 := by exact prefixLift 2509968
  have htrace : WordTrace (prefixWord ++ tailWord_2509968) baseStart_2509968 baseEnd_2509968 := by
    simpa [prefixWord, tailWord_2509968, baseEnd_2509968] using wordTrace_append hprefix tailTrace_2509968
  have hstable : (prefixWord ++ tailWord_2509968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509968).length < 2 ^ (prefixWord ++ tailWord_2509968).sum := by decide
  have hdescent : baseEnd_2509968 < baseStart_2509968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2509999 : List Nat := [1, 1, 2, 1, 2, 3, 5, 3, 1, 1, 3]
def baseStart_2509999 : Nat := 118140960795 + 2509999 * 2 ^ 59
def prefixEnd_2509999 : Nat := 4983230072969 + 3 ^ 40 * 2509999 * 2
def baseEnd_2509999 : Nat := 1288835929304630351069231

theorem tailTrace_2509999 : CollatzResearch.WordTrace tailWord_2509999 prefixEnd_2509999 1288835929304630351069231 := by
  unfold tailWord_2509999
  simp only [CollatzResearch.WordTrace]
  refine ⟨91547184433709771545853051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61031456289139847697235367 91547184433709771545853051)
  ·
    refine ⟨137320776650564657318779577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91547184433709771545853051 137320776650564657318779577)
    ·
      refine ⟨102990582487923492989084683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137320776650564657318779577 102990582487923492989084683)
      ·
        refine ⟨154485873731885239483627025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102990582487923492989084683 154485873731885239483627025)
        ·
          refine ⟨115864405298913929612720269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154485873731885239483627025 115864405298913929612720269)
          ·
            refine ⟨43449151987092723604770101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115864405298913929612720269 43449151987092723604770101)
            ·
              refine ⟨4073357998789942837947197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43449151987092723604770101 4073357998789942837947197)
              ·
                refine ⟨1527509249546228564230199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4073357998789942837947197 1527509249546228564230199)
                ·
                  refine ⟨2291263874319342846345299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527509249546228564230199 2291263874319342846345299)
                  ·
                    refine ⟨3436895811479014269517949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2291263874319342846345299 3436895811479014269517949)
                    ·
                      refine ⟨1288835929304630351069231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3436895811479014269517949 1288835929304630351069231)
                      ·
                        rfl

theorem cell23_2509999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 3, 1, 1, 3].length) (baseStart_2509999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2509999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2509999 prefixEnd_2509999 := by exact prefixLift 2509999
  have htrace : WordTrace (prefixWord ++ tailWord_2509999) baseStart_2509999 baseEnd_2509999 := by
    simpa [prefixWord, tailWord_2509999, baseEnd_2509999] using wordTrace_append hprefix tailTrace_2509999
  have hstable : (prefixWord ++ tailWord_2509999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2509999).length < 2 ^ (prefixWord ++ tailWord_2509999).sum := by decide
  have hdescent : baseEnd_2509999 < baseStart_2509999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2509999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510015 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 4, 4]
def baseStart_2510015 : Nat := 118140960795 + 2510015 * 2 ^ 59
def prefixEnd_2510015 : Nat := 4983230072969 + 3 ^ 40 * 2510015 * 2
def baseEnd_2510015 : Nat := 429614714998367429489719

theorem tailTrace_2510015 : CollatzResearch.WordTrace tailWord_2510015 prefixEnd_2510015 429614714998367429489719 := by
  unfold tailWord_2510015
  simp only [CollatzResearch.WordTrace]
  refine ⟨91547768001651806278435499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61031845334434537518956999 91547768001651806278435499)
  ·
    refine ⟨137321652002477709417653249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91547768001651806278435499 137321652002477709417653249)
    ·
      refine ⟨102991239001858282063239937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137321652002477709417653249 102991239001858282063239937)
      ·
        refine ⟨77243429251393711547429953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102991239001858282063239937 77243429251393711547429953)
        ·
          refine ⟨57932571938545283660572465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77243429251393711547429953 57932571938545283660572465)
          ·
            refine ⟨43449428953908962745429349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57932571938545283660572465 43449428953908962745429349)
            ·
              refine ⟨8146767928857930514768003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43449428953908962745429349 8146767928857930514768003)
              ·
                refine ⟨12220151893286895772152005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8146767928857930514768003 12220151893286895772152005)
                ·
                  refine ⟨2291278479991292957278501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12220151893286895772152005 2291278479991292957278501)
                  ·
                    refine ⟨429614714998367429489719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2291278479991292957278501 429614714998367429489719)
                    ·
                      rfl

theorem cell23_2510015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 4].length) (baseStart_2510015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510015 prefixEnd_2510015 := by exact prefixLift 2510015
  have htrace : WordTrace (prefixWord ++ tailWord_2510015) baseStart_2510015 baseEnd_2510015 := by
    simpa [prefixWord, tailWord_2510015, baseEnd_2510015] using wordTrace_append hprefix tailTrace_2510015
  have hstable : (prefixWord ++ tailWord_2510015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510015).length < 2 ^ (prefixWord ++ tailWord_2510015).sum := by decide
  have hdescent : baseEnd_2510015 < baseStart_2510015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510016 : List Nat := [2, 1, 1, 2, 7, 1, 1, 1, 3, 1, 3]
def baseStart_2510016 : Nat := 118140960795 + 2510016 * 2 ^ 59
def prefixEnd_2510016 : Nat := 4983230072969 + 3 ^ 40 * 2510016 * 2
def baseEnd_2510016 : Nat := 1288844658475756784556653

theorem tailTrace_2510016 : CollatzResearch.WordTrace tailWord_2510016 prefixEnd_2510016 1288844658475756784556653 := by
  unfold tailWord_2510016
  simp only [CollatzResearch.WordTrace]
  refine ⟨45773902237324091724610951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61031869649765455632814601 45773902237324091724610951)
  ·
    refine ⟨68660853355986137586916427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45773902237324091724610951 68660853355986137586916427)
    ·
      refine ⟨102991280033979206380374641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68660853355986137586916427 102991280033979206380374641)
      ·
        refine ⟨77243460025484404785280981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102991280033979206380374641 77243460025484404785280981)
        ·
          refine ⟨1810393594347290737155023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 77243460025484404785280981 1810393594347290737155023)
          ·
            refine ⟨2715590391520936105732535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810393594347290737155023 2715590391520936105732535)
            ·
              refine ⟨4073385587281404158598803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715590391520936105732535 4073385587281404158598803)
              ·
                refine ⟨6110078380922106237898205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073385587281404158598803 6110078380922106237898205)
                ·
                  refine ⟨2291279392845789839211827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6110078380922106237898205 2291279392845789839211827)
                  ·
                    refine ⟨3436919089268684758817741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2291279392845789839211827 3436919089268684758817741)
                    ·
                      refine ⟨1288844658475756784556653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3436919089268684758817741 1288844658475756784556653)
                      ·
                        rfl

theorem cell23_2510016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 1, 3, 1, 3].length) (baseStart_2510016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510016 prefixEnd_2510016 := by exact prefixLift 2510016
  have htrace : WordTrace (prefixWord ++ tailWord_2510016) baseStart_2510016 baseEnd_2510016 := by
    simpa [prefixWord, tailWord_2510016, baseEnd_2510016] using wordTrace_append hprefix tailTrace_2510016
  have hstable : (prefixWord ++ tailWord_2510016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510016).length < 2 ^ (prefixWord ++ tailWord_2510016).sum := by decide
  have hdescent : baseEnd_2510016 < baseStart_2510016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510036 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_2510036 : Nat := 118140960795 + 2510036 * 2 ^ 59
def prefixEnd_2510036 : Nat := 4983230072969 + 3 ^ 40 * 2510036 * 2
def baseEnd_2510036 : Nat := 429618309362948902102187

theorem tailTrace_2510036 : CollatzResearch.WordTrace tailWord_2510036 prefixEnd_2510036 429618309362948902102187 := by
  unfold tailWord_2510036
  simp only [CollatzResearch.WordTrace]
  refine ⟨45774266967287863432474981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61032355956383817909966641 45774266967287863432474981)
  ·
    refine ⟨8582675056366474393589059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45774266967287863432474981 8582675056366474393589059)
    ·
      refine ⟨12874012584549711590383589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8582675056366474393589059 12874012584549711590383589)
      ·
        refine ⟨2413877359603070923196923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12874012584549711590383589 2413877359603070923196923)
        ·
          refine ⟨3620816039404606384795385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413877359603070923196923 3620816039404606384795385)
          ·
            refine ⟨2715612029553454788596539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3620816039404606384795385 2715612029553454788596539)
            ·
              refine ⟨4073418044330182182894809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715612029553454788596539 4073418044330182182894809)
              ·
                refine ⟨3055063533247636637171107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4073418044330182182894809 3055063533247636637171107)
                ·
                  refine ⟨4582595299871454955756661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055063533247636637171107 4582595299871454955756661)
                  ·
                    refine ⟨429618309362948902102187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4582595299871454955756661 429618309362948902102187)
                    ·
                      rfl

theorem cell23_2510036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_2510036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510036 prefixEnd_2510036 := by exact prefixLift 2510036
  have htrace : WordTrace (prefixWord ++ tailWord_2510036) baseStart_2510036 baseEnd_2510036 := by
    simpa [prefixWord, tailWord_2510036, baseEnd_2510036] using wordTrace_append hprefix tailTrace_2510036
  have hstable : (prefixWord ++ tailWord_2510036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510036).length < 2 ^ (prefixWord ++ tailWord_2510036).sum := by decide
  have hdescent : baseEnd_2510036 < baseStart_2510036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510056 : List Nat := [2, 1, 4, 1, 2, 1, 2, 5, 1, 2, 2]
def baseStart_2510056 : Nat := 118140960795 + 2510056 * 2 ^ 59
def prefixEnd_2510056 : Nat := 4983230072969 + 3 ^ 40 * 2510056 * 2
def baseEnd_2510056 : Nat := 1288865197701936628056469

theorem tailTrace_2510056 : CollatzResearch.WordTrace tailWord_2510056 prefixEnd_2510056 1288865197701936628056469 := by
  unfold tailWord_2510056
  simp only [CollatzResearch.WordTrace]
  refine ⟨45774631697251635140339011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61032842263002180187118681 45774631697251635140339011)
  ·
    refine ⟨68661947545877452710508517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45774631697251635140339011 68661947545877452710508517)
    ·
      refine ⟨12874115164852022383220347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68661947545877452710508517 12874115164852022383220347)
      ·
        refine ⟨19311172747278033574830521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12874115164852022383220347 19311172747278033574830521)
        ·
          refine ⟨14483379560458525181122891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19311172747278033574830521 14483379560458525181122891)
          ·
            refine ⟨21725069340687787771684337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14483379560458525181122891 21725069340687787771684337)
            ·
              refine ⟨16293802005515840828763253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21725069340687787771684337 16293802005515840828763253)
              ·
                refine ⟨1527543938017110077696555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16293802005515840828763253 1527543938017110077696555)
                ·
                  refine ⟨2291315907025665116544833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527543938017110077696555 2291315907025665116544833)
                  ·
                    refine ⟨1718486930269248837408625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2291315907025665116544833 1718486930269248837408625)
                    ·
                      refine ⟨1288865197701936628056469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718486930269248837408625 1288865197701936628056469)
                      ·
                        rfl

theorem cell23_2510056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 5, 1, 2, 2].length) (baseStart_2510056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510056 prefixEnd_2510056 := by exact prefixLift 2510056
  have htrace : WordTrace (prefixWord ++ tailWord_2510056) baseStart_2510056 baseEnd_2510056 := by
    simpa [prefixWord, tailWord_2510056, baseEnd_2510056] using wordTrace_append hprefix tailTrace_2510056
  have hstable : (prefixWord ++ tailWord_2510056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510056).length < 2 ^ (prefixWord ++ tailWord_2510056).sum := by decide
  have hdescent : baseEnd_2510056 < baseStart_2510056 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510059 : List Nat := [1, 1, 1, 1, 2, 7, 3, 1, 1, 2, 3]
def baseStart_2510059 : Nat := 118140960795 + 2510059 * 2 ^ 59
def prefixEnd_2510059 : Nat := 4983230072969 + 3 ^ 40 * 2510059 * 2
def baseEnd_2510059 : Nat := 1288866738143900116318955

theorem tailTrace_2510059 : CollatzResearch.WordTrace tailWord_2510059 prefixEnd_2510059 1288866738143900116318955 := by
  unfold tailWord_2510059
  simp only [CollatzResearch.WordTrace]
  refine ⟨91549372813492401793037231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61032915208994934528691487 91549372813492401793037231)
  ·
    refine ⟨137324059220238602689555847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91549372813492401793037231 137324059220238602689555847)
    ·
      refine ⟨205986088830357904034333771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137324059220238602689555847 205986088830357904034333771)
      ·
        refine ⟨308979133245536856051500657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205986088830357904034333771 308979133245536856051500657)
        ·
          refine ⟨231734349934152642038625493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308979133245536856051500657 231734349934152642038625493)
          ·
            refine ⟨5431273826581702547780285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 231734349934152642038625493 5431273826581702547780285)
            ·
              refine ⟨2036727684968138455417607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5431273826581702547780285 2036727684968138455417607)
              ·
                refine ⟨3055091527452207683126411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036727684968138455417607 3055091527452207683126411)
                ·
                  refine ⟨4582637291178311524689617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055091527452207683126411 4582637291178311524689617)
                  ·
                    refine ⟨3436977968383733643517213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4582637291178311524689617 3436977968383733643517213)
                    ·
                      refine ⟨1288866738143900116318955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3436977968383733643517213 1288866738143900116318955)
                      ·
                        rfl

theorem cell23_2510059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 3, 1, 1, 2, 3].length) (baseStart_2510059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510059 prefixEnd_2510059 := by exact prefixLift 2510059
  have htrace : WordTrace (prefixWord ++ tailWord_2510059) baseStart_2510059 baseEnd_2510059 := by
    simpa [prefixWord, tailWord_2510059, baseEnd_2510059] using wordTrace_append hprefix tailTrace_2510059
  have hstable : (prefixWord ++ tailWord_2510059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510059).length < 2 ^ (prefixWord ++ tailWord_2510059).sum := by decide
  have hdescent : baseEnd_2510059 < baseStart_2510059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510110 : List Nat := [4, 3, 2, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_2510110 : Nat := 118140960795 + 2510110 * 2 ^ 59
def prefixEnd_2510110 : Nat := 4983230072969 + 3 ^ 40 * 2510110 * 2
def baseEnd_2510110 : Nat := 1288892925657279416781221

theorem tailTrace_2510110 : CollatzResearch.WordTrace tailWord_2510110 prefixEnd_2510110 1288892925657279416781221 := by
  unfold tailWord_2510110
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443904117038454687892973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61034155290871758335429189 11443904117038454687892973)
  ·
    refine ⟨4291464043889420507959865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11443904117038454687892973 4291464043889420507959865)
    ·
      refine ⟨3218598032917065380969899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4291464043889420507959865 3218598032917065380969899)
      ·
        refine ⟨4827897049375598071454849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218598032917065380969899 4827897049375598071454849)
        ·
          refine ⟨3620922787031698553591137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4827897049375598071454849 3620922787031698553591137)
          ·
            refine ⟨2715692090273773915193353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3620922787031698553591137 2715692090273773915193353)
            ·
              refine ⟨2036769067705330436395015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2715692090273773915193353 2036769067705330436395015)
              ·
                refine ⟨3055153601557995654592523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036769067705330436395015 3055153601557995654592523)
                ·
                  refine ⟨4582730402336993481888785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055153601557995654592523 4582730402336993481888785)
                  ·
                    refine ⟨3437047801752745111416589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4582730402336993481888785 3437047801752745111416589)
                    ·
                      refine ⟨1288892925657279416781221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3437047801752745111416589 1288892925657279416781221)
                      ·
                        rfl

theorem cell23_2510110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_2510110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510110 prefixEnd_2510110 := by exact prefixLift 2510110
  have htrace : WordTrace (prefixWord ++ tailWord_2510110) baseStart_2510110 baseEnd_2510110 := by
    simpa [prefixWord, tailWord_2510110, baseEnd_2510110] using wordTrace_append hprefix tailTrace_2510110
  have hstable : (prefixWord ++ tailWord_2510110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510110).length < 2 ^ (prefixWord ++ tailWord_2510110).sum := by decide
  have hdescent : baseEnd_2510110 < baseStart_2510110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510122 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_2510122 : Nat := 118140960795 + 2510122 * 2 ^ 59
def prefixEnd_2510122 : Nat := 4983230072969 + 3 ^ 40 * 2510122 * 2
def baseEnd_2510122 : Nat := 429633029141711123277055

theorem tailTrace_2510122 : CollatzResearch.WordTrace tailWord_2510122 prefixEnd_2510122 429633029141711123277055 := by
  unfold tailWord_2510122
  simp only [CollatzResearch.WordTrace]
  refine ⟨22887917653066040888145155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61034447074842775701720413 22887917653066040888145155)
  ·
    refine ⟨34331876479599061332217733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22887917653066040888145155 34331876479599061332217733)
    ·
      refine ⟨6437226839924823999790825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34331876479599061332217733 6437226839924823999790825)
      ·
        refine ⟨4827920129943617999843119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6437226839924823999790825 4827920129943617999843119)
        ·
          refine ⟨7241880194915426999764679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827920129943617999843119 7241880194915426999764679)
          ·
            refine ⟨10862820292373140499647019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7241880194915426999764679 10862820292373140499647019)
            ·
              refine ⟨16294230438559710749470529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10862820292373140499647019 16294230438559710749470529)
              ·
                refine ⟨12220672828919783062102897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16294230438559710749470529 12220672828919783062102897)
                ·
                  refine ⟨9165504621689837296577173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12220672828919783062102897 9165504621689837296577173)
                  ·
                    refine ⟨429633029141711123277055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9165504621689837296577173 429633029141711123277055)
                    ·
                      rfl

theorem cell23_2510122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_2510122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510122 prefixEnd_2510122 := by exact prefixLift 2510122
  have htrace : WordTrace (prefixWord ++ tailWord_2510122) baseStart_2510122 baseEnd_2510122 := by
    simpa [prefixWord, tailWord_2510122, baseEnd_2510122] using wordTrace_append hprefix tailTrace_2510122
  have hstable : (prefixWord ++ tailWord_2510122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510122).length < 2 ^ (prefixWord ++ tailWord_2510122).sum := by decide
  have hdescent : baseEnd_2510122 < baseStart_2510122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510142 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 2, 2, 4]
def baseStart_2510142 : Nat := 118140960795 + 2510142 * 2 ^ 59
def prefixEnd_2510142 : Nat := 4983230072969 + 3 ^ 40 * 2510142 * 2
def baseEnd_2510142 : Nat := 1288909357038223291581073

theorem tailTrace_2510142 : CollatzResearch.WordTrace tailWord_2510142 prefixEnd_2510142 1288909357038223291581073 := by
  unfold tailWord_2510142
  simp only [CollatzResearch.WordTrace]
  refine ⟨11444050009023963371038585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61034933381461137978872453 11444050009023963371038585)
  ·
    refine ⟨8583037506767972528278939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11444050009023963371038585 8583037506767972528278939)
    ·
      refine ⟨12874556260151958792418409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8583037506767972528278939 12874556260151958792418409)
      ·
        refine ⟨9655917195113969094313807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12874556260151958792418409 9655917195113969094313807)
        ·
          refine ⟨14483875792670953641470711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9655917195113969094313807 14483875792670953641470711)
          ·
            refine ⟨21725813689006430462206067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14483875792670953641470711 21725813689006430462206067)
            ·
              refine ⟨32588720533509645693309101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21725813689006430462206067 32588720533509645693309101)
              ·
                refine ⟨12220770200066117134990913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32588720533509645693309101 12220770200066117134990913)
                ·
                  refine ⟨9165577650049587851243185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12220770200066117134990913 9165577650049587851243185)
                  ·
                    refine ⟨6874183237537190888432389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9165577650049587851243185 6874183237537190888432389)
                    ·
                      refine ⟨1288909357038223291581073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6874183237537190888432389 1288909357038223291581073)
                      ·
                        rfl

theorem cell23_2510142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_2510142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510142 prefixEnd_2510142 := by exact prefixLift 2510142
  have htrace : WordTrace (prefixWord ++ tailWord_2510142) baseStart_2510142 baseEnd_2510142 := by
    simpa [prefixWord, tailWord_2510142, baseEnd_2510142] using wordTrace_append hprefix tailTrace_2510142
  have hstable : (prefixWord ++ tailWord_2510142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510142).length < 2 ^ (prefixWord ++ tailWord_2510142).sum := by decide
  have hdescent : baseEnd_2510142 < baseStart_2510142 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510175 : List Nat := [1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 5]
def baseStart_2510175 : Nat := 118140960795 + 2510175 * 2 ^ 59
def prefixEnd_2510175 : Nat := 4983230072969 + 3 ^ 40 * 2510175 * 2
def baseEnd_2510175 : Nat := 1288926301899821662468421

theorem tailTrace_2510175 : CollatzResearch.WordTrace tailWord_2510175 prefixEnd_2510175 1288926301899821662468421 := by
  unfold tailWord_2510175
  simp only [CollatzResearch.WordTrace]
  refine ⟨91553603681072153604259979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61035735787381435736173319 91553603681072153604259979)
  ·
    refine ⟨137330405521608230406389969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91553603681072153604259979 137330405521608230406389969)
    ·
      refine ⟨102997804141206172804792477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137330405521608230406389969 102997804141206172804792477)
      ·
        refine ⟨38624176552952314801797179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102997804141206172804792477 38624176552952314801797179)
        ·
          refine ⟨57936264829428472202695769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38624176552952314801797179 57936264829428472202695769)
          ·
            refine ⟨43452198622071354152021827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57936264829428472202695769 43452198622071354152021827)
            ·
              refine ⟨65178297933107031228032741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43452198622071354152021827 65178297933107031228032741)
              ·
                refine ⟨12220930862457568355256139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65178297933107031228032741 12220930862457568355256139)
                ·
                  refine ⟨18331396293686352532884209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12220930862457568355256139 18331396293686352532884209)
                  ·
                    refine ⟨13748547220264764399663157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18331396293686352532884209 13748547220264764399663157)
                    ·
                      refine ⟨1288926301899821662468421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13748547220264764399663157 1288926301899821662468421)
                      ·
                        rfl

theorem cell23_2510175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_2510175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510175 prefixEnd_2510175 := by exact prefixLift 2510175
  have htrace : WordTrace (prefixWord ++ tailWord_2510175) baseStart_2510175 baseEnd_2510175 := by
    simpa [prefixWord, tailWord_2510175, baseEnd_2510175] using wordTrace_append hprefix tailTrace_2510175
  have hstable : (prefixWord ++ tailWord_2510175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510175).length < 2 ^ (prefixWord ++ tailWord_2510175).sum := by decide
  have hdescent : baseEnd_2510175 < baseStart_2510175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510185 : List Nat := [1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 4]
def baseStart_2510185 : Nat := 118140960795 + 2510185 * 2 ^ 59
def prefixEnd_2510185 : Nat := 4983230072969 + 3 ^ 40 * 2510185 * 2
def baseEnd_2510185 : Nat := 1288931436706366623343375

theorem tailTrace_2510185 : CollatzResearch.WordTrace tailWord_2510185 prefixEnd_2510185 1288931436706366623343375 := by
  unfold tailWord_2510185
  simp only [CollatzResearch.WordTrace]
  refine ⟨91553968411035925312124009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61035978940690616874749339 91553968411035925312124009)
  ·
    refine ⟨68665476308276943984093007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91553968411035925312124009 68665476308276943984093007)
    ·
      refine ⟨102998214462415415976139511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68665476308276943984093007 102998214462415415976139511)
      ·
        refine ⟨154497321693623123964209267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102998214462415415976139511 154497321693623123964209267)
        ·
          refine ⟨231745982540434685946313901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154497321693623123964209267 231745982540434685946313901)
          ·
            refine ⟨86904743452663007229867713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231745982540434685946313901 86904743452663007229867713)
            ·
              refine ⟨65178557589497255422400785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86904743452663007229867713 65178557589497255422400785)
              ·
                refine ⟨48883918192122941566800589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65178557589497255422400785 48883918192122941566800589)
                ·
                  refine ⟨18331469322046103087550221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48883918192122941566800589 18331469322046103087550221)
                  ·
                    refine ⟨6874300995767288657831333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18331469322046103087550221 6874300995767288657831333)
                    ·
                      refine ⟨1288931436706366623343375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6874300995767288657831333 1288931436706366623343375)
                      ·
                        rfl

theorem cell23_2510185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 4].length) (baseStart_2510185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510185 prefixEnd_2510185 := by exact prefixLift 2510185
  have htrace : WordTrace (prefixWord ++ tailWord_2510185) baseStart_2510185 baseEnd_2510185 := by
    simpa [prefixWord, tailWord_2510185, baseEnd_2510185] using wordTrace_append hprefix tailTrace_2510185
  have hstable : (prefixWord ++ tailWord_2510185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510185).length < 2 ^ (prefixWord ++ tailWord_2510185).sum := by decide
  have hdescent : baseEnd_2510185 < baseStart_2510185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510186 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 7]
def baseStart_2510186 : Nat := 118140960795 + 2510186 * 2 ^ 59
def prefixEnd_2510186 : Nat := 4983230072969 + 3 ^ 40 * 2510186 * 2
def baseEnd_2510186 : Nat := 143214661131891235492319

theorem tailTrace_2510186 : CollatzResearch.WordTrace tailWord_2510186 prefixEnd_2510186 143214661131891235492319 := by
  unfold tailWord_2510186
  simp only [CollatzResearch.WordTrace]
  refine ⟨22888501221008075620727603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61036003256021534988606941 22888501221008075620727603)
  ·
    refine ⟨34332751831512113431091405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22888501221008075620727603 34332751831512113431091405)
    ·
      refine ⟨12874781936817042536659277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34332751831512113431091405 12874781936817042536659277)
      ·
        refine ⟨4828043226306390951247229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12874781936817042536659277 4828043226306390951247229)
        ·
          refine ⟨1810516209864896606717711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4828043226306390951247229 1810516209864896606717711)
          ·
            refine ⟨2715774314797344910076567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810516209864896606717711 2715774314797344910076567)
            ·
              refine ⟨4073661472196017365114851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715774314797344910076567 4073661472196017365114851)
              ·
                refine ⟨6110492208294026047672277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073661472196017365114851 6110492208294026047672277)
                ·
                  refine ⟨143214661131891235492319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6110492208294026047672277 143214661131891235492319)
                  ·
                    rfl

theorem cell23_2510186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 7].length) (baseStart_2510186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510186 prefixEnd_2510186 := by exact prefixLift 2510186
  have htrace : WordTrace (prefixWord ++ tailWord_2510186) baseStart_2510186 baseEnd_2510186 := by
    simpa [prefixWord, tailWord_2510186, baseEnd_2510186] using wordTrace_append hprefix tailTrace_2510186
  have hstable : (prefixWord ++ tailWord_2510186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510186).length < 2 ^ (prefixWord ++ tailWord_2510186).sum := by decide
  have hdescent : baseEnd_2510186 < baseStart_2510186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510197 : List Nat := [1, 3, 4, 1, 4, 1, 2, 1, 2, 2, 2]
def baseStart_2510197 : Nat := 118140960795 + 2510197 * 2 ^ 59
def prefixEnd_2510197 : Nat := 4983230072969 + 3 ^ 40 * 2510197 * 2
def baseEnd_2510197 : Nat := 1288937598474220576393321

theorem tailTrace_2510197 : CollatzResearch.WordTrace tailWord_2510197 prefixEnd_2510197 1288937598474220576393321 := by
  unfold tailWord_2510197
  simp only [CollatzResearch.WordTrace]
  refine ⟨91554406086992451361560845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61036270724661634241040563 91554406086992451361560845)
  ·
    refine ⟨34332902282622169260585317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91554406086992451361560845 34332902282622169260585317)
    ·
      refine ⟨6437419177991656736359747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34332902282622169260585317 6437419177991656736359747)
      ·
        refine ⟨9656128766987485104539621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6437419177991656736359747 9656128766987485104539621)
        ·
          refine ⟨1810524143810153457101179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9656128766987485104539621 1810524143810153457101179)
          ·
            refine ⟨2715786215715230185651769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810524143810153457101179 2715786215715230185651769)
            ·
              refine ⟨2036839661786422639238827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2715786215715230185651769 2036839661786422639238827)
              ·
                refine ⟨3055259492679633958858241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036839661786422639238827 3055259492679633958858241)
                ·
                  refine ⟨2291444619509725469143681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3055259492679633958858241 2291444619509725469143681)
                  ·
                    refine ⟨1718583464632294101857761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2291444619509725469143681 1718583464632294101857761)
                    ·
                      refine ⟨1288937598474220576393321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718583464632294101857761 1288937598474220576393321)
                      ·
                        rfl

theorem cell23_2510197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_2510197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510197 prefixEnd_2510197 := by exact prefixLift 2510197
  have htrace : WordTrace (prefixWord ++ tailWord_2510197) baseStart_2510197 baseEnd_2510197 := by
    simpa [prefixWord, tailWord_2510197, baseEnd_2510197] using wordTrace_append hprefix tailTrace_2510197
  have hstable : (prefixWord ++ tailWord_2510197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510197).length < 2 ^ (prefixWord ++ tailWord_2510197).sum := by decide
  have hdescent : baseEnd_2510197 < baseStart_2510197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510239 : List Nat := [1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 3]
def baseStart_2510239 : Nat := 118140960795 + 2510239 * 2 ^ 59
def prefixEnd_2510239 : Nat := 4983230072969 + 3 ^ 40 * 2510239 * 2
def baseEnd_2510239 : Nat := 1288959164661709412068127

theorem tailTrace_2510239 : CollatzResearch.WordTrace tailWord_2510239 prefixEnd_2510239 1288959164661709412068127 := by
  unfold tailWord_2510239
  simp only [CollatzResearch.WordTrace]
  refine ⟨91555937952840292534589771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61037291968560195023059847 91555937952840292534589771)
  ·
    refine ⟨137333906929260438801884657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91555937952840292534589771 137333906929260438801884657)
    ·
      refine ⟨103000430196945329101413493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137333906929260438801884657 103000430196945329101413493)
      ·
        refine ⟨9656290330963624603257515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 103000430196945329101413493 9656290330963624603257515)
        ·
          refine ⟨14484435496445436904886273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9656290330963624603257515 14484435496445436904886273)
          ·
            refine ⟨10863326622334077678664705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14484435496445436904886273 10863326622334077678664705)
            ·
              refine ⟨8147494966750558258998529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10863326622334077678664705 8147494966750558258998529)
              ·
                refine ⟨6110621225062918694248897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8147494966750558258998529 6110621225062918694248897)
                ·
                  refine ⟨4582965918797189020686673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6110621225062918694248897 4582965918797189020686673)
                  ·
                    refine ⟨3437224439097891765515005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4582965918797189020686673 3437224439097891765515005)
                    ·
                      refine ⟨1288959164661709412068127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3437224439097891765515005 1288959164661709412068127)
                      ·
                        rfl

theorem cell23_2510239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_2510239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510239 prefixEnd_2510239 := by exact prefixLift 2510239
  have htrace : WordTrace (prefixWord ++ tailWord_2510239) baseStart_2510239 baseEnd_2510239 := by
    simpa [prefixWord, tailWord_2510239, baseEnd_2510239] using wordTrace_append hprefix tailTrace_2510239
  have hstable : (prefixWord ++ tailWord_2510239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510239).length < 2 ^ (prefixWord ++ tailWord_2510239).sum := by decide
  have hdescent : baseEnd_2510239 < baseStart_2510239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510272 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 3, 5]
def baseStart_2510272 : Nat := 118140960795 + 2510272 * 2 ^ 59
def prefixEnd_2510272 : Nat := 4983230072969 + 3 ^ 40 * 2510272 * 2
def baseEnd_2510272 : Nat := 429658703174435927651825

theorem tailTrace_2510272 : CollatzResearch.WordTrace tailWord_2510272 prefixEnd_2510272 429658703174435927651825 := by
  unfold tailWord_2510272
  simp only [CollatzResearch.WordTrace]
  refine ⟨45778570780860369585270535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61038094374480492780360713 45778570780860369585270535)
  ·
    refine ⟨68667856171290554377905803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45778570780860369585270535 68667856171290554377905803)
    ·
      refine ⟨103001784256935831566858705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68667856171290554377905803 103001784256935831566858705)
      ·
        refine ⟨77251338192701873675144029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103001784256935831566858705 77251338192701873675144029)
        ·
          refine ⟨28969251822263202628179011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77251338192701873675144029 28969251822263202628179011)
          ·
            refine ⟨43453877733394803942268517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28969251822263202628179011 43453877733394803942268517)
            ·
              refine ⟨8147602075011525739175347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43453877733394803942268517 8147602075011525739175347)
              ·
                refine ⟨12221403112517288608763021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8147602075011525739175347 12221403112517288608763021)
                ·
                  refine ⟨4583026167193983228286133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12221403112517288608763021 4583026167193983228286133)
                  ·
                    refine ⟨429658703174435927651825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4583026167193983228286133 429658703174435927651825)
                    ·
                      rfl

theorem cell23_2510272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_2510272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510272 prefixEnd_2510272 := by exact prefixLift 2510272
  have htrace : WordTrace (prefixWord ++ tailWord_2510272) baseStart_2510272 baseEnd_2510272 := by
    simpa [prefixWord, tailWord_2510272, baseEnd_2510272] using wordTrace_append hprefix tailTrace_2510272
  have hstable : (prefixWord ++ tailWord_2510272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510272).length < 2 ^ (prefixWord ++ tailWord_2510272).sum := by decide
  have hdescent : baseEnd_2510272 < baseStart_2510272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510279 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 1, 5, 2]
def baseStart_2510279 : Nat := 118140960795 + 2510279 * 2 ^ 59
def prefixEnd_2510279 : Nat := 4983230072969 + 3 ^ 40 * 2510279 * 2
def baseEnd_2510279 : Nat := 1288979703887889255567943

theorem tailTrace_2510279 : CollatzResearch.WordTrace tailWord_2510279 prefixEnd_2510279 1288979703887889255567943 := by
  unfold tailWord_2510279
  simp only [CollatzResearch.WordTrace]
  refine ⟨91557396872695379366045891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61038264581796919577363927 91557396872695379366045891)
  ·
    refine ⟨137336095309043069049068837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91557396872695379366045891 137336095309043069049068837)
    ·
      refine ⟨25750517870445575446700407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137336095309043069049068837 25750517870445575446700407)
      ·
        refine ⟨38625776805668363170050611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25750517870445575446700407 38625776805668363170050611)
        ·
          refine ⟨57938665208502544755075917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38625776805668363170050611 57938665208502544755075917)
          ·
            refine ⟨21726999453188454283153469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57938665208502544755075917 21726999453188454283153469)
            ·
              refine ⟨8147624794945670356182551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21726999453188454283153469 8147624794945670356182551)
              ·
                refine ⟨12221437192418505534273827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8147624794945670356182551 12221437192418505534273827)
                ·
                  refine ⟨18332155788627758301410741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12221437192418505534273827 18332155788627758301410741)
                  ·
                    refine ⟨1718639605183852340757257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18332155788627758301410741 1718639605183852340757257)
                    ·
                      refine ⟨1288979703887889255567943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718639605183852340757257 1288979703887889255567943)
                      ·
                        rfl

theorem cell23_2510279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 1, 5, 2].length) (baseStart_2510279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510279 prefixEnd_2510279 := by exact prefixLift 2510279
  have htrace : WordTrace (prefixWord ++ tailWord_2510279) baseStart_2510279 baseEnd_2510279 := by
    simpa [prefixWord, tailWord_2510279, baseEnd_2510279] using wordTrace_append hprefix tailTrace_2510279
  have hstable : (prefixWord ++ tailWord_2510279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510279).length < 2 ^ (prefixWord ++ tailWord_2510279).sum := by decide
  have hdescent : baseEnd_2510279 < baseStart_2510279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510319 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 2, 4]
def baseStart_2510319 : Nat := 118140960795 + 2510319 * 2 ^ 59
def prefixEnd_2510319 : Nat := 4983230072969 + 3 ^ 40 * 2510319 * 2
def baseEnd_2510319 : Nat := 429666747704689699689253

theorem tailTrace_2510319 : CollatzResearch.WordTrace tailWord_2510319 prefixEnd_2510319 429666747704689699689253 := by
  unfold tailWord_2510319
  simp only [CollatzResearch.WordTrace]
  refine ⟨91558855792550466197502011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61039237195033644131668007 91558855792550466197502011)
  ·
    refine ⟨137338283688825699296253017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91558855792550466197502011 137338283688825699296253017)
    ·
      refine ⟨103003712766619274472189763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137338283688825699296253017 103003712766619274472189763)
      ·
        refine ⟨154505569149928911708284645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103003712766619274472189763 154505569149928911708284645)
        ·
          refine ⟨28969794215611670945303371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154505569149928911708284645 28969794215611670945303371)
          ·
            refine ⟨43454691323417506417955057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28969794215611670945303371 43454691323417506417955057)
            ·
              refine ⟨32591018492563129813466293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43454691323417506417955057 32591018492563129813466293)
              ·
                refine ⟨3055407983677793420012465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32591018492563129813466293 3055407983677793420012465)
                ·
                  refine ⟨2291555987758345065009349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3055407983677793420012465 2291555987758345065009349)
                  ·
                    refine ⟨429666747704689699689253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2291555987758345065009349 429666747704689699689253)
                    ·
                      rfl

theorem cell23_2510319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 4].length) (baseStart_2510319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510319 prefixEnd_2510319 := by exact prefixLift 2510319
  have htrace : WordTrace (prefixWord ++ tailWord_2510319) baseStart_2510319 baseEnd_2510319 := by
    simpa [prefixWord, tailWord_2510319, baseEnd_2510319] using wordTrace_append hprefix tailTrace_2510319
  have hstable : (prefixWord ++ tailWord_2510319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510319).length < 2 ^ (prefixWord ++ tailWord_2510319).sum := by decide
  have hdescent : baseEnd_2510319 < baseStart_2510319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510326 : List Nat := [5, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4]
def baseStart_2510326 : Nat := 118140960795 + 2510326 * 2 ^ 59
def prefixEnd_2510326 : Nat := 4983230072969 + 3 ^ 40 * 2510326 * 2
def baseEnd_2510326 : Nat := 1289003837478650571680227

theorem tailTrace_2510326 : CollatzResearch.WordTrace tailWord_2510326 prefixEnd_2510326 1289003837478650571680227 := by
  unfold tailWord_2510326
  simp only [CollatzResearch.WordTrace]
  refine ⟨5722444443970319149562927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61039407402350070928671221 5722444443970319149562927)
  ·
    refine ⟨8583666665955478724344391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5722444443970319149562927 8583666665955478724344391)
    ·
      refine ⟨12875499998933218086516587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8583666665955478724344391 12875499998933218086516587)
      ·
        refine ⟨19313249998399827129774881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12875499998933218086516587 19313249998399827129774881)
        ·
          refine ⟨14484937498799870347331161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19313249998399827129774881 14484937498799870347331161)
          ·
            refine ⟨10863703124099902760498371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14484937498799870347331161 10863703124099902760498371)
            ·
              refine ⟨16295554686149854140747557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10863703124099902760498371 16295554686149854140747557)
              ·
                refine ⟨3055416503653097651390167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16295554686149854140747557 3055416503653097651390167)
                ·
                  refine ⟨4583124755479646477085251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055416503653097651390167 4583124755479646477085251)
                  ·
                    refine ⟨6874687133219469715627877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4583124755479646477085251 6874687133219469715627877)
                    ·
                      refine ⟨1289003837478650571680227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6874687133219469715627877 1289003837478650571680227)
                      ·
                        rfl

theorem cell23_2510326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 1, 1, 4].length) (baseStart_2510326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510326 prefixEnd_2510326 := by exact prefixLift 2510326
  have htrace : WordTrace (prefixWord ++ tailWord_2510326) baseStart_2510326 baseEnd_2510326 := by
    simpa [prefixWord, tailWord_2510326, baseEnd_2510326] using wordTrace_append hprefix tailTrace_2510326
  have hstable : (prefixWord ++ tailWord_2510326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510326).length < 2 ^ (prefixWord ++ tailWord_2510326).sum := by decide
  have hdescent : baseEnd_2510326 < baseStart_2510326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510337 : List Nat := [1, 2, 4, 1, 5, 1, 1, 3, 1, 1, 3]
def baseStart_2510337 : Nat := 118140960795 + 2510337 * 2 ^ 59
def prefixEnd_2510337 : Nat := 4983230072969 + 3 ^ 40 * 2510337 * 2
def baseEnd_2510337 : Nat := 1289009485765850028642677

theorem tailTrace_2510337 : CollatzResearch.WordTrace tailWord_2510337 prefixEnd_2510337 1289009485765850028642677 := by
  unfold tailWord_2510337
  simp only [CollatzResearch.WordTrace]
  refine ⟨91559512306485255271657265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61039674870990170181104843 91559512306485255271657265)
  ·
    refine ⟨68669634229863941453742949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91559512306485255271657265 68669634229863941453742949)
    ·
      refine ⟨12875556418099489022576803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68669634229863941453742949 12875556418099489022576803)
      ·
        refine ⟨19313334627149233533865205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12875556418099489022576803 19313334627149233533865205)
        ·
          refine ⟨1810625121295240643799863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19313334627149233533865205 1810625121295240643799863)
          ·
            refine ⟨2715937681942860965699795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810625121295240643799863 2715937681942860965699795)
            ·
              refine ⟨4073906522914291448549693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715937681942860965699795 4073906522914291448549693)
              ·
                refine ⟨1527714946092859293206135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4073906522914291448549693 1527714946092859293206135)
                ·
                  refine ⟨2291572419139288939809203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527714946092859293206135 2291572419139288939809203)
                  ·
                    refine ⟨3437358628708933409713805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2291572419139288939809203 3437358628708933409713805)
                    ·
                      refine ⟨1289009485765850028642677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3437358628708933409713805 1289009485765850028642677)
                      ·
                        rfl

theorem cell23_2510337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 3, 1, 1, 3].length) (baseStart_2510337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510337 prefixEnd_2510337 := by exact prefixLift 2510337
  have htrace : WordTrace (prefixWord ++ tailWord_2510337) baseStart_2510337 baseEnd_2510337 := by
    simpa [prefixWord, tailWord_2510337, baseEnd_2510337] using wordTrace_append hprefix tailTrace_2510337
  have hstable : (prefixWord ++ tailWord_2510337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510337).length < 2 ^ (prefixWord ++ tailWord_2510337).sum := by decide
  have hdescent : baseEnd_2510337 < baseStart_2510337 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510346 : List Nat := [3, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3]
def baseStart_2510346 : Nat := 118140960795 + 2510346 * 2 ^ 59
def prefixEnd_2510346 : Nat := 4983230072969 + 3 ^ 40 * 2510346 * 2
def baseEnd_2510346 : Nat := 1289014107091740493430135

theorem tailTrace_2510346 : CollatzResearch.WordTrace tailWord_2510346 prefixEnd_2510346 1289014107091740493430135 := by
  unfold tailWord_2510346
  simp only [CollatzResearch.WordTrace]
  refine ⟨22889960140863162452183723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61039893708968433205823261 22889960140863162452183723)
  ·
    refine ⟨34334940211294743678275585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22889960140863162452183723 34334940211294743678275585)
    ·
      refine ⟨25751205158471057758706689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34334940211294743678275585 25751205158471057758706689)
      ·
        refine ⟨19313403868853293319030017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25751205158471057758706689 19313403868853293319030017)
        ·
          refine ⟨14485052901639969989272513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19313403868853293319030017 14485052901639969989272513)
          ·
            refine ⟨10863789676229977491954385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14485052901639969989272513 10863789676229977491954385)
            ·
              refine ⟨8147842257172483118965789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10863789676229977491954385 8147842257172483118965789)
              ·
                refine ⟨3055440846439681169612171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8147842257172483118965789 3055440846439681169612171)
                ·
                  refine ⟨4583161269659521754418257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055440846439681169612171 4583161269659521754418257)
                  ·
                    refine ⟨3437370952244641315813693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4583161269659521754418257 3437370952244641315813693)
                    ·
                      refine ⟨1289014107091740493430135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3437370952244641315813693 1289014107091740493430135)
                      ·
                        rfl

theorem cell23_2510346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_2510346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510346 prefixEnd_2510346 := by exact prefixLift 2510346
  have htrace : WordTrace (prefixWord ++ tailWord_2510346) baseStart_2510346 baseEnd_2510346 := by
    simpa [prefixWord, tailWord_2510346, baseEnd_2510346] using wordTrace_append hprefix tailTrace_2510346
  have hstable : (prefixWord ++ tailWord_2510346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510346).length < 2 ^ (prefixWord ++ tailWord_2510346).sum := by decide
  have hdescent : baseEnd_2510346 < baseStart_2510346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510360 : List Nat := [2, 1, 2, 3, 4, 2, 1, 1, 3, 2, 2]
def baseStart_2510360 : Nat := 118140960795 + 2510360 * 2 ^ 59
def prefixEnd_2510360 : Nat := 4983230072969 + 3 ^ 40 * 2510360 * 2
def baseEnd_2510360 : Nat := 1289021295820903438655071

theorem tailTrace_2510360 : CollatzResearch.WordTrace tailWord_2510360 prefixEnd_2510360 1289021295820903438655071 := by
  unfold tailWord_2510360
  simp only [CollatzResearch.WordTrace]
  refine ⟨45780175592700965099872267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61040234123601286799829689 45780175592700965099872267)
  ·
    refine ⟨68670263389051447649808401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45780175592700965099872267 68670263389051447649808401)
    ·
      refine ⟨51502697541788585737356301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68670263389051447649808401 51502697541788585737356301)
      ·
        refine ⟨19313511578170719651508613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51502697541788585737356301 19313511578170719651508613)
        ·
          refine ⟨3621283420907009934657865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19313511578170719651508613 3621283420907009934657865)
          ·
            refine ⟨2715962565680257450993399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3621283420907009934657865 2715962565680257450993399)
            ·
              refine ⟨4073943848520386176490099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715962565680257450993399 4073943848520386176490099)
              ·
                refine ⟨6110915772780579264735149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073943848520386176490099 6110915772780579264735149)
                ·
                  refine ⟨2291593414792717224275681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6110915772780579264735149 2291593414792717224275681)
                  ·
                    refine ⟨1718695061094537918206761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2291593414792717224275681 1718695061094537918206761)
                    ·
                      refine ⟨1289021295820903438655071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718695061094537918206761 1289021295820903438655071)
                      ·
                        rfl

theorem cell23_2510360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_2510360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510360 prefixEnd_2510360 := by exact prefixLift 2510360
  have htrace : WordTrace (prefixWord ++ tailWord_2510360) baseStart_2510360 baseEnd_2510360 := by
    simpa [prefixWord, tailWord_2510360, baseEnd_2510360] using wordTrace_append hprefix tailTrace_2510360
  have hstable : (prefixWord ++ tailWord_2510360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510360).length < 2 ^ (prefixWord ++ tailWord_2510360).sum := by decide
  have hdescent : baseEnd_2510360 < baseStart_2510360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510362 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_2510362 : Nat := 118140960795 + 2510362 * 2 ^ 59
def prefixEnd_2510362 : Nat := 4983230072969 + 3 ^ 40 * 2510362 * 2
def baseEnd_2510362 : Nat := 429674107594070810276687

theorem tailTrace_2510362 : CollatzResearch.WordTrace tailWord_2510362 prefixEnd_2510362 429674107594070810276687 := by
  unfold tailWord_2510362
  simp only [CollatzResearch.WordTrace]
  refine ⟨22890106032848671135329335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61040282754263123027544893 22890106032848671135329335)
  ·
    refine ⟨34335159049273006702994003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22890106032848671135329335 34335159049273006702994003)
    ·
      refine ⟨51502738573909510054491005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34335159049273006702994003 51502738573909510054491005)
      ·
        refine ⟨19313526965216066270434127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51502738573909510054491005 19313526965216066270434127)
        ·
          refine ⟨28970290447824099405651191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19313526965216066270434127 28970290447824099405651191)
          ·
            refine ⟨43455435671736149108476787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28970290447824099405651191 43455435671736149108476787)
            ·
              refine ⟨65183153507604223662715181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43455435671736149108476787 65183153507604223662715181)
              ·
                refine ⟨24443682565351583873518193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65183153507604223662715181 24443682565351583873518193)
                ·
                  refine ⟨18332761924013687905138645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24443682565351583873518193 18332761924013687905138645)
                  ·
                    refine ⟨429674107594070810276687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18332761924013687905138645 429674107594070810276687)
                    ·
                      rfl

theorem cell23_2510362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_2510362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510362 prefixEnd_2510362 := by exact prefixLift 2510362
  have htrace : WordTrace (prefixWord ++ tailWord_2510362) baseStart_2510362 baseEnd_2510362 := by
    simpa [prefixWord, tailWord_2510362, baseEnd_2510362] using wordTrace_append hprefix tailTrace_2510362
  have hstable : (prefixWord ++ tailWord_2510362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510362).length < 2 ^ (prefixWord ++ tailWord_2510362).sum := by decide
  have hdescent : baseEnd_2510362 < baseStart_2510362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510433 : List Nat := [1, 2, 3, 1, 1, 3, 1, 5, 2, 2, 2]
def baseStart_2510433 : Nat := 118140960795 + 2510433 * 2 ^ 59
def prefixEnd_2510433 : Nat := 4983230072969 + 3 ^ 40 * 2510433 * 2
def baseEnd_2510433 : Nat := 1289058779908681653042235

theorem tailTrace_2510433 : CollatzResearch.WordTrace tailWord_2510433 prefixEnd_2510433 1289058779908681653042235 := by
  unfold tailWord_2510433
  simp only [CollatzResearch.WordTrace]
  refine ⟨91563013714137463667151953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61042009142758309111434635 91563013714137463667151953)
  ·
    refine ⟨68672260285603097750363965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91563013714137463667151953 68672260285603097750363965)
    ·
      refine ⟨25752097607101161656386487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68672260285603097750363965 25752097607101161656386487)
      ·
        refine ⟨38628146410651742484579731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25752097607101161656386487 38628146410651742484579731)
        ·
          refine ⟨57942219615977613726869597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38628146410651742484579731 57942219615977613726869597)
          ·
            refine ⟨21728332355991605147576099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57942219615977613726869597 21728332355991605147576099)
            ·
              refine ⟨32592498533987407721364149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21728332355991605147576099 32592498533987407721364149)
              ·
                refine ⟨3055546737561319473877889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32592498533987407721364149 3055546737561319473877889)
                ·
                  refine ⟨2291660053170989605408417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3055546737561319473877889 2291660053170989605408417)
                  ·
                    refine ⟨1718745039878242204056313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2291660053170989605408417 1718745039878242204056313)
                    ·
                      refine ⟨1289058779908681653042235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718745039878242204056313 1289058779908681653042235)
                      ·
                        rfl

theorem cell23_2510433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 2, 2, 2].length) (baseStart_2510433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510433 prefixEnd_2510433 := by exact prefixLift 2510433
  have htrace : WordTrace (prefixWord ++ tailWord_2510433) baseStart_2510433 baseEnd_2510433 := by
    simpa [prefixWord, tailWord_2510433, baseEnd_2510433] using wordTrace_append hprefix tailTrace_2510433
  have hstable : (prefixWord ++ tailWord_2510433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510433).length < 2 ^ (prefixWord ++ tailWord_2510433).sum := by decide
  have hdescent : baseEnd_2510433 < baseStart_2510433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510469 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 4, 5]
def baseStart_2510469 : Nat := 118140960795 + 2510469 * 2 ^ 59
def prefixEnd_2510469 : Nat := 4983230072969 + 3 ^ 40 * 2510469 * 2
def baseEnd_2510469 : Nat := 429692421737414504064023

theorem tailTrace_2510469 : CollatzResearch.WordTrace tailWord_2510469 prefixEnd_2510469 429692421737414504064023 := by
  unfold tailWord_2510469
  simp only [CollatzResearch.WordTrace]
  refine ⟨91564326742007041815462461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61042884494671361210308307 91564326742007041815462461)
  ·
    refine ⟨34336622528252640680798423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91564326742007041815462461 34336622528252640680798423)
    ·
      refine ⟨51504933792378961021197635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34336622528252640680798423 51504933792378961021197635)
      ·
        refine ⟨77257400688568441531796453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51504933792378961021197635 77257400688568441531796453)
        ·
          refine ⟨14485762629106582787211835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77257400688568441531796453 14485762629106582787211835)
          ·
            refine ⟨21728643943659874180817753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14485762629106582787211835 21728643943659874180817753)
            ·
              refine ⟨16296482957744905635613315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21728643943659874180817753 16296482957744905635613315)
              ·
                refine ⟨24444724436617358453419973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16296482957744905635613315 24444724436617358453419973)
                ·
                  refine ⟨4583385831865754710016245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24444724436617358453419973 4583385831865754710016245)
                  ·
                    refine ⟨429692421737414504064023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4583385831865754710016245 429692421737414504064023)
                    ·
                      rfl

theorem cell23_2510469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 5].length) (baseStart_2510469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510469 prefixEnd_2510469 := by exact prefixLift 2510469
  have htrace : WordTrace (prefixWord ++ tailWord_2510469) baseStart_2510469 baseEnd_2510469 := by
    simpa [prefixWord, tailWord_2510469, baseEnd_2510469] using wordTrace_append hprefix tailTrace_2510469
  have hstable : (prefixWord ++ tailWord_2510469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510469).length < 2 ^ (prefixWord ++ tailWord_2510469).sum := by decide
  have hdescent : baseEnd_2510469 < baseStart_2510469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510484 : List Nat := [2, 4, 2, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_2510484 : Nat := 118140960795 + 2510484 * 2 ^ 59
def prefixEnd_2510484 : Nat := 4983230072969 + 3 ^ 40 * 2510484 * 2
def baseEnd_2510484 : Nat := 1289084967422060953504501

theorem tailTrace_2510484 : CollatzResearch.WordTrace tailWord_2510484 prefixEnd_2510484 1289084967422060953504501 := by
  unfold tailWord_2510484
  simp only [CollatzResearch.WordTrace]
  refine ⟨45782436918476349688629253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61043249224635132918172337 45782436918476349688629253)
  ·
    refine ⟨8584206922214315566617985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45782436918476349688629253 8584206922214315566617985)
    ·
      refine ⟨6438155191660736674963489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8584206922214315566617985 6438155191660736674963489)
      ·
        refine ⟨4828616393745552506222617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6438155191660736674963489 4828616393745552506222617)
        ·
          refine ⟨3621462295309164379666963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4828616393745552506222617 3621462295309164379666963)
          ·
            refine ⟨5432193442963746569500445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621462295309164379666963 5432193442963746569500445)
            ·
              refine ⟨2037072541111404963562667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5432193442963746569500445 2037072541111404963562667)
              ·
                refine ⟨3055608811667107445344001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037072541111404963562667 3055608811667107445344001)
                ·
                  refine ⟨2291706608750330584008001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3055608811667107445344001 2291706608750330584008001)
                  ·
                    refine ⟨1718779956562747938006001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2291706608750330584008001 1718779956562747938006001)
                    ·
                      refine ⟨1289084967422060953504501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718779956562747938006001 1289084967422060953504501)
                      ·
                        rfl

theorem cell23_2510484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_2510484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510484 prefixEnd_2510484 := by exact prefixLift 2510484
  have htrace : WordTrace (prefixWord ++ tailWord_2510484) baseStart_2510484 baseEnd_2510484 := by
    simpa [prefixWord, tailWord_2510484, baseEnd_2510484] using wordTrace_append hprefix tailTrace_2510484
  have hstable : (prefixWord ++ tailWord_2510484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510484).length < 2 ^ (prefixWord ++ tailWord_2510484).sum := by decide
  have hdescent : baseEnd_2510484 < baseStart_2510484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510489 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 4]
def baseStart_2510489 : Nat := 118140960795 + 2510489 * 2 ^ 59
def prefixEnd_2510489 : Nat := 4983230072969 + 3 ^ 40 * 2510489 * 2
def baseEnd_2510489 : Nat := 1289087534825333433941977

theorem tailTrace_2510489 : CollatzResearch.WordTrace tailWord_2510489 prefixEnd_2510489 1289087534825333433941977 := by
  unfold tailWord_2510489
  simp only [CollatzResearch.WordTrace]
  refine ⟨91565056201934585231190521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61043370801289723487460347 91565056201934585231190521)
  ·
    refine ⟨68673792151450938923392891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91565056201934585231190521 68673792151450938923392891)
    ·
      refine ⟨103010688227176408385089337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68673792151450938923392891 103010688227176408385089337)
      ·
        refine ⟨77258016170382306288817003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103010688227176408385089337 77258016170382306288817003)
        ·
          refine ⟨115887024255573459433225505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77258016170382306288817003 115887024255573459433225505)
          ·
            refine ⟨86915268191680094574919129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115887024255573459433225505 86915268191680094574919129)
            ·
              refine ⟨65186451143760070931189347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86915268191680094574919129 65186451143760070931189347)
              ·
                refine ⟨97779676715640106396784021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65186451143760070931189347 97779676715640106396784021)
                ·
                  refine ⟨4583422346045629987349251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97779676715640106396784021 4583422346045629987349251)
                  ·
                    refine ⟨6875133519068444981023877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4583422346045629987349251 6875133519068444981023877)
                    ·
                      refine ⟨1289087534825333433941977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6875133519068444981023877 1289087534825333433941977)
                      ·
                        rfl

theorem cell23_2510489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 6, 1, 4].length) (baseStart_2510489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510489 prefixEnd_2510489 := by exact prefixLift 2510489
  have htrace : WordTrace (prefixWord ++ tailWord_2510489) baseStart_2510489 baseEnd_2510489 := by
    simpa [prefixWord, tailWord_2510489, baseEnd_2510489] using wordTrace_append hprefix tailTrace_2510489
  have hstable : (prefixWord ++ tailWord_2510489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510489).length < 2 ^ (prefixWord ++ tailWord_2510489).sum := by decide
  have hdescent : baseEnd_2510489 < baseStart_2510489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510580 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 6]
def baseStart_2510580 : Nat := 118140960795 + 2510580 * 2 ^ 59
def prefixEnd_2510580 : Nat := 4983230072969 + 3 ^ 40 * 2510580 * 2
def baseEnd_2510580 : Nat := 143237140173876953100451

theorem tailTrace_2510580 : CollatzResearch.WordTrace tailWord_2510580 prefixEnd_2510580 143237140173876953100451 := by
  unfold tailWord_2510580
  simp only [CollatzResearch.WordTrace]
  refine ⟨45784187622302453886376597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61045583496403271848502129 45784187622302453886376597)
  ·
    refine ⟨2146133794795427525923903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 45784187622302453886376597 2146133794795427525923903)
    ·
      refine ⟨3219200692193141288885855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146133794795427525923903 3219200692193141288885855)
      ·
        refine ⟨4828801038289711933328783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219200692193141288885855 4828801038289711933328783)
        ·
          refine ⟨7243201557434567899993175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4828801038289711933328783 7243201557434567899993175)
          ·
            refine ⟨10864802336151851849989763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7243201557434567899993175 10864802336151851849989763)
            ·
              refine ⟨16297203504227777774984645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10864802336151851849989763 16297203504227777774984645)
              ·
                refine ⟨3055725657042708332809621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16297203504227777774984645 3055725657042708332809621)
                ·
                  refine ⟨143237140173876953100451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3055725657042708332809621 143237140173876953100451)
                  ·
                    rfl

theorem cell23_2510580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_2510580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510580 prefixEnd_2510580 := by exact prefixLift 2510580
  have htrace : WordTrace (prefixWord ++ tailWord_2510580) baseStart_2510580 baseEnd_2510580 := by
    simpa [prefixWord, tailWord_2510580, baseEnd_2510580] using wordTrace_append hprefix tailTrace_2510580
  have hstable : (prefixWord ++ tailWord_2510580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510580).length < 2 ^ (prefixWord ++ tailWord_2510580).sum := by decide
  have hdescent : baseEnd_2510580 < baseStart_2510580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510583 : List Nat := [1, 1, 3, 1, 1, 1, 6, 2, 2, 3, 2]
def baseStart_2510583 : Nat := 118140960795 + 2510583 * 2 ^ 59
def prefixEnd_2510583 : Nat := 4983230072969 + 3 ^ 40 * 2510583 * 2
def baseEnd_2510583 : Nat := 1289135802006856066166545

theorem tailTrace_2510583 : CollatzResearch.WordTrace tailWord_2510583 prefixEnd_2510583 1289135802006856066166545 := by
  unfold tailWord_2510583
  simp only [CollatzResearch.WordTrace]
  refine ⟨91568484663594039285112403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61045656442396026190074935 91568484663594039285112403)
  ·
    refine ⟨137352726995391058927668605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91568484663594039285112403 137352726995391058927668605)
    ·
      refine ⟨51507272623271647097875727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137352726995391058927668605 51507272623271647097875727)
      ·
        refine ⟨77260908934907470646813591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51507272623271647097875727 77260908934907470646813591)
        ·
          refine ⟨115891363402361205970220387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77260908934907470646813591 115891363402361205970220387)
          ·
            refine ⟨173837045103541808955330581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115891363402361205970220387 173837045103541808955330581)
            ·
              refine ⟨8148611489228522294781121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173837045103541808955330581 8148611489228522294781121)
              ·
                refine ⟨6111458616921391721085841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8148611489228522294781121 6111458616921391721085841)
                ·
                  refine ⟨4583593962691043790814381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6111458616921391721085841 4583593962691043790814381)
                  ·
                    refine ⟨1718847736009141421555393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4583593962691043790814381 1718847736009141421555393)
                    ·
                      refine ⟨1289135802006856066166545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718847736009141421555393 1289135802006856066166545)
                      ·
                        rfl

theorem cell23_2510583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2, 3, 2].length) (baseStart_2510583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510583 prefixEnd_2510583 := by exact prefixLift 2510583
  have htrace : WordTrace (prefixWord ++ tailWord_2510583) baseStart_2510583 baseEnd_2510583 := by
    simpa [prefixWord, tailWord_2510583, baseEnd_2510583] using wordTrace_append hprefix tailTrace_2510583
  have hstable : (prefixWord ++ tailWord_2510583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510583).length < 2 ^ (prefixWord ++ tailWord_2510583).sum := by decide
  have hdescent : baseEnd_2510583 < baseStart_2510583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510606 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 1, 6]
def baseStart_2510606 : Nat := 118140960795 + 2510606 * 2 ^ 59
def prefixEnd_2510606 : Nat := 4983230072969 + 3 ^ 40 * 2510606 * 2
def baseEnd_2510606 : Nat := 429715870687303158726313

theorem tailTrace_2510606 : CollatzResearch.WordTrace tailWord_2510606 prefixEnd_2510606 429715870687303158726313 := by
  unfold tailWord_2510606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11446165442813839276649959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61046215695007142808799781 11446165442813839276649959)
  ·
    refine ⟨17169248164220758914974939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11446165442813839276649959 17169248164220758914974939)
    ·
      refine ⟨25753872246331138372462409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17169248164220758914974939 25753872246331138372462409)
      ·
        refine ⟨19315404184748353779346807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25753872246331138372462409 19315404184748353779346807)
        ·
          refine ⟨28973106277122530669020211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19315404184748353779346807 28973106277122530669020211)
          ·
            refine ⟨43459659415683796003530317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28973106277122530669020211 43459659415683796003530317)
            ·
              refine ⟨16297372280881423501323869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43459659415683796003530317 16297372280881423501323869)
              ·
                refine ⟨6111514605330533812996451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16297372280881423501323869 6111514605330533812996451)
                ·
                  refine ⟨9167271907995800719494677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6111514605330533812996451 9167271907995800719494677)
                  ·
                    refine ⟨429715870687303158726313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9167271907995800719494677 429715870687303158726313)
                    ·
                      rfl

theorem cell23_2510606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 6].length) (baseStart_2510606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510606 prefixEnd_2510606 := by exact prefixLift 2510606
  have htrace : WordTrace (prefixWord ++ tailWord_2510606) baseStart_2510606 baseEnd_2510606 := by
    simpa [prefixWord, tailWord_2510606, baseEnd_2510606] using wordTrace_append hprefix tailTrace_2510606
  have hstable : (prefixWord ++ tailWord_2510606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510606).length < 2 ^ (prefixWord ++ tailWord_2510606).sum := by decide
  have hdescent : baseEnd_2510606 < baseStart_2510606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510663 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 3]
def baseStart_2510663 : Nat := 118140960795 + 2510663 * 2 ^ 59
def prefixEnd_2510663 : Nat := 4983230072969 + 3 ^ 40 * 2510663 * 2
def baseEnd_2510663 : Nat := 1289176880459215753166177

theorem tailTrace_2510663 : CollatzResearch.WordTrace tailWord_2510663 prefixEnd_2510663 1289176880459215753166177 := by
  unfold tailWord_2510663
  simp only [CollatzResearch.WordTrace]
  refine ⟨91571402503304212948024643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61047601668869475298683095 91571402503304212948024643)
  ·
    refine ⟨137357103754956319422036965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91571402503304212948024643 137357103754956319422036965)
    ·
      refine ⟨25754456954054309891631931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137357103754956319422036965 25754456954054309891631931)
      ·
        refine ⟨38631685431081464837447897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25754456954054309891631931 38631685431081464837447897)
        ·
          refine ⟨28973764073311098628085923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38631685431081464837447897 28973764073311098628085923)
          ·
            refine ⟨43460646109966647942128885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28973764073311098628085923 43460646109966647942128885)
            ·
              refine ⟨4074435572809373244574583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43460646109966647942128885 4074435572809373244574583)
              ·
                refine ⟨6111653359214059866861875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074435572809373244574583 6111653359214059866861875)
                ·
                  refine ⟨9167480038821089800292813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6111653359214059866861875 9167480038821089800292813)
                  ·
                    refine ⟨3437805014557908675109805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9167480038821089800292813 3437805014557908675109805)
                    ·
                      refine ⟨1289176880459215753166177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3437805014557908675109805 1289176880459215753166177)
                      ·
                        rfl

theorem cell23_2510663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 3, 3].length) (baseStart_2510663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510663 prefixEnd_2510663 := by exact prefixLift 2510663
  have htrace : WordTrace (prefixWord ++ tailWord_2510663) baseStart_2510663 baseEnd_2510663 := by
    simpa [prefixWord, tailWord_2510663, baseEnd_2510663] using wordTrace_append hprefix tailTrace_2510663
  have hstable : (prefixWord ++ tailWord_2510663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510663).length < 2 ^ (prefixWord ++ tailWord_2510663).sum := by decide
  have hdescent : baseEnd_2510663 < baseStart_2510663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510698 : List Nat := [3, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2]
def baseStart_2510698 : Nat := 118140960795 + 2510698 * 2 ^ 59
def prefixEnd_2510698 : Nat := 4983230072969 + 3 ^ 40 * 2510698 * 2
def baseEnd_2510698 : Nat := 1289194852282123116228517

theorem tailTrace_2510698 : CollatzResearch.WordTrace tailWord_2510698 prefixEnd_2510698 1289194852282123116228517 := by
  unfold tailWord_2510698
  simp only [CollatzResearch.WordTrace]
  refine ⟨22893169764544353481387187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61048452705451609283699165 22893169764544353481387187)
  ·
    refine ⟨34339754646816530222080781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22893169764544353481387187 34339754646816530222080781)
    ·
      refine ⟨12877407992556198833280293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34339754646816530222080781 12877407992556198833280293)
      ·
        refine ⟨2414513998604287281240055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12877407992556198833280293 2414513998604287281240055)
        ·
          refine ⟨3621770997906430921860083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414513998604287281240055 3621770997906430921860083)
          ·
            refine ⟨5432656496859646382790125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621770997906430921860083 5432656496859646382790125)
            ·
              refine ⟨2037246186322367393546297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5432656496859646382790125 2037246186322367393546297)
              ·
                refine ⟨1527934639741775545159723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037246186322367393546297 1527934639741775545159723)
                ·
                  refine ⟨2291901959612663317739585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1527934639741775545159723 2291901959612663317739585)
                  ·
                    refine ⟨1718926469709497488304689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2291901959612663317739585 1718926469709497488304689)
                    ·
                      refine ⟨1289194852282123116228517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1718926469709497488304689 1289194852282123116228517)
                      ·
                        rfl

theorem cell23_2510698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_2510698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510698 prefixEnd_2510698 := by exact prefixLift 2510698
  have htrace : WordTrace (prefixWord ++ tailWord_2510698) baseStart_2510698 baseEnd_2510698 := by
    simpa [prefixWord, tailWord_2510698, baseEnd_2510698] using wordTrace_append hprefix tailTrace_2510698
  have hstable : (prefixWord ++ tailWord_2510698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510698).length < 2 ^ (prefixWord ++ tailWord_2510698).sum := by decide
  have hdescent : baseEnd_2510698 < baseStart_2510698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510706 : List Nat := [3, 2, 1, 2, 1, 1, 1, 1, 3, 3, 5]
def baseStart_2510706 : Nat := 118140960795 + 2510706 * 2 ^ 59
def prefixEnd_2510706 : Nat := 4983230072969 + 3 ^ 40 * 2510706 * 2
def baseEnd_2510706 : Nat := 1289198960127359084928479

theorem tailTrace_2510706 : CollatzResearch.WordTrace tailWord_2510706 prefixEnd_2510706 1289198960127359084928479 := by
  unfold tailWord_2510706
  simp only [CollatzResearch.WordTrace]
  refine ⟨22893242710537107822959993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61048647228098954194559981 22893242710537107822959993)
  ·
    refine ⟨17169932032902830867219995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22893242710537107822959993 17169932032902830867219995)
    ·
      refine ⟨25754898049354246300829993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17169932032902830867219995 25754898049354246300829993)
      ·
        refine ⟨19316173537015684725622495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25754898049354246300829993 19316173537015684725622495)
        ·
          refine ⟨28974260305523527088433743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19316173537015684725622495 28974260305523527088433743)
          ·
            refine ⟨43461390458285290632650615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28974260305523527088433743 43461390458285290632650615)
            ·
              refine ⟨65192085687427935948975923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43461390458285290632650615 65192085687427935948975923)
              ·
                refine ⟨97788128531141903923463885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65192085687427935948975923 97788128531141903923463885)
                ·
                  refine ⟨36670548199178213971298957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97788128531141903923463885 36670548199178213971298957)
                  ·
                    refine ⟨13751455574691830239237109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36670548199178213971298957 13751455574691830239237109)
                    ·
                      refine ⟨1289198960127359084928479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13751455574691830239237109 1289198960127359084928479)
                      ·
                        rfl

theorem cell23_2510706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_2510706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510706 prefixEnd_2510706 := by exact prefixLift 2510706
  have htrace : WordTrace (prefixWord ++ tailWord_2510706) baseStart_2510706 baseEnd_2510706 := by
    simpa [prefixWord, tailWord_2510706, baseEnd_2510706] using wordTrace_append hprefix tailTrace_2510706
  have hstable : (prefixWord ++ tailWord_2510706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510706).length < 2 ^ (prefixWord ++ tailWord_2510706).sum := by decide
  have hdescent : baseEnd_2510706 < baseStart_2510706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510820 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_2510820 : Nat := 118140960795 + 2510820 * 2 ^ 59
def prefixEnd_2510820 : Nat := 4983230072969 + 3 ^ 40 * 2510820 * 2
def baseEnd_2510820 : Nat := 429752498973990546300985

theorem tailTrace_2510820 : CollatzResearch.WordTrace tailWord_2510820 prefixEnd_2510820 429752498973990546300985 := by
  unfold tailWord_2510820
  simp only [CollatzResearch.WordTrace]
  refine ⟨45788564381867714380744957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61051419175823619174326609 45788564381867714380744957)
  ·
    refine ⟨17170711643200392892779359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45788564381867714380744957 17170711643200392892779359)
    ·
      refine ⟨25756067464800589339169039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17170711643200392892779359 25756067464800589339169039)
      ·
        refine ⟨38634101197200884008753559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25756067464800589339169039 38634101197200884008753559)
        ·
          refine ⟨57951151795801326013130339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38634101197200884008753559 57951151795801326013130339)
          ·
            refine ⟨86926727693701989019695509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57951151795801326013130339 86926727693701989019695509)
            ·
              refine ⟨4074690360642280735298227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86926727693701989019695509 4074690360642280735298227)
              ·
                refine ⟨6112035540963421102947341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074690360642280735298227 6112035540963421102947341)
                ·
                  refine ⟨2292013327861282913605253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6112035540963421102947341 2292013327861282913605253)
                  ·
                    refine ⟨429752498973990546300985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2292013327861282913605253 429752498973990546300985)
                    ·
                      rfl

theorem cell23_2510820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_2510820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510820 prefixEnd_2510820 := by exact prefixLift 2510820
  have htrace : WordTrace (prefixWord ++ tailWord_2510820) baseStart_2510820 baseEnd_2510820 := by
    simpa [prefixWord, tailWord_2510820, baseEnd_2510820] using wordTrace_append hprefix tailTrace_2510820
  have hstable : (prefixWord ++ tailWord_2510820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510820).length < 2 ^ (prefixWord ++ tailWord_2510820).sum := by decide
  have hdescent : baseEnd_2510820 < baseStart_2510820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510830 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3]
def baseStart_2510830 : Nat := 118140960795 + 2510830 * 2 ^ 59
def prefixEnd_2510830 : Nat := 4983230072969 + 3 ^ 40 * 2510830 * 2
def baseEnd_2510830 : Nat := 1289262631728516599777909

theorem tailTrace_2510830 : CollatzResearch.WordTrace tailWord_2510830 prefixEnd_2510830 1289262631728516599777909 := by
  unfold tailWord_2510830
  simp only [CollatzResearch.WordTrace]
  refine ⟨11447186686712400058669243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61051662329132800312902629 11447186686712400058669243)
  ·
    refine ⟨17170780030068600088003865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11447186686712400058669243 17170780030068600088003865)
    ·
      refine ⟨12878085022551450066002899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17170780030068600088003865 12878085022551450066002899)
      ·
        refine ⟨19317127533827175099004349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12878085022551450066002899 19317127533827175099004349)
        ·
          refine ⟨7243922825185190662126631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19317127533827175099004349 7243922825185190662126631)
          ·
            refine ⟨10865884237777785993189947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7243922825185190662126631 10865884237777785993189947)
            ·
              refine ⟨16298826356666678989784921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10865884237777785993189947 16298826356666678989784921)
              ·
                refine ⟨12224119767500009242338691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16298826356666678989784921 12224119767500009242338691)
                ·
                  refine ⟨18336179651250013863508037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12224119767500009242338691 18336179651250013863508037)
                  ·
                    refine ⟨3438033684609377599407757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18336179651250013863508037 3438033684609377599407757)
                    ·
                      refine ⟨1289262631728516599777909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3438033684609377599407757 1289262631728516599777909)
                      ·
                        rfl

theorem cell23_2510830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_2510830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510830 prefixEnd_2510830 := by exact prefixLift 2510830
  have htrace : WordTrace (prefixWord ++ tailWord_2510830) baseStart_2510830 baseEnd_2510830 := by
    simpa [prefixWord, tailWord_2510830, baseEnd_2510830] using wordTrace_append hprefix tailTrace_2510830
  have hstable : (prefixWord ++ tailWord_2510830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510830).length < 2 ^ (prefixWord ++ tailWord_2510830).sum := by decide
  have hdescent : baseEnd_2510830 < baseStart_2510830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510861 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 2, 1, 4]
def baseStart_2510861 : Nat := 118140960795 + 2510861 * 2 ^ 59
def prefixEnd_2510861 : Nat := 4983230072969 + 3 ^ 40 * 2510861 * 2
def baseEnd_2510861 : Nat := 1289278549628805978490267

theorem tailTrace_2510861 : CollatzResearch.WordTrace tailWord_2510861 prefixEnd_2510861 1289278549628805978490267 := by
  unfold tailWord_2510861
  simp only [CollatzResearch.WordTrace]
  refine ⟨91578624156586892763732437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61052416104391261842488291 91578624156586892763732437)
  ·
    refine ⟨2146374003670005299149979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 91578624156586892763732437 2146374003670005299149979)
    ·
      refine ⟨3219561005505007948724969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2146374003670005299149979 3219561005505007948724969)
      ·
        refine ⟨2414670754128755961543727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3219561005505007948724969 2414670754128755961543727)
        ·
          refine ⟨3622006131193133942315591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414670754128755961543727 3622006131193133942315591)
          ·
            refine ⟨5433009196789700913473387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622006131193133942315591 5433009196789700913473387)
            ·
              refine ⟨8149513795184551370210081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433009196789700913473387 8149513795184551370210081)
              ·
                refine ⟨6112135346388413527657561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8149513795184551370210081 6112135346388413527657561)
                ·
                  refine ⟨4584101509791310145743171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6112135346388413527657561 4584101509791310145743171)
                  ·
                    refine ⟨6876152264686965218614757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4584101509791310145743171 6876152264686965218614757)
                    ·
                      refine ⟨1289278549628805978490267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6876152264686965218614757 1289278549628805978490267)
                      ·
                        rfl

theorem cell23_2510861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_2510861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510861 prefixEnd_2510861 := by exact prefixLift 2510861
  have htrace : WordTrace (prefixWord ++ tailWord_2510861) baseStart_2510861 baseEnd_2510861 := by
    simpa [prefixWord, tailWord_2510861, baseEnd_2510861] using wordTrace_append hprefix tailTrace_2510861
  have hstable : (prefixWord ++ tailWord_2510861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510861).length < 2 ^ (prefixWord ++ tailWord_2510861).sum := by decide
  have hdescent : baseEnd_2510861 < baseStart_2510861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510871 : List Nat := [1, 1, 3, 5, 2, 1, 3, 2, 1, 4]
def baseStart_2510871 : Nat := 118140960795 + 2510871 * 2 ^ 59
def prefixEnd_2510871 : Nat := 4983230072969 + 3 ^ 40 * 2510871 * 2
def baseEnd_2510871 : Nat := 429761228145116979788407

theorem tailTrace_2510871 : CollatzResearch.WordTrace tailWord_2510871 prefixEnd_2510871 429761228145116979788407 := by
  unfold tailWord_2510871
  simp only [CollatzResearch.WordTrace]
  refine ⟨91578988886550664471596467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61052659257700442981064311 91578988886550664471596467)
  ·
    refine ⟨137368483329825996707394701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91578988886550664471596467 137368483329825996707394701)
    ·
      refine ⟨51513181248684748765273013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137368483329825996707394701 51513181248684748765273013)
      ·
        refine ⟨4829360742064195196744345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51513181248684748765273013 4829360742064195196744345)
        ·
          refine ⟨3622020556548146397558259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4829360742064195196744345 3622020556548146397558259)
          ·
            refine ⟨5433030834822219596337389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622020556548146397558259 5433030834822219596337389)
            ·
              refine ⟨2037386563058332348626521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5433030834822219596337389 2037386563058332348626521)
              ·
                refine ⟨1528039922293749261469891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037386563058332348626521 1528039922293749261469891)
                ·
                  refine ⟨2292059883440623892204837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528039922293749261469891 2292059883440623892204837)
                  ·
                    refine ⟨429761228145116979788407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2292059883440623892204837 429761228145116979788407)
                    ·
                      rfl

theorem cell23_2510871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 4].length) (baseStart_2510871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510871 prefixEnd_2510871 := by exact prefixLift 2510871
  have htrace : WordTrace (prefixWord ++ tailWord_2510871) baseStart_2510871 baseEnd_2510871 := by
    simpa [prefixWord, tailWord_2510871, baseEnd_2510871] using wordTrace_append hprefix tailTrace_2510871
  have hstable : (prefixWord ++ tailWord_2510871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510871).length < 2 ^ (prefixWord ++ tailWord_2510871).sum := by decide
  have hdescent : baseEnd_2510871 < baseStart_2510871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510884 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 6]
def baseStart_2510884 : Nat := 118140960795 + 2510884 * 2 ^ 59
def prefixEnd_2510884 : Nat := 4983230072969 + 3 ^ 40 * 2510884 * 2
def baseEnd_2510884 : Nat := 143254484409317709833629

theorem tailTrace_2510884 : CollatzResearch.WordTrace tailWord_2510884 prefixEnd_2510884 143254484409317709833629 := by
  unfold tailWord_2510884
  simp only [CollatzResearch.WordTrace]
  refine ⟨45789731517751783845909853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61052975357002378461213137 45789731517751783845909853)
  ·
    refine ⟨17171149319156918942216195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45789731517751783845909853 17171149319156918942216195)
    ·
      refine ⟨25756723978735378413324293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17171149319156918942216195 25756723978735378413324293)
      ·
        refine ⟨4829385746012883452498305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25756723978735378413324293 4829385746012883452498305)
        ·
          refine ⟨3622039309509662589373729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4829385746012883452498305 3622039309509662589373729)
          ·
            refine ⟨2716529482132246942030297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3622039309509662589373729 2716529482132246942030297)
            ·
              refine ⟨2037397111599185206522723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2716529482132246942030297 2037397111599185206522723)
              ·
                refine ⟨3056095667398777809784085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037397111599185206522723 3056095667398777809784085)
                ·
                  refine ⟨143254484409317709833629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3056095667398777809784085 143254484409317709833629)
                  ·
                    rfl

theorem cell23_2510884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_2510884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510884 prefixEnd_2510884 := by exact prefixLift 2510884
  have htrace : WordTrace (prefixWord ++ tailWord_2510884) baseStart_2510884 baseEnd_2510884 := by
    simpa [prefixWord, tailWord_2510884, baseEnd_2510884] using wordTrace_append hprefix tailTrace_2510884
  have hstable : (prefixWord ++ tailWord_2510884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510884).length < 2 ^ (prefixWord ++ tailWord_2510884).sum := by decide
  have hdescent : baseEnd_2510884 < baseStart_2510884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510897 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 1, 5]
def baseStart_2510897 : Nat := 118140960795 + 2510897 * 2 ^ 59
def prefixEnd_2510897 : Nat := 4983230072969 + 3 ^ 40 * 2510897 * 2
def baseEnd_2510897 : Nat := 429765678310789279213367

theorem tailTrace_2510897 : CollatzResearch.WordTrace tailWord_2510897 prefixEnd_2510897 429765678310789279213367 := by
  unfold tailWord_2510897
  simp only [CollatzResearch.WordTrace]
  refine ⟨91579937184456470912042945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61053291456304313941361963 91579937184456470912042945)
  ·
    refine ⟨68684952888342353184032209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91579937184456470912042945 68684952888342353184032209)
    ·
      refine ⟨51513714666256764888024157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68684952888342353184032209 51513714666256764888024157)
      ·
        refine ⟨19317642999846286833009059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51513714666256764888024157 19317642999846286833009059)
        ·
          refine ⟨28976464499769430249513589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19317642999846286833009059 28976464499769430249513589)
          ·
            refine ⟨2716543546853384085891899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28976464499769430249513589 2716543546853384085891899)
            ·
              refine ⟨4074815320280076128837849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2716543546853384085891899 4074815320280076128837849)
              ·
                refine ⟨3056111490210057096628387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4074815320280076128837849 3056111490210057096628387)
                ·
                  refine ⟨4584167235315085644942581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056111490210057096628387 4584167235315085644942581)
                  ·
                    refine ⟨429765678310789279213367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4584167235315085644942581 429765678310789279213367)
                    ·
                      rfl

theorem cell23_2510897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 5].length) (baseStart_2510897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510897 prefixEnd_2510897 := by exact prefixLift 2510897
  have htrace : WordTrace (prefixWord ++ tailWord_2510897) baseStart_2510897 baseEnd_2510897 := by
    simpa [prefixWord, tailWord_2510897, baseEnd_2510897] using wordTrace_append hprefix tailTrace_2510897
  have hstable : (prefixWord ++ tailWord_2510897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510897).length < 2 ^ (prefixWord ++ tailWord_2510897).sum := by decide
  have hdescent : baseEnd_2510897 < baseStart_2510897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510903 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 5]
def baseStart_2510903 : Nat := 118140960795 + 2510903 * 2 ^ 59
def prefixEnd_2510903 : Nat := 4983230072969 + 3 ^ 40 * 2510903 * 2
def baseEnd_2510903 : Nat := 1289300115816294814165073

theorem tailTrace_2510903 : CollatzResearch.WordTrace tailWord_2510903 prefixEnd_2510903 1289300115816294814165073 := by
  unfold tailWord_2510903
  simp only [CollatzResearch.WordTrace]
  refine ⟨91580156022434733936761363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61053437348289822624507575 91580156022434733936761363)
  ·
    refine ⟨137370234033652100905142045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91580156022434733936761363 137370234033652100905142045)
    ·
      refine ⟨51513837762619537839428267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137370234033652100905142045 51513837762619537839428267)
      ·
        refine ⟨77270756643929306759142401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51513837762619537839428267 77270756643929306759142401)
        ·
          refine ⟨57953067482946980069356801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77270756643929306759142401 57953067482946980069356801)
          ·
            refine ⟨43464800612210235052017601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57953067482946980069356801 43464800612210235052017601)
            ·
              refine ⟨32598600459157676289013201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43464800612210235052017601 32598600459157676289013201)
              ·
                refine ⟨24448950344368257216759901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32598600459157676289013201 24448950344368257216759901)
                ·
                  refine ⟨9168356379138096456284963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24448950344368257216759901 9168356379138096456284963)
                  ·
                    refine ⟨13752534568707144684427445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9168356379138096456284963 13752534568707144684427445)
                    ·
                      refine ⟨1289300115816294814165073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13752534568707144684427445 1289300115816294814165073)
                      ·
                        rfl

theorem cell23_2510903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 3, 1, 5].length) (baseStart_2510903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510903 prefixEnd_2510903 := by exact prefixLift 2510903
  have htrace : WordTrace (prefixWord ++ tailWord_2510903) baseStart_2510903 baseEnd_2510903 := by
    simpa [prefixWord, tailWord_2510903, baseEnd_2510903] using wordTrace_append hprefix tailTrace_2510903
  have hstable : (prefixWord ++ tailWord_2510903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510903).length < 2 ^ (prefixWord ++ tailWord_2510903).sum := by decide
  have hdescent : baseEnd_2510903 < baseStart_2510903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510904 : List Nat := [2, 1, 2, 1, 6, 1, 2, 1, 2, 3, 2]
def baseStart_2510904 : Nat := 118140960795 + 2510904 * 2 ^ 59
def prefixEnd_2510904 : Nat := 4983230072969 + 3 ^ 40 * 2510904 * 2
def baseEnd_2510904 : Nat := 1289300629296949310252569

theorem tailTrace_2510904 : CollatzResearch.WordTrace tailWord_2510904 prefixEnd_2510904 1289300629296949310252569 := by
  unfold tailWord_2510904
  simp only [CollatzResearch.WordTrace]
  refine ⟨45790096247715555553773883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61053461663620740738365177 45790096247715555553773883)
  ·
    refine ⟨68685144371573333330660825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45790096247715555553773883 68685144371573333330660825)
    ·
      refine ⟨51513858278679999997995619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68685144371573333330660825 51513858278679999997995619)
      ·
        refine ⟨77270787418019999996993429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51513858278679999997995619 77270787418019999996993429)
        ·
          refine ⟨3622068160219687499859067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 77270787418019999996993429 3622068160219687499859067)
          ·
            refine ⟨5433102240329531249788601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622068160219687499859067 5433102240329531249788601)
            ·
              refine ⟨4074826680247148437341451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5433102240329531249788601 4074826680247148437341451)
              ·
                refine ⟨6112240020370722656012177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074826680247148437341451 6112240020370722656012177)
                ·
                  refine ⟨4584180015278041992009133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6112240020370722656012177 4584180015278041992009133)
                  ·
                    refine ⟨1719067505729265747003425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4584180015278041992009133 1719067505729265747003425)
                    ·
                      refine ⟨1289300629296949310252569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719067505729265747003425 1289300629296949310252569)
                      ·
                        rfl

theorem cell23_2510904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 2, 3, 2].length) (baseStart_2510904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510904 prefixEnd_2510904 := by exact prefixLift 2510904
  have htrace : WordTrace (prefixWord ++ tailWord_2510904) baseStart_2510904 baseEnd_2510904 := by
    simpa [prefixWord, tailWord_2510904, baseEnd_2510904] using wordTrace_append hprefix tailTrace_2510904
  have hstable : (prefixWord ++ tailWord_2510904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510904).length < 2 ^ (prefixWord ++ tailWord_2510904).sum := by decide
  have hdescent : baseEnd_2510904 < baseStart_2510904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510934 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4]
def baseStart_2510934 : Nat := 118140960795 + 2510934 * 2 ^ 59
def prefixEnd_2510934 : Nat := 4983230072969 + 3 ^ 40 * 2510934 * 2
def baseEnd_2510934 : Nat := 1289316033716584192877431

theorem tailTrace_2510934 : CollatzResearch.WordTrace tailWord_2510934 prefixEnd_2510934 1289316033716584192877431 := by
  unfold tailWord_2510934
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723830417832651639446241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61054191123548284154093237 5723830417832651639446241)
  ·
    refine ⟨4292872813374488729584681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5723830417832651639446241 4292872813374488729584681)
    ·
      refine ⟨3219654610030866547188511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4292872813374488729584681 3219654610030866547188511)
      ·
        refine ⟨4829481915046299820782767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219654610030866547188511 4829481915046299820782767)
        ·
          refine ⟨7244222872569449731174151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829481915046299820782767 7244222872569449731174151)
          ·
            refine ⟨10866334308854174596761227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7244222872569449731174151 10866334308854174596761227)
            ·
              refine ⟨16299501463281261895141841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10866334308854174596761227 16299501463281261895141841)
              ·
                refine ⟨12224626097460946421356381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16299501463281261895141841 12224626097460946421356381)
                ·
                  refine ⟨4584234786547854908008643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12224626097460946421356381 4584234786547854908008643)
                  ·
                    refine ⟨6876352179821782362012965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4584234786547854908008643 6876352179821782362012965)
                    ·
                      refine ⟨1289316033716584192877431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6876352179821782362012965 1289316033716584192877431)
                      ·
                        rfl

theorem cell23_2510934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_2510934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510934 prefixEnd_2510934 := by exact prefixLift 2510934
  have htrace : WordTrace (prefixWord ++ tailWord_2510934) baseStart_2510934 baseEnd_2510934 := by
    simpa [prefixWord, tailWord_2510934, baseEnd_2510934] using wordTrace_append hprefix tailTrace_2510934
  have hstable : (prefixWord ++ tailWord_2510934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510934).length < 2 ^ (prefixWord ++ tailWord_2510934).sum := by decide
  have hdescent : baseEnd_2510934 < baseStart_2510934 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510940 : List Nat := [2, 2, 4, 1, 1, 2, 3, 8]
def baseStart_2510940 : Nat := 118140960795 + 2510940 * 2 ^ 59
def prefixEnd_2510940 : Nat := 4983230072969 + 3 ^ 40 * 2510940 * 2
def baseEnd_2510940 : Nat := 47752559800018932200089

theorem tailTrace_2510940 : CollatzResearch.WordTrace tailWord_2510940 prefixEnd_2510940 47752559800018932200089 := by
  unfold tailWord_2510940
  simp only [CollatzResearch.WordTrace]
  refine ⟨45790752761650344627929137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61054337015533792837238849 45790752761650344627929137)
  ·
    refine ⟨34343064571237758470946853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45790752761650344627929137 34343064571237758470946853)
    ·
      refine ⟨6439324607107079713302535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34343064571237758470946853 6439324607107079713302535)
      ·
        refine ⟨9658986910660619569953803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6439324607107079713302535 9658986910660619569953803)
        ·
          refine ⟨14488480365990929354930705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9658986910660619569953803 14488480365990929354930705)
          ·
            refine ⟨10866360274493197016198029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14488480365990929354930705 10866360274493197016198029)
            ·
              refine ⟨4074885102934948881074261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10866360274493197016198029 4074885102934948881074261)
              ·
                refine ⟨47752559800018932200089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4074885102934948881074261 47752559800018932200089)
                ·
                  rfl

theorem cell23_2510940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 8].length) (baseStart_2510940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510940 prefixEnd_2510940 := by exact prefixLift 2510940
  have htrace : WordTrace (prefixWord ++ tailWord_2510940) baseStart_2510940 baseEnd_2510940 := by
    simpa [prefixWord, tailWord_2510940, baseEnd_2510940] using wordTrace_append hprefix tailTrace_2510940
  have hstable : (prefixWord ++ tailWord_2510940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510940).length < 2 ^ (prefixWord ++ tailWord_2510940).sum := by decide
  have hdescent : baseEnd_2510940 < baseStart_2510940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510953 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 2, 7]
def baseStart_2510953 : Nat := 118140960795 + 2510953 * 2 ^ 59
def prefixEnd_2510953 : Nat := 4983230072969 + 3 ^ 40 * 2510953 * 2
def baseEnd_2510953 : Nat := 429775263283006539513281

theorem tailTrace_2510953 : CollatzResearch.WordTrace tailWord_2510953 prefixEnd_2510953 429775263283006539513281 := by
  unfold tailWord_2510953
  simp only [CollatzResearch.WordTrace]
  refine ⟨91581979672253592476081513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61054653114835728317387675 91581979672253592476081513)
  ·
    refine ⟨68686484754190194357061135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91581979672253592476081513 68686484754190194357061135)
    ·
      refine ⟨103029727131285291535591703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68686484754190194357061135 103029727131285291535591703)
      ·
        refine ⟨154544590696927937303387555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103029727131285291535591703 154544590696927937303387555)
        ·
          refine ⟨231816886045391905955081333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154544590696927937303387555 231816886045391905955081333)
          ·
            refine ⟨21732833066755491183288875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231816886045391905955081333 21732833066755491183288875)
            ·
              refine ⟨32599249600133236774933313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21732833066755491183288875 32599249600133236774933313)
              ·
                refine ⟨24449437200099927581199985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32599249600133236774933313 24449437200099927581199985)
                ·
                  refine ⟨18337077900074945685899989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24449437200099927581199985 18337077900074945685899989)
                  ·
                    refine ⟨429775263283006539513281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18337077900074945685899989 429775263283006539513281)
                    ·
                      rfl

theorem cell23_2510953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 7].length) (baseStart_2510953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510953 prefixEnd_2510953 := by exact prefixLift 2510953
  have htrace : WordTrace (prefixWord ++ tailWord_2510953) baseStart_2510953 baseEnd_2510953 := by
    simpa [prefixWord, tailWord_2510953, baseEnd_2510953] using wordTrace_append hprefix tailTrace_2510953
  have hstable : (prefixWord ++ tailWord_2510953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510953).length < 2 ^ (prefixWord ++ tailWord_2510953).sum := by decide
  have hdescent : baseEnd_2510953 < baseStart_2510953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510984 : List Nat := [2, 1, 3, 4, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2510984 : Nat := 118140960795 + 2510984 * 2 ^ 59
def prefixEnd_2510984 : Nat := 4983230072969 + 3 ^ 40 * 2510984 * 2
def baseEnd_2510984 : Nat := 1289341707749308997252201

theorem tailTrace_2510984 : CollatzResearch.WordTrace tailWord_2510984 prefixEnd_2510984 1289341707749308997252201 := by
  unfold tailWord_2510984
  simp only [CollatzResearch.WordTrace]
  refine ⟨45791555167570642385230003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61055406890094189846973337 45791555167570642385230003)
  ·
    refine ⟨68687332751355963577845005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45791555167570642385230003 68687332751355963577845005)
    ·
      refine ⟨25757749781758486341691877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68687332751355963577845005 25757749781758486341691877)
      ·
        refine ⟨4829578084079716189067227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25757749781758486341691877 4829578084079716189067227)
        ·
          refine ⟨7244367126119574283600841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829578084079716189067227 7244367126119574283600841)
          ·
            refine ⟨5433275344589680712700631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7244367126119574283600841 5433275344589680712700631)
            ·
              refine ⟨8149913016884521069050947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433275344589680712700631 8149913016884521069050947)
              ·
                refine ⟨12224869525326781603576421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8149913016884521069050947 12224869525326781603576421)
                ·
                  refine ⟨2292163035998771550670579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12224869525326781603576421 2292163035998771550670579)
                  ·
                    refine ⟨3438244553998157326005869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2292163035998771550670579 3438244553998157326005869)
                    ·
                      refine ⟨1289341707749308997252201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3438244553998157326005869 1289341707749308997252201)
                      ·
                        rfl

theorem cell23_2510984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2510984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510984 prefixEnd_2510984 := by exact prefixLift 2510984
  have htrace : WordTrace (prefixWord ++ tailWord_2510984) baseStart_2510984 baseEnd_2510984 := by
    simpa [prefixWord, tailWord_2510984, baseEnd_2510984] using wordTrace_append hprefix tailTrace_2510984
  have hstable : (prefixWord ++ tailWord_2510984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510984).length < 2 ^ (prefixWord ++ tailWord_2510984).sum := by decide
  have hdescent : baseEnd_2510984 < baseStart_2510984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2510998 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 1, 1, 6]
def baseStart_2510998 : Nat := 118140960795 + 2510998 * 2 ^ 59
def prefixEnd_2510998 : Nat := 4983230072969 + 3 ^ 40 * 2510998 * 2
def baseEnd_2510998 : Nat := 1289348896478471942477137

theorem tailTrace_2510998 : CollatzResearch.WordTrace tailWord_2510998 prefixEnd_2510998 1289348896478471942477137 := by
  unfold tailWord_2510998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723976309818160322591853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61055747304727043440979765 5723976309818160322591853)
  ·
    refine ⟨2146491116181810120971945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5723976309818160322591853 2146491116181810120971945)
    ·
      refine ⟨1609868337136357590728959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2146491116181810120971945 1609868337136357590728959)
      ·
        refine ⟨2414802505704536386093439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1609868337136357590728959 2414802505704536386093439)
        ·
          refine ⟨3622203758556804579140159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2414802505704536386093439 3622203758556804579140159)
          ·
            refine ⟨5433305637835206868710239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622203758556804579140159 5433305637835206868710239)
            ·
              refine ⟨8149958456752810303065359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433305637835206868710239 8149958456752810303065359)
              ·
                refine ⟨12224937685129215454598039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8149958456752810303065359 12224937685129215454598039)
                ·
                  refine ⟨18337406527693823181897059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12224937685129215454598039 18337406527693823181897059)
                  ·
                    refine ⟨27506109791540734772845589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18337406527693823181897059 27506109791540734772845589)
                    ·
                      refine ⟨1289348896478471942477137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27506109791540734772845589 1289348896478471942477137)
                      ·
                        rfl

theorem cell23_2510998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_2510998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2510998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2510998 prefixEnd_2510998 := by exact prefixLift 2510998
  have htrace : WordTrace (prefixWord ++ tailWord_2510998) baseStart_2510998 baseEnd_2510998 := by
    simpa [prefixWord, tailWord_2510998, baseEnd_2510998] using wordTrace_append hprefix tailTrace_2510998
  have hstable : (prefixWord ++ tailWord_2510998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2510998).length < 2 ^ (prefixWord ++ tailWord_2510998).sum := by decide
  have hdescent : baseEnd_2510998 < baseStart_2510998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2510998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511003 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 6]
def baseStart_2511003 : Nat := 118140960795 + 2511003 * 2 ^ 59
def prefixEnd_2511003 : Nat := 4983230072969 + 3 ^ 40 * 2511003 * 2
def baseEnd_2511003 : Nat := 1289351463881744422914613

theorem tailTrace_2511003 : CollatzResearch.WordTrace tailWord_2511003 prefixEnd_2511003 1289351463881744422914613 := by
  unfold tailWord_2511003
  simp only [CollatzResearch.WordTrace]
  refine ⟨91583803322072451015401663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61055868881381634010267775 91583803322072451015401663)
  ·
    refine ⟨137375704983108676523102495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91583803322072451015401663 137375704983108676523102495)
    ·
      refine ⟨206063557474663014784653743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137375704983108676523102495 206063557474663014784653743)
      ·
        refine ⟨309095336211994522176980615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206063557474663014784653743 309095336211994522176980615)
        ·
          refine ⟨463643004317991783265470923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309095336211994522176980615 463643004317991783265470923)
          ·
            refine ⟨695464506476987674898206385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463643004317991783265470923 695464506476987674898206385)
            ·
              refine ⟨521598379857740756173654789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695464506476987674898206385 521598379857740756173654789)
              ·
                refine ⟨97799696223326391782560273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 521598379857740756173654789 97799696223326391782560273)
                ·
                  refine ⟨73349772167494793836920205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97799696223326391782560273 73349772167494793836920205)
                  ·
                    refine ⟨27506164562810547688845077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 73349772167494793836920205 27506164562810547688845077)
                    ·
                      refine ⟨1289351463881744422914613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27506164562810547688845077 1289351463881744422914613)
                      ·
                        rfl

theorem cell23_2511003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_2511003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511003 prefixEnd_2511003 := by exact prefixLift 2511003
  have htrace : WordTrace (prefixWord ++ tailWord_2511003) baseStart_2511003 baseEnd_2511003 := by
    simpa [prefixWord, tailWord_2511003, baseEnd_2511003] using wordTrace_append hprefix tailTrace_2511003
  have hstable : (prefixWord ++ tailWord_2511003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511003).length < 2 ^ (prefixWord ++ tailWord_2511003).sum := by decide
  have hdescent : baseEnd_2511003 < baseStart_2511003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511058 : List Nat := [3, 2, 2, 2, 1, 2, 4, 1, 2, 2, 2]
def baseStart_2511058 : Nat := 118140960795 + 2511058 * 2 ^ 59
def prefixEnd_2511058 : Nat := 4983230072969 + 3 ^ 40 * 2511058 * 2
def baseEnd_2511058 : Nat := 1289379705317741707726861

theorem tailTrace_2511058 : CollatzResearch.WordTrace tailWord_2511058 prefixEnd_2511058 1289379705317741707726861 := by
  unfold tailWord_2511058
  simp only [CollatzResearch.WordTrace]
  refine ⟨22896452334218298852163457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61057206224582130272435885 22896452334218298852163457)
  ·
    refine ⟨17172339250663724139122593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22896452334218298852163457 17172339250663724139122593)
    ·
      refine ⟨12879254437997793104341945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17172339250663724139122593 12879254437997793104341945)
      ·
        refine ⟨9659440828498344828256459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12879254437997793104341945 9659440828498344828256459)
        ·
          refine ⟨14489161242747517242384689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9659440828498344828256459 14489161242747517242384689)
          ·
            refine ⟨10866870932060637931788517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14489161242747517242384689 10866870932060637931788517)
            ·
              refine ⟨2037538299761369612210347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10866870932060637931788517 2037538299761369612210347)
              ·
                refine ⟨3056307449642054418315521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037538299761369612210347 3056307449642054418315521)
                ·
                  refine ⟨2292230587231540813736641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3056307449642054418315521 2292230587231540813736641)
                  ·
                    refine ⟨1719172940423655610302481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2292230587231540813736641 1719172940423655610302481)
                    ·
                      refine ⟨1289379705317741707726861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719172940423655610302481 1289379705317741707726861)
                      ·
                        rfl

theorem cell23_2511058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 1, 2, 2, 2].length) (baseStart_2511058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511058 prefixEnd_2511058 := by exact prefixLift 2511058
  have htrace : WordTrace (prefixWord ++ tailWord_2511058) baseStart_2511058 baseEnd_2511058 := by
    simpa [prefixWord, tailWord_2511058, baseEnd_2511058] using wordTrace_append hprefix tailTrace_2511058
  have hstable : (prefixWord ++ tailWord_2511058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511058).length < 2 ^ (prefixWord ++ tailWord_2511058).sum := by decide
  have hdescent : baseEnd_2511058 < baseStart_2511058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511077 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 2, 5]
def baseStart_2511077 : Nat := 118140960795 + 2511077 * 2 ^ 59
def prefixEnd_2511077 : Nat := 4983230072969 + 3 ^ 40 * 2511077 * 2
def baseEnd_2511077 : Nat := 429796487150059044463091

theorem tailTrace_2511077 : CollatzResearch.WordTrace tailWord_2511077 prefixEnd_2511077 429796487150059044463091 := by
  unfold tailWord_2511077
  simp only [CollatzResearch.WordTrace]
  refine ⟨91586502323804361653595485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61057668215869574435730323 91586502323804361653595485)
  ·
    refine ⟨34344938371426635620098307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91586502323804361653595485 34344938371426635620098307)
    ·
      refine ⟨51517407557139953430147461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34344938371426635620098307 51517407557139953430147461)
      ·
        refine ⟨9659513916963741268152649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51517407557139953430147461 9659513916963741268152649)
        ·
          refine ⟨7244635437722805951114487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9659513916963741268152649 7244635437722805951114487)
          ·
            refine ⟨10866953156584208926671731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7244635437722805951114487 10866953156584208926671731)
            ·
              refine ⟨16300429734876313390007597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10866953156584208926671731 16300429734876313390007597)
              ·
                refine ⟨6112661150578617521252849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16300429734876313390007597 6112661150578617521252849)
                ·
                  refine ⟨4584495862933963140939637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6112661150578617521252849 4584495862933963140939637)
                  ·
                    refine ⟨429796487150059044463091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4584495862933963140939637 429796487150059044463091)
                    ·
                      rfl

theorem cell23_2511077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 5].length) (baseStart_2511077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511077 prefixEnd_2511077 := by exact prefixLift 2511077
  have htrace : WordTrace (prefixWord ++ tailWord_2511077) baseStart_2511077 baseEnd_2511077 := by
    simpa [prefixWord, tailWord_2511077, baseEnd_2511077] using wordTrace_append hprefix tailTrace_2511077
  have hstable : (prefixWord ++ tailWord_2511077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511077).length < 2 ^ (prefixWord ++ tailWord_2511077).sum := by decide
  have hdescent : baseEnd_2511077 < baseStart_2511077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511107 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 3, 4]
def baseStart_2511107 : Nat := 118140960795 + 2511107 * 2 ^ 59
def prefixEnd_2511107 : Nat := 4983230072969 + 3 ^ 40 * 2511107 * 2
def baseEnd_2511107 : Nat := 429801621956604005338045

theorem tailTrace_2511107 : CollatzResearch.WordTrace tailWord_2511107 prefixEnd_2511107 429801621956604005338045 := by
  unfold tailWord_2511107
  simp only [CollatzResearch.WordTrace]
  refine ⟨91587596513695676777187575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61058397675797117851458383 91587596513695676777187575)
  ·
    refine ⟨137381394770543515165781363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91587596513695676777187575 137381394770543515165781363)
    ·
      refine ⟨206072092155815272748672045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137381394770543515165781363 206072092155815272748672045)
      ·
        refine ⟨77277034558430727280752017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206072092155815272748672045 77277034558430727280752017)
        ·
          refine ⟨57957775918823045460564013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77277034558430727280752017 57957775918823045460564013)
          ·
            refine ⟨21734165969558642047711505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57957775918823045460564013 21734165969558642047711505)
            ·
              refine ⟨16300624477168981535783629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21734165969558642047711505 16300624477168981535783629)
              ·
                refine ⟨6112734178938368075918861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16300624477168981535783629 6112734178938368075918861)
                ·
                  refine ⟨2292275317101888028469573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6112734178938368075918861 2292275317101888028469573)
                  ·
                    refine ⟨429801621956604005338045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2292275317101888028469573 429801621956604005338045)
                    ·
                      rfl

theorem cell23_2511107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 4].length) (baseStart_2511107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511107 prefixEnd_2511107 := by exact prefixLift 2511107
  have htrace : WordTrace (prefixWord ++ tailWord_2511107) baseStart_2511107 baseEnd_2511107 := by
    simpa [prefixWord, tailWord_2511107, baseEnd_2511107] using wordTrace_append hprefix tailTrace_2511107
  have hstable : (prefixWord ++ tailWord_2511107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511107).length < 2 ^ (prefixWord ++ tailWord_2511107).sum := by decide
  have hdescent : baseEnd_2511107 < baseStart_2511107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511184 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 1, 5]
def baseStart_2511184 : Nat := 118140960795 + 2511184 * 2 ^ 59
def prefixEnd_2511184 : Nat := 4983230072969 + 3 ^ 40 * 2511184 * 2
def baseEnd_2511184 : Nat := 429814801293402738250427

theorem tailTrace_2511184 : CollatzResearch.WordTrace tailWord_2511184 prefixEnd_2511184 429814801293402738250427 := by
  unfold tailWord_2511184
  simp only [CollatzResearch.WordTrace]
  refine ⟨45795202467208359463870303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61060269956277812618493737 45795202467208359463870303)
  ·
    refine ⟨68692803700812539195805455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45795202467208359463870303 68692803700812539195805455)
    ·
      refine ⟨103039205551218808793708183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68692803700812539195805455 103039205551218808793708183)
      ·
        refine ⟨154558808326828213190562275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103039205551218808793708183 154558808326828213190562275)
        ·
          refine ⟨231838212490242319785843413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154558808326828213190562275 231838212490242319785843413)
          ·
            refine ⟨5433708105240054369980705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 231838212490242319785843413 5433708105240054369980705)
            ·
              refine ⟨4075281078930040777485529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5433708105240054369980705 4075281078930040777485529)
              ·
                refine ⟨3056460809197530583114147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4075281078930040777485529 3056460809197530583114147)
                ·
                  refine ⟨4584691213796295874671221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056460809197530583114147 4584691213796295874671221)
                  ·
                    refine ⟨429814801293402738250427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4584691213796295874671221 429814801293402738250427)
                    ·
                      rfl

theorem cell23_2511184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 5].length) (baseStart_2511184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511184 prefixEnd_2511184 := by exact prefixLift 2511184
  have htrace : WordTrace (prefixWord ++ tailWord_2511184) baseStart_2511184 baseEnd_2511184 := by
    simpa [prefixWord, tailWord_2511184, baseEnd_2511184] using wordTrace_append hprefix tailTrace_2511184
  have hstable : (prefixWord ++ tailWord_2511184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511184).length < 2 ^ (prefixWord ++ tailWord_2511184).sum := by decide
  have hdescent : baseEnd_2511184 < baseStart_2511184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511204 : List Nat := [2, 3, 1, 1, 3, 1, 1, 5, 1, 1, 4]
def baseStart_2511204 : Nat := 118140960795 + 2511204 * 2 ^ 59
def prefixEnd_2511204 : Nat := 4983230072969 + 3 ^ 40 * 2511204 * 2
def baseEnd_2511204 : Nat := 1289454673493298136501189

theorem tailTrace_2511204 : CollatzResearch.WordTrace tailWord_2511204 prefixEnd_2511204 1289454673493298136501189 := by
  unfold tailWord_2511204
  simp only [CollatzResearch.WordTrace]
  refine ⟨45795567197172131171734333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61060756262896174895645777 45795567197172131171734333)
  ·
    refine ⟨17173337698939549189400375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45795567197172131171734333 17173337698939549189400375)
    ·
      refine ⟨25760006548409323784100563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17173337698939549189400375 25760006548409323784100563)
      ·
        refine ⟨38640009822613985676150845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25760006548409323784100563 38640009822613985676150845)
        ·
          refine ⟨14490003683480244628556567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38640009822613985676150845 14490003683480244628556567)
          ·
            refine ⟨21735005525220366942834851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14490003683480244628556567 21735005525220366942834851)
            ·
              refine ⟨32602508287830550414252277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21735005525220366942834851 32602508287830550414252277)
              ·
                refine ⟨3056485151984114101336151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32602508287830550414252277 3056485151984114101336151)
                ·
                  refine ⟨4584727727976171152004227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056485151984114101336151 4584727727976171152004227)
                  ·
                    refine ⟨6877091591964256728006341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4584727727976171152004227 6877091591964256728006341)
                    ·
                      refine ⟨1289454673493298136501189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6877091591964256728006341 1289454673493298136501189)
                      ·
                        rfl

theorem cell23_2511204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_2511204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511204 prefixEnd_2511204 := by exact prefixLift 2511204
  have htrace : WordTrace (prefixWord ++ tailWord_2511204) baseStart_2511204 baseEnd_2511204 := by
    simpa [prefixWord, tailWord_2511204, baseEnd_2511204] using wordTrace_append hprefix tailTrace_2511204
  have hstable : (prefixWord ++ tailWord_2511204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511204).length < 2 ^ (prefixWord ++ tailWord_2511204).sum := by decide
  have hdescent : baseEnd_2511204 < baseStart_2511204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511227 : List Nat := [1, 1, 1, 1, 1, 8, 2, 8]
def baseStart_2511227 : Nat := 118140960795 + 2511227 * 2 ^ 59
def prefixEnd_2511227 : Nat := 4983230072969 + 3 ^ 40 * 2511227 * 2
def baseEnd_2511227 : Nat := 47758017909198205426429

theorem tailTrace_2511227 : CollatzResearch.WordTrace tailWord_2511227 prefixEnd_2511227 47758017909198205426429 := by
  unfold tailWord_2511227
  simp only [CollatzResearch.WordTrace]
  refine ⟨91591973273260937271555935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61061315515507291514370623 91591973273260937271555935)
  ·
    refine ⟨137387959909891405907333903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91591973273260937271555935 137387959909891405907333903)
    ·
      refine ⟨206081939864837108861000855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137387959909891405907333903 206081939864837108861000855)
      ·
        refine ⟨309122909797255663291501283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206081939864837108861000855 309122909797255663291501283)
        ·
          refine ⟨463684364695883494937251925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309122909797255663291501283 463684364695883494937251925)
          ·
            refine ⟨5433801148779884706295921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 463684364695883494937251925 5433801148779884706295921)
            ·
              refine ⟨4075350861584913529721941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5433801148779884706295921 4075350861584913529721941)
              ·
                refine ⟨47758017909198205426429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4075350861584913529721941 47758017909198205426429)
                ·
                  rfl

theorem cell23_2511227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 8].length) (baseStart_2511227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511227 prefixEnd_2511227 := by exact prefixLift 2511227
  have htrace : WordTrace (prefixWord ++ tailWord_2511227) baseStart_2511227 baseEnd_2511227 := by
    simpa [prefixWord, tailWord_2511227, baseEnd_2511227] using wordTrace_append hprefix tailTrace_2511227
  have hstable : (prefixWord ++ tailWord_2511227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511227).length < 2 ^ (prefixWord ++ tailWord_2511227).sum := by decide
  have hdescent : baseEnd_2511227 < baseStart_2511227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511241 : List Nat := [1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 3]
def baseStart_2511241 : Nat := 118140960795 + 2511241 * 2 ^ 59
def prefixEnd_2511241 : Nat := 4983230072969 + 3 ^ 40 * 2511241 * 2
def baseEnd_2511241 : Nat := 1289473672277514491738519

theorem tailTrace_2511241 : CollatzResearch.WordTrace tailWord_2511241 prefixEnd_2511241 1289473672277514491738519 := by
  unfold tailWord_2511241
  simp only [CollatzResearch.WordTrace]
  refine ⟨91592483895210217662565577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61061655930140145108377051 91592483895210217662565577)
  ·
    refine ⟨68694362921407663246924183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91592483895210217662565577 68694362921407663246924183)
    ·
      refine ⟨103041544382111494870386275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68694362921407663246924183 103041544382111494870386275)
      ·
        refine ⟨154562316573167242305579413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103041544382111494870386275 154562316573167242305579413)
        ·
          refine ⟨7245108589367214483074035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 154562316573167242305579413 7245108589367214483074035)
          ·
            refine ⟨10867662884050821724611053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7245108589367214483074035 10867662884050821724611053)
            ·
              refine ⟨4075373581519058146729145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10867662884050821724611053 4075373581519058146729145)
              ·
                refine ⟨3056530186139293610046859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4075373581519058146729145 3056530186139293610046859)
                ·
                  refine ⟨4584795279208940415070289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056530186139293610046859 4584795279208940415070289)
                  ·
                    refine ⟨3438596459406705311302717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4584795279208940415070289 3438596459406705311302717)
                    ·
                      refine ⟨1289473672277514491738519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3438596459406705311302717 1289473672277514491738519)
                      ·
                        rfl

theorem cell23_2511241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 3].length) (baseStart_2511241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511241 prefixEnd_2511241 := by exact prefixLift 2511241
  have htrace : WordTrace (prefixWord ++ tailWord_2511241) baseStart_2511241 baseEnd_2511241 := by
    simpa [prefixWord, tailWord_2511241, baseEnd_2511241] using wordTrace_append hprefix tailTrace_2511241
  have hstable : (prefixWord ++ tailWord_2511241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511241).length < 2 ^ (prefixWord ++ tailWord_2511241).sum := by decide
  have hdescent : baseEnd_2511241 < baseStart_2511241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511258 : List Nat := [3, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3]
def baseStart_2511258 : Nat := 118140960795 + 2511258 * 2 ^ 59
def prefixEnd_2511258 : Nat := 4983230072969 + 3 ^ 40 * 2511258 * 2
def baseEnd_2511258 : Nat := 1289482401448640925225941

theorem tailTrace_2511258 : CollatzResearch.WordTrace tailWord_2511258 prefixEnd_2511258 1289482401448640925225941 := by
  unfold tailWord_2511258
  simp only [CollatzResearch.WordTrace]
  refine ⟨22898275984037157391483607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61062069290765753043956285 22898275984037157391483607)
  ·
    refine ⟨34347413976055736087225411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22898275984037157391483607 34347413976055736087225411)
    ·
      refine ⟨51521120964083604130838117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34347413976055736087225411 51521120964083604130838117)
      ·
        refine ⟨9660210180765675774532147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51521120964083604130838117 9660210180765675774532147)
        ·
          refine ⟨14490315271148513661798221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9660210180765675774532147 14490315271148513661798221)
          ·
            refine ⟨5433868226680692623174333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14490315271148513661798221 5433868226680692623174333)
            ·
              refine ⟨2037700585005259733690375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5433868226680692623174333 2037700585005259733690375)
              ·
                refine ⟨3056550877507889600535563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037700585005259733690375 3056550877507889600535563)
                ·
                  refine ⟨4584826316261834400803345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056550877507889600535563 4584826316261834400803345)
                  ·
                    refine ⟨3438619737196375800602509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4584826316261834400803345 3438619737196375800602509)
                    ·
                      refine ⟨1289482401448640925225941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3438619737196375800602509 1289482401448640925225941)
                      ·
                        rfl

theorem cell23_2511258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 3, 1, 1, 2, 3].length) (baseStart_2511258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511258 prefixEnd_2511258 := by exact prefixLift 2511258
  have htrace : WordTrace (prefixWord ++ tailWord_2511258) baseStart_2511258 baseEnd_2511258 := by
    simpa [prefixWord, tailWord_2511258, baseEnd_2511258] using wordTrace_append hprefix tailTrace_2511258
  have hstable : (prefixWord ++ tailWord_2511258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511258).length < 2 ^ (prefixWord ++ tailWord_2511258).sum := by decide
  have hdescent : baseEnd_2511258 < baseStart_2511258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511272 : List Nat := [2, 1, 6, 1, 1, 2, 1, 4, 1, 2, 2]
def baseStart_2511272 : Nat := 118140960795 + 2511272 * 2 ^ 59
def prefixEnd_2511272 : Nat := 4983230072969 + 3 ^ 40 * 2511272 * 2
def baseEnd_2511272 : Nat := 1289489590177803870450877

theorem tailTrace_2511272 : CollatzResearch.WordTrace tailWord_2511272 prefixEnd_2511272 1289489590177803870450877 := by
  unfold tailWord_2511272
  simp only [CollatzResearch.WordTrace]
  refine ⟨45796807279048954978472035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61062409705398606637962713 45796807279048954978472035)
  ·
    refine ⟨68695210918573432467708053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45796807279048954978472035 68695210918573432467708053)
    ·
      refine ⟨3220088011808129646923815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68695210918573432467708053 3220088011808129646923815)
      ·
        refine ⟨4830132017712194470385723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3220088011808129646923815 4830132017712194470385723)
        ·
          refine ⟨7245198026568291705578585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4830132017712194470385723 7245198026568291705578585)
          ·
            refine ⟨5433898519926218779183939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7245198026568291705578585 5433898519926218779183939)
            ·
              refine ⟨8150847779889328168775909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433898519926218779183939 8150847779889328168775909)
              ·
                refine ⟨1528283958729249031645483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8150847779889328168775909 1528283958729249031645483)
                ·
                  refine ⟨2292425938093873547468225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528283958729249031645483 2292425938093873547468225)
                  ·
                    refine ⟨1719319453570405160601169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2292425938093873547468225 1719319453570405160601169)
                    ·
                      refine ⟨1289489590177803870450877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719319453570405160601169 1289489590177803870450877)
                      ·
                        rfl

theorem cell23_2511272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_2511272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511272 prefixEnd_2511272 := by exact prefixLift 2511272
  have htrace : WordTrace (prefixWord ++ tailWord_2511272) baseStart_2511272 baseEnd_2511272 := by
    simpa [prefixWord, tailWord_2511272, baseEnd_2511272] using wordTrace_append hprefix tailTrace_2511272
  have hstable : (prefixWord ++ tailWord_2511272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511272).length < 2 ^ (prefixWord ++ tailWord_2511272).sum := by decide
  have hdescent : baseEnd_2511272 < baseStart_2511272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511281 : List Nat := [1, 2, 2, 4, 1, 2, 1, 2, 3, 3, 2]
def baseStart_2511281 : Nat := 118140960795 + 2511281 * 2 ^ 59
def prefixEnd_2511281 : Nat := 4983230072969 + 3 ^ 40 * 2511281 * 2
def baseEnd_2511281 : Nat := 1289494211503694335238335

theorem tailTrace_2511281 : CollatzResearch.WordTrace tailWord_2511281 prefixEnd_2511281 1289494211503694335238335 := by
  unfold tailWord_2511281
  simp only [CollatzResearch.WordTrace]
  refine ⟨91593942815065304494021697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61062628543376869662681131 91593942815065304494021697)
  ·
    refine ⟨68695457111298978370516273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91593942815065304494021697 68695457111298978370516273)
    ·
      refine ⟨51521592833474233777887205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68695457111298978370516273 51521592833474233777887205)
      ·
        refine ⟨9660298656276418833353851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51521592833474233777887205 9660298656276418833353851)
        ·
          refine ⟨14490447984414628250030777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9660298656276418833353851 14490447984414628250030777)
          ·
            refine ⟨10867835988310971187523083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14490447984414628250030777 10867835988310971187523083)
            ·
              refine ⟨16301753982466456781284625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10867835988310971187523083 16301753982466456781284625)
              ·
                refine ⟨12226315486849842585963469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16301753982466456781284625 12226315486849842585963469)
                ·
                  refine ⟨4584868307568690969736301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12226315486849842585963469 4584868307568690969736301)
                  ·
                    refine ⟨1719325615338259113651113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4584868307568690969736301 1719325615338259113651113)
                    ·
                      refine ⟨1289494211503694335238335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719325615338259113651113 1289494211503694335238335)
                      ·
                        rfl

theorem cell23_2511281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_2511281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511281 prefixEnd_2511281 := by exact prefixLift 2511281
  have htrace : WordTrace (prefixWord ++ tailWord_2511281) baseStart_2511281 baseEnd_2511281 := by
    simpa [prefixWord, tailWord_2511281, baseEnd_2511281] using wordTrace_append hprefix tailTrace_2511281
  have hstable : (prefixWord ++ tailWord_2511281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511281).length < 2 ^ (prefixWord ++ tailWord_2511281).sum := by decide
  have hdescent : baseEnd_2511281 < baseStart_2511281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511287 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 1, 8]
def baseStart_2511287 : Nat := 118140960795 + 2511287 * 2 ^ 59
def prefixEnd_2511287 : Nat := 4983230072969 + 3 ^ 40 * 2511287 * 2
def baseEnd_2511287 : Nat := 429832430795873770587769

theorem tailTrace_2511287 : CollatzResearch.WordTrace tailWord_2511287 prefixEnd_2511287 429832430795873770587769 := by
  unfold tailWord_2511287
  simp only [CollatzResearch.WordTrace]
  refine ⟨91594161653043567518740115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61062774435362378345826743 91594161653043567518740115)
  ·
    refine ⟨137391242479565351278110173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91594161653043567518740115 137391242479565351278110173)
    ·
      refine ⟨51521715929837006729291315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137391242479565351278110173 51521715929837006729291315)
      ·
        refine ⟨77282573894755510093936973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51521715929837006729291315 77282573894755510093936973)
        ·
          refine ⟨28980965210533316285226365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77282573894755510093936973 28980965210533316285226365)
          ·
            refine ⟨10867861953949993606959887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28980965210533316285226365 10867861953949993606959887)
            ·
              refine ⟨16301792930924990410439831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10867861953949993606959887 16301792930924990410439831)
              ·
                refine ⟨24452689396387485615659747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16301792930924990410439831 24452689396387485615659747)
                ·
                  refine ⟨36679034094581228423489621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24452689396387485615659747 36679034094581228423489621)
                  ·
                    refine ⟨429832430795873770587769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 36679034094581228423489621 429832430795873770587769)
                    ·
                      rfl

theorem cell23_2511287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 8].length) (baseStart_2511287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511287 prefixEnd_2511287 := by exact prefixLift 2511287
  have htrace : WordTrace (prefixWord ++ tailWord_2511287) baseStart_2511287 baseEnd_2511287 := by
    simpa [prefixWord, tailWord_2511287, baseEnd_2511287] using wordTrace_append hprefix tailTrace_2511287
  have hstable : (prefixWord ++ tailWord_2511287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511287).length < 2 ^ (prefixWord ++ tailWord_2511287).sum := by decide
  have hdescent : baseEnd_2511287 < baseStart_2511287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511307 : List Nat := [1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 4]
def baseStart_2511307 : Nat := 118140960795 + 2511307 * 2 ^ 59
def prefixEnd_2511307 : Nat := 4983230072969 + 3 ^ 40 * 2511307 * 2
def baseEnd_2511307 : Nat := 1289507562000711233513215

theorem tailTrace_2511307 : CollatzResearch.WordTrace tailWord_2511307 prefixEnd_2511307 1289507562000711233513215 := by
  unfold tailWord_2511307
  simp only [CollatzResearch.WordTrace]
  refine ⟨91594891112971110934468175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61063260741980740622978783 91594891112971110934468175)
  ·
    refine ⟨137392336669456666401702263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91594891112971110934468175 137392336669456666401702263)
    ·
      refine ⟨206088505004184999602553395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137392336669456666401702263 206088505004184999602553395)
      ·
        refine ⟨309132757506277499403830093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206088505004184999602553395 309132757506277499403830093)
        ·
          refine ⟨115924784064854062276436285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309132757506277499403830093 115924784064854062276436285)
          ·
            refine ⟨43471794024320273353663607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115924784064854062276436285 43471794024320273353663607)
            ·
              refine ⟨65207691036480410030495411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43471794024320273353663607 65207691036480410030495411)
              ·
                refine ⟨97811536554720615045743117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65207691036480410030495411 97811536554720615045743117)
                ·
                  refine ⟨36679326208020230642153669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97811536554720615045743117 36679326208020230642153669)
                  ·
                    refine ⟨6877373664003793245403813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36679326208020230642153669 6877373664003793245403813)
                    ·
                      refine ⟨1289507562000711233513215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6877373664003793245403813 1289507562000711233513215)
                      ·
                        rfl

theorem cell23_2511307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 4].length) (baseStart_2511307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511307 prefixEnd_2511307 := by exact prefixLift 2511307
  have htrace : WordTrace (prefixWord ++ tailWord_2511307) baseStart_2511307 baseEnd_2511307 := by
    simpa [prefixWord, tailWord_2511307, baseEnd_2511307] using wordTrace_append hprefix tailTrace_2511307
  have hstable : (prefixWord ++ tailWord_2511307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511307).length < 2 ^ (prefixWord ++ tailWord_2511307).sum := by decide
  have hdescent : baseEnd_2511307 < baseStart_2511307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511311 : List Nat := [1, 1, 2, 1, 1, 4, 1, 4, 4, 2, 2]
def baseStart_2511311 : Nat := 118140960795 + 2511311 * 2 ^ 59
def prefixEnd_2511311 : Nat := 4983230072969 + 3 ^ 40 * 2511311 * 2
def baseEnd_2511311 : Nat := 1289509615923329217863197

theorem tailTrace_2511311 : CollatzResearch.WordTrace tailWord_2511311 prefixEnd_2511311 1289509615923329217863197 := by
  unfold tailWord_2511311
  simp only [CollatzResearch.WordTrace]
  refine ⟨91595037004956619617613787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61063358003304413078409191 91595037004956619617613787)
  ·
    refine ⟨137392555507434929426420681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91595037004956619617613787 137392555507434929426420681)
    ·
      refine ⟨103044416630576197069815511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137392555507434929426420681 103044416630576197069815511)
      ·
        refine ⟨154566624945864295604723267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103044416630576197069815511 154566624945864295604723267)
        ·
          refine ⟨231849937418796443407084901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154566624945864295604723267 231849937418796443407084901)
          ·
            refine ⟨43471863266024333138828419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231849937418796443407084901 43471863266024333138828419)
            ·
              refine ⟨65207794899036499708242629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43471863266024333138828419 65207794899036499708242629)
              ·
                refine ⟨12226461543569343695295493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65207794899036499708242629 12226461543569343695295493)
                ·
                  refine ⟨2292461539419251942867905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12226461543569343695295493 2292461539419251942867905)
                  ·
                    refine ⟨1719346154564438957150929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2292461539419251942867905 1719346154564438957150929)
                    ·
                      refine ⟨1289509615923329217863197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719346154564438957150929 1289509615923329217863197)
                      ·
                        rfl

theorem cell23_2511311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 4, 4, 2, 2].length) (baseStart_2511311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511311 prefixEnd_2511311 := by exact prefixLift 2511311
  have htrace : WordTrace (prefixWord ++ tailWord_2511311) baseStart_2511311 baseEnd_2511311 := by
    simpa [prefixWord, tailWord_2511311, baseEnd_2511311] using wordTrace_append hprefix tailTrace_2511311
  have hstable : (prefixWord ++ tailWord_2511311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511311).length < 2 ^ (prefixWord ++ tailWord_2511311).sum := by decide
  have hdescent : baseEnd_2511311 < baseStart_2511311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511341 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2511341 : Nat := 118140960795 + 2511341 * 2 ^ 59
def prefixEnd_2511341 : Nat := 4983230072969 + 3 ^ 40 * 2511341 * 2
def baseEnd_2511341 : Nat := 1289525020342964100488059

theorem tailTrace_2511341 : CollatzResearch.WordTrace tailWord_2511341 prefixEnd_2511341 1289525020342964100488059 := by
  unfold tailWord_2511341
  simp only [CollatzResearch.WordTrace]
  refine ⟨91596131194847934741205877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61064087463231956494137251 91596131194847934741205877)
  ·
    refine ⟨8587137299516993881988051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91596131194847934741205877 8587137299516993881988051)
    ·
      refine ⟨12880705949275490822982077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8587137299516993881988051 12880705949275490822982077)
      ·
        refine ⟨4830264730978309058618279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12880705949275490822982077 4830264730978309058618279)
        ·
          refine ⟨7245397096467463587927419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4830264730978309058618279 7245397096467463587927419)
          ·
            refine ⟨10868095644701195381891129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7245397096467463587927419 10868095644701195381891129)
            ·
              refine ⟨8151071733525896536418347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10868095644701195381891129 8151071733525896536418347)
              ·
                refine ⟨12226607600288844804627521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8151071733525896536418347 12226607600288844804627521)
                ·
                  refine ⟨9169955700216633603470641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12226607600288844804627521 9169955700216633603470641)
                  ·
                    refine ⟨6877466775162475202602981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9169955700216633603470641 6877466775162475202602981)
                    ·
                      refine ⟨1289525020342964100488059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6877466775162475202602981 1289525020342964100488059)
                      ·
                        rfl

theorem cell23_2511341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2511341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511341 prefixEnd_2511341 := by exact prefixLift 2511341
  have htrace : WordTrace (prefixWord ++ tailWord_2511341) baseStart_2511341 baseEnd_2511341 := by
    simpa [prefixWord, tailWord_2511341, baseEnd_2511341] using wordTrace_append hprefix tailTrace_2511341
  have hstable : (prefixWord ++ tailWord_2511341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511341).length < 2 ^ (prefixWord ++ tailWord_2511341).sum := by decide
  have hdescent : baseEnd_2511341 < baseStart_2511341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511344 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 3]
def baseStart_2511344 : Nat := 118140960795 + 2511344 * 2 ^ 59
def prefixEnd_2511344 : Nat := 4983230072969 + 3 ^ 40 * 2511344 * 2
def baseEnd_2511344 : Nat := 1289526560784927588750545

theorem tailTrace_2511344 : CollatzResearch.WordTrace tailWord_2511344 prefixEnd_2511344 1289526560784927588750545 := by
  unfold tailWord_2511344
  simp only [CollatzResearch.WordTrace]
  refine ⟨45798120306918533126782543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61064160409224710835710057 45798120306918533126782543)
  ·
    refine ⟨68697180460377799690173815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45798120306918533126782543 68697180460377799690173815)
    ·
      refine ⟨103045770690566699535260723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68697180460377799690173815 103045770690566699535260723)
      ·
        refine ⟨154568656035850049302891085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103045770690566699535260723 154568656035850049302891085)
        ·
          refine ⟨57963246013443768488584157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154568656035850049302891085 57963246013443768488584157)
          ·
            refine ⟨21736217255041413183219059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57963246013443768488584157 21736217255041413183219059)
            ·
              refine ⟨32604325882562119774828589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21736217255041413183219059 32604325882562119774828589)
              ·
                refine ⟨12226622205960794915560721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32604325882562119774828589 12226622205960794915560721)
                ·
                  refine ⟨9169966654470596186670541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12226622205960794915560721 9169966654470596186670541)
                  ·
                    refine ⟨3438737495426473570001453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9169966654470596186670541 3438737495426473570001453)
                    ·
                      refine ⟨1289526560784927588750545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3438737495426473570001453 1289526560784927588750545)
                      ·
                        rfl

theorem cell23_2511344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 3].length) (baseStart_2511344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511344 prefixEnd_2511344 := by exact prefixLift 2511344
  have htrace : WordTrace (prefixWord ++ tailWord_2511344) baseStart_2511344 baseEnd_2511344 := by
    simpa [prefixWord, tailWord_2511344, baseEnd_2511344] using wordTrace_append hprefix tailTrace_2511344
  have hstable : (prefixWord ++ tailWord_2511344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511344).length < 2 ^ (prefixWord ++ tailWord_2511344).sum := by decide
  have hdescent : baseEnd_2511344 < baseStart_2511344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511345 : List Nat := [1, 2, 2, 2, 3, 1, 5, 1, 2, 2, 2]
def baseStart_2511345 : Nat := 118140960795 + 2511345 * 2 ^ 59
def prefixEnd_2511345 : Nat := 4983230072969 + 3 ^ 40 * 2511345 * 2
def baseEnd_2511345 : Nat := 1289527074265582084838041

theorem tailTrace_2511345 : CollatzResearch.WordTrace tailWord_2511345 prefixEnd_2511345 1289527074265582084838041 := by
  unfold tailWord_2511345
  simp only [CollatzResearch.WordTrace]
  refine ⟨91596277086833443424351489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61064184724555628949567659 91596277086833443424351489)
  ·
    refine ⟨68697207815125082568263617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91596277086833443424351489 68697207815125082568263617)
    ·
      refine ⟨51522905861343811926197713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68697207815125082568263617 51522905861343811926197713)
      ·
        refine ⟨38642179396007858944648285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51522905861343811926197713 38642179396007858944648285)
        ·
          refine ⟨14490817273502947104243107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38642179396007858944648285 14490817273502947104243107)
          ·
            refine ⟨21736225910254420656364661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14490817273502947104243107 21736225910254420656364661)
            ·
              refine ⟨2037771179086351936534187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21736225910254420656364661 2037771179086351936534187)
              ·
                refine ⟨3056656768629527904801281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037771179086351936534187 3056656768629527904801281)
                ·
                  refine ⟨2292492576472145928600961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3056656768629527904801281 2292492576472145928600961)
                  ·
                    refine ⟨1719369432354109446450721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2292492576472145928600961 1719369432354109446450721)
                    ·
                      refine ⟨1289527074265582084838041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719369432354109446450721 1289527074265582084838041)
                      ·
                        rfl

theorem cell23_2511345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 2, 2, 2].length) (baseStart_2511345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511345 prefixEnd_2511345 := by exact prefixLift 2511345
  have htrace : WordTrace (prefixWord ++ tailWord_2511345) baseStart_2511345 baseEnd_2511345 := by
    simpa [prefixWord, tailWord_2511345, baseEnd_2511345] using wordTrace_append hprefix tailTrace_2511345
  have hstable : (prefixWord ++ tailWord_2511345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511345).length < 2 ^ (prefixWord ++ tailWord_2511345).sum := by decide
  have hdescent : baseEnd_2511345 < baseStart_2511345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511347 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 3, 7]
def baseStart_2511347 : Nat := 118140960795 + 2511347 * 2 ^ 59
def prefixEnd_2511347 : Nat := 4983230072969 + 3 ^ 40 * 2511347 * 2
def baseEnd_2511347 : Nat := 429842700408963692337677

theorem tailTrace_2511347 : CollatzResearch.WordTrace tailWord_2511347 prefixEnd_2511347 429842700408963692337677 := by
  unfold tailWord_2511347
  simp only [CollatzResearch.WordTrace]
  refine ⟨91596350032826197765924295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61064233355217465177282863 91596350032826197765924295)
  ·
    refine ⟨137394525049239296648886443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91596350032826197765924295 137394525049239296648886443)
    ·
      refine ⟨206091787573858944973329665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137394525049239296648886443 206091787573858944973329665)
      ·
        refine ⟨154568840680394208729997249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206091787573858944973329665 154568840680394208729997249)
        ·
          refine ⟨115926630510295656547497937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154568840680394208729997249 115926630510295656547497937)
          ·
            refine ⟨86944972882721742410623453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115926630510295656547497937 86944972882721742410623453)
            ·
              refine ⟨32604364831020653403983795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86944972882721742410623453 32604364831020653403983795)
              ·
                refine ⟨48906547246530980105975693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32604364831020653403983795 48906547246530980105975693)
                ·
                  refine ⟨18339955217449117539740885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48906547246530980105975693 18339955217449117539740885)
                  ·
                    refine ⟨429842700408963692337677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18339955217449117539740885 429842700408963692337677)
                    ·
                      rfl

theorem cell23_2511347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 7].length) (baseStart_2511347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511347 prefixEnd_2511347 := by exact prefixLift 2511347
  have htrace : WordTrace (prefixWord ++ tailWord_2511347) baseStart_2511347 baseEnd_2511347 := by
    simpa [prefixWord, tailWord_2511347, baseEnd_2511347] using wordTrace_append hprefix tailTrace_2511347
  have hstable : (prefixWord ++ tailWord_2511347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511347).length < 2 ^ (prefixWord ++ tailWord_2511347).sum := by decide
  have hdescent : baseEnd_2511347 < baseStart_2511347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511396 : List Nat := [2, 3, 1, 5, 2, 1, 2, 1, 2, 2, 2]
def baseStart_2511396 : Nat := 118140960795 + 2511396 * 2 ^ 59
def prefixEnd_2511396 : Nat := 4983230072969 + 3 ^ 40 * 2511396 * 2
def baseEnd_2511396 : Nat := 1289553261778961385300307

theorem tailTrace_2511396 : CollatzResearch.WordTrace tailWord_2511396 prefixEnd_2511396 1289553261778961385300307 := by
  unfold tailWord_2511396
  simp only [CollatzResearch.WordTrace]
  refine ⟨45799068604824339567229021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61065424806432452756305361 45799068604824339567229021)
  ·
    refine ⟨17174650726809127337710883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45799068604824339567229021 17174650726809127337710883)
    ·
      refine ⟨25761976090213691006566325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17174650726809127337710883 25761976090213691006566325)
      ·
        refine ⟨2415185258457533531865593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25761976090213691006566325 2415185258457533531865593)
        ·
          refine ⟨1811388943843150148899195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2415185258457533531865593 1811388943843150148899195)
          ·
            refine ⟨2717083415764725223348793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811388943843150148899195 2717083415764725223348793)
            ·
              refine ⟨2037812561823543917511595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717083415764725223348793 2037812561823543917511595)
              ·
                refine ⟨3056718842735315876267393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037812561823543917511595 3056718842735315876267393)
                ·
                  refine ⟨2292539132051486907200545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3056718842735315876267393 2292539132051486907200545)
                  ·
                    refine ⟨1719404349038615180400409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2292539132051486907200545 1719404349038615180400409)
                    ·
                      refine ⟨1289553261778961385300307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719404349038615180400409 1289553261778961385300307)
                      ·
                        rfl

theorem cell23_2511396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_2511396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511396 prefixEnd_2511396 := by exact prefixLift 2511396
  have htrace : WordTrace (prefixWord ++ tailWord_2511396) baseStart_2511396 baseEnd_2511396 := by
    simpa [prefixWord, tailWord_2511396, baseEnd_2511396] using wordTrace_append hprefix tailTrace_2511396
  have hstable : (prefixWord ++ tailWord_2511396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511396).length < 2 ^ (prefixWord ++ tailWord_2511396).sum := by decide
  have hdescent : baseEnd_2511396 < baseStart_2511396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511404 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 3]
def baseStart_2511404 : Nat := 118140960795 + 2511404 * 2 ^ 59
def prefixEnd_2511404 : Nat := 4983230072969 + 3 ^ 40 * 2511404 * 2
def baseEnd_2511404 : Nat := 1289557369624197354000269

theorem tailTrace_2511404 : CollatzResearch.WordTrace tailWord_2511404 prefixEnd_2511404 1289557369624197354000269 := by
  unfold tailWord_2511404
  simp only [CollatzResearch.WordTrace]
  refine ⟨45799214496809848250374633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61065619329079797667166177 45799214496809848250374633)
  ·
    refine ⟨34349410872607386187780975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45799214496809848250374633 34349410872607386187780975)
    ·
      refine ⟨51524116308911079281671463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34349410872607386187780975 51524116308911079281671463)
      ·
        refine ⟨77286174463366618922507195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51524116308911079281671463 77286174463366618922507195)
        ·
          refine ⟨115929261695049928383760793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77286174463366618922507195 115929261695049928383760793)
          ·
            refine ⟨86946946271287446287820595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115929261695049928383760793 86946946271287446287820595)
            ·
              refine ⟨130420419406931169431730893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86946946271287446287820595 130420419406931169431730893)
              ·
                refine ⟨48907657277599188536899085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130420419406931169431730893 48907657277599188536899085)
                ·
                  refine ⟨18340371479099695701337157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48907657277599188536899085 18340371479099695701337157)
                  ·
                    refine ⟨3438819652331192944000717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18340371479099695701337157 3438819652331192944000717)
                    ·
                      refine ⟨1289557369624197354000269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3438819652331192944000717 1289557369624197354000269)
                      ·
                        rfl

theorem cell23_2511404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_2511404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511404 prefixEnd_2511404 := by exact prefixLift 2511404
  have htrace : WordTrace (prefixWord ++ tailWord_2511404) baseStart_2511404 baseEnd_2511404 := by
    simpa [prefixWord, tailWord_2511404, baseEnd_2511404] using wordTrace_append hprefix tailTrace_2511404
  have hstable : (prefixWord ++ tailWord_2511404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511404).length < 2 ^ (prefixWord ++ tailWord_2511404).sum := by decide
  have hdescent : baseEnd_2511404 < baseStart_2511404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511441 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 6]
def baseStart_2511441 : Nat := 118140960795 + 2511441 * 2 ^ 59
def prefixEnd_2511441 : Nat := 4983230072969 + 3 ^ 40 * 2511441 * 2
def baseEnd_2511441 : Nat := 143286263156490412137511

theorem tailTrace_2511441 : CollatzResearch.WordTrace tailWord_2511441 prefixEnd_2511441 143286263156490412137511 := by
  unfold tailWord_2511441
  simp only [CollatzResearch.WordTrace]
  refine ⟨91599778494485651819846177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61066518996323767879897451 91599778494485651819846177)
  ·
    refine ⟨68699833870864238864884633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91599778494485651819846177 68699833870864238864884633)
    ·
      refine ⟨51524875403148179148663475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68699833870864238864884633 51524875403148179148663475)
      ·
        refine ⟨77287313104722268722995213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51524875403148179148663475 77287313104722268722995213)
        ·
          refine ⟨28982742414270850771123205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77287313104722268722995213 28982742414270850771123205)
          ·
            refine ⟨5434264202675784519585601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28982742414270850771123205 5434264202675784519585601)
            ·
              refine ⟨4075698152006838389689201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5434264202675784519585601 4075698152006838389689201)
              ·
                refine ⟨3056773614005128792266901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4075698152006838389689201 3056773614005128792266901)
                ·
                  refine ⟨143286263156490412137511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3056773614005128792266901 143286263156490412137511)
                  ·
                    rfl

theorem cell23_2511441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 6].length) (baseStart_2511441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511441 prefixEnd_2511441 := by exact prefixLift 2511441
  have htrace : WordTrace (prefixWord ++ tailWord_2511441) baseStart_2511441 baseEnd_2511441 := by
    simpa [prefixWord, tailWord_2511441, baseEnd_2511441] using wordTrace_append hprefix tailTrace_2511441
  have hstable : (prefixWord ++ tailWord_2511441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511441).length < 2 ^ (prefixWord ++ tailWord_2511441).sum := by decide
  have hdescent : baseEnd_2511441 < baseStart_2511441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511445 : List Nat := [1, 3, 2, 2, 1, 1, 6, 2, 1, 4]
def baseStart_2511445 : Nat := 118140960795 + 2511445 * 2 ^ 59
def prefixEnd_2511445 : Nat := 4983230072969 + 3 ^ 40 * 2511445 * 2
def baseEnd_2511445 : Nat := 429859474110343897862527

theorem tailTrace_2511445 : CollatzResearch.WordTrace tailWord_2511445 prefixEnd_2511445 429859474110343897862527 := by
  unfold tailWord_2511445
  simp only [CollatzResearch.WordTrace]
  refine ⟨91599924386471160502991789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61066616257647440335327859 91599924386471160502991789)
  ·
    refine ⟨34349971644926685188621921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91599924386471160502991789 34349971644926685188621921)
    ·
      refine ⟨25762478733695013891466441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34349971644926685188621921 25762478733695013891466441)
      ·
        refine ⟨19321859050271260418599831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25762478733695013891466441 19321859050271260418599831)
        ·
          refine ⟨28982788575406890627899747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19321859050271260418599831 28982788575406890627899747)
          ·
            refine ⟨43474182863110335941849621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28982788575406890627899747 43474182863110335941849621)
            ·
              refine ⟨2037852321708296997274201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43474182863110335941849621 2037852321708296997274201)
              ·
                refine ⟨1528389241281222747955651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2037852321708296997274201 1528389241281222747955651)
                ·
                  refine ⟨2292583861921834121933477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528389241281222747955651 2292583861921834121933477)
                  ·
                    refine ⟨429859474110343897862527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2292583861921834121933477 429859474110343897862527)
                    ·
                      rfl

theorem cell23_2511445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 4].length) (baseStart_2511445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511445 prefixEnd_2511445 := by exact prefixLift 2511445
  have htrace : WordTrace (prefixWord ++ tailWord_2511445) baseStart_2511445 baseEnd_2511445 := by
    simpa [prefixWord, tailWord_2511445, baseEnd_2511445] using wordTrace_append hprefix tailTrace_2511445
  have hstable : (prefixWord ++ tailWord_2511445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511445).length < 2 ^ (prefixWord ++ tailWord_2511445).sum := by decide
  have hdescent : baseEnd_2511445 < baseStart_2511445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511488 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 1, 5]
def baseStart_2511488 : Nat := 118140960795 + 2511488 * 2 ^ 59
def prefixEnd_2511488 : Nat := 4983230072969 + 3 ^ 40 * 2511488 * 2
def baseEnd_2511488 : Nat := 429866833999725008449961

theorem tailTrace_2511488 : CollatzResearch.WordTrace tailWord_2511488 prefixEnd_2511488 429866833999725008449961 := by
  unfold tailWord_2511488
  simp only [CollatzResearch.WordTrace]
  refine ⟨45800746362657689423403559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61067661816876919231204745 45800746362657689423403559)
  ·
    refine ⟨68701119543986534135105339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45800746362657689423403559 68701119543986534135105339)
    ·
      refine ⟨103051679315979801202658009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68701119543986534135105339 103051679315979801202658009)
      ·
        refine ⟨77288759486984850901993507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103051679315979801202658009 77288759486984850901993507)
        ·
          refine ⟨115933139230477276352990261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77288759486984850901993507 115933139230477276352990261)
          ·
            refine ⟨10868731802857244658092837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115933139230477276352990261 10868731802857244658092837)
            ·
              refine ⟨2037887213035733373392407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10868731802857244658092837 2037887213035733373392407)
              ·
                refine ⟨3056830819553600060088611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2037887213035733373392407 3056830819553600060088611)
                ·
                  refine ⟨4585246229330400090132917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056830819553600060088611 4585246229330400090132917)
                  ·
                    refine ⟨429866833999725008449961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4585246229330400090132917 429866833999725008449961)
                    ·
                      rfl

theorem cell23_2511488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 5].length) (baseStart_2511488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511488 prefixEnd_2511488 := by exact prefixLift 2511488
  have htrace : WordTrace (prefixWord ++ tailWord_2511488) baseStart_2511488 baseEnd_2511488 := by
    simpa [prefixWord, tailWord_2511488, baseEnd_2511488] using wordTrace_append hprefix tailTrace_2511488
  have hstable : (prefixWord ++ tailWord_2511488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511488).length < 2 ^ (prefixWord ++ tailWord_2511488).sum := by decide
  have hdescent : baseEnd_2511488 < baseStart_2511488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511504 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_2511504 : Nat := 118140960795 + 2511504 * 2 ^ 59
def prefixEnd_2511504 : Nat := 4983230072969 + 3 ^ 40 * 2511504 * 2
def baseEnd_2511504 : Nat := 1289608717689646962749809

theorem tailTrace_2511504 : CollatzResearch.WordTrace tailWord_2511504 prefixEnd_2511504 1289608717689646962749809 := by
  unfold tailWord_2511504
  simp only [CollatzResearch.WordTrace]
  refine ⟨45801038146628706789694783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61068050862171609052926377 45801038146628706789694783)
  ·
    refine ⟨68701557219943060184542175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45801038146628706789694783 68701557219943060184542175)
    ·
      refine ⟨103052335829914590276813263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68701557219943060184542175 103052335829914590276813263)
      ·
        refine ⟨154578503744871885415219895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103052335829914590276813263 154578503744871885415219895)
        ·
          refine ⟨231867755617307828122829843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154578503744871885415219895 231867755617307828122829843)
          ·
            refine ⟨347801633425961742184244765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231867755617307828122829843 347801633425961742184244765)
            ·
              refine ⟨130425612534735653319091787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347801633425961742184244765 130425612534735653319091787)
              ·
                refine ⟨195638418802103479978637681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130425612534735653319091787 195638418802103479978637681)
                ·
                  refine ⟨146728814101577609983978261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195638418802103479978637681 146728814101577609983978261)
                  ·
                    refine ⟨6877913161011450467998981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 146728814101577609983978261 6877913161011450467998981)
                    ·
                      refine ⟨1289608717689646962749809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6877913161011450467998981 1289608717689646962749809)
                      ·
                        rfl

theorem cell23_2511504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_2511504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511504 prefixEnd_2511504 := by exact prefixLift 2511504
  have htrace : WordTrace (prefixWord ++ tailWord_2511504) baseStart_2511504 baseEnd_2511504 := by
    simpa [prefixWord, tailWord_2511504, baseEnd_2511504] using wordTrace_append hprefix tailTrace_2511504
  have hstable : (prefixWord ++ tailWord_2511504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511504).length < 2 ^ (prefixWord ++ tailWord_2511504).sum := by decide
  have hdescent : baseEnd_2511504 < baseStart_2511504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511511 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 5]
def baseStart_2511511 : Nat := 118140960795 + 2511511 * 2 ^ 59
def prefixEnd_2511511 : Nat := 4983230072969 + 3 ^ 40 * 2511511 * 2
def baseEnd_2511511 : Nat := 1289612312054228435362277

theorem tailTrace_2511511 : CollatzResearch.WordTrace tailWord_2511511 prefixEnd_2511511 1289612312054228435362277 := by
  unfold tailWord_2511511
  simp only [CollatzResearch.WordTrace]
  refine ⟨91602331604232053774894387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61068221069488035849929591 91602331604232053774894387)
  ·
    refine ⟨137403497406348080662341581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91602331604232053774894387 137403497406348080662341581)
    ·
      refine ⟨51526311527380530248378093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137403497406348080662341581 51526311527380530248378093)
      ·
        refine ⟨19322366822767698843141785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51526311527380530248378093 19322366822767698843141785)
        ·
          refine ⟨14491775117075774132356339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19322366822767698843141785 14491775117075774132356339)
          ·
            refine ⟨21737662675613661198534509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14491775117075774132356339 21737662675613661198534509)
            ·
              refine ⟨8151623503355122949450441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21737662675613661198534509 8151623503355122949450441)
              ·
                refine ⟨6113717627516342212087831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8151623503355122949450441 6113717627516342212087831)
                ·
                  refine ⟨9170576441274513318131747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6113717627516342212087831 9170576441274513318131747)
                  ·
                    refine ⟨13755864661911769977197621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9170576441274513318131747 13755864661911769977197621)
                    ·
                      refine ⟨1289612312054228435362277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13755864661911769977197621 1289612312054228435362277)
                      ·
                        rfl

theorem cell23_2511511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_2511511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511511 prefixEnd_2511511 := by exact prefixLift 2511511
  have htrace : WordTrace (prefixWord ++ tailWord_2511511) baseStart_2511511 baseEnd_2511511 := by
    simpa [prefixWord, tailWord_2511511, baseEnd_2511511] using wordTrace_append hprefix tailTrace_2511511
  have hstable : (prefixWord ++ tailWord_2511511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511511).length < 2 ^ (prefixWord ++ tailWord_2511511).sum := by decide
  have hdescent : baseEnd_2511511 < baseStart_2511511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511544 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 3, 9]
def baseStart_2511544 : Nat := 118140960795 + 2511544 * 2 ^ 59
def prefixEnd_2511544 : Nat := 4983230072969 + 3 ^ 40 * 2511544 * 2
def baseEnd_2511544 : Nat := 429876418971942268749875

theorem tailTrace_2511544 : CollatzResearch.WordTrace tailWord_2511544 prefixEnd_2511544 429876418971942268749875 := by
  unfold tailWord_2511544
  simp only [CollatzResearch.WordTrace]
  refine ⟨45801767606556250205422843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61069023475408333607230457 45801767606556250205422843)
  ·
    refine ⟨68702651409834375308134265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45801767606556250205422843 68702651409834375308134265)
    ·
      refine ⟨51526988557375781481100699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68702651409834375308134265 51526988557375781481100699)
      ·
        refine ⟨77290482836063672221651049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51526988557375781481100699 77290482836063672221651049)
        ·
          refine ⟨57967862127047754166238287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77290482836063672221651049 57967862127047754166238287)
          ·
            refine ⟨86951793190571631249357431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57967862127047754166238287 86951793190571631249357431)
            ·
              refine ⟨130427689785857446874036147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86951793190571631249357431 130427689785857446874036147)
              ·
                refine ⟨195641534678786170311054221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130427689785857446874036147 195641534678786170311054221)
                ·
                  refine ⟨73365575504544813866645333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 195641534678786170311054221 73365575504544813866645333)
                  ·
                    refine ⟨429876418971942268749875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73365575504544813866645333 429876418971942268749875)
                    ·
                      rfl

theorem cell23_2511544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_2511544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511544 prefixEnd_2511544 := by exact prefixLift 2511544
  have htrace : WordTrace (prefixWord ++ tailWord_2511544) baseStart_2511544 baseEnd_2511544 := by
    simpa [prefixWord, tailWord_2511544, baseEnd_2511544] using wordTrace_append hprefix tailTrace_2511544
  have hstable : (prefixWord ++ tailWord_2511544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511544).length < 2 ^ (prefixWord ++ tailWord_2511544).sum := by decide
  have hdescent : baseEnd_2511544 < baseStart_2511544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511565 : List Nat := [1, 6, 2, 1, 2, 1, 2, 8]
def baseStart_2511565 : Nat := 118140960795 + 2511565 * 2 ^ 59
def prefixEnd_2511565 : Nat := 4983230072969 + 3 ^ 40 * 2511565 * 2
def baseEnd_2511565 : Nat := 47764445926280415706927

theorem tailTrace_2511565 : CollatzResearch.WordTrace tailWord_2511565 prefixEnd_2511565 47764445926280415706927 := by
  unfold tailWord_2511565
  simp only [CollatzResearch.WordTrace]
  refine ⟨91604301146036420997360149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61069534097357613998240099 91604301146036420997360149)
  ·
    refine ⟨4293951616220457234251257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 91604301146036420997360149 4293951616220457234251257)
    ·
      refine ⟨3220463712165342925688443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4293951616220457234251257 3220463712165342925688443)
      ·
        refine ⟨4830695568248014388532665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3220463712165342925688443 4830695568248014388532665)
        ·
          refine ⟨3623021676186010791399499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4830695568248014388532665 3623021676186010791399499)
          ·
            refine ⟨5434532514279016187099249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623021676186010791399499 5434532514279016187099249)
            ·
              refine ⟨4075899385709262140324437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5434532514279016187099249 4075899385709262140324437)
              ·
                refine ⟨47764445926280415706927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4075899385709262140324437 47764445926280415706927)
                ·
                  rfl

theorem cell23_2511565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 8].length) (baseStart_2511565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511565 prefixEnd_2511565 := by exact prefixLift 2511565
  have htrace : WordTrace (prefixWord ++ tailWord_2511565) baseStart_2511565 baseEnd_2511565 := by
    simpa [prefixWord, tailWord_2511565, baseEnd_2511565] using wordTrace_append hprefix tailTrace_2511565
  have hstable : (prefixWord ++ tailWord_2511565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511565).length < 2 ^ (prefixWord ++ tailWord_2511565).sum := by decide
  have hdescent : baseEnd_2511565 < baseStart_2511565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511575 : List Nat := [1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 3]
def baseStart_2511575 : Nat := 118140960795 + 2511575 * 2 ^ 59
def prefixEnd_2511575 : Nat := 4983230072969 + 3 ^ 40 * 2511575 * 2
def baseEnd_2511575 : Nat := 1289645174816116184961983

theorem tailTrace_2511575 : CollatzResearch.WordTrace tailWord_2511575 prefixEnd_2511575 1289645174816116184961983 := by
  unfold tailWord_2511575
  simp only [CollatzResearch.WordTrace]
  refine ⟨91604665876000192705224179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61069777250666795136816119 91604665876000192705224179)
  ·
    refine ⟨137406998814000289057836269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91604665876000192705224179 137406998814000289057836269)
    ·
      refine ⟨51527624555250108396688601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137406998814000289057836269 51527624555250108396688601)
      ·
        refine ⟨38645718416437581297516451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51527624555250108396688601 38645718416437581297516451)
        ·
          refine ⟨57968577624656371946274677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38645718416437581297516451 57968577624656371946274677)
          ·
            refine ⟨5434554152311534869963251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57968577624656371946274677 5434554152311534869963251)
            ·
              refine ⟨8151831228467302304944877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5434554152311534869963251 8151831228467302304944877)
              ·
                refine ⟨3056936710675238364354329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8151831228467302304944877 3056936710675238364354329)
                ·
                  refine ⟨2292702533006428773265747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3056936710675238364354329 2292702533006428773265747)
                  ·
                    refine ⟨3439053799509643159898621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2292702533006428773265747 3439053799509643159898621)
                    ·
                      refine ⟨1289645174816116184961983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3439053799509643159898621 1289645174816116184961983)
                      ·
                        rfl

theorem cell23_2511575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_2511575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511575 prefixEnd_2511575 := by exact prefixLift 2511575
  have htrace : WordTrace (prefixWord ++ tailWord_2511575) baseStart_2511575 baseEnd_2511575 := by
    simpa [prefixWord, tailWord_2511575, baseEnd_2511575] using wordTrace_append hprefix tailTrace_2511575
  have hstable : (prefixWord ++ tailWord_2511575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511575).length < 2 ^ (prefixWord ++ tailWord_2511575).sum := by decide
  have hdescent : baseEnd_2511575 < baseStart_2511575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511585 : List Nat := [1, 2, 3, 1, 4, 2, 1, 1, 3, 3, 2]
def baseStart_2511585 : Nat := 118140960795 + 2511585 * 2 ^ 59
def prefixEnd_2511585 : Nat := 4983230072969 + 3 ^ 40 * 2511585 * 2
def baseEnd_2511585 : Nat := 1289650309622661145836937

theorem tailTrace_2511585 : CollatzResearch.WordTrace tailWord_2511585 prefixEnd_2511585 1289650309622661145836937 := by
  unfold tailWord_2511585
  simp only [CollatzResearch.WordTrace]
  refine ⟨91605030605963964413088209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61070020403975976275392139 91605030605963964413088209)
  ·
    refine ⟨68703772954472973309816157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91605030605963964413088209 68703772954472973309816157)
    ·
      refine ⟨25763914857927364991181059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68703772954472973309816157 25763914857927364991181059)
      ·
        refine ⟨38645872286891047486771589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25763914857927364991181059 38645872286891047486771589)
        ·
          refine ⟨7246101053792071403769673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38645872286891047486771589 7246101053792071403769673)
          ·
            refine ⟨5434575790344053552827255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7246101053792071403769673 5434575790344053552827255)
            ·
              refine ⟨8151863685516080329240883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5434575790344053552827255 8151863685516080329240883)
              ·
                refine ⟨12227795528274120493861325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8151863685516080329240883 12227795528274120493861325)
                ·
                  refine ⟨4585423323102795185197997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12227795528274120493861325 4585423323102795185197997)
                  ·
                    refine ⟨1719533746163548194449249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4585423323102795185197997 1719533746163548194449249)
                    ·
                      refine ⟨1289650309622661145836937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719533746163548194449249 1289650309622661145836937)
                      ·
                        rfl

theorem cell23_2511585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_2511585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511585 prefixEnd_2511585 := by exact prefixLift 2511585
  have htrace : WordTrace (prefixWord ++ tailWord_2511585) baseStart_2511585 baseEnd_2511585 := by
    simpa [prefixWord, tailWord_2511585, baseEnd_2511585] using wordTrace_append hprefix tailTrace_2511585
  have hstable : (prefixWord ++ tailWord_2511585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511585).length < 2 ^ (prefixWord ++ tailWord_2511585).sum := by decide
  have hdescent : baseEnd_2511585 < baseStart_2511585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511601 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 5]
def baseStart_2511601 : Nat := 118140960795 + 2511601 * 2 ^ 59
def prefixEnd_2511601 : Nat := 4983230072969 + 3 ^ 40 * 2511601 * 2
def baseEnd_2511601 : Nat := 1289658525313133083236863

theorem tailTrace_2511601 : CollatzResearch.WordTrace tailWord_2511601 prefixEnd_2511601 1289658525313133083236863 := by
  unfold tailWord_2511601
  simp only [CollatzResearch.WordTrace]
  refine ⟨91605614173905999145670657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61070409449270666097113771 91605614173905999145670657)
  ·
    refine ⟨68704210630429499359252993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91605614173905999145670657 68704210630429499359252993)
    ·
      refine ⟨51528157972822124519439745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68704210630429499359252993 51528157972822124519439745)
      ·
        refine ⟨38646118479616593389579809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51528157972822124519439745 38646118479616593389579809)
        ·
          refine ⟨28984588859712445042184857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38646118479616593389579809 28984588859712445042184857)
          ·
            refine ⟨21738441644784333781638643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28984588859712445042184857 21738441644784333781638643)
            ·
              refine ⟨32607662467176500672457965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21738441644784333781638643 32607662467176500672457965)
              ·
                refine ⟨12227873425191187752171737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32607662467176500672457965 12227873425191187752171737)
                ·
                  refine ⟨9170905068893390814128803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12227873425191187752171737 9170905068893390814128803)
                  ·
                    refine ⟨13756357603340086221193205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9170905068893390814128803 13756357603340086221193205)
                    ·
                      refine ⟨1289658525313133083236863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13756357603340086221193205 1289658525313133083236863)
                      ·
                        rfl

theorem cell23_2511601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 5].length) (baseStart_2511601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511601 prefixEnd_2511601 := by exact prefixLift 2511601
  have htrace : WordTrace (prefixWord ++ tailWord_2511601) baseStart_2511601 baseEnd_2511601 := by
    simpa [prefixWord, tailWord_2511601, baseEnd_2511601] using wordTrace_append hprefix tailTrace_2511601
  have hstable : (prefixWord ++ tailWord_2511601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511601).length < 2 ^ (prefixWord ++ tailWord_2511601).sum := by decide
  have hdescent : baseEnd_2511601 < baseStart_2511601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511711 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 10]
def baseStart_2511711 : Nat := 118140960795 + 2511711 * 2 ^ 59
def prefixEnd_2511711 : Nat := 4983230072969 + 3 ^ 40 * 2511711 * 2
def baseEnd_2511711 : Nat := 143301667576125294762373

theorem tailTrace_2511711 : CollatzResearch.WordTrace tailWord_2511711 prefixEnd_2511711 143301667576125294762373 := by
  unfold tailWord_2511711
  simp only [CollatzResearch.WordTrace]
  refine ⟨91609626203507487932174987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61073084135671658621449991 91609626203507487932174987)
  ·
    refine ⟨137414439305261231898262481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91609626203507487932174987 137414439305261231898262481)
    ·
      refine ⟨103060829478945923923696861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137414439305261231898262481 103060829478945923923696861)
      ·
        refine ⟨38647811054604721471386323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103060829478945923923696861 38647811054604721471386323)
        ·
          refine ⟨57971716581907082207079485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38647811054604721471386323 57971716581907082207079485)
          ·
            refine ⟨21739393718215155827654807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57971716581907082207079485 21739393718215155827654807)
            ·
              refine ⟨32609090577322733741482211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21739393718215155827654807 32609090577322733741482211)
              ·
                refine ⟨48913635865984100612223317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32609090577322733741482211 48913635865984100612223317)
                ·
                  refine ⟨143301667576125294762373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 48913635865984100612223317 143301667576125294762373)
                  ·
                    rfl

theorem cell23_2511711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 10].length) (baseStart_2511711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511711 prefixEnd_2511711 := by exact prefixLift 2511711
  have htrace : WordTrace (prefixWord ++ tailWord_2511711) baseStart_2511711 baseEnd_2511711 := by
    simpa [prefixWord, tailWord_2511711, baseEnd_2511711] using wordTrace_append hprefix tailTrace_2511711
  have hstable : (prefixWord ++ tailWord_2511711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511711).length < 2 ^ (prefixWord ++ tailWord_2511711).sum := by decide
  have hdescent : baseEnd_2511711 < baseStart_2511711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511731 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 8]
def baseStart_2511731 : Nat := 118140960795 + 2511731 * 2 ^ 59
def prefixEnd_2511731 : Nat := 4983230072969 + 3 ^ 40 * 2511731 * 2
def baseEnd_2511731 : Nat := 1289725277798217574611265

theorem tailTrace_2511731 : CollatzResearch.WordTrace tailWord_2511731 prefixEnd_2511731 1289725277798217574611265 := by
  unfold tailWord_2511731
  simp only [CollatzResearch.WordTrace]
  refine ⟨91610355663435031347903047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61073570442290020898602031 91610355663435031347903047)
  ·
    refine ⟨137415533495152547021854571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91610355663435031347903047 137415533495152547021854571)
    ·
      refine ⟨206123300242728820532781857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137415533495152547021854571 206123300242728820532781857)
      ·
        refine ⟨154592475182046615399586393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206123300242728820532781857 154592475182046615399586393)
        ·
          refine ⟨115944356386534961549689795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154592475182046615399586393 115944356386534961549689795)
          ·
            refine ⟨173916534579802442324534693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115944356386534961549689795 173916534579802442324534693)
            ·
              refine ⟨32609350233712957935850255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173916534579802442324534693 32609350233712957935850255)
              ·
                refine ⟨48914025350569436903775383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32609350233712957935850255 48914025350569436903775383)
                ·
                  refine ⟨73371038025854155355663075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48914025350569436903775383 73371038025854155355663075)
                  ·
                    refine ⟨110056557038781233033494613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73371038025854155355663075 110056557038781233033494613)
                    ·
                      refine ⟨1289725277798217574611265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 110056557038781233033494613 1289725277798217574611265)
                      ·
                        rfl

theorem cell23_2511731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 8].length) (baseStart_2511731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511731 prefixEnd_2511731 := by exact prefixLift 2511731
  have htrace : WordTrace (prefixWord ++ tailWord_2511731) baseStart_2511731 baseEnd_2511731 := by
    simpa [prefixWord, tailWord_2511731, baseEnd_2511731] using wordTrace_append hprefix tailTrace_2511731
  have hstable : (prefixWord ++ tailWord_2511731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511731).length < 2 ^ (prefixWord ++ tailWord_2511731).sum := by decide
  have hdescent : baseEnd_2511731 < baseStart_2511731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511755 : List Nat := [1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 3]
def baseStart_2511755 : Nat := 118140960795 + 2511755 * 2 ^ 59
def prefixEnd_2511755 : Nat := 4983230072969 + 3 ^ 40 * 2511755 * 2
def baseEnd_2511755 : Nat := 1289737601333925480711155

theorem tailTrace_2511755 : CollatzResearch.WordTrace tailWord_2511755 prefixEnd_2511755 1289737601333925480711155 := by
  unfold tailWord_2511755
  simp only [CollatzResearch.WordTrace]
  refine ⟨91611231015348083446776719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61074154010232055631184479 91611231015348083446776719)
  ·
    refine ⟨137416846523022125170165079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91611231015348083446776719 137416846523022125170165079)
    ·
      refine ⟨206125269784533187755247619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137416846523022125170165079 206125269784533187755247619)
      ·
        refine ⟨309187904676799781632871429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206125269784533187755247619 309187904676799781632871429)
        ·
          refine ⟨57972732126899959056163393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309187904676799781632871429 57972732126899959056163393)
          ·
            refine ⟨43479549095174969292122545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57972732126899959056163393 43479549095174969292122545)
            ·
              refine ⟨32609661821381226969091909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43479549095174969292122545 32609661821381226969091909)
              ·
                refine ⟨6114311591508980056704733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32609661821381226969091909 6114311591508980056704733)
                ·
                  refine ⟨2292866846815867521264275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6114311591508980056704733 2292866846815867521264275)
                  ·
                    refine ⟨3439300270223801281896413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2292866846815867521264275 3439300270223801281896413)
                    ·
                      refine ⟨1289737601333925480711155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3439300270223801281896413 1289737601333925480711155)
                      ·
                        rfl

theorem cell23_2511755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 3].length) (baseStart_2511755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511755 prefixEnd_2511755 := by exact prefixLift 2511755
  have htrace : WordTrace (prefixWord ++ tailWord_2511755) baseStart_2511755 baseEnd_2511755 := by
    simpa [prefixWord, tailWord_2511755, baseEnd_2511755] using wordTrace_append hprefix tailTrace_2511755
  have hstable : (prefixWord ++ tailWord_2511755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511755).length < 2 ^ (prefixWord ++ tailWord_2511755).sum := by decide
  have hdescent : baseEnd_2511755 < baseStart_2511755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511783 : List Nat := [1, 1, 6, 1, 4, 1, 2, 2, 1, 4]
def baseStart_2511783 : Nat := 118140960795 + 2511783 * 2 ^ 59
def prefixEnd_2511783 : Nat := 4983230072969 + 3 ^ 40 * 2511783 * 2
def baseEnd_2511783 : Nat := 429917326264083790387009

theorem tailTrace_2511783 : CollatzResearch.WordTrace tailWord_2511783 prefixEnd_2511783 429917326264083790387009 := by
  unfold tailWord_2511783
  simp only [CollatzResearch.WordTrace]
  refine ⟨91612252259246644228796003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61074834839497762819197335 91612252259246644228796003)
  ·
    refine ⟨137418378388869966343194005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91612252259246644228796003 137418378388869966343194005)
    ·
      refine ⟨6441486486978279672337219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 137418378388869966343194005 6441486486978279672337219)
      ·
        refine ⟨9662229730467419508505829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6441486486978279672337219 9662229730467419508505829)
        ·
          refine ⟨1811668074462641157844843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9662229730467419508505829 1811668074462641157844843)
          ·
            refine ⟨2717502111693961736767265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811668074462641157844843 2717502111693961736767265)
            ·
              refine ⟨2038126583770471302575449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717502111693961736767265 2038126583770471302575449)
              ·
                refine ⟨1528594937827853476931587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2038126583770471302575449 1528594937827853476931587)
                ·
                  refine ⟨2292892406741780215397381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528594937827853476931587 2292892406741780215397381)
                  ·
                    refine ⟨429917326264083790387009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2292892406741780215397381 429917326264083790387009)
                    ·
                      rfl

theorem cell23_2511783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_2511783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511783 prefixEnd_2511783 := by exact prefixLift 2511783
  have htrace : WordTrace (prefixWord ++ tailWord_2511783) baseStart_2511783 baseEnd_2511783 := by
    simpa [prefixWord, tailWord_2511783, baseEnd_2511783] using wordTrace_append hprefix tailTrace_2511783
  have hstable : (prefixWord ++ tailWord_2511783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511783).length < 2 ^ (prefixWord ++ tailWord_2511783).sum := by decide
  have hdescent : baseEnd_2511783 < baseStart_2511783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511815 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 3]
def baseStart_2511815 : Nat := 118140960795 + 2511815 * 2 ^ 59
def prefixEnd_2511815 : Nat := 4983230072969 + 3 ^ 40 * 2511815 * 2
def baseEnd_2511815 : Nat := 1289768410173195245960879

theorem tailTrace_2511815 : CollatzResearch.WordTrace tailWord_2511815 prefixEnd_2511815 1289768410173195245960879 := by
  unfold tailWord_2511815
  simp only [CollatzResearch.WordTrace]
  refine ⟨91613419395130713693960899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61075612930087142462640599 91613419395130713693960899)
  ·
    refine ⟨137420129092696070540941349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91613419395130713693960899 137420129092696070540941349)
    ·
      refine ⟨25766274204880513226426503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137420129092696070540941349 25766274204880513226426503)
      ·
        refine ⟨38649411307320769839639755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25766274204880513226426503 38649411307320769839639755)
        ·
          refine ⟨57974116960981154759459633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38649411307320769839639755 57974116960981154759459633)
          ·
            refine ⟨43480587720735866069594725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57974116960981154759459633 43480587720735866069594725)
            ·
              refine ⟨8152610197637974888049011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43480587720735866069594725 8152610197637974888049011)
              ·
                refine ⟨12228915296456962332073517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8152610197637974888049011 12228915296456962332073517)
                ·
                  refine ⟨4585843236171360874527569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12228915296456962332073517 4585843236171360874527569)
                  ·
                    refine ⟨3439382427128520655895677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4585843236171360874527569 3439382427128520655895677)
                    ·
                      refine ⟨1289768410173195245960879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3439382427128520655895677 1289768410173195245960879)
                      ·
                        rfl

theorem cell23_2511815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 3].length) (baseStart_2511815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511815 prefixEnd_2511815 := by exact prefixLift 2511815
  have htrace : WordTrace (prefixWord ++ tailWord_2511815) baseStart_2511815 baseEnd_2511815 := by
    simpa [prefixWord, tailWord_2511815, baseEnd_2511815] using wordTrace_append hprefix tailTrace_2511815
  have hstable : (prefixWord ++ tailWord_2511815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511815).length < 2 ^ (prefixWord ++ tailWord_2511815).sum := by decide
  have hdescent : baseEnd_2511815 < baseStart_2511815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511816 : List Nat := [2, 1, 3, 1, 6, 1, 1, 1, 2, 3, 2]
def baseStart_2511816 : Nat := 118140960795 + 2511816 * 2 ^ 59
def prefixEnd_2511816 : Nat := 4983230072969 + 3 ^ 40 * 2511816 * 2
def baseEnd_2511816 : Nat := 1289768923653849742048375

theorem tailTrace_2511816 : CollatzResearch.WordTrace tailWord_2511816 prefixEnd_2511816 1289768923653849742048375 := by
  unfold tailWord_2511816
  simp only [CollatzResearch.WordTrace]
  refine ⟨45806727934063545432373651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61075637245418060576498201 45806727934063545432373651)
  ·
    refine ⟨68710091901095318148560477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45806727934063545432373651 68710091901095318148560477)
    ·
      refine ⟨25766284462910744305710179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68710091901095318148560477 25766284462910744305710179)
      ·
        refine ⟨38649426694366116458565269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25766284462910744305710179 38649426694366116458565269)
        ·
          refine ⟨1811691876298411708995247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38649426694366116458565269 1811691876298411708995247)
          ·
            refine ⟨2717537814447617563492871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1811691876298411708995247 2717537814447617563492871)
            ·
              refine ⟨4076306721671426345239307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2717537814447617563492871 4076306721671426345239307)
              ·
                refine ⟨6114460082507139517858961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4076306721671426345239307 6114460082507139517858961)
                ·
                  refine ⟨4585845061880354638394221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6114460082507139517858961 4585845061880354638394221)
                  ·
                    refine ⟨1719691898205132989397833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4585845061880354638394221 1719691898205132989397833)
                    ·
                      refine ⟨1289768923653849742048375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719691898205132989397833 1289768923653849742048375)
                      ·
                        rfl

theorem cell23_2511816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_2511816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511816 prefixEnd_2511816 := by exact prefixLift 2511816
  have htrace : WordTrace (prefixWord ++ tailWord_2511816) baseStart_2511816 baseEnd_2511816 := by
    simpa [prefixWord, tailWord_2511816, baseEnd_2511816] using wordTrace_append hprefix tailTrace_2511816
  have hstable : (prefixWord ++ tailWord_2511816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511816).length < 2 ^ (prefixWord ++ tailWord_2511816).sum := by decide
  have hdescent : baseEnd_2511816 < baseStart_2511816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511832 : List Nat := [2, 1, 2, 2, 2, 4, 1, 3, 1, 2, 3]
def baseStart_2511832 : Nat := 118140960795 + 2511832 * 2 ^ 59
def prefixEnd_2511832 : Nat := 4983230072969 + 3 ^ 40 * 2511832 * 2
def baseEnd_2511832 : Nat := 1289777139344321679448301

theorem tailTrace_2511832 : CollatzResearch.WordTrace tailWord_2511832 prefixEnd_2511832 1289777139344321679448301 := by
  unfold tailWord_2511832
  simp only [CollatzResearch.WordTrace]
  refine ⟨45807019718034562798664875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61076026290712750398219833 45807019718034562798664875)
  ·
    refine ⟨68710529577051844197997313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45807019718034562798664875 68710529577051844197997313)
    ·
      refine ⟨51532897182788883148497985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68710529577051844197997313 51532897182788883148497985)
      ·
        refine ⟨38649672887091662361373489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51532897182788883148497985 38649672887091662361373489)
        ·
          refine ⟨28987254665318746771030117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38649672887091662361373489 28987254665318746771030117)
          ·
            refine ⟨5435110249747265019568147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28987254665318746771030117 5435110249747265019568147)
            ·
              refine ⟨8152665374620897529352221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435110249747265019568147 8152665374620897529352221)
              ·
                refine ⟨3057249515482836573507083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8152665374620897529352221 3057249515482836573507083)
                ·
                  refine ⟨4585874273224254860260625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057249515482836573507083 4585874273224254860260625)
                  ·
                    refine ⟨3439405704918191145195469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4585874273224254860260625 3439405704918191145195469)
                    ·
                      refine ⟨1289777139344321679448301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3439405704918191145195469 1289777139344321679448301)
                      ·
                        rfl

theorem cell23_2511832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_2511832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511832 prefixEnd_2511832 := by exact prefixLift 2511832
  have htrace : WordTrace (prefixWord ++ tailWord_2511832) baseStart_2511832 baseEnd_2511832 := by
    simpa [prefixWord, tailWord_2511832, baseEnd_2511832] using wordTrace_append hprefix tailTrace_2511832
  have hstable : (prefixWord ++ tailWord_2511832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511832).length < 2 ^ (prefixWord ++ tailWord_2511832).sum := by decide
  have hdescent : baseEnd_2511832 < baseStart_2511832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511839 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 2, 4]
def baseStart_2511839 : Nat := 118140960795 + 2511839 * 2 ^ 59
def prefixEnd_2511839 : Nat := 4983230072969 + 3 ^ 40 * 2511839 * 2
def baseEnd_2511839 : Nat := 429926911236301050686923

theorem tailTrace_2511839 : CollatzResearch.WordTrace tailWord_2511839 prefixEnd_2511839 429926911236301050686923 := by
  unfold tailWord_2511839
  simp only [CollatzResearch.WordTrace]
  refine ⟨91614294747043765792834571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61076196498029177195223047 91614294747043765792834571)
  ·
    refine ⟨137421442120565648689251857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91614294747043765792834571 137421442120565648689251857)
    ·
      refine ⟨103066081590424236516938893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137421442120565648689251857 103066081590424236516938893)
      ·
        refine ⟨38649780596409088693852085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103066081590424236516938893 38649780596409088693852085)
        ·
          refine ⟨3623416930913352065048633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38649780596409088693852085 3623416930913352065048633)
          ·
            refine ⟨2717562698185014048786475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3623416930913352065048633 2717562698185014048786475)
            ·
              refine ⟨4076344047277521073179713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2717562698185014048786475 4076344047277521073179713)
              ·
                refine ⟨3057258035458140804884785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4076344047277521073179713 3057258035458140804884785)
                ·
                  refine ⟨2292943526593605603663589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3057258035458140804884785 2292943526593605603663589)
                  ·
                    refine ⟨429926911236301050686923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2292943526593605603663589 429926911236301050686923)
                    ·
                      rfl

theorem cell23_2511839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 4].length) (baseStart_2511839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511839 prefixEnd_2511839 := by exact prefixLift 2511839
  have htrace : WordTrace (prefixWord ++ tailWord_2511839) baseStart_2511839 baseEnd_2511839 := by
    simpa [prefixWord, tailWord_2511839, baseEnd_2511839] using wordTrace_append hprefix tailTrace_2511839
  have hstable : (prefixWord ++ tailWord_2511839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511839).length < 2 ^ (prefixWord ++ tailWord_2511839).sum := by decide
  have hdescent : baseEnd_2511839 < baseStart_2511839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511848 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 1, 9]
def baseStart_2511848 : Nat := 118140960795 + 2511848 * 2 ^ 59
def prefixEnd_2511848 : Nat := 4983230072969 + 3 ^ 40 * 2511848 * 2
def baseEnd_2511848 : Nat := 429928451678264538949409

theorem tailTrace_2511848 : CollatzResearch.WordTrace tailWord_2511848 prefixEnd_2511848 429928451678264538949409 := by
  unfold tailWord_2511848
  simp only [CollatzResearch.WordTrace]
  refine ⟨45807311502005580164956099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61076415336007440219941465 45807311502005580164956099)
  ·
    refine ⟨68710967253008370247434149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45807311502005580164956099 68710967253008370247434149)
    ·
      refine ⟨12883306359939069421393903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68710967253008370247434149 12883306359939069421393903)
      ·
        refine ⟨19324959539908604132090855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12883306359939069421393903 19324959539908604132090855)
        ·
          refine ⟨28987439309862906198136283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19324959539908604132090855 28987439309862906198136283)
          ·
            refine ⟨43481158964794359297204425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28987439309862906198136283 43481158964794359297204425)
            ·
              refine ⟨32610869223595769472903319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43481158964794359297204425 32610869223595769472903319)
              ·
                refine ⟨48916303835393654209354979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32610869223595769472903319 48916303835393654209354979)
                ·
                  refine ⟨73374455753090481314032469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48916303835393654209354979 73374455753090481314032469)
                  ·
                    refine ⟨429928451678264538949409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 73374455753090481314032469 429928451678264538949409)
                    ·
                      rfl

theorem cell23_2511848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_2511848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511848 prefixEnd_2511848 := by exact prefixLift 2511848
  have htrace : WordTrace (prefixWord ++ tailWord_2511848) baseStart_2511848 baseEnd_2511848 := by
    simpa [prefixWord, tailWord_2511848, baseEnd_2511848] using wordTrace_append hprefix tailTrace_2511848
  have hstable : (prefixWord ++ tailWord_2511848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511848).length < 2 ^ (prefixWord ++ tailWord_2511848).sum := by decide
  have hdescent : baseEnd_2511848 < baseStart_2511848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511935 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 3]
def baseStart_2511935 : Nat := 118140960795 + 2511935 * 2 ^ 59
def prefixEnd_2511935 : Nat := 4983230072969 + 3 ^ 40 * 2511935 * 2
def baseEnd_2511935 : Nat := 1289830027851734776460327

theorem tailTrace_2511935 : CollatzResearch.WordTrace tailWord_2511935 prefixEnd_2511935 1289830027851734776460327 := by
  unfold tailWord_2511935
  simp only [CollatzResearch.WordTrace]
  refine ⟨91617796154695974188329259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61078530769797316125552839 91617796154695974188329259)
  ·
    refine ⟨137426694232043961282493889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91617796154695974188329259 137426694232043961282493889)
    ·
      refine ⟨103070020674032970961870417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137426694232043961282493889 103070020674032970961870417)
      ·
        refine ⟨77302515505524728221402813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103070020674032970961870417 77302515505524728221402813)
        ·
          refine ⟨28988443314571773083026055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77302515505524728221402813 28988443314571773083026055)
          ·
            refine ⟨43482664971857659624539083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28988443314571773083026055 43482664971857659624539083)
            ·
              refine ⟨65223997457786489436808625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43482664971857659624539083 65223997457786489436808625)
              ·
                refine ⟨48917998093339867077606469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65223997457786489436808625 48917998093339867077606469)
                ·
                  refine ⟨9172124642501225077051213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48917998093339867077606469 9172124642501225077051213)
                  ·
                    refine ⟨3439546740937959403894205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9172124642501225077051213 3439546740937959403894205)
                    ·
                      refine ⟨1289830027851734776460327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3439546740937959403894205 1289830027851734776460327)
                      ·
                        rfl

theorem cell23_2511935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 3].length) (baseStart_2511935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511935 prefixEnd_2511935 := by exact prefixLift 2511935
  have htrace : WordTrace (prefixWord ++ tailWord_2511935) baseStart_2511935 baseEnd_2511935 := by
    simpa [prefixWord, tailWord_2511935, baseEnd_2511935] using wordTrace_append hprefix tailTrace_2511935
  have hstable : (prefixWord ++ tailWord_2511935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511935).length < 2 ^ (prefixWord ++ tailWord_2511935).sum := by decide
  have hdescent : baseEnd_2511935 < baseStart_2511935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511966 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 2, 2, 4]
def baseStart_2511966 : Nat := 118140960795 + 2511966 * 2 ^ 59
def prefixEnd_2511966 : Nat := 4983230072969 + 3 ^ 40 * 2511966 * 2
def baseEnd_2511966 : Nat := 1289845945752024155172685

theorem tailTrace_2511966 : CollatzResearch.WordTrace tailWord_2511966 prefixEnd_2511966 1289845945752024155172685 := by
  unfold tailWord_2511966
  simp only [CollatzResearch.WordTrace]
  refine ⟨11452365852197958310338469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61079284545055777655138501 11452365852197958310338469)
  ·
    refine ⟨2147318597287117183188463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11452365852197958310338469 2147318597287117183188463)
    ·
      refine ⟨3220977895930675774782695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2147318597287117183188463 3220977895930675774782695)
      ·
        refine ⟨4831466843896013662174043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3220977895930675774782695 4831466843896013662174043)
        ·
          refine ⟨7247200265844020493261065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4831466843896013662174043 7247200265844020493261065)
          ·
            refine ⟨5435400199383015369945799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7247200265844020493261065 5435400199383015369945799)
            ·
              refine ⟨8153100299074523054918699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435400199383015369945799 8153100299074523054918699)
              ·
                refine ⟨12229650448611784582378049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8153100299074523054918699 12229650448611784582378049)
                ·
                  refine ⟨9172237836458838436783537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12229650448611784582378049 9172237836458838436783537)
                  ·
                    refine ⟨6879178377344128827587653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9172237836458838436783537 6879178377344128827587653)
                    ·
                      refine ⟨1289845945752024155172685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6879178377344128827587653 1289845945752024155172685)
                      ·
                        rfl

theorem cell23_2511966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_2511966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511966 prefixEnd_2511966 := by exact prefixLift 2511966
  have htrace : WordTrace (prefixWord ++ tailWord_2511966) baseStart_2511966 baseEnd_2511966 := by
    simpa [prefixWord, tailWord_2511966, baseEnd_2511966] using wordTrace_append hprefix tailTrace_2511966
  have hstable : (prefixWord ++ tailWord_2511966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511966).length < 2 ^ (prefixWord ++ tailWord_2511966).sum := by decide
  have hdescent : baseEnd_2511966 < baseStart_2511966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511989 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 1, 7]
def baseStart_2511989 : Nat := 118140960795 + 2511989 * 2 ^ 59
def prefixEnd_2511989 : Nat := 4983230072969 + 3 ^ 40 * 2511989 * 2
def baseEnd_2511989 : Nat := 429952585269025855061693

theorem tailTrace_2511989 : CollatzResearch.WordTrace tailWord_2511989 prefixEnd_2511989 429952585269025855061693 := by
  unfold tailWord_2511989
  simp only [CollatzResearch.WordTrace]
  refine ⟨91619765696500341410795021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61079843797666894273863347 91619765696500341410795021)
  ·
    refine ⟨34357412136187628029048133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91619765696500341410795021 34357412136187628029048133)
    ·
      refine ⟨6442014775535180255446525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34357412136187628029048133 6442014775535180255446525)
      ·
        refine ⟨2415755540825692595792447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6442014775535180255446525 2415755540825692595792447)
        ·
          refine ⟨3623633311238538893688671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2415755540825692595792447 3623633311238538893688671)
          ·
            refine ⟨5435449966857808340533007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623633311238538893688671 5435449966857808340533007)
            ·
              refine ⟨8153174950286712510799511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435449966857808340533007 8153174950286712510799511)
              ·
                refine ⟨12229762425430068766199267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8153174950286712510799511 12229762425430068766199267)
                ·
                  refine ⟨18344643638145103149298901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12229762425430068766199267 18344643638145103149298901)
                  ·
                    refine ⟨429952585269025855061693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18344643638145103149298901 429952585269025855061693)
                    ·
                      rfl

theorem cell23_2511989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_2511989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511989 prefixEnd_2511989 := by exact prefixLift 2511989
  have htrace : WordTrace (prefixWord ++ tailWord_2511989) baseStart_2511989 baseEnd_2511989 := by
    simpa [prefixWord, tailWord_2511989, baseEnd_2511989] using wordTrace_append hprefix tailTrace_2511989
  have hstable : (prefixWord ++ tailWord_2511989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511989).length < 2 ^ (prefixWord ++ tailWord_2511989).sum := by decide
  have hdescent : baseEnd_2511989 < baseStart_2511989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2511992 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 2, 1, 4]
def baseStart_2511992 : Nat := 118140960795 + 2511992 * 2 ^ 59
def prefixEnd_2511992 : Nat := 4983230072969 + 3 ^ 40 * 2511992 * 2
def baseEnd_2511992 : Nat := 1289859296249041053447565

theorem tailTrace_2511992 : CollatzResearch.WordTrace tailWord_2511992 prefixEnd_2511992 1289859296249041053447565 := by
  unfold tailWord_2511992
  simp only [CollatzResearch.WordTrace]
  refine ⟨45809937557744736461577115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61079916743659648615436153 45809937557744736461577115)
  ·
    refine ⟨68714906336617104692365673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45809937557744736461577115 68714906336617104692365673)
    ·
      refine ⟨51536179752462828519274255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68714906336617104692365673 51536179752462828519274255)
      ·
        refine ⟨77304269628694242778911383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51536179752462828519274255 77304269628694242778911383)
        ·
          refine ⟨115956404443041364168367075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77304269628694242778911383 115956404443041364168367075)
          ·
            refine ⟨173934606664562046252550613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115956404443041364168367075 173934606664562046252550613)
            ·
              refine ⟨4076592343700672959044155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 173934606664562046252550613 4076592343700672959044155)
              ·
                refine ⟨6114888515551009438566233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4076592343700672959044155 6114888515551009438566233)
                ·
                  refine ⟨4586166386663257078924675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6114888515551009438566233 4586166386663257078924675)
                  ·
                    refine ⟨6879249579994885618387013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4586166386663257078924675 6879249579994885618387013)
                    ·
                      refine ⟨1289859296249041053447565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6879249579994885618387013 1289859296249041053447565)
                      ·
                        rfl

theorem cell23_2511992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_2511992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2511992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2511992 prefixEnd_2511992 := by exact prefixLift 2511992
  have htrace : WordTrace (prefixWord ++ tailWord_2511992) baseStart_2511992 baseEnd_2511992 := by
    simpa [prefixWord, tailWord_2511992, baseEnd_2511992] using wordTrace_append hprefix tailTrace_2511992
  have hstable : (prefixWord ++ tailWord_2511992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2511992).length < 2 ^ (prefixWord ++ tailWord_2511992).sum := by decide
  have hdescent : baseEnd_2511992 < baseStart_2511992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2511992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512012 : List Nat := [2, 2, 1, 2, 1, 1, 1, 6, 2, 2, 3]
def baseStart_2512012 : Nat := 118140960795 + 2512012 * 2 ^ 59
def prefixEnd_2512012 : Nat := 4983230072969 + 3 ^ 40 * 2512012 * 2
def baseEnd_2512012 : Nat := 1289869565862130975197473

theorem tailTrace_2512012 : CollatzResearch.WordTrace tailWord_2512012 prefixEnd_2512012 1289869565862130975197473 := by
  unfold tailWord_2512012
  simp only [CollatzResearch.WordTrace]
  refine ⟨45810302287708508169441145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61080403050278010892588193 45810302287708508169441145)
  ·
    refine ⟨34357726715781381127080859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45810302287708508169441145 34357726715781381127080859)
    ·
      refine ⟨51536590073672071690621289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34357726715781381127080859 51536590073672071690621289)
      ·
        refine ⟨38652442555254053767965967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51536590073672071690621289 38652442555254053767965967)
        ·
          refine ⟨57978663832881080651948951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38652442555254053767965967 57978663832881080651948951)
          ·
            refine ⟨86967995749321620977923427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57978663832881080651948951 86967995749321620977923427)
            ·
              refine ⟨130451993623982431466885141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86967995749321620977923427 130451993623982431466885141)
              ·
                refine ⟨6114937201124176475010241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130451993623982431466885141 6114937201124176475010241)
                ·
                  refine ⟨4586202900843132356257681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6114937201124176475010241 4586202900843132356257681)
                  ·
                    refine ⟨3439652175632349267193261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4586202900843132356257681 3439652175632349267193261)
                    ·
                      refine ⟨1289869565862130975197473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3439652175632349267193261 1289869565862130975197473)
                      ·
                        rfl

theorem cell23_2512012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_2512012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512012 prefixEnd_2512012 := by exact prefixLift 2512012
  have htrace : WordTrace (prefixWord ++ tailWord_2512012) baseStart_2512012 baseEnd_2512012 := by
    simpa [prefixWord, tailWord_2512012, baseEnd_2512012] using wordTrace_append hprefix tailTrace_2512012
  have hstable : (prefixWord ++ tailWord_2512012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512012).length < 2 ^ (prefixWord ++ tailWord_2512012).sum := by decide
  have hdescent : baseEnd_2512012 < baseStart_2512012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512019 : List Nat := [1, 1, 1, 2, 1, 2, 6, 4, 1, 4]
def baseStart_2512019 : Nat := 118140960795 + 2512019 * 2 ^ 59
def prefixEnd_2512019 : Nat := 4983230072969 + 3 ^ 40 * 2512019 * 2
def baseEnd_2512019 : Nat := 429957720075570815936647

theorem tailTrace_2512019 : CollatzResearch.WordTrace tailWord_2512019 prefixEnd_2512019 429957720075570815936647 := by
  unfold tailWord_2512019
  simp only [CollatzResearch.WordTrace]
  refine ⟨91620859886391656534387111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61080573257594437689591407 91620859886391656534387111)
  ·
    refine ⟨137431289829587484801580667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91620859886391656534387111 137431289829587484801580667)
    ·
      refine ⟨206146934744381227202371001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137431289829587484801580667 206146934744381227202371001)
      ·
        refine ⟨154610201058285920401778251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206146934744381227202371001 154610201058285920401778251)
        ·
          refine ⟨231915301587428880602667377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154610201058285920401778251 231915301587428880602667377)
          ·
            refine ⟨173936476190571660452000533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231915301587428880602667377 173936476190571660452000533)
            ·
              refine ⟨8153272321433046583687525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173936476190571660452000533 8153272321433046583687525)
              ·
                refine ⟨1528738560268696234441411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8153272321433046583687525 1528738560268696234441411)
                ·
                  refine ⟨2293107840403044351662117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528738560268696234441411 2293107840403044351662117)
                  ·
                    refine ⟨429957720075570815936647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293107840403044351662117 429957720075570815936647)
                    ·
                      rfl

theorem cell23_2512019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 4].length) (baseStart_2512019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512019 prefixEnd_2512019 := by exact prefixLift 2512019
  have htrace : WordTrace (prefixWord ++ tailWord_2512019) baseStart_2512019 baseEnd_2512019 := by
    simpa [prefixWord, tailWord_2512019, baseEnd_2512019] using wordTrace_append hprefix tailTrace_2512019
  have hstable : (prefixWord ++ tailWord_2512019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512019).length < 2 ^ (prefixWord ++ tailWord_2512019).sum := by decide
  have hdescent : baseEnd_2512019 < baseStart_2512019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512075 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 5, 6]
def baseStart_2512075 : Nat := 118140960795 + 2512075 * 2 ^ 59
def prefixEnd_2512075 : Nat := 4983230072969 + 3 ^ 40 * 2512075 * 2
def baseEnd_2512075 : Nat := 429967305047788076236561

theorem tailTrace_2512075 : CollatzResearch.WordTrace tailWord_2512075 prefixEnd_2512075 429967305047788076236561 := by
  unfold tailWord_2512075
  simp only [CollatzResearch.WordTrace]
  refine ⟨91622902374188778098425679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61081934916125852065617119 91622902374188778098425679)
  ·
    refine ⟨137434353561283167147638519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91622902374188778098425679 137434353561283167147638519)
    ·
      refine ⟨206151530341924750721457779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137434353561283167147638519 206151530341924750721457779)
      ·
        refine ⟨309227295512887126082186669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206151530341924750721457779 309227295512887126082186669)
        ·
          refine ⟨115960235817332672280820001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309227295512887126082186669 115960235817332672280820001)
          ·
            refine ⟨86970176862999504210615001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115960235817332672280820001 86970176862999504210615001)
            ·
              refine ⟨65227632647249628157961251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86970176862999504210615001 65227632647249628157961251)
              ·
                refine ⟨97841448970874442236941877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65227632647249628157961251 97841448970874442236941877)
                ·
                  refine ⟨9172635841019478959713301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97841448970874442236941877 9172635841019478959713301)
                  ·
                    refine ⟨429967305047788076236561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9172635841019478959713301 429967305047788076236561)
                    ·
                      rfl

theorem cell23_2512075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 6].length) (baseStart_2512075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512075 prefixEnd_2512075 := by exact prefixLift 2512075
  have htrace : WordTrace (prefixWord ++ tailWord_2512075) baseStart_2512075 baseEnd_2512075 := by
    simpa [prefixWord, tailWord_2512075, baseEnd_2512075] using wordTrace_append hprefix tailTrace_2512075
  have hstable : (prefixWord ++ tailWord_2512075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512075).length < 2 ^ (prefixWord ++ tailWord_2512075).sum := by decide
  have hdescent : baseEnd_2512075 < baseStart_2512075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512103 : List Nat := [1, 1, 5, 3, 2, 1, 2, 1, 2, 3, 2]
def baseStart_2512103 : Nat := 118140960795 + 2512103 * 2 ^ 59
def prefixEnd_2512103 : Nat := 4983230072969 + 3 ^ 40 * 2512103 * 2
def baseEnd_2512103 : Nat := 1289916292601690119159555

theorem tailTrace_2512103 : CollatzResearch.WordTrace tailWord_2512103 prefixEnd_2512103 1289916292601690119159555 := by
  unfold tailWord_2512103
  simp only [CollatzResearch.WordTrace]
  refine ⟨91623923618087338880444963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61082615745391559253629975 91623923618087338880444963)
  ·
    refine ⟨137435885427131008320667445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91623923618087338880444963 137435885427131008320667445)
    ·
      refine ⟨12884614258793532030062573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137435885427131008320667445 12884614258793532030062573)
      ·
        refine ⟨4831730347047574511273465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12884614258793532030062573 4831730347047574511273465)
        ·
          refine ⟨3623797760285680883455099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4831730347047574511273465 3623797760285680883455099)
          ·
            refine ⟨5435696640428521325182649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623797760285680883455099 5435696640428521325182649)
            ·
              refine ⟨4076772480321390993886987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5435696640428521325182649 4076772480321390993886987)
              ·
                refine ⟨6115158720482086490830481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4076772480321390993886987 6115158720482086490830481)
                ·
                  refine ⟨4586369040361564868122861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6115158720482086490830481 4586369040361564868122861)
                  ·
                    refine ⟨1719888390135586825546073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4586369040361564868122861 1719888390135586825546073)
                    ·
                      refine ⟨1289916292601690119159555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719888390135586825546073 1289916292601690119159555)
                      ·
                        rfl

theorem cell23_2512103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_2512103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512103 prefixEnd_2512103 := by exact prefixLift 2512103
  have htrace : WordTrace (prefixWord ++ tailWord_2512103) baseStart_2512103 baseEnd_2512103 := by
    simpa [prefixWord, tailWord_2512103, baseEnd_2512103] using wordTrace_append hprefix tailTrace_2512103
  have hstable : (prefixWord ++ tailWord_2512103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512103).length < 2 ^ (prefixWord ++ tailWord_2512103).sum := by decide
  have hdescent : baseEnd_2512103 < baseStart_2512103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512109 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 1, 6]
def baseStart_2512109 : Nat := 118140960795 + 2512109 * 2 ^ 59
def prefixEnd_2512109 : Nat := 4983230072969 + 3 ^ 40 * 2512109 * 2
def baseEnd_2512109 : Nat := 429973124495205698561509

theorem tailTrace_2512109 : CollatzResearch.WordTrace tailWord_2512109 prefixEnd_2512109 429973124495205698561509 := by
  unfold tailWord_2512109
  simp only [CollatzResearch.WordTrace]
  refine ⟨91624142456065601905163381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61082761637377067936775587 91624142456065601905163381)
  ·
    refine ⟨8589763355256150178609067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91624142456065601905163381 8589763355256150178609067)
    ·
      refine ⟨12884645032884225267913601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8589763355256150178609067 12884645032884225267913601)
      ·
        refine ⟨9663483774663168950935201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12884645032884225267913601 9663483774663168950935201)
        ·
          refine ⟨7247612830997376713201401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9663483774663168950935201 7247612830997376713201401)
          ·
            refine ⟨5435709623248032534901051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7247612830997376713201401 5435709623248032534901051)
            ·
              refine ⟨8153564434872048802351577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435709623248032534901051 8153564434872048802351577)
              ·
                refine ⟨6115173326154036601763683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8153564434872048802351577 6115173326154036601763683)
                ·
                  refine ⟨9172759989231054902645525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6115173326154036601763683 9172759989231054902645525)
                  ·
                    refine ⟨429973124495205698561509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9172759989231054902645525 429973124495205698561509)
                    ·
                      rfl

theorem cell23_2512109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_2512109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512109 prefixEnd_2512109 := by exact prefixLift 2512109
  have htrace : WordTrace (prefixWord ++ tailWord_2512109) baseStart_2512109 baseEnd_2512109 := by
    simpa [prefixWord, tailWord_2512109, baseEnd_2512109] using wordTrace_append hprefix tailTrace_2512109
  have hstable : (prefixWord ++ tailWord_2512109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512109).length < 2 ^ (prefixWord ++ tailWord_2512109).sum := by decide
  have hdescent : baseEnd_2512109 < baseStart_2512109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512126 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_2512126 : Nat := 118140960795 + 2512126 * 2 ^ 59
def prefixEnd_2512126 : Nat := 4983230072969 + 3 ^ 40 * 2512126 * 2
def baseEnd_2512126 : Nat := 429976034218914509723983

theorem tailTrace_2512126 : CollatzResearch.WordTrace tailWord_2512126 prefixEnd_2512126 429976034218914509723983 := by
  unfold tailWord_2512126
  simp only [CollatzResearch.WordTrace]
  refine ⟨11453095312125501726066529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61083174998002675872354821 11453095312125501726066529)
  ·
    refine ⟨8589821484094126294549897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11453095312125501726066529 8589821484094126294549897)
    ·
      refine ⟨6442366113070594720912423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8589821484094126294549897 6442366113070594720912423)
      ·
        refine ⟨9663549169605892081368635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6442366113070594720912423 9663549169605892081368635)
        ·
          refine ⟨14495323754408838122052953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9663549169605892081368635 14495323754408838122052953)
          ·
            refine ⟨10871492815806628591539715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14495323754408838122052953 10871492815806628591539715)
            ·
              refine ⟨16307239223709942887309573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10871492815806628591539715 16307239223709942887309573)
              ·
                refine ⟨3057607354445614291370545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16307239223709942887309573 3057607354445614291370545)
                ·
                  refine ⟨2293205515834210718527909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3057607354445614291370545 2293205515834210718527909)
                  ·
                    refine ⟨429976034218914509723983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293205515834210718527909 429976034218914509723983)
                    ·
                      rfl

theorem cell23_2512126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_2512126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512126 prefixEnd_2512126 := by exact prefixLift 2512126
  have htrace : WordTrace (prefixWord ++ tailWord_2512126) baseStart_2512126 baseEnd_2512126 := by
    simpa [prefixWord, tailWord_2512126, baseEnd_2512126] using wordTrace_append hprefix tailTrace_2512126
  have hstable : (prefixWord ++ tailWord_2512126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512126).length < 2 ^ (prefixWord ++ tailWord_2512126).sum := by decide
  have hdescent : baseEnd_2512126 < baseStart_2512126 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512133 : List Nat := [1, 3, 1, 1, 2, 1, 5, 4, 1, 2, 2]
def baseStart_2512133 : Nat := 118140960795 + 2512133 * 2 ^ 59
def prefixEnd_2512133 : Nat := 4983230072969 + 3 ^ 40 * 2512133 * 2
def baseEnd_2512133 : Nat := 1289931697021325001784417

theorem tailTrace_2512133 : CollatzResearch.WordTrace tailWord_2512133 prefixEnd_2512133 1289931697021325001784417 := by
  unfold tailWord_2512133
  simp only [CollatzResearch.WordTrace]
  refine ⟨91625017807978654004037053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61083345205319102669358035 91625017807978654004037053)
  ·
    refine ⟨34359381677991995251513895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91625017807978654004037053 34359381677991995251513895)
    ·
      refine ⟨51539072516987992877270843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34359381677991995251513895 51539072516987992877270843)
      ·
        refine ⟨77308608775481989315906265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51539072516987992877270843 77308608775481989315906265)
        ·
          refine ⟨57981456581611491986929699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77308608775481989315906265 57981456581611491986929699)
          ·
            refine ⟨86972184872417237980394549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57981456581611491986929699 86972184872417237980394549)
            ·
              refine ⟨8153642331789116060661989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86972184872417237980394549 8153642331789116060661989)
              ·
                refine ⟨1528807937210459261374123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8153642331789116060661989 1528807937210459261374123)
                ·
                  refine ⟨2293211905815688892061185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1528807937210459261374123 2293211905815688892061185)
                  ·
                    refine ⟨1719908929361766669045889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2293211905815688892061185 1719908929361766669045889)
                    ·
                      refine ⟨1289931697021325001784417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719908929361766669045889 1289931697021325001784417)
                      ·
                        rfl

theorem cell23_2512133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 4, 1, 2, 2].length) (baseStart_2512133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512133 prefixEnd_2512133 := by exact prefixLift 2512133
  have htrace : WordTrace (prefixWord ++ tailWord_2512133) baseStart_2512133 baseEnd_2512133 := by
    simpa [prefixWord, tailWord_2512133, baseEnd_2512133] using wordTrace_append hprefix tailTrace_2512133
  have hstable : (prefixWord ++ tailWord_2512133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512133).length < 2 ^ (prefixWord ++ tailWord_2512133).sum := by decide
  have hdescent : baseEnd_2512133 < baseStart_2512133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512149 : List Nat := [1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 3]
def baseStart_2512149 : Nat := 118140960795 + 2512149 * 2 ^ 59
def prefixEnd_2512149 : Nat := 4983230072969 + 3 ^ 40 * 2512149 * 2
def baseEnd_2512149 : Nat := 1289939912711796939184343

theorem tailTrace_2512149 : CollatzResearch.WordTrace tailWord_2512149 prefixEnd_2512149 1289939912711796939184343 := by
  unfold tailWord_2512149
  simp only [CollatzResearch.WordTrace]
  refine ⟨91625601375920688736619501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61083734250613792491079667 91625601375920688736619501)
  ·
    refine ⟨34359600515970258276232313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91625601375920688736619501 34359600515970258276232313)
    ·
      refine ⟨25769700386977693707174235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34359600515970258276232313 25769700386977693707174235)
      ·
        refine ⟨38654550580466540560761353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25769700386977693707174235 38654550580466540560761353)
        ·
          refine ⟨28990912935349905420571015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38654550580466540560761353 28990912935349905420571015)
          ·
            refine ⟨43486369403024858130856523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28990912935349905420571015 43486369403024858130856523)
            ·
              refine ⟨65229554104537287196284785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43486369403024858130856523 65229554104537287196284785)
              ·
                refine ⟨48922165578402965397213589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65229554104537287196284785 48922165578402965397213589)
                ·
                  refine ⟨2293226511487639002994387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48922165578402965397213589 2293226511487639002994387)
                  ·
                    refine ⟨3439839767231458504491581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2293226511487639002994387 3439839767231458504491581)
                    ·
                      refine ⟨1289939912711796939184343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3439839767231458504491581 1289939912711796939184343)
                      ·
                        rfl

theorem cell23_2512149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_2512149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512149 prefixEnd_2512149 := by exact prefixLift 2512149
  have htrace : WordTrace (prefixWord ++ tailWord_2512149) baseStart_2512149 baseEnd_2512149 := by
    simpa [prefixWord, tailWord_2512149, baseEnd_2512149] using wordTrace_append hprefix tailTrace_2512149
  have hstable : (prefixWord ++ tailWord_2512149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512149).length < 2 ^ (prefixWord ++ tailWord_2512149).sum := by decide
  have hdescent : baseEnd_2512149 < baseStart_2512149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512170 : List Nat := [3, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3]
def baseStart_2512170 : Nat := 118140960795 + 2512170 * 2 ^ 59
def prefixEnd_2512170 : Nat := 4983230072969 + 3 ^ 40 * 2512170 * 2
def baseEnd_2512170 : Nat := 1289950695805541357021747

theorem tailTrace_2512170 : CollatzResearch.WordTrace tailWord_2512170 prefixEnd_2512170 1289950695805541357021747 := by
  unfold tailWord_2512170
  simp only [CollatzResearch.WordTrace]
  refine ⟨22906591827211152330783491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61084244872563072882089309 22906591827211152330783491)
  ·
    refine ⟨34359887740816728496175237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22906591827211152330783491 34359887740816728496175237)
    ·
      refine ⟨6442478951403136593032857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34359887740816728496175237 6442478951403136593032857)
      ·
        refine ⟨4831859213552352444774643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6442478951403136593032857 4831859213552352444774643)
        ·
          refine ⟨7247788820328528667161965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4831859213552352444774643 7247788820328528667161965)
          ·
            refine ⟨2717920807623198250185737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7247788820328528667161965 2717920807623198250185737)
            ·
              refine ⟨2038440605717398687639303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2717920807623198250185737 2038440605717398687639303)
              ·
                refine ⟨3057660908576098031458955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038440605717398687639303 3057660908576098031458955)
                ·
                  refine ⟨4586491362864147047188433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057660908576098031458955 4586491362864147047188433)
                  ·
                    refine ⟨3439868522148110285391325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4586491362864147047188433 3439868522148110285391325)
                    ·
                      refine ⟨1289950695805541357021747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3439868522148110285391325 1289950695805541357021747)
                      ·
                        rfl

theorem cell23_2512170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3].length) (baseStart_2512170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512170 prefixEnd_2512170 := by exact prefixLift 2512170
  have htrace : WordTrace (prefixWord ++ tailWord_2512170) baseStart_2512170 baseEnd_2512170 := by
    simpa [prefixWord, tailWord_2512170, baseEnd_2512170] using wordTrace_append hprefix tailTrace_2512170
  have hstable : (prefixWord ++ tailWord_2512170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512170).length < 2 ^ (prefixWord ++ tailWord_2512170).sum := by decide
  have hdescent : baseEnd_2512170 < baseStart_2512170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512176 : List Nat := [2, 1, 1, 1, 2, 2, 5, 3, 1, 3, 2]
def baseStart_2512176 : Nat := 118140960795 + 2512176 * 2 ^ 59
def prefixEnd_2512176 : Nat := 4983230072969 + 3 ^ 40 * 2512176 * 2
def baseEnd_2512176 : Nat := 1289953776689468333546719

theorem tailTrace_2512176 : CollatzResearch.WordTrace tailWord_2512176 prefixEnd_2512176 1289953776689468333546719 := by
  unfold tailWord_2512176
  simp only [CollatzResearch.WordTrace]
  refine ⟨45813293073411436173926191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61084390764548581565234921 45813293073411436173926191)
  ·
    refine ⟨68719939610117154260889287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45813293073411436173926191 68719939610117154260889287)
    ·
      refine ⟨103079909415175731391333931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68719939610117154260889287 103079909415175731391333931)
      ·
        refine ⟨154619864122763597087000897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103079909415175731391333931 154619864122763597087000897)
        ·
          refine ⟨115964898092072697815250673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154619864122763597087000897 115964898092072697815250673)
          ·
            refine ⟨86973673569054523361438005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115964898092072697815250673 86973673569054523361438005)
            ·
              refine ⟨8153781897098861565134813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86973673569054523361438005 8153781897098861565134813)
              ·
                refine ⟨3057668211412073086925555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8153781897098861565134813 3057668211412073086925555)
                ·
                  refine ⟨4586502317118109630388333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057668211412073086925555 4586502317118109630388333)
                  ·
                    refine ⟨1719938368919291111395625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4586502317118109630388333 1719938368919291111395625)
                    ·
                      refine ⟨1289953776689468333546719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1719938368919291111395625 1289953776689468333546719)
                      ·
                        rfl

theorem cell23_2512176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 1, 3, 2].length) (baseStart_2512176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512176 prefixEnd_2512176 := by exact prefixLift 2512176
  have htrace : WordTrace (prefixWord ++ tailWord_2512176) baseStart_2512176 baseEnd_2512176 := by
    simpa [prefixWord, tailWord_2512176, baseEnd_2512176] using wordTrace_append hprefix tailTrace_2512176
  have hstable : (prefixWord ++ tailWord_2512176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512176).length < 2 ^ (prefixWord ++ tailWord_2512176).sum := by decide
  have hdescent : baseEnd_2512176 < baseStart_2512176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512276 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_2512276 : Nat := 118140960795 + 2512276 * 2 ^ 59
def prefixEnd_2512276 : Nat := 4983230072969 + 3 ^ 40 * 2512276 * 2
def baseEnd_2512276 : Nat := 430001708251639314098753

theorem tailTrace_2512276 : CollatzResearch.WordTrace tailWord_2512276 prefixEnd_2512276 430001708251639314098753 := by
  unfold tailWord_2512276
  simp only [CollatzResearch.WordTrace]
  refine ⟨45815116723230294713246341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61086822297640392950995121 45815116723230294713246341)
  ·
    refine ⟨8590334385605680258733689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45815116723230294713246341 8590334385605680258733689)
    ·
      refine ⟨6442750789204260194050267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8590334385605680258733689 6442750789204260194050267)
      ·
        refine ⟨9664126183806390291075401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6442750789204260194050267 9664126183806390291075401)
        ·
          refine ⟨7248094637854792718306551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9664126183806390291075401 7248094637854792718306551)
          ·
            refine ⟨10872141956782189077459827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7248094637854792718306551 10872141956782189077459827)
            ·
              refine ⟨16308212935173283616189741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10872141956782189077459827 16308212935173283616189741)
              ·
                refine ⟨6115579850689981356071153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16308212935173283616189741 6115579850689981356071153)
                ·
                  refine ⟨4586684888017486017053365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6115579850689981356071153 4586684888017486017053365)
                  ·
                    refine ⟨430001708251639314098753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4586684888017486017053365 430001708251639314098753)
                    ·
                      rfl

theorem cell23_2512276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_2512276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512276 prefixEnd_2512276 := by exact prefixLift 2512276
  have htrace : WordTrace (prefixWord ++ tailWord_2512276) baseStart_2512276 baseEnd_2512276 := by
    simpa [prefixWord, tailWord_2512276, baseEnd_2512276] using wordTrace_append hprefix tailTrace_2512276
  have hstable : (prefixWord ++ tailWord_2512276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512276).length < 2 ^ (prefixWord ++ tailWord_2512276).sum := by decide
  have hdescent : baseEnd_2512276 < baseStart_2512276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512299 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 3]
def baseStart_2512299 : Nat := 118140960795 + 2512299 * 2 ^ 59
def prefixEnd_2512299 : Nat := 4983230072969 + 3 ^ 40 * 2512299 * 2
def baseEnd_2512299 : Nat := 1290016934809971352308653

theorem tailTrace_2512299 : CollatzResearch.WordTrace tailWord_2512299 prefixEnd_2512299 1290016934809971352308653 := by
  unfold tailWord_2512299
  simp only [CollatzResearch.WordTrace]
  refine ⟨91631072325377264354579951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61087381550251509569719967 91631072325377264354579951)
  ·
    refine ⟨137446608488065896531869927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91631072325377264354579951 137446608488065896531869927)
    ·
      refine ⟨206169912732098844797804891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137446608488065896531869927 206169912732098844797804891)
      ·
        refine ⟨309254869098148267196707337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206169912732098844797804891 309254869098148267196707337)
        ·
          refine ⟨231941151823611200397530503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309254869098148267196707337 231941151823611200397530503)
          ·
            refine ⟨347911727735416800596295755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231941151823611200397530503 347911727735416800596295755)
            ·
              refine ⟨521867591603125200894443633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347911727735416800596295755 521867591603125200894443633)
              ·
                refine ⟨391400693702343900670832725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521867591603125200894443633 391400693702343900670832725)
                ·
                  refine ⟨4586726879324342585986321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 391400693702343900670832725 4586726879324342585986321)
                  ·
                    refine ⟨3440045159493256939489741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4586726879324342585986321 3440045159493256939489741)
                    ·
                      refine ⟨1290016934809971352308653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3440045159493256939489741 1290016934809971352308653)
                      ·
                        rfl

theorem cell23_2512299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 8, 2, 3].length) (baseStart_2512299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512299 prefixEnd_2512299 := by exact prefixLift 2512299
  have htrace : WordTrace (prefixWord ++ tailWord_2512299) baseStart_2512299 baseEnd_2512299 := by
    simpa [prefixWord, tailWord_2512299, baseEnd_2512299] using wordTrace_append hprefix tailTrace_2512299
  have hstable : (prefixWord ++ tailWord_2512299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512299).length < 2 ^ (prefixWord ++ tailWord_2512299).sum := by decide
  have hdescent : baseEnd_2512299 < baseStart_2512299 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512313 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 2, 4, 2]
def baseStart_2512313 : Nat := 118140960795 + 2512313 * 2 ^ 59
def prefixEnd_2512313 : Nat := 4983230072969 + 3 ^ 40 * 2512313 * 2
def baseEnd_2512313 : Nat := 1290024123539134297533589

theorem tailTrace_2512313 : CollatzResearch.WordTrace tailWord_2512313 prefixEnd_2512313 1290024123539134297533589 := by
  unfold tailWord_2512313
  simp only [CollatzResearch.WordTrace]
  refine ⟨91631582947326544745589593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61087721964884363163726395 91631582947326544745589593)
  ·
    refine ⟨68723687210494908559192195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91631582947326544745589593 68723687210494908559192195)
    ·
      refine ⟨103085530815742362838788293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68723687210494908559192195 103085530815742362838788293)
      ·
        refine ⟨19328537027951693032272805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103085530815742362838788293 19328537027951693032272805)
        ·
          refine ⟨3624100692740942443551151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19328537027951693032272805 3624100692740942443551151)
          ·
            refine ⟨5436151039111413665326727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624100692740942443551151 5436151039111413665326727)
            ·
              refine ⟨8154226558667120497990091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5436151039111413665326727 8154226558667120497990091)
              ·
                refine ⟨12231339838000680746985137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8154226558667120497990091 12231339838000680746985137)
                ·
                  refine ⟨9173504878500510560238853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12231339838000680746985137 9173504878500510560238853)
                  ·
                    refine ⟨1720032164718845730044785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9173504878500510560238853 1720032164718845730044785)
                    ·
                      refine ⟨1290024123539134297533589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1720032164718845730044785 1290024123539134297533589)
                      ·
                        rfl

theorem cell23_2512313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_2512313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512313 prefixEnd_2512313 := by exact prefixLift 2512313
  have htrace : WordTrace (prefixWord ++ tailWord_2512313) baseStart_2512313 baseEnd_2512313 := by
    simpa [prefixWord, tailWord_2512313, baseEnd_2512313] using wordTrace_append hprefix tailTrace_2512313
  have hstable : (prefixWord ++ tailWord_2512313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512313).length < 2 ^ (prefixWord ++ tailWord_2512313).sum := by decide
  have hdescent : baseEnd_2512313 < baseStart_2512313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512389 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 5]
def baseStart_2512389 : Nat := 118140960795 + 2512389 * 2 ^ 59
def prefixEnd_2512389 : Nat := 4983230072969 + 3 ^ 40 * 2512389 * 2
def baseEnd_2512389 : Nat := 1290063148068876000183239

theorem tailTrace_2512389 : CollatzResearch.WordTrace tailWord_2512389 prefixEnd_2512389 1290063148068876000183239 := by
  unfold tailWord_2512389
  simp only [CollatzResearch.WordTrace]
  refine ⟨91634354895051209725356221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61089569930034139816904147 91634354895051209725356221)
  ·
    refine ⟨34362883085644203647008583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91634354895051209725356221 34362883085644203647008583)
    ·
      refine ⟨51544324628466305470512875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34362883085644203647008583 51544324628466305470512875)
      ·
        refine ⟨77316486942699458205769313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51544324628466305470512875 77316486942699458205769313)
        ·
          refine ⟨57987365207024593654326985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77316486942699458205769313 57987365207024593654326985)
          ·
            refine ⟨43490523905268445240745239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57987365207024593654326985 43490523905268445240745239)
            ·
              refine ⟨65235785857902667861117859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43490523905268445240745239 65235785857902667861117859)
              ·
                refine ⟨97853678786854001791676789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65235785857902667861117859 97853678786854001791676789)
                ·
                  refine ⟨9173782386267562667969699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97853678786854001791676789 9173782386267562667969699)
                  ·
                    refine ⟨13760673579401344001954549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9173782386267562667969699 13760673579401344001954549)
                    ·
                      refine ⟨1290063148068876000183239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13760673579401344001954549 1290063148068876000183239)
                      ·
                        rfl

theorem cell23_2512389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 5].length) (baseStart_2512389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512389 prefixEnd_2512389 := by exact prefixLift 2512389
  have htrace : WordTrace (prefixWord ++ tailWord_2512389) baseStart_2512389 baseEnd_2512389 := by
    simpa [prefixWord, tailWord_2512389, baseEnd_2512389] using wordTrace_append hprefix tailTrace_2512389
  have hstable : (prefixWord ++ tailWord_2512389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512389).length < 2 ^ (prefixWord ++ tailWord_2512389).sum := by decide
  have hdescent : baseEnd_2512389 < baseStart_2512389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512413 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 2, 4]
def baseStart_2512413 : Nat := 118140960795 + 2512413 * 2 ^ 59
def prefixEnd_2512413 : Nat := 4983230072969 + 3 ^ 40 * 2512413 * 2
def baseEnd_2512413 : Nat := 430025157201527968761043

theorem tailTrace_2512413 : CollatzResearch.WordTrace tailWord_2512413 prefixEnd_2512413 430025157201527968761043 := by
  unfold tailWord_2512413
  simp only [CollatzResearch.WordTrace]
  refine ⟨91635230246964261824229893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61090153497976174549486595 91635230246964261824229893)
  ·
    refine ⟨17181605671305799092043105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91635230246964261824229893 17181605671305799092043105)
    ·
      refine ⟨12886204253479349319032329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17181605671305799092043105 12886204253479349319032329)
      ·
        refine ⟨9664653190109511989274247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12886204253479349319032329 9664653190109511989274247)
        ·
          refine ⟨14496979785164267983911371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9664653190109511989274247 14496979785164267983911371)
          ·
            refine ⟨21745469677746401975867057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14496979785164267983911371 21745469677746401975867057)
            ·
              refine ⟨16309102258309801481900293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21745469677746401975867057 16309102258309801481900293)
              ·
                refine ⟨3057956673433087777856305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16309102258309801481900293 3057956673433087777856305)
                ·
                  refine ⟨2293467505074815833392229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3057956673433087777856305 2293467505074815833392229)
                  ·
                    refine ⟨430025157201527968761043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293467505074815833392229 430025157201527968761043)
                    ·
                      rfl

theorem cell23_2512413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 4].length) (baseStart_2512413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512413 prefixEnd_2512413 := by exact prefixLift 2512413
  have htrace : WordTrace (prefixWord ++ tailWord_2512413) baseStart_2512413 baseEnd_2512413 := by
    simpa [prefixWord, tailWord_2512413, baseEnd_2512413] using wordTrace_append hprefix tailTrace_2512413
  have hstable : (prefixWord ++ tailWord_2512413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512413).length < 2 ^ (prefixWord ++ tailWord_2512413).sum := by decide
  have hdescent : baseEnd_2512413 < baseStart_2512413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512416 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_2512416 : Nat := 118140960795 + 2512416 * 2 ^ 59
def prefixEnd_2512416 : Nat := 4983230072969 + 3 ^ 40 * 2512416 * 2
def baseEnd_2512416 : Nat := 1290077012046547394545615

theorem tailTrace_2512416 : CollatzResearch.WordTrace tailWord_2512416 prefixEnd_2512416 1290077012046547394545615 := by
  unfold tailWord_2512416
  simp only [CollatzResearch.WordTrace]
  refine ⟨45817669832976696668294551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61090226443968928891059401 45817669832976696668294551)
  ·
    refine ⟨68726504749465045002441827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45817669832976696668294551 68726504749465045002441827)
    ·
      refine ⟨103089757124197567503662741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68726504749465045002441827 103089757124197567503662741)
      ·
        refine ⟨4832332365196760976734191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103089757124197567503662741 4832332365196760976734191)
        ·
          refine ⟨7248498547795141465101287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4832332365196760976734191 7248498547795141465101287)
          ·
            refine ⟨10872747821692712197651931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7248498547795141465101287 10872747821692712197651931)
            ·
              refine ⟨16309121732539068296477897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10872747821692712197651931 16309121732539068296477897)
              ·
                refine ⟨12231841299404301222358423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16309121732539068296477897 12231841299404301222358423)
                ·
                  refine ⟨18347761949106451833537635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12231841299404301222358423 18347761949106451833537635)
                  ·
                    refine ⟨27521642923659677750306453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18347761949106451833537635 27521642923659677750306453)
                    ·
                      refine ⟨1290077012046547394545615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27521642923659677750306453 1290077012046547394545615)
                      ·
                        rfl

theorem cell23_2512416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_2512416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512416 prefixEnd_2512416 := by exact prefixLift 2512416
  have htrace : WordTrace (prefixWord ++ tailWord_2512416) baseStart_2512416 baseEnd_2512416 := by
    simpa [prefixWord, tailWord_2512416, baseEnd_2512416] using wordTrace_append hprefix tailTrace_2512416
  have hstable : (prefixWord ++ tailWord_2512416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512416).length < 2 ^ (prefixWord ++ tailWord_2512416).sum := by decide
  have hdescent : baseEnd_2512416 < baseStart_2512416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512426 : List Nat := [3, 1, 4, 1, 1, 1, 4, 8]
def baseStart_2512426 : Nat := 118140960795 + 2512426 * 2 ^ 59
def prefixEnd_2512426 : Nat := 4983230072969 + 3 ^ 40 * 2512426 * 2
def baseEnd_2512426 : Nat := 47780820253818235385947

theorem tailTrace_2512426 : CollatzResearch.WordTrace tailWord_2512426 prefixEnd_2512426 47780820253818235385947 := by
  unfold tailWord_2512426
  simp only [CollatzResearch.WordTrace]
  refine ⟨22908926098979291261113283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61090469597278110029635421 22908926098979291261113283)
  ·
    refine ⟨34363389148468936891669925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22908926098979291261113283 34363389148468936891669925)
    ·
      refine ⟨6443135465337925667188111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34363389148468936891669925 6443135465337925667188111)
      ·
        refine ⟨9664703198006888500782167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6443135465337925667188111 9664703198006888500782167)
        ·
          refine ⟨14497054797010332751173251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9664703198006888500782167 14497054797010332751173251)
          ·
            refine ⟨21745582195515499126759877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14497054797010332751173251 21745582195515499126759877)
            ·
              refine ⟨4077296661659156086267477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21745582195515499126759877 4077296661659156086267477)
              ·
                refine ⟨47780820253818235385947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4077296661659156086267477 47780820253818235385947)
                ·
                  rfl

theorem cell23_2512426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 8].length) (baseStart_2512426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512426 prefixEnd_2512426 := by exact prefixLift 2512426
  have htrace : WordTrace (prefixWord ++ tailWord_2512426) baseStart_2512426 baseEnd_2512426 := by
    simpa [prefixWord, tailWord_2512426, baseEnd_2512426] using wordTrace_append hprefix tailTrace_2512426
  have hstable : (prefixWord ++ tailWord_2512426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512426).length < 2 ^ (prefixWord ++ tailWord_2512426).sum := by decide
  have hdescent : baseEnd_2512426 < baseStart_2512426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512430 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 2, 4]
def baseStart_2512430 : Nat := 118140960795 + 2512430 * 2 ^ 59
def prefixEnd_2512430 : Nat := 4983230072969 + 3 ^ 40 * 2512430 * 2
def baseEnd_2512430 : Nat := 430028066925236779923517

theorem tailTrace_2512430 : CollatzResearch.WordTrace tailWord_2512430 prefixEnd_2512430 430028066925236779923517 := by
  unfold tailWord_2512430
  simp only [CollatzResearch.WordTrace]
  refine ⟨11454481285987834215949843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61090566858601782485065829 11454481285987834215949843)
  ·
    refine ⟨17181721928981751323924765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11454481285987834215949843 17181721928981751323924765)
    ·
      refine ⟨6443145723368156746471787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17181721928981751323924765 6443145723368156746471787)
      ·
        refine ⟨9664718585052235119707681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6443145723368156746471787 9664718585052235119707681)
        ·
          refine ⟨7248538938789176339780761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9664718585052235119707681 7248538938789176339780761)
          ·
            refine ⟨5436404204091882254835571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7248538938789176339780761 5436404204091882254835571)
            ·
              refine ⟨8154606306137823382253357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5436404204091882254835571 8154606306137823382253357)
              ·
                refine ⟨3057977364801683768345009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8154606306137823382253357 3057977364801683768345009)
                ·
                  refine ⟨2293483023601262826258757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3057977364801683768345009 2293483023601262826258757)
                  ·
                    refine ⟨430028066925236779923517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2293483023601262826258757 430028066925236779923517)
                    ·
                      rfl

theorem cell23_2512430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_2512430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512430 prefixEnd_2512430 := by exact prefixLift 2512430
  have htrace : WordTrace (prefixWord ++ tailWord_2512430) baseStart_2512430 baseEnd_2512430 := by
    simpa [prefixWord, tailWord_2512430, baseEnd_2512430] using wordTrace_append hprefix tailTrace_2512430
  have hstable : (prefixWord ++ tailWord_2512430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512430).length < 2 ^ (prefixWord ++ tailWord_2512430).sum := by decide
  have hdescent : baseEnd_2512430 < baseStart_2512430 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512440 : List Nat := [2, 1, 2, 1, 4, 4, 1, 2, 1, 2, 3]
def baseStart_2512440 : Nat := 118140960795 + 2512440 * 2 ^ 59
def prefixEnd_2512440 : Nat := 4983230072969 + 3 ^ 40 * 2512440 * 2
def baseEnd_2512440 : Nat := 1290089335582255300645505

theorem tailTrace_2512440 : CollatzResearch.WordTrace tailWord_2512440 prefixEnd_2512440 1290089335582255300645505 := by
  unfold tailWord_2512440
  simp only [CollatzResearch.WordTrace]
  refine ⟨45818107508933222717731387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61090810011910963623641849 45818107508933222717731387)
  ·
    refine ⟨68727161263399834076597081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45818107508933222717731387 68727161263399834076597081)
    ·
      refine ⟨51545370947549875557447811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68727161263399834076597081 51545370947549875557447811)
      ·
        refine ⟨77318056421324813336171717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51545370947549875557447811 77318056421324813336171717)
        ·
          refine ⟨14497135578998402500532197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77318056421324813336171717 14497135578998402500532197)
          ·
            refine ⟨2718212921062200468849787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14497135578998402500532197 2718212921062200468849787)
            ·
              refine ⟨4077319381593300703274681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718212921062200468849787 4077319381593300703274681)
              ·
                refine ⟨3057989536194975527456011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4077319381593300703274681 3057989536194975527456011)
                ·
                  refine ⟨4586984304292463291184017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057989536194975527456011 4586984304292463291184017)
                  ·
                    refine ⟨3440238228219347468388013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4586984304292463291184017 3440238228219347468388013)
                    ·
                      refine ⟨1290089335582255300645505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3440238228219347468388013 1290089335582255300645505)
                      ·
                        rfl

theorem cell23_2512440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_2512440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512440 prefixEnd_2512440 := by exact prefixLift 2512440
  have htrace : WordTrace (prefixWord ++ tailWord_2512440) baseStart_2512440 baseEnd_2512440 := by
    simpa [prefixWord, tailWord_2512440, baseEnd_2512440] using wordTrace_append hprefix tailTrace_2512440
  have hstable : (prefixWord ++ tailWord_2512440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512440).length < 2 ^ (prefixWord ++ tailWord_2512440).sum := by decide
  have hdescent : baseEnd_2512440 < baseStart_2512440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512454 : List Nat := [6, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_2512454 : Nat := 118140960795 + 2512454 * 2 ^ 59
def prefixEnd_2512454 : Nat := 4983230072969 + 3 ^ 40 * 2512454 * 2
def baseEnd_2512454 : Nat := 1290096524311418245870441

theorem tailTrace_2512454 : CollatzResearch.WordTrace tailWord_2512454 prefixEnd_2512454 1290096524311418245870441 := by
  unfold tailWord_2512454
  simp only [CollatzResearch.WordTrace]
  refine ⟨2863647676244241432077263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61091150426543817217648277 2863647676244241432077263)
  ·
    refine ⟨4295471514366362148115895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2863647676244241432077263 4295471514366362148115895)
    ·
      refine ⟨6443207271549543222173843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4295471514366362148115895 6443207271549543222173843)
      ·
        refine ⟨9664810907324314833260765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6443207271549543222173843 9664810907324314833260765)
        ·
          refine ⟨3624304090246618062472787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9664810907324314833260765 3624304090246618062472787)
          ·
            refine ⟨5436456135369927093709181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3624304090246618062472787 5436456135369927093709181)
            ·
              refine ⟨2038671050763722660140943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5436456135369927093709181 2038671050763722660140943)
              ·
                refine ⟨3058006576145583990211415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2038671050763722660140943 3058006576145583990211415)
                ·
                  refine ⟨4587009864218375985317123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3058006576145583990211415 4587009864218375985317123)
                  ·
                    refine ⟨6880514796327563977975685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4587009864218375985317123 6880514796327563977975685)
                    ·
                      refine ⟨1290096524311418245870441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6880514796327563977975685 1290096524311418245870441)
                      ·
                        rfl

theorem cell23_2512454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_2512454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512454 prefixEnd_2512454 := by exact prefixLift 2512454
  have htrace : WordTrace (prefixWord ++ tailWord_2512454) baseStart_2512454 baseEnd_2512454 := by
    simpa [prefixWord, tailWord_2512454, baseEnd_2512454] using wordTrace_append hprefix tailTrace_2512454
  have hstable : (prefixWord ++ tailWord_2512454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512454).length < 2 ^ (prefixWord ++ tailWord_2512454).sum := by decide
  have hdescent : baseEnd_2512454 < baseStart_2512454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2512477 : List Nat := [1, 4, 4, 2, 2, 1, 1, 8]
def baseStart_2512477 : Nat := 118140960795 + 2512477 * 2 ^ 59
def prefixEnd_2512477 : Nat := 4983230072969 + 3 ^ 40 * 2512477 * 2
def baseEnd_2512477 : Nat := 47781790161721172440105

theorem tailTrace_2512477 : CollatzResearch.WordTrace tailWord_2512477 prefixEnd_2512477 47781790161721172440105 := by
  unfold tailWord_2512477
  simp only [CollatzResearch.WordTrace]
  refine ⟨91637564518732400754559685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61091709679154933836373123 91637564518732400754559685)
  ·
    refine ⟨17182043347262325141479941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91637564518732400754559685 17182043347262325141479941)
    ·
      refine ⟨3221633127611685964027489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17182043347262325141479941 3221633127611685964027489)
      ·
        refine ⟨2416224845708764473020617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3221633127611685964027489 2416224845708764473020617)
        ·
          refine ⟨1812168634281573354765463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2416224845708764473020617 1812168634281573354765463)
          ·
            refine ⟨2718252951422360032148195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1812168634281573354765463 2718252951422360032148195)
            ·
              refine ⟨4077379427133540048222293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2718252951422360032148195 4077379427133540048222293)
              ·
                refine ⟨47781790161721172440105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4077379427133540048222293 47781790161721172440105)
                ·
                  rfl

theorem cell23_2512477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 8].length) (baseStart_2512477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2512477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2512477 prefixEnd_2512477 := by exact prefixLift 2512477
  have htrace : WordTrace (prefixWord ++ tailWord_2512477) baseStart_2512477 baseEnd_2512477 := by
    simpa [prefixWord, tailWord_2512477, baseEnd_2512477] using wordTrace_append hprefix tailTrace_2512477
  have hstable : (prefixWord ++ tailWord_2512477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2512477).length < 2 ^ (prefixWord ++ tailWord_2512477).sum := by decide
  have hdescent : baseEnd_2512477 < baseStart_2512477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2512477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
