import V185TrunkScan23Chunk0896

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5309752 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 5, 3, 2]
def baseStart_5309752 : Nat := 118140960795 + 5309752 * 2 ^ 59
def prefixEnd_5309752 : Nat := 4983230072969 + 3 ^ 40 * 5309752 * 2
def baseEnd_5309752 : Nat := 2726454932172014804580901

theorem tailTrace_5309752 : CollatzResearch.WordTrace tailWord_5309752 prefixEnd_5309752 2726454932172014804580901 := by
  unfold tailWord_5309752
  simp only [CollatzResearch.WordTrace]
  refine ⟨96831282729841406145005755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129108376973121874860007673 96831282729841406145005755)
  ·
    refine ⟨145246924094762109217508633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96831282729841406145005755 145246924094762109217508633)
    ·
      refine ⟨108935193071071581913131475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145246924094762109217508633 108935193071071581913131475)
      ·
        refine ⟨163402789606607372869697213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108935193071071581913131475 163402789606607372869697213)
        ·
          refine ⟨61276046102477764826136455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163402789606607372869697213 61276046102477764826136455)
          ·
            refine ⟨91914069153716647239204683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61276046102477764826136455 91914069153716647239204683)
            ·
              refine ⟨137871103730574970858807025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91914069153716647239204683 137871103730574970858807025)
              ·
                refine ⟨103403327797931228144105269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137871103730574970858807025 103403327797931228144105269)
                ·
                  refine ⟨9694061981056052638509869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103403327797931228144105269 9694061981056052638509869)
                  ·
                    refine ⟨3635273242896019739441201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9694061981056052638509869 3635273242896019739441201)
                    ·
                      refine ⟨2726454932172014804580901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635273242896019739441201 2726454932172014804580901)
                      ·
                        rfl

theorem cell23_5309752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 5, 3, 2].length) (baseStart_5309752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309752 prefixEnd_5309752 := by exact prefixLift 5309752
  have htrace : WordTrace (prefixWord ++ tailWord_5309752) baseStart_5309752 baseEnd_5309752 := by
    simpa [prefixWord, tailWord_5309752, baseEnd_5309752] using wordTrace_append hprefix tailTrace_5309752
  have hstable : (prefixWord ++ tailWord_5309752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309752).length < 2 ^ (prefixWord ++ tailWord_5309752).sum := by decide
  have hdescent : baseEnd_5309752 < baseStart_5309752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309766 : List Nat := [6, 1, 1, 3, 1, 1, 2, 8]
def baseStart_5309766 : Nat := 118140960795 + 5309766 * 2 ^ 59
def prefixEnd_5309766 : Nat := 4983230072969 + 3 ^ 40 * 5309766 * 2
def baseEnd_5309766 : Nat := 100980078551895472215031

theorem tailTrace_5309766 : CollatzResearch.WordTrace tailWord_5309766 prefixEnd_5309766 100980078551895472215031 := by
  unfold tailWord_5309766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6051971127551002896281911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129108717387754728454014101 6051971127551002896281911)
  ·
    refine ⟨9077956691326504344422867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6051971127551002896281911 9077956691326504344422867)
    ·
      refine ⟨13616935036989756516634301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9077956691326504344422867 13616935036989756516634301)
      ·
        refine ⟨5106350638871158693737863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13616935036989756516634301 5106350638871158693737863)
        ·
          refine ⟨7659525958306738040606795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5106350638871158693737863 7659525958306738040606795)
          ·
            refine ⟨11489288937460107060910193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7659525958306738040606795 11489288937460107060910193)
            ·
              refine ⟨8616966703095080295682645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11489288937460107060910193 8616966703095080295682645)
              ·
                refine ⟨100980078551895472215031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8616966703095080295682645 100980078551895472215031)
                ·
                  rfl

theorem cell23_5309766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_5309766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309766 prefixEnd_5309766 := by exact prefixLift 5309766
  have htrace : WordTrace (prefixWord ++ tailWord_5309766) baseStart_5309766 baseEnd_5309766 := by
    simpa [prefixWord, tailWord_5309766, baseEnd_5309766] using wordTrace_append hprefix tailTrace_5309766
  have hstable : (prefixWord ++ tailWord_5309766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309766).length < 2 ^ (prefixWord ++ tailWord_5309766).sum := by decide
  have hdescent : baseEnd_5309766 < baseStart_5309766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309785 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 5]
def baseStart_5309785 : Nat := 118140960795 + 5309785 * 2 ^ 59
def prefixEnd_5309785 : Nat := 4983230072969 + 3 ^ 40 * 5309785 * 2
def baseEnd_5309785 : Nat := 2726471877033613175468249

theorem tailTrace_5309785 : CollatzResearch.WordTrace tailWord_5309785 prefixEnd_5309785 2726471877033613175468249 := by
  unfold tailWord_5309785
  simp only [CollatzResearch.WordTrace]
  refine ⟨193663769068563258925962809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129109179379042172617308539 193663769068563258925962809)
  ·
    refine ⟨145247826801422444194472107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193663769068563258925962809 145247826801422444194472107)
    ·
      refine ⟨217871740202133666291708161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145247826801422444194472107 217871740202133666291708161)
      ·
        refine ⟨163403805151600249718781121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217871740202133666291708161 163403805151600249718781121)
        ·
          refine ⟨122552853863700187289085841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163403805151600249718781121 122552853863700187289085841)
          ·
            refine ⟨91914640397775140466814381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122552853863700187289085841 91914640397775140466814381)
            ·
              refine ⟨34467990149165677675055393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91914640397775140466814381 34467990149165677675055393)
              ·
                refine ⟨25850992611874258256291545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34467990149165677675055393 25850992611874258256291545)
                ·
                  refine ⟨19388244458905693692218659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25850992611874258256291545 19388244458905693692218659)
                  ·
                    refine ⟨29082366688358540538327989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19388244458905693692218659 29082366688358540538327989)
                    ·
                      refine ⟨2726471877033613175468249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29082366688358540538327989 2726471877033613175468249)
                      ·
                        rfl

theorem cell23_5309785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 5].length) (baseStart_5309785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309785 prefixEnd_5309785 := by exact prefixLift 5309785
  have htrace : WordTrace (prefixWord ++ tailWord_5309785) baseStart_5309785 baseEnd_5309785 := by
    simpa [prefixWord, tailWord_5309785, baseEnd_5309785] using wordTrace_append hprefix tailTrace_5309785
  have hstable : (prefixWord ++ tailWord_5309785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309785).length < 2 ^ (prefixWord ++ tailWord_5309785).sum := by decide
  have hdescent : baseEnd_5309785 < baseStart_5309785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309832 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 1, 5, 3]
def baseStart_5309832 : Nat := 118140960795 + 5309832 * 2 ^ 59
def prefixEnd_5309832 : Nat := 4983230072969 + 3 ^ 40 * 5309832 * 2
def baseEnd_5309832 : Nat := 2726496010624374491580533

theorem tailTrace_5309832 : CollatzResearch.WordTrace tailWord_5309832 prefixEnd_5309832 2726496010624374491580533 := by
  unfold tailWord_5309832
  simp only [CollatzResearch.WordTrace]
  refine ⟨96832741649696492976461875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129110322199595323968615833 96832741649696492976461875)
  ·
    refine ⟨145249112474544739464692813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96832741649696492976461875 145249112474544739464692813)
    ·
      refine ⟨54468417177954277299259805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145249112474544739464692813 54468417177954277299259805)
      ·
        refine ⟨20425656441732853987222427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54468417177954277299259805 20425656441732853987222427)
        ·
          refine ⟨30638484662599280980833641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20425656441732853987222427 30638484662599280980833641)
          ·
            refine ⟨22978863496949460735625231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30638484662599280980833641 22978863496949460735625231)
            ·
              refine ⟨34468295245424191103437847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22978863496949460735625231 34468295245424191103437847)
              ·
                refine ⟨51702442868136286655156771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34468295245424191103437847 51702442868136286655156771)
                ·
                  refine ⟨77553664302204429982735157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51702442868136286655156771 77553664302204429982735157)
                  ·
                    refine ⟨7270656028331665310881421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77553664302204429982735157 7270656028331665310881421)
                    ·
                      refine ⟨2726496010624374491580533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7270656028331665310881421 2726496010624374491580533)
                      ·
                        rfl

theorem cell23_5309832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 1, 5, 3].length) (baseStart_5309832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309832 prefixEnd_5309832 := by exact prefixLift 5309832
  have htrace : WordTrace (prefixWord ++ tailWord_5309832) baseStart_5309832 baseEnd_5309832 := by
    simpa [prefixWord, tailWord_5309832, baseEnd_5309832] using wordTrace_append hprefix tailTrace_5309832
  have hstable : (prefixWord ++ tailWord_5309832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309832).length < 2 ^ (prefixWord ++ tailWord_5309832).sum := by decide
  have hdescent : baseEnd_5309832 < baseStart_5309832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309835 : List Nat := [1, 1, 1, 1, 4, 3, 2, 2, 1, 7]
def baseStart_5309835 : Nat := 118140960795 + 5309835 * 2 ^ 59
def prefixEnd_5309835 : Nat := 4983230072969 + 3 ^ 40 * 5309835 * 2
def baseEnd_5309835 : Nat := 908832517022112659947673

theorem tailTrace_5309835 : CollatzResearch.WordTrace tailWord_5309835 prefixEnd_5309835 908832517022112659947673 := by
  unfold tailWord_5309835
  simp only [CollatzResearch.WordTrace]
  refine ⟨193665592718382117465282959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129110395145588078310188639 193665592718382117465282959)
  ·
    refine ⟨290498389077573176197924439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193665592718382117465282959 290498389077573176197924439)
    ·
      refine ⟨435747583616359764296886659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290498389077573176197924439 435747583616359764296886659)
      ·
        refine ⟨653621375424539646445329989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435747583616359764296886659 653621375424539646445329989)
        ·
          refine ⟨122554007892101183708499373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 653621375424539646445329989 122554007892101183708499373)
          ·
            refine ⟨45957752959537943890687265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122554007892101183708499373 45957752959537943890687265)
            ·
              refine ⟨34468314719653457918015449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45957752959537943890687265 34468314719653457918015449)
              ·
                refine ⟨25851236039740093438511587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34468314719653457918015449 25851236039740093438511587)
                ·
                  refine ⟨38776854059610140157767381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25851236039740093438511587 38776854059610140157767381)
                  ·
                    refine ⟨908832517022112659947673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38776854059610140157767381 908832517022112659947673)
                    ·
                      rfl

theorem cell23_5309835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 7].length) (baseStart_5309835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309835 prefixEnd_5309835 := by exact prefixLift 5309835
  have htrace : WordTrace (prefixWord ++ tailWord_5309835) baseStart_5309835 baseEnd_5309835 := by
    simpa [prefixWord, tailWord_5309835, baseEnd_5309835] using wordTrace_append hprefix tailTrace_5309835
  have hstable : (prefixWord ++ tailWord_5309835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309835).length < 2 ^ (prefixWord ++ tailWord_5309835).sum := by decide
  have hdescent : baseEnd_5309835 < baseStart_5309835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309845 : List Nat := [1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 7]
def baseStart_5309845 : Nat := 118140960795 + 5309845 * 2 ^ 59
def prefixEnd_5309845 : Nat := 4983230072969 + 3 ^ 40 * 5309845 * 2
def baseEnd_5309845 : Nat := 2726502685872882940717973

theorem tailTrace_5309845 : CollatzResearch.WordTrace tailWord_5309845 prefixEnd_5309845 2726502685872882940717973 := by
  unfold tailWord_5309845
  simp only [CollatzResearch.WordTrace]
  refine ⟨193665957448345889173146989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129110638298897259448764659 193665957448345889173146989)
  ·
    refine ⟨72624734043129708439930121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193665957448345889173146989 72624734043129708439930121)
    ·
      refine ⟨54468550532347281329947591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72624734043129708439930121 54468550532347281329947591)
      ·
        refine ⟨81702825798520921994921387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54468550532347281329947591 81702825798520921994921387)
        ·
          refine ⟨122554238697781382992382081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81702825798520921994921387 122554238697781382992382081)
          ·
            refine ⟨91915679023336037244286561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122554238697781382992382081 91915679023336037244286561)
            ·
              refine ⟨68936759267502027933214921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91915679023336037244286561 68936759267502027933214921)
              ·
                refine ⟨51702569450626520949911191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68936759267502027933214921 51702569450626520949911191)
                ·
                  refine ⟨77553854175939781424866787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51702569450626520949911191 77553854175939781424866787)
                  ·
                    refine ⟨116330781263909672137300181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77553854175939781424866787 116330781263909672137300181)
                    ·
                      refine ⟨2726502685872882940717973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116330781263909672137300181 2726502685872882940717973)
                      ·
                        rfl

theorem cell23_5309845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_5309845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309845 prefixEnd_5309845 := by exact prefixLift 5309845
  have htrace : WordTrace (prefixWord ++ tailWord_5309845) baseStart_5309845 baseEnd_5309845 := by
    simpa [prefixWord, tailWord_5309845, baseEnd_5309845] using wordTrace_append hprefix tailTrace_5309845
  have hstable : (prefixWord ++ tailWord_5309845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309845).length < 2 ^ (prefixWord ++ tailWord_5309845).sum := by decide
  have hdescent : baseEnd_5309845 < baseStart_5309845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309875 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 5]
def baseStart_5309875 : Nat := 118140960795 + 5309875 * 2 ^ 59
def prefixEnd_5309875 : Nat := 4983230072969 + 3 ^ 40 * 5309875 * 2
def baseEnd_5309875 : Nat := 2726518090292517823342835

theorem tailTrace_5309875 : CollatzResearch.WordTrace tailWord_5309875 prefixEnd_5309875 2726518090292517823342835 := by
  unfold tailWord_5309875
  simp only [CollatzResearch.WordTrace]
  refine ⟨193667051638237204296739079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129111367758824802864492719 193667051638237204296739079)
  ·
    refine ⟨290500577457355806445108619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193667051638237204296739079 290500577457355806445108619)
    ·
      refine ⟨435750866186033709667662929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290500577457355806445108619 435750866186033709667662929)
      ·
        refine ⟨326813149639525282250747197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435750866186033709667662929 326813149639525282250747197)
        ·
          refine ⟨122554931114821980844030199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326813149639525282250747197 122554931114821980844030199)
          ·
            refine ⟨183832396672232971266045299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122554931114821980844030199 183832396672232971266045299)
            ·
              refine ⟨275748595008349456899067949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183832396672232971266045299 275748595008349456899067949)
              ·
                refine ⟨103405723128131046337150481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 275748595008349456899067949 103405723128131046337150481)
                ·
                  refine ⟨77554292346098284752862861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103405723128131046337150481 77554292346098284752862861)
                  ·
                    refine ⟨29082859629786856782323573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77554292346098284752862861 29082859629786856782323573)
                    ·
                      refine ⟨2726518090292517823342835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29082859629786856782323573 2726518090292517823342835)
                      ·
                        rfl

theorem cell23_5309875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 3, 5].length) (baseStart_5309875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309875 prefixEnd_5309875 := by exact prefixLift 5309875
  have htrace : WordTrace (prefixWord ++ tailWord_5309875) baseStart_5309875 baseEnd_5309875 := by
    simpa [prefixWord, tailWord_5309875, baseEnd_5309875] using wordTrace_append hprefix tailTrace_5309875
  have hstable : (prefixWord ++ tailWord_5309875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309875).length < 2 ^ (prefixWord ++ tailWord_5309875).sum := by decide
  have hdescent : baseEnd_5309875 < baseStart_5309875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309905 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 9]
def baseStart_5309905 : Nat := 118140960795 + 5309905 * 2 ^ 59
def prefixEnd_5309905 : Nat := 4983230072969 + 3 ^ 40 * 5309905 * 2
def baseEnd_5309905 : Nat := 2726533494712152705967697

theorem tailTrace_5309905 : CollatzResearch.WordTrace tailWord_5309905 prefixEnd_5309905 2726533494712152705967697 := by
  unfold tailWord_5309905
  simp only [CollatzResearch.WordTrace]
  refine ⟨193668145828128519420331169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129112097218752346280220779 193668145828128519420331169)
  ·
    refine ⟨145251109371096389565248377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193668145828128519420331169 145251109371096389565248377)
    ·
      refine ⟨108938332028322292173936283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145251109371096389565248377 108938332028322292173936283)
      ·
        refine ⟨163407498042483438260904425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108938332028322292173936283 163407498042483438260904425)
        ·
          refine ⟨122555623531862578695678319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163407498042483438260904425 122555623531862578695678319)
          ·
            refine ⟨183833435297793868043517479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122555623531862578695678319 183833435297793868043517479)
            ·
              refine ⟨275750152946690802065276219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183833435297793868043517479 275750152946690802065276219)
              ·
                refine ⟨413625229420036203097914329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275750152946690802065276219 413625229420036203097914329)
                ·
                  refine ⟨310218922065027152323435747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 413625229420036203097914329 310218922065027152323435747)
                  ·
                    refine ⟨465328383097540728485153621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 310218922065027152323435747 465328383097540728485153621)
                    ·
                      refine ⟨2726533494712152705967697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 465328383097540728485153621 2726533494712152705967697)
                      ·
                        rfl

theorem cell23_5309905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_5309905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309905 prefixEnd_5309905 := by exact prefixLift 5309905
  have htrace : WordTrace (prefixWord ++ tailWord_5309905) baseStart_5309905 baseEnd_5309905 := by
    simpa [prefixWord, tailWord_5309905, baseEnd_5309905] using wordTrace_append hprefix tailTrace_5309905
  have hstable : (prefixWord ++ tailWord_5309905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309905).length < 2 ^ (prefixWord ++ tailWord_5309905).sum := by decide
  have hdescent : baseEnd_5309905 < baseStart_5309905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309909 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 3]
def baseStart_5309909 : Nat := 118140960795 + 5309909 * 2 ^ 59
def prefixEnd_5309909 : Nat := 4983230072969 + 3 ^ 40 * 5309909 * 2
def baseEnd_5309909 : Nat := 2726535548634770690317679

theorem tailTrace_5309909 : CollatzResearch.WordTrace tailWord_5309909 prefixEnd_5309909 2726535548634770690317679 := by
  unfold tailWord_5309909
  simp only [CollatzResearch.WordTrace]
  refine ⟨193668291720114028103476781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129112194480076018735651187 193668291720114028103476781)
  ·
    refine ⟨72625609395042760538803793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193668291720114028103476781 72625609395042760538803793)
    ·
      refine ⟨54469207046282070404102845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72625609395042760538803793 54469207046282070404102845)
      ·
        refine ⟨20425952642355776401538567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54469207046282070404102845 20425952642355776401538567)
        ·
          refine ⟨30638928963533664602307851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20425952642355776401538567 30638928963533664602307851)
          ·
            refine ⟨45958393445300496903461777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30638928963533664602307851 45958393445300496903461777)
            ·
              refine ⟨34468795083975372677596333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45958393445300496903461777 34468795083975372677596333)
              ·
                refine ⟨12925798156490764754098625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34468795083975372677596333 12925798156490764754098625)
                ·
                  refine ⟨9694348617368073565573969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12925798156490764754098625 9694348617368073565573969)
                  ·
                    refine ⟨7270761463026055174180477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9694348617368073565573969 7270761463026055174180477)
                    ·
                      refine ⟨2726535548634770690317679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7270761463026055174180477 2726535548634770690317679)
                      ·
                        rfl

theorem cell23_5309909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_5309909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309909 prefixEnd_5309909 := by exact prefixLift 5309909
  have htrace : WordTrace (prefixWord ++ tailWord_5309909) baseStart_5309909 baseEnd_5309909 := by
    simpa [prefixWord, tailWord_5309909, baseEnd_5309909] using wordTrace_append hprefix tailTrace_5309909
  have hstable : (prefixWord ++ tailWord_5309909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309909).length < 2 ^ (prefixWord ++ tailWord_5309909).sum := by decide
  have hdescent : baseEnd_5309909 < baseStart_5309909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309933 : List Nat := [1, 5, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_5309933 : Nat := 118140960795 + 5309933 * 2 ^ 59
def prefixEnd_5309933 : Nat := 4983230072969 + 3 ^ 40 * 5309933 * 2
def baseEnd_5309933 : Nat := 908849290723492865472523

theorem tailTrace_5309933 : CollatzResearch.WordTrace tailWord_5309933 prefixEnd_5309933 908849290723492865472523 := by
  unfold tailWord_5309933
  simp only [CollatzResearch.WordTrace]
  refine ⟨193669167072027080202350453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129112778048018053468233635 193669167072027080202350453)
  ·
    refine ⟨18156484413002538768970355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193669167072027080202350453 18156484413002538768970355)
    ·
      refine ⟨27234726619503808153455533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18156484413002538768970355 27234726619503808153455533)
      ·
        refine ⟨10213022482313928057545825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27234726619503808153455533 10213022482313928057545825)
        ·
          refine ⟨7659766861735446043159369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10213022482313928057545825 7659766861735446043159369)
          ·
            refine ⟨5744825146301584532369527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7659766861735446043159369 5744825146301584532369527)
            ·
              refine ⟨8617237719452376798554291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5744825146301584532369527 8617237719452376798554291)
              ·
                refine ⟨12925856579178565197831437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8617237719452376798554291 12925856579178565197831437)
                ·
                  refine ⟨4847196217191961949186789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12925856579178565197831437 4847196217191961949186789)
                  ·
                    refine ⟨908849290723492865472523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4847196217191961949186789 908849290723492865472523)
                    ·
                      rfl

theorem cell23_5309933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_5309933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309933 prefixEnd_5309933 := by exact prefixLift 5309933
  have htrace : WordTrace (prefixWord ++ tailWord_5309933) baseStart_5309933 baseEnd_5309933 := by
    simpa [prefixWord, tailWord_5309933, baseEnd_5309933] using wordTrace_append hprefix tailTrace_5309933
  have hstable : (prefixWord ++ tailWord_5309933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309933).length < 2 ^ (prefixWord ++ tailWord_5309933).sum := by decide
  have hdescent : baseEnd_5309933 < baseStart_5309933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309939 : List Nat := [1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 3]
def baseStart_5309939 : Nat := 118140960795 + 5309939 * 2 ^ 59
def prefixEnd_5309939 : Nat := 4983230072969 + 3 ^ 40 * 5309939 * 2
def baseEnd_5309939 : Nat := 2726550953054405572942541

theorem tailTrace_5309939 : CollatzResearch.WordTrace tailWord_5309939 prefixEnd_5309939 2726550953054405572942541 := by
  unfold tailWord_5309939
  simp only [CollatzResearch.WordTrace]
  refine ⟨193669385910005343227068871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129112923940003562151379247 193669385910005343227068871)
  ·
    refine ⟨290504078865008014840603307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193669385910005343227068871 290504078865008014840603307)
    ·
      refine ⟨435756118297512022260904961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290504078865008014840603307 435756118297512022260904961)
      ·
        refine ⟨326817088723134016695678721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435756118297512022260904961 326817088723134016695678721)
        ·
          refine ⟨245112816542350512521759041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326817088723134016695678721 245112816542350512521759041)
          ·
            refine ⟨183834612406762884391319281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245112816542350512521759041 183834612406762884391319281)
            ·
              refine ⟨137875959305072163293489461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183834612406762884391319281 137875959305072163293489461)
              ·
                refine ⟨12925871184850515308764637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137875959305072163293489461 12925871184850515308764637)
                ·
                  refine ⟨4847201694318943240786739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12925871184850515308764637 4847201694318943240786739)
                  ·
                    refine ⟨7270802541478414861180109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4847201694318943240786739 7270802541478414861180109)
                    ·
                      refine ⟨2726550953054405572942541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7270802541478414861180109 2726550953054405572942541)
                      ·
                        rfl

theorem cell23_5309939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 3].length) (baseStart_5309939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309939 prefixEnd_5309939 := by exact prefixLift 5309939
  have htrace : WordTrace (prefixWord ++ tailWord_5309939) baseStart_5309939 baseEnd_5309939 := by
    simpa [prefixWord, tailWord_5309939, baseEnd_5309939] using wordTrace_append hprefix tailTrace_5309939
  have hstable : (prefixWord ++ tailWord_5309939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309939).length < 2 ^ (prefixWord ++ tailWord_5309939).sum := by decide
  have hdescent : baseEnd_5309939 < baseStart_5309939 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5309959 : List Nat := [1, 1, 4, 3, 2, 2, 1, 1, 3, 5]
def baseStart_5309959 : Nat := 118140960795 + 5309959 * 2 ^ 59
def prefixEnd_5309959 : Nat := 4983230072969 + 3 ^ 40 * 5309959 * 2
def baseEnd_5309959 : Nat := 908853740889165164897483

theorem tailTrace_5309959 : CollatzResearch.WordTrace tailWord_5309959 prefixEnd_5309959 908853740889165164897483 := by
  unfold tailWord_5309959
  simp only [CollatzResearch.WordTrace]
  refine ⟨193670115369932886642796931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129113410246621924428531287 193670115369932886642796931)
  ·
    refine ⟨290505173054899329964195397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193670115369932886642796931 290505173054899329964195397)
    ·
      refine ⟨54469719947793624368286637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290505173054899329964195397 54469719947793624368286637)
      ·
        refine ⟨20426144980422609138107489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54469719947793624368286637 20426144980422609138107489)
        ·
          refine ⟨15319608735316956853580617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20426144980422609138107489 15319608735316956853580617)
          ·
            refine ⟨11489706551487717640185463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15319608735316956853580617 11489706551487717640185463)
            ·
              refine ⟨17234559827231576460278195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11489706551487717640185463 17234559827231576460278195)
              ·
                refine ⟨25851839740847364690417293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17234559827231576460278195 25851839740847364690417293)
                ·
                  refine ⟨9694439902817761758906485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25851839740847364690417293 9694439902817761758906485)
                  ·
                    refine ⟨908853740889165164897483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9694439902817761758906485 908853740889165164897483)
                    ·
                      rfl

theorem cell23_5309959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 1, 3, 5].length) (baseStart_5309959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5309959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5309959 prefixEnd_5309959 := by exact prefixLift 5309959
  have htrace : WordTrace (prefixWord ++ tailWord_5309959) baseStart_5309959 baseEnd_5309959 := by
    simpa [prefixWord, tailWord_5309959, baseEnd_5309959] using wordTrace_append hprefix tailTrace_5309959
  have hstable : (prefixWord ++ tailWord_5309959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5309959).length < 2 ^ (prefixWord ++ tailWord_5309959).sum := by decide
  have hdescent : baseEnd_5309959 < baseStart_5309959 := by decide
  rcases family_descends (prefixWord ++ tailWord_5309959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310009 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5310009 : Nat := 118140960795 + 5310009 * 2 ^ 59
def prefixEnd_5310009 : Nat := 4983230072969 + 3 ^ 40 * 5310009 * 2
def baseEnd_5310009 : Nat := 2726586896700220299067219

theorem tailTrace_5310009 : CollatzResearch.WordTrace tailWord_5310009 prefixEnd_5310009 2726586896700220299067219 := by
  unfold tailWord_5310009
  simp only [CollatzResearch.WordTrace]
  refine ⟨193671939019751745182117081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129114626013167830121411387 193671939019751745182117081)
  ·
    refine ⟨145253954264813808886587811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193671939019751745182117081 145253954264813808886587811)
    ·
      refine ⟨217880931397220713329881717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145253954264813808886587811 217880931397220713329881717)
      ·
        refine ⟨20426337318489441874676411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 217880931397220713329881717 20426337318489441874676411)
        ·
          refine ⟨30639505977734162812014617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20426337318489441874676411 30639505977734162812014617)
          ·
            refine ⟨22979629483300622109010963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30639505977734162812014617 22979629483300622109010963)
            ·
              refine ⟨34469444224950933163516445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22979629483300622109010963 34469444224950933163516445)
              ·
                refine ⟨12926041584356599936318667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34469444224950933163516445 12926041584356599936318667)
                ·
                  refine ⟨19389062376534899904478001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12926041584356599936318667 19389062376534899904478001)
                  ·
                    refine ⟨14541796782401174928358501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19389062376534899904478001 14541796782401174928358501)
                    ·
                      refine ⟨2726586896700220299067219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14541796782401174928358501 2726586896700220299067219)
                      ·
                        rfl

theorem cell23_5310009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5310009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310009 prefixEnd_5310009 := by exact prefixLift 5310009
  have htrace : WordTrace (prefixWord ++ tailWord_5310009) baseStart_5310009 baseEnd_5310009 := by
    simpa [prefixWord, tailWord_5310009, baseEnd_5310009] using wordTrace_append hprefix tailTrace_5310009
  have hstable : (prefixWord ++ tailWord_5310009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310009).length < 2 ^ (prefixWord ++ tailWord_5310009).sum := by decide
  have hdescent : baseEnd_5310009 < baseStart_5310009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310073 : List Nat := [1, 2, 1, 3, 3, 1, 4, 2, 1, 3, 2]
def baseStart_5310073 : Nat := 118140960795 + 5310073 * 2 ^ 59
def prefixEnd_5310073 : Nat := 4983230072969 + 3 ^ 40 * 5310073 * 2
def baseEnd_5310073 : Nat := 2726619759462108048666925

theorem tailTrace_5310073 : CollatzResearch.WordTrace tailWord_5310073 prefixEnd_5310073 2726619759462108048666925 := by
  unfold tailWord_5310073
  simp only [CollatzResearch.WordTrace]
  refine ⟨193674273291519884112446873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129116182194346589408297915 193674273291519884112446873)
  ·
    refine ⟨145255704968639913084335155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193674273291519884112446873 145255704968639913084335155)
    ·
      refine ⟨217883557452959869626502733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145255704968639913084335155 217883557452959869626502733)
      ·
        refine ⟨81706334044859951109938525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217883557452959869626502733 81706334044859951109938525)
        ·
          refine ⟨30639875266822481666226947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81706334044859951109938525 30639875266822481666226947)
          ·
            refine ⟨45959812900233722499340421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30639875266822481666226947 45959812900233722499340421)
            ·
              refine ⟨8617464918793822968626329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45959812900233722499340421 8617464918793822968626329)
              ·
                refine ⟨6463098689095367226469747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8617464918793822968626329 6463098689095367226469747)
                ·
                  refine ⟨9694648033643050839704621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6463098689095367226469747 9694648033643050839704621)
                  ·
                    refine ⟨3635493012616144064889233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9694648033643050839704621 3635493012616144064889233)
                    ·
                      refine ⟨2726619759462108048666925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635493012616144064889233 2726619759462108048666925)
                      ·
                        rfl

theorem cell23_5310073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 2, 1, 3, 2].length) (baseStart_5310073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310073 prefixEnd_5310073 := by exact prefixLift 5310073
  have htrace : WordTrace (prefixWord ++ tailWord_5310073) baseStart_5310073 baseEnd_5310073 := by
    simpa [prefixWord, tailWord_5310073, baseEnd_5310073] using wordTrace_append hprefix tailTrace_5310073
  have hstable : (prefixWord ++ tailWord_5310073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310073).length < 2 ^ (prefixWord ++ tailWord_5310073).sum := by decide
  have hdescent : baseEnd_5310073 < baseStart_5310073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310103 : List Nat := [1, 1, 3, 3, 2, 2, 2, 1, 4, 2, 2]
def baseStart_5310103 : Nat := 118140960795 + 5310103 * 2 ^ 59
def prefixEnd_5310103 : Nat := 4983230072969 + 3 ^ 40 * 5310103 * 2
def baseEnd_5310103 : Nat := 2726635163881742931291787

theorem tailTrace_5310103 : CollatzResearch.WordTrace tailWord_5310103 prefixEnd_5310103 2726635163881742931291787 := by
  unfold tailWord_5310103
  simp only [CollatzResearch.WordTrace]
  refine ⟨193675367481411199236038963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129116911654274132824025975 193675367481411199236038963)
  ·
    refine ⟨290513051222116798854058445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193675367481411199236038963 290513051222116798854058445)
    ·
      refine ⟨108942394208293799570271917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290513051222116798854058445 108942394208293799570271917)
      ·
        refine ⟨40853397828110174838851969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108942394208293799570271917 40853397828110174838851969)
        ·
          refine ⟨30640048371082631129138977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40853397828110174838851969 30640048371082631129138977)
          ·
            refine ⟨22980036278311973346854233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30640048371082631129138977 22980036278311973346854233)
            ·
              refine ⟨17235027208733980010140675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22980036278311973346854233 17235027208733980010140675)
              ·
                refine ⟨25852540813100970015211013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17235027208733980010140675 25852540813100970015211013)
                ·
                  refine ⟨4847351402456431877852065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25852540813100970015211013 4847351402456431877852065)
                  ·
                    refine ⟨3635513551842323908389049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4847351402456431877852065 3635513551842323908389049)
                    ·
                      refine ⟨2726635163881742931291787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635513551842323908389049 2726635163881742931291787)
                      ·
                        rfl

theorem cell23_5310103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 1, 4, 2, 2].length) (baseStart_5310103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310103 prefixEnd_5310103 := by exact prefixLift 5310103
  have htrace : WordTrace (prefixWord ++ tailWord_5310103) baseStart_5310103 baseEnd_5310103 := by
    simpa [prefixWord, tailWord_5310103, baseEnd_5310103] using wordTrace_append hprefix tailTrace_5310103
  have hstable : (prefixWord ++ tailWord_5310103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310103).length < 2 ^ (prefixWord ++ tailWord_5310103).sum := by decide
  have hdescent : baseEnd_5310103 < baseStart_5310103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310114 : List Nat := [3, 3, 1, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_5310114 : Nat := 118140960795 + 5310114 * 2 ^ 59
def prefixEnd_5310114 : Nat := 4983230072969 + 3 ^ 40 * 5310114 * 2
def baseEnd_5310114 : Nat := 2726640812168942388254237

theorem tailTrace_5310114 : CollatzResearch.WordTrace tailWord_5310114 prefixEnd_5310114 2726640812168942388254237 := by
  unfold tailWord_5310114
  simp only [CollatzResearch.WordTrace]
  refine ⟨48418942171092837028672349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129117179122914232076459597 48418942171092837028672349)
  ·
    refine ⟨18157103314159813885752131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48418942171092837028672349 18157103314159813885752131)
    ·
      refine ⟨27235654971239720828628197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18157103314159813885752131 27235654971239720828628197)
      ·
        refine ⟨5106685307107447655367787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27235654971239720828628197 5106685307107447655367787)
        ·
          refine ⟨7660027960661171483051681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5106685307107447655367787 7660027960661171483051681)
          ·
            refine ⟨5745020970495878612288761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7660027960661171483051681 5745020970495878612288761)
            ·
              refine ⟨4308765727871908959216571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5745020970495878612288761 4308765727871908959216571)
              ·
                refine ⟨6463148591807863438824857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4308765727871908959216571 6463148591807863438824857)
                ·
                  refine ⟨4847361443855897579118643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6463148591807863438824857 4847361443855897579118643)
                  ·
                    refine ⟨7271042165783846368677965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4847361443855897579118643 7271042165783846368677965)
                    ·
                      refine ⟨2726640812168942388254237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7271042165783846368677965 2726640812168942388254237)
                      ·
                        rfl

theorem cell23_5310114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_5310114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310114 prefixEnd_5310114 := by exact prefixLift 5310114
  have htrace : WordTrace (prefixWord ++ tailWord_5310114) baseStart_5310114 baseEnd_5310114 := by
    simpa [prefixWord, tailWord_5310114, baseEnd_5310114] using wordTrace_append hprefix tailTrace_5310114
  have hstable : (prefixWord ++ tailWord_5310114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310114).length < 2 ^ (prefixWord ++ tailWord_5310114).sum := by decide
  have hdescent : baseEnd_5310114 < baseStart_5310114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310176 : List Nat := [2, 1, 1, 3, 1, 2, 3, 1, 1, 6, 2]
def baseStart_5310176 : Nat := 118140960795 + 5310176 * 2 ^ 59
def prefixEnd_5310176 : Nat := 4983230072969 + 3 ^ 40 * 5310176 * 2
def baseEnd_5310176 : Nat := 2726672647969521145678951

theorem tailTrace_5310176 : CollatzResearch.WordTrace tailWord_5310176 prefixEnd_5310176 2726672647969521145678951 := by
  unfold tailWord_5310176
  simp only [CollatzResearch.WordTrace]
  refine ⟨96839015005073366351723191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129118686673431155135630921 96839015005073366351723191)
  ·
    refine ⟨145258522507610049527584787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96839015005073366351723191 145258522507610049527584787)
    ·
      refine ⟨217887783761415074291377181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145258522507610049527584787 217887783761415074291377181)
      ·
        refine ⟨81707918910530652859266443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217887783761415074291377181 81707918910530652859266443)
        ·
          refine ⟨122561878365795979288899665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81707918910530652859266443 122561878365795979288899665)
          ·
            refine ⟨91921408774346984466674749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122561878365795979288899665 91921408774346984466674749)
            ·
              refine ⟨34470528290380119175003031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91921408774346984466674749 34470528290380119175003031)
              ·
                refine ⟨51705792435570178762504547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34470528290380119175003031 51705792435570178762504547)
                ·
                  refine ⟨77558688653355268143756821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51705792435570178762504547 77558688653355268143756821)
                  ·
                    refine ⟨3635563530626028194238601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77558688653355268143756821 3635563530626028194238601)
                    ·
                      refine ⟨2726672647969521145678951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635563530626028194238601 2726672647969521145678951)
                      ·
                        rfl

theorem cell23_5310176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 3, 1, 1, 6, 2].length) (baseStart_5310176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310176 prefixEnd_5310176 := by exact prefixLift 5310176
  have htrace : WordTrace (prefixWord ++ tailWord_5310176) baseStart_5310176 baseEnd_5310176 := by
    simpa [prefixWord, tailWord_5310176, baseEnd_5310176] using wordTrace_append hprefix tailTrace_5310176
  have hstable : (prefixWord ++ tailWord_5310176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310176).length < 2 ^ (prefixWord ++ tailWord_5310176).sum := by decide
  have hdescent : baseEnd_5310176 < baseStart_5310176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310186 : List Nat := [3, 1, 3, 1, 1, 1, 3, 1, 5, 4]
def baseStart_5310186 : Nat := 118140960795 + 5310186 * 2 ^ 59
def prefixEnd_5310186 : Nat := 4983230072969 + 3 ^ 40 * 5310186 * 2
def baseEnd_5310186 : Nat := 908892594258688702184635

theorem tailTrace_5310186 : CollatzResearch.WordTrace tailWord_5310186 prefixEnd_5310186 908892594258688702184635 := by
  unfold tailWord_5310186
  simp only [CollatzResearch.WordTrace]
  refine ⟨48419598685027626102827603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129118929826740336274206941 48419598685027626102827603)
  ·
    refine ⟨72629398027541439154241405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48419598685027626102827603 72629398027541439154241405)
    ·
      refine ⟨27236024260328039682840527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72629398027541439154241405 27236024260328039682840527)
      ·
        refine ⟨40854036390492059524260791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27236024260328039682840527 40854036390492059524260791)
        ·
          refine ⟨61281054585738089286391187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40854036390492059524260791 61281054585738089286391187)
          ·
            refine ⟨91921581878607133929586781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61281054585738089286391187 91921581878607133929586781)
            ·
              refine ⟨34470593204477675223595043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91921581878607133929586781 34470593204477675223595043)
              ·
                refine ⟨51705889806716512835392565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34470593204477675223595043 51705889806716512835392565)
                ·
                  refine ⟨4847427169379673078318053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51705889806716512835392565 4847427169379673078318053)
                  ·
                    refine ⟨908892594258688702184635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4847427169379673078318053 908892594258688702184635)
                    ·
                      rfl

theorem cell23_5310186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_5310186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310186 prefixEnd_5310186 := by exact prefixLift 5310186
  have htrace : WordTrace (prefixWord ++ tailWord_5310186) baseStart_5310186 baseEnd_5310186 := by
    simpa [prefixWord, tailWord_5310186, baseEnd_5310186] using wordTrace_append hprefix tailTrace_5310186
  have hstable : (prefixWord ++ tailWord_5310186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310186).length < 2 ^ (prefixWord ++ tailWord_5310186).sum := by decide
  have hdescent : baseEnd_5310186 < baseStart_5310186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310193 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 4]
def baseStart_5310193 : Nat := 118140960795 + 5310193 * 2 ^ 59
def prefixEnd_5310193 : Nat := 4983230072969 + 3 ^ 40 * 5310193 * 2
def baseEnd_5310193 : Nat := 2726681377140647579166373

theorem tailTrace_5310193 : CollatzResearch.WordTrace tailWord_5310193 prefixEnd_5310193 2726681377140647579166373 := by
  unfold tailWord_5310193
  simp only [CollatzResearch.WordTrace]
  refine ⟨193678650051085144606815233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129119100034056763071210155 193678650051085144606815233)
  ·
    refine ⟨145258987538313858455111425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193678650051085144606815233 145258987538313858455111425)
    ·
      refine ⟨108944240653735393841333569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145258987538313858455111425 108944240653735393841333569)
      ·
        refine ⟨81708180490301545381000177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108944240653735393841333569 81708180490301545381000177)
        ·
          refine ⟨61281135367726159035750133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81708180490301545381000177 61281135367726159035750133)
          ·
            refine ⟨5745106440724327409601575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61281135367726159035750133 5745106440724327409601575)
            ·
              refine ⟨8617659661086491114402363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745106440724327409601575 8617659661086491114402363)
              ·
                refine ⟨12926489491629736671603545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8617659661086491114402363 12926489491629736671603545)
                ·
                  refine ⟨9694867118722302503702659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12926489491629736671603545 9694867118722302503702659)
                  ·
                    refine ⟨14542300678083453755553989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9694867118722302503702659 14542300678083453755553989)
                    ·
                      refine ⟨2726681377140647579166373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14542300678083453755553989 2726681377140647579166373)
                      ·
                        rfl

theorem cell23_5310193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_5310193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310193 prefixEnd_5310193 := by exact prefixLift 5310193
  have htrace : WordTrace (prefixWord ++ tailWord_5310193) baseStart_5310193 baseEnd_5310193 := by
    simpa [prefixWord, tailWord_5310193, baseEnd_5310193] using wordTrace_append hprefix tailTrace_5310193
  have hstable : (prefixWord ++ tailWord_5310193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310193).length < 2 ^ (prefixWord ++ tailWord_5310193).sum := by decide
  have hdescent : baseEnd_5310193 < baseStart_5310193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310219 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 6]
def baseStart_5310219 : Nat := 118140960795 + 5310219 * 2 ^ 59
def prefixEnd_5310219 : Nat := 4983230072969 + 3 ^ 40 * 5310219 * 2
def baseEnd_5310219 : Nat := 2726694727637664477441253

theorem tailTrace_5310219 : CollatzResearch.WordTrace tailWord_5310219 prefixEnd_5310219 2726694727637664477441253 := by
  unfold tailWord_5310219
  simp only [CollatzResearch.WordTrace]
  refine ⟨193679598348990951047261711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129119732232660634031507807 193679598348990951047261711)
  ·
    refine ⟨290519397523486426570892567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193679598348990951047261711 290519397523486426570892567)
    ·
      refine ⟨435779096285229639856338851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290519397523486426570892567 435779096285229639856338851)
      ·
        refine ⟨653668644427844459784508277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435779096285229639856338851 653668644427844459784508277)
        ·
          refine ⟨61281435415110418104797651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 653668644427844459784508277 61281435415110418104797651)
          ·
            refine ⟨91922153122665627157196477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61281435415110418104797651 91922153122665627157196477)
            ·
              refine ⟨34470807420999610183948679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91922153122665627157196477 34470807420999610183948679)
              ·
                refine ⟨51706211131499415275923019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34470807420999610183948679 51706211131499415275923019)
                ·
                  refine ⟨77559316697249122913884529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51706211131499415275923019 77559316697249122913884529)
                  ·
                    refine ⟨58169487522936842185413397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77559316697249122913884529 58169487522936842185413397)
                    ·
                      refine ⟨2726694727637664477441253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58169487522936842185413397 2726694727637664477441253)
                      ·
                        rfl

theorem cell23_5310219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 6].length) (baseStart_5310219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310219 prefixEnd_5310219 := by exact prefixLift 5310219
  have htrace : WordTrace (prefixWord ++ tailWord_5310219) baseStart_5310219 baseEnd_5310219 := by
    simpa [prefixWord, tailWord_5310219, baseEnd_5310219] using wordTrace_append hprefix tailTrace_5310219
  have hstable : (prefixWord ++ tailWord_5310219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310219).length < 2 ^ (prefixWord ++ tailWord_5310219).sum := by decide
  have hdescent : baseEnd_5310219 < baseStart_5310219 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310243 : List Nat := [1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 3]
def baseStart_5310243 : Nat := 118140960795 + 5310243 * 2 ^ 59
def prefixEnd_5310243 : Nat := 4983230072969 + 3 ^ 40 * 5310243 * 2
def baseEnd_5310243 : Nat := 2726707051173372383541143

theorem tailTrace_5310243 : CollatzResearch.WordTrace tailWord_5310243 prefixEnd_5310243 2726707051173372383541143 := by
  unfold tailWord_5310243
  simp only [CollatzResearch.WordTrace]
  refine ⟨193680473700904003146135383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129120315800602668764090255 193680473700904003146135383)
  ·
    refine ⟨290520710551356004719203075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193680473700904003146135383 290520710551356004719203075)
    ·
      refine ⟨435781065827034007078804613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290520710551356004719203075 435781065827034007078804613)
      ·
        refine ⟨81708949842568876327275865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 435781065827034007078804613 81708949842568876327275865)
        ·
          refine ⟨61281712381926657245456899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81708949842568876327275865 61281712381926657245456899)
          ·
            refine ⟨91922568572889985868185349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61281712381926657245456899 91922568572889985868185349)
            ·
              refine ⟨17235481607416872350284753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91922568572889985868185349 17235481607416872350284753)
              ·
                refine ⟨12926611205562654262713565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17235481607416872350284753 12926611205562654262713565)
                ·
                  refine ⟨4847479202085995348517587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12926611205562654262713565 4847479202085995348517587)
                  ·
                    refine ⟨7271218803128993022776381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4847479202085995348517587 7271218803128993022776381)
                    ·
                      refine ⟨2726707051173372383541143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7271218803128993022776381 2726707051173372383541143)
                      ·
                        rfl

theorem cell23_5310243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2, 3, 1, 3].length) (baseStart_5310243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310243 prefixEnd_5310243 := by exact prefixLift 5310243
  have htrace : WordTrace (prefixWord ++ tailWord_5310243) baseStart_5310243 baseEnd_5310243 := by
    simpa [prefixWord, tailWord_5310243, baseEnd_5310243] using wordTrace_append hprefix tailTrace_5310243
  have hstable : (prefixWord ++ tailWord_5310243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310243).length < 2 ^ (prefixWord ++ tailWord_5310243).sum := by decide
  have hdescent : baseEnd_5310243 < baseStart_5310243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310254 : List Nat := [4, 1, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_5310254 : Nat := 118140960795 + 5310254 * 2 ^ 59
def prefixEnd_5310254 : Nat := 4983230072969 + 3 ^ 40 * 5310254 * 2
def baseEnd_5310254 : Nat := 908904233153523946834531

theorem tailTrace_5310254 : CollatzResearch.WordTrace tailWord_5310254 prefixEnd_5310254 908904233153523946834531 := by
  unfold tailWord_5310254
  simp only [CollatzResearch.WordTrace]
  refine ⟨24210109362983019003098227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129120583269242768016523877 24210109362983019003098227)
  ·
    refine ⟨36315164044474528504647341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24210109362983019003098227 36315164044474528504647341)
    ·
      refine ⟨13618186516677948189242753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36315164044474528504647341 13618186516677948189242753)
      ·
        refine ⟨10213639887508461141932065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13618186516677948189242753 10213639887508461141932065)
        ·
          refine ⟨7660229915631345856449049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10213639887508461141932065 7660229915631345856449049)
          ·
            refine ⟨5745172436723509392336787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7660229915631345856449049 5745172436723509392336787)
            ·
              refine ⟨8617758655085264088505181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745172436723509392336787 8617758655085264088505181)
              ·
                refine ⟨3231659495656974033189443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8617758655085264088505181 3231659495656974033189443)
                ·
                  refine ⟨4847489243485461049784165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231659495656974033189443 4847489243485461049784165)
                  ·
                    refine ⟨908904233153523946834531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4847489243485461049784165 908904233153523946834531)
                    ·
                      rfl

theorem cell23_5310254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_5310254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310254 prefixEnd_5310254 := by exact prefixLift 5310254
  have htrace : WordTrace (prefixWord ++ tailWord_5310254) baseStart_5310254 baseEnd_5310254 := by
    simpa [prefixWord, tailWord_5310254, baseEnd_5310254] using wordTrace_append hprefix tailTrace_5310254
  have hstable : (prefixWord ++ tailWord_5310254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310254).length < 2 ^ (prefixWord ++ tailWord_5310254).sum := by decide
  have hdescent : baseEnd_5310254 < baseStart_5310254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310270 : List Nat := [4, 2, 1, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_5310270 : Nat := 118140960795 + 5310270 * 2 ^ 59
def prefixEnd_5310270 : Nat := 4983230072969 + 3 ^ 40 * 5310270 * 2
def baseEnd_5310270 : Nat := 2726720915151043777903519

theorem tailTrace_5310270 : CollatzResearch.WordTrace tailWord_5310270 prefixEnd_5310270 2726720915151043777903519 := by
  unfold tailWord_5310270
  simp only [CollatzResearch.WordTrace]
  refine ⟨24210182308975773344671033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129120972314537457838245509 24210182308975773344671033)
  ·
    refine ⟨18157636731731830008503275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24210182308975773344671033 18157636731731830008503275)
    ·
      refine ⟨27236455097597745012754913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18157636731731830008503275 27236455097597745012754913)
      ·
        refine ⟨20427341323198308759566185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27236455097597745012754913 20427341323198308759566185)
        ·
          refine ⟨15320505992398731569674639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20427341323198308759566185 15320505992398731569674639)
          ·
            refine ⟨22980758988598097354511959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15320505992398731569674639 22980758988598097354511959)
            ·
              refine ⟨34471138482897146031767939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22980758988598097354511959 34471138482897146031767939)
              ·
                refine ⟨51706707724345719047651909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34471138482897146031767939 51706707724345719047651909)
                ·
                  refine ⟨9695007698314822321434733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51706707724345719047651909 9695007698314822321434733)
                  ·
                    refine ⟨3635627886868058370538025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9695007698314822321434733 3635627886868058370538025)
                    ·
                      refine ⟨2726720915151043777903519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635627886868058370538025 2726720915151043777903519)
                      ·
                        rfl

theorem cell23_5310270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_5310270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310270 prefixEnd_5310270 := by exact prefixLift 5310270
  have htrace : WordTrace (prefixWord ++ tailWord_5310270) baseStart_5310270 baseEnd_5310270 := by
    simpa [prefixWord, tailWord_5310270, baseEnd_5310270] using wordTrace_append hprefix tailTrace_5310270
  have hstable : (prefixWord ++ tailWord_5310270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310270).length < 2 ^ (prefixWord ++ tailWord_5310270).sum := by decide
  have hdescent : baseEnd_5310270 < baseStart_5310270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310277 : List Nat := [1, 3, 1, 1, 1, 2, 7, 2, 1, 1, 3]
def baseStart_5310277 : Nat := 118140960795 + 5310277 * 2 ^ 59
def prefixEnd_5310277 : Nat := 4983230072969 + 3 ^ 40 * 5310277 * 2
def baseEnd_5310277 : Nat := 2726724509515625250515987

theorem tailTrace_5310277 : CollatzResearch.WordTrace tailWord_5310277 prefixEnd_5310277 2726724509515625250515987 := by
  unfold tailWord_5310277
  simp only [CollatzResearch.WordTrace]
  refine ⟨193681713782780826952873085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129121142521853884635248723 193681713782780826952873085)
  ·
    refine ⟨72630642668542810107327407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193681713782780826952873085 72630642668542810107327407)
    ·
      refine ⟨108945964002814215160991111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72630642668542810107327407 108945964002814215160991111)
      ·
        refine ⟨163418946004221322741486667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108945964002814215160991111 163418946004221322741486667)
        ·
          refine ⟨245128419006331984112230001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163418946004221322741486667 245128419006331984112230001)
          ·
            refine ⟨183846314254748988084172501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245128419006331984112230001 183846314254748988084172501)
            ·
              refine ⟨4308897990345679408222793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 183846314254748988084172501 4308897990345679408222793)
              ·
                refine ⟨3231673492759259556167095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4308897990345679408222793 3231673492759259556167095)
                ·
                  refine ⟨4847510239138889334250643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231673492759259556167095 4847510239138889334250643)
                  ·
                    refine ⟨7271265358708334001375965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4847510239138889334250643 7271265358708334001375965)
                    ·
                      refine ⟨2726724509515625250515987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7271265358708334001375965 2726724509515625250515987)
                      ·
                        rfl

theorem cell23_5310277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 7, 2, 1, 1, 3].length) (baseStart_5310277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310277 prefixEnd_5310277 := by exact prefixLift 5310277
  have htrace : WordTrace (prefixWord ++ tailWord_5310277) baseStart_5310277 baseEnd_5310277 := by
    simpa [prefixWord, tailWord_5310277, baseEnd_5310277] using wordTrace_append hprefix tailTrace_5310277
  have hstable : (prefixWord ++ tailWord_5310277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310277).length < 2 ^ (prefixWord ++ tailWord_5310277).sum := by decide
  have hdescent : baseEnd_5310277 < baseStart_5310277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310286 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_5310286 : Nat := 118140960795 + 5310286 * 2 ^ 59
def prefixEnd_5310286 : Nat := 4983230072969 + 3 ^ 40 * 5310286 * 2
def baseEnd_5310286 : Nat := 2726729130841515715303445

theorem tailTrace_5310286 : CollatzResearch.WordTrace tailWord_5310286 prefixEnd_5310286 2726729130841515715303445 := by
  unfold tailWord_5310286
  simp only [CollatzResearch.WordTrace]
  refine ⟨24210255254968527686243839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129121361359832147659967141 24210255254968527686243839)
  ·
    refine ⟨36315382882452791529365759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24210255254968527686243839 36315382882452791529365759)
    ·
      refine ⟨54473074323679187294048639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36315382882452791529365759 54473074323679187294048639)
      ·
        refine ⟨81709611485518780941072959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54473074323679187294048639 81709611485518780941072959)
        ·
          refine ⟨122564417228278171411609439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81709611485518780941072959 122564417228278171411609439)
          ·
            refine ⟨183846625842417257117414159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122564417228278171411609439 183846625842417257117414159)
            ·
              refine ⟨275769938763625885676121239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183846625842417257117414159 275769938763625885676121239)
              ·
                refine ⟨413654908145438828514181859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275769938763625885676121239 413654908145438828514181859)
                ·
                  refine ⟨620482362218158242771272789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413654908145438828514181859 620482362218158242771272789)
                  ·
                    refine ⟨7271277682244041907475853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 620482362218158242771272789 7271277682244041907475853)
                    ·
                      refine ⟨2726729130841515715303445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7271277682244041907475853 2726729130841515715303445)
                      ·
                        rfl

theorem cell23_5310286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_5310286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310286 prefixEnd_5310286 := by exact prefixLift 5310286
  have htrace : WordTrace (prefixWord ++ tailWord_5310286) baseStart_5310286 baseEnd_5310286 := by
    simpa [prefixWord, tailWord_5310286, baseEnd_5310286] using wordTrace_append hprefix tailTrace_5310286
  have hstable : (prefixWord ++ tailWord_5310286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310286).length < 2 ^ (prefixWord ++ tailWord_5310286).sum := by decide
  have hdescent : baseEnd_5310286 < baseStart_5310286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310300 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 3, 1, 4]
def baseStart_5310300 : Nat := 118140960795 + 5310300 * 2 ^ 59
def prefixEnd_5310300 : Nat := 4983230072969 + 3 ^ 40 * 5310300 * 2
def baseEnd_5310300 : Nat := 2726736319570678660528381

theorem tailTrace_5310300 : CollatzResearch.WordTrace tailWord_5310300 prefixEnd_5310300 2726736319570678660528381 := by
  unfold tailWord_5310300
  simp only [CollatzResearch.WordTrace]
  refine ⟨96841276330848750940480177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129121701774465001253973569 96841276330848750940480177)
  ·
    refine ⟨72630957248136563205360133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96841276330848750940480177 72630957248136563205360133)
    ·
      refine ⟨13618304484025605601005025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72630957248136563205360133 13618304484025605601005025)
      ·
        refine ⟨10213728363019204200753769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13618304484025605601005025 10213728363019204200753769)
        ·
          refine ⟨7660296272264403150565327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10213728363019204200753769 7660296272264403150565327)
          ·
            refine ⟨11490444408396604725847991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7660296272264403150565327 11490444408396604725847991)
            ·
              refine ⟨17235666612594907088771987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11490444408396604725847991 17235666612594907088771987)
              ·
                refine ⟨25853499918892360633157981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17235666612594907088771987 25853499918892360633157981)
                ·
                  refine ⟨9695062469584635237434243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25853499918892360633157981 9695062469584635237434243)
                  ·
                    refine ⟨14542593704376952856151365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9695062469584635237434243 14542593704376952856151365)
                    ·
                      refine ⟨2726736319570678660528381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14542593704376952856151365 2726736319570678660528381)
                      ·
                        rfl

theorem cell23_5310300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_5310300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310300 prefixEnd_5310300 := by exact prefixLift 5310300
  have htrace : WordTrace (prefixWord ++ tailWord_5310300) baseStart_5310300 baseEnd_5310300 := by
    simpa [prefixWord, tailWord_5310300, baseEnd_5310300] using wordTrace_append hprefix tailTrace_5310300
  have hstable : (prefixWord ++ tailWord_5310300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310300).length < 2 ^ (prefixWord ++ tailWord_5310300).sum := by decide
  have hdescent : baseEnd_5310300 < baseStart_5310300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310303 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 3]
def baseStart_5310303 : Nat := 118140960795 + 5310303 * 2 ^ 59
def prefixEnd_5310303 : Nat := 4983230072969 + 3 ^ 40 * 5310303 * 2
def baseEnd_5310303 : Nat := 2726737860012642148790867

theorem tailTrace_5310303 : CollatzResearch.WordTrace tailWord_5310303 prefixEnd_5310303 2726737860012642148790867 := by
  unfold tailWord_5310303
  simp only [CollatzResearch.WordTrace]
  refine ⟨193682662080686633393319563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129121774720457755595546375 193682662080686633393319563)
  ·
    refine ⟨290523993121029950089979345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193682662080686633393319563 290523993121029950089979345)
    ·
      refine ⟨217892994840772462567484509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290523993121029950089979345 217892994840772462567484509)
      ·
        refine ⟨81709873065289673462806691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217892994840772462567484509 81709873065289673462806691)
        ·
          refine ⟨122564809597934510194210037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81709873065289673462806691 122564809597934510194210037)
          ·
            refine ⟨11490450899806360330707191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122564809597934510194210037 11490450899806360330707191)
            ·
              refine ⟨17235676349709540496060787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11490450899806360330707191 17235676349709540496060787)
              ·
                refine ⟨25853514524564310744091181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17235676349709540496060787 25853514524564310744091181)
                ·
                  refine ⟨9695067946711616529034193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25853514524564310744091181 9695067946711616529034193)
                  ·
                    refine ⟨7271300960033712396775645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9695067946711616529034193 7271300960033712396775645)
                    ·
                      refine ⟨2726737860012642148790867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7271300960033712396775645 2726737860012642148790867)
                      ·
                        rfl

theorem cell23_5310303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_5310303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310303 prefixEnd_5310303 := by exact prefixLift 5310303
  have htrace : WordTrace (prefixWord ++ tailWord_5310303) baseStart_5310303 baseEnd_5310303 := by
    simpa [prefixWord, tailWord_5310303, baseEnd_5310303] using wordTrace_append hprefix tailTrace_5310303
  have hstable : (prefixWord ++ tailWord_5310303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310303).length < 2 ^ (prefixWord ++ tailWord_5310303).sum := by decide
  have hdescent : baseEnd_5310303 < baseStart_5310303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310483 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 3]
def baseStart_5310483 : Nat := 118140960795 + 5310483 * 2 ^ 59
def prefixEnd_5310483 : Nat := 4983230072969 + 3 ^ 40 * 5310483 * 2
def baseEnd_5310483 : Nat := 2726830286530451444540039

theorem tailTrace_5310483 : CollatzResearch.WordTrace tailWord_5310483 prefixEnd_5310483 2726830286530451444540039 := by
  unfold tailWord_5310483
  simp only [CollatzResearch.WordTrace]
  refine ⟨193689227220034524134872103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129126151480023016089914735 193689227220034524134872103)
  ·
    refine ⟨290533840830051786202308155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193689227220034524134872103 290533840830051786202308155)
    ·
      refine ⟨435800761245077679303462233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290533840830051786202308155 435800761245077679303462233)
      ·
        refine ⟨326850570933808259477596675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435800761245077679303462233 326850570933808259477596675)
        ·
          refine ⟨490275856400712389216395013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326850570933808259477596675 490275856400712389216395013)
          ·
            refine ⟨91926723075133572978074065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 490275856400712389216395013 91926723075133572978074065)
            ·
              refine ⟨68945042306350179733555549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91926723075133572978074065 68945042306350179733555549)
              ·
                refine ⟨25854390864881317400083331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68945042306350179733555549 25854390864881317400083331)
                ·
                  refine ⟨38781586297321976100124997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25854390864881317400083331 38781586297321976100124997)
                  ·
                    refine ⟨7271547430747870518773437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38781586297321976100124997 7271547430747870518773437)
                    ·
                      refine ⟨2726830286530451444540039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7271547430747870518773437 2726830286530451444540039)
                      ·
                        rfl

theorem cell23_5310483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 4, 3].length) (baseStart_5310483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310483 prefixEnd_5310483 := by exact prefixLift 5310483
  have htrace : WordTrace (prefixWord ++ tailWord_5310483) baseStart_5310483 baseEnd_5310483 := by
    simpa [prefixWord, tailWord_5310483, baseEnd_5310483] using wordTrace_append hprefix tailTrace_5310483
  have hstable : (prefixWord ++ tailWord_5310483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310483).length < 2 ^ (prefixWord ++ tailWord_5310483).sum := by decide
  have hdescent : baseEnd_5310483 < baseStart_5310483 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310563 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 3, 6]
def baseStart_5310563 : Nat := 118140960795 + 5310563 * 2 ^ 59
def prefixEnd_5310563 : Nat := 4983230072969 + 3 ^ 40 * 5310563 * 2
def baseEnd_5310563 : Nat := 908957121660937043846557

theorem tailTrace_5310563 : CollatzResearch.WordTrace tailWord_5310563 prefixEnd_5310563 908957121660937043846557 := by
  unfold tailWord_5310563
  simp only [CollatzResearch.WordTrace]
  refine ⟨193692145059744697797784343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129128096706496465198522895 193692145059744697797784343)
  ·
    refine ⟨290538217589617046696676515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193692145059744697797784343 290538217589617046696676515)
    ·
      refine ⟨435807326384425570045014773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290538217589617046696676515 435807326384425570045014773)
      ·
        refine ⟨40856936848539897191720135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 435807326384425570045014773 40856936848539897191720135)
        ·
          refine ⟨61285405272809845787580203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40856936848539897191720135 61285405272809845787580203)
          ·
            refine ⟨91928107909214768681370305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61285405272809845787580203 91928107909214768681370305)
            ·
              refine ⟨68946080931911076511027729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91928107909214768681370305 68946080931911076511027729)
              ·
                refine ⟨51709560698933307383270797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68946080931911076511027729 51709560698933307383270797)
                ·
                  refine ⟨19391085262099990268726549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51709560698933307383270797 19391085262099990268726549)
                  ·
                    refine ⟨908957121660937043846557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19391085262099990268726549 908957121660937043846557)
                    ·
                      rfl

theorem cell23_5310563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 6].length) (baseStart_5310563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310563 prefixEnd_5310563 := by exact prefixLift 5310563
  have htrace : WordTrace (prefixWord ++ tailWord_5310563) baseStart_5310563 baseEnd_5310563 := by
    simpa [prefixWord, tailWord_5310563, baseEnd_5310563] using wordTrace_append hprefix tailTrace_5310563
  have hstable : (prefixWord ++ tailWord_5310563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310563).length < 2 ^ (prefixWord ++ tailWord_5310563).sum := by decide
  have hdescent : baseEnd_5310563 < baseStart_5310563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310564 : List Nat := [2, 3, 1, 1, 2, 1, 4, 4, 1, 1, 3]
def baseStart_5310564 : Nat := 118140960795 + 5310564 * 2 ^ 59
def prefixEnd_5310564 : Nat := 4983230072969 + 3 ^ 40 * 5310564 * 2
def baseEnd_5310564 : Nat := 2726871878463465627627167

theorem tailTrace_5310564 : CollatzResearch.WordTrace tailWord_5310564 prefixEnd_5310564 2726871878463465627627167 := by
  unfold tailWord_5310564
  simp only [CollatzResearch.WordTrace]
  refine ⟨96846090766370537484285373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129128121021827383312380497 96846090766370537484285373)
  ·
    refine ⟨36317284037388951556607015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96846090766370537484285373 36317284037388951556607015)
    ·
      refine ⟨54475926056083427334910523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36317284037388951556607015 54475926056083427334910523)
      ·
        refine ⟨81713889084125141002365785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54475926056083427334910523 81713889084125141002365785)
        ·
          refine ⟨61285416813093855751774339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81713889084125141002365785 61285416813093855751774339)
          ·
            refine ⟨91928125219640783627661509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61285416813093855751774339 91928125219640783627661509)
            ·
              refine ⟨17236523478682646930186533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91928125219640783627661509 17236523478682646930186533)
              ·
                refine ⟨3231848152252996299409975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17236523478682646930186533 3231848152252996299409975)
                ·
                  refine ⟨4847772228379494449114963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3231848152252996299409975 4847772228379494449114963)
                  ·
                    refine ⟨7271658342569241673672445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4847772228379494449114963 7271658342569241673672445)
                    ·
                      refine ⟨2726871878463465627627167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7271658342569241673672445 2726871878463465627627167)
                      ·
                        rfl

theorem cell23_5310564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_5310564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310564 prefixEnd_5310564 := by exact prefixLift 5310564
  have htrace : WordTrace (prefixWord ++ tailWord_5310564) baseStart_5310564 baseEnd_5310564 := by
    simpa [prefixWord, tailWord_5310564, baseEnd_5310564] using wordTrace_append hprefix tailTrace_5310564
  have hstable : (prefixWord ++ tailWord_5310564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310564).length < 2 ^ (prefixWord ++ tailWord_5310564).sum := by decide
  have hdescent : baseEnd_5310564 < baseStart_5310564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310621 : List Nat := [1, 4, 2, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_5310621 : Nat := 118140960795 + 5310621 * 2 ^ 59
def prefixEnd_5310621 : Nat := 4983230072969 + 3 ^ 40 * 5310621 * 2
def baseEnd_5310621 : Nat := 2726901146860771904614405

theorem tailTrace_5310621 : CollatzResearch.WordTrace tailWord_5310621 prefixEnd_5310621 2726901146860771904614405 := by
  unfold tailWord_5310621
  simp only [CollatzResearch.WordTrace]
  refine ⟨193694260493534573703395717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129129506995689715802263811 193694260493534573703395717)
  ·
    refine ⟨36317673842537732569386697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193694260493534573703395717 36317673842537732569386697)
    ·
      refine ⟨27238255381903299427040023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36317673842537732569386697 27238255381903299427040023)
      ·
        refine ⟨40857383072854949140560035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27238255381903299427040023 40857383072854949140560035)
        ·
          refine ⟨61286074609282423710840053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40857383072854949140560035 61286074609282423710840053)
          ·
            refine ⟨5745569494620227222891255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61286074609282423710840053 5745569494620227222891255)
            ·
              refine ⟨8618354241930340834336883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745569494620227222891255 8618354241930340834336883)
              ·
                refine ⟨12927531362895511251505325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8618354241930340834336883 12927531362895511251505325)
                ·
                  refine ⟨4847824261085816719314497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12927531362895511251505325 4847824261085816719314497)
                  ·
                    refine ⟨3635868195814362539485873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4847824261085816719314497 3635868195814362539485873)
                    ·
                      refine ⟨2726901146860771904614405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635868195814362539485873 2726901146860771904614405)
                      ·
                        rfl

theorem cell23_5310621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_5310621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310621 prefixEnd_5310621 := by exact prefixLift 5310621
  have htrace : WordTrace (prefixWord ++ tailWord_5310621) baseStart_5310621 baseEnd_5310621 := by
    simpa [prefixWord, tailWord_5310621, baseEnd_5310621] using wordTrace_append hprefix tailTrace_5310621
  have hstable : (prefixWord ++ tailWord_5310621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310621).length < 2 ^ (prefixWord ++ tailWord_5310621).sum := by decide
  have hdescent : baseEnd_5310621 < baseStart_5310621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310638 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5310638 : Nat := 118140960795 + 5310638 * 2 ^ 59
def prefixEnd_5310638 : Nat := 4983230072969 + 3 ^ 40 * 5310638 * 2
def baseEnd_5310638 : Nat := 2726909876031898338101827

theorem tailTrace_5310638 : CollatzResearch.WordTrace tailWord_5310638 prefixEnd_5310638 2726909876031898338101827 := by
  unfold tailWord_5310638
  simp only [CollatzResearch.WordTrace]
  refine ⟨24211860066809123200845571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129129920356315323737843045 24211860066809123200845571)
  ·
    refine ⟨36317790100213684801268357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24211860066809123200845571 36317790100213684801268357)
    ·
      refine ⟨6809585643790065900237817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36317790100213684801268357 6809585643790065900237817)
      ·
        refine ⟨5107189232842549425178363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6809585643790065900237817 5107189232842549425178363)
        ·
          refine ⟨7660783849263824137767545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107189232842549425178363 7660783849263824137767545)
          ·
            refine ⟨5745587886947868103325659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7660783849263824137767545 5745587886947868103325659)
            ·
              refine ⟨8618381830421802154988489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745587886947868103325659 8618381830421802154988489)
              ·
                refine ⟨6463786372816351616241367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8618381830421802154988489 6463786372816351616241367)
                ·
                  refine ⟨9695679559224527424362051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6463786372816351616241367 9695679559224527424362051)
                  ·
                    refine ⟨14543519338836791136543077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9695679559224527424362051 14543519338836791136543077)
                    ·
                      refine ⟨2726909876031898338101827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14543519338836791136543077 2726909876031898338101827)
                      ·
                        rfl

theorem cell23_5310638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5310638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310638 prefixEnd_5310638 := by exact prefixLift 5310638
  have htrace : WordTrace (prefixWord ++ tailWord_5310638) baseStart_5310638 baseEnd_5310638 := by
    simpa [prefixWord, tailWord_5310638, baseEnd_5310638] using wordTrace_append hprefix tailTrace_5310638
  have hstable : (prefixWord ++ tailWord_5310638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310638).length < 2 ^ (prefixWord ++ tailWord_5310638).sum := by decide
  have hdescent : baseEnd_5310638 < baseStart_5310638 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310641 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 3]
def baseStart_5310641 : Nat := 118140960795 + 5310641 * 2 ^ 59
def prefixEnd_5310641 : Nat := 4983230072969 + 3 ^ 40 * 5310641 * 2
def baseEnd_5310641 : Nat := 2726911416473861826364313

theorem tailTrace_5310641 : CollatzResearch.WordTrace tailWord_5310641 prefixEnd_5310641 2726911416473861826364313 := by
  unfold tailWord_5310641
  simp only [CollatzResearch.WordTrace]
  refine ⟨193694989953462117119123777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129129993302308078079415851 193694989953462117119123777)
  ·
    refine ⟨145271242465096587839342833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193694989953462117119123777 145271242465096587839342833)
    ·
      refine ⟨108953431848822440879507125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145271242465096587839342833 108953431848822440879507125)
      ·
        refine ⟨10214384235827103832453793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108953431848822440879507125 10214384235827103832453793)
        ·
          refine ⟨7660788176870327874340345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10214384235827103832453793 7660788176870327874340345)
          ·
            refine ⟨5745591132652745905755259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7660788176870327874340345 5745591132652745905755259)
            ·
              refine ⟨8618386698979118858632889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745591132652745905755259 8618386698979118858632889)
              ·
                refine ⟨6463790024234339143974667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8618386698979118858632889 6463790024234339143974667)
                ·
                  refine ⟨9695685036351508715962001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6463790024234339143974667 9695685036351508715962001)
                  ·
                    refine ⟨7271763777263631536971501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9695685036351508715962001 7271763777263631536971501)
                    ·
                      refine ⟨2726911416473861826364313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7271763777263631536971501 2726911416473861826364313)
                      ·
                        rfl

theorem cell23_5310641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_5310641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310641 prefixEnd_5310641 := by exact prefixLift 5310641
  have htrace : WordTrace (prefixWord ++ tailWord_5310641) baseStart_5310641 baseEnd_5310641 := by
    simpa [prefixWord, tailWord_5310641, baseEnd_5310641] using wordTrace_append hprefix tailTrace_5310641
  have hstable : (prefixWord ++ tailWord_5310641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310641).length < 2 ^ (prefixWord ++ tailWord_5310641).sum := by decide
  have hdescent : baseEnd_5310641 < baseStart_5310641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310643 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 8]
def baseStart_5310643 : Nat := 118140960795 + 5310643 * 2 ^ 59
def prefixEnd_5310643 : Nat := 4983230072969 + 3 ^ 40 * 5310643 * 2
def baseEnd_5310643 : Nat := 2726912443435170818539303

theorem tailTrace_5310643 : CollatzResearch.WordTrace tailWord_5310643 prefixEnd_5310643 2726912443435170818539303 := by
  unfold tailWord_5310643
  simp only [CollatzResearch.WordTrace]
  refine ⟨193695062899454871460696583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129130041932969914307131055 193695062899454871460696583)
  ·
    refine ⟨290542594349182307191044875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193695062899454871460696583 290542594349182307191044875)
    ·
      refine ⟨435813891523773460786567313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290542594349182307191044875 435813891523773460786567313)
      ·
        refine ⟨326860418642830095589925485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435813891523773460786567313 326860418642830095589925485)
        ·
          refine ⟨122572656991061285846222057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 326860418642830095589925485 122572656991061285846222057)
          ·
            refine ⟨91929492743295964384666543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122572656991061285846222057 91929492743295964384666543)
            ·
              refine ⟨137894239114943946576999815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91929492743295964384666543 137894239114943946576999815)
              ·
                refine ⟨206841358672415919865499723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137894239114943946576999815 206841358672415919865499723)
                ·
                  refine ⟨310262038008623879798249585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206841358672415919865499723 310262038008623879798249585)
                  ·
                    refine ⟨232696528506467909848687189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 310262038008623879798249585 232696528506467909848687189)
                    ·
                      refine ⟨2726912443435170818539303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 232696528506467909848687189 2726912443435170818539303)
                      ·
                        rfl

theorem cell23_5310643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 8].length) (baseStart_5310643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310643 prefixEnd_5310643 := by exact prefixLift 5310643
  have htrace : WordTrace (prefixWord ++ tailWord_5310643) baseStart_5310643 baseEnd_5310643 := by
    simpa [prefixWord, tailWord_5310643, baseEnd_5310643] using wordTrace_append hprefix tailTrace_5310643
  have hstable : (prefixWord ++ tailWord_5310643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310643).length < 2 ^ (prefixWord ++ tailWord_5310643).sum := by decide
  have hdescent : baseEnd_5310643 < baseStart_5310643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310654 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_5310654 : Nat := 118140960795 + 5310654 * 2 ^ 59
def prefixEnd_5310654 : Nat := 4983230072969 + 3 ^ 40 * 5310654 * 2
def baseEnd_5310654 : Nat := 2726918091722370275501753

theorem tailTrace_5310654 : CollatzResearch.WordTrace tailWord_5310654 prefixEnd_5310654 2726918091722370275501753 := by
  unfold tailWord_5310654
  simp only [CollatzResearch.WordTrace]
  refine ⟨24211933012801877542418377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129130309401610013559564677 24211933012801877542418377)
  ·
    refine ⟨18158949759601408156813783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24211933012801877542418377 18158949759601408156813783)
    ·
      refine ⟨27238424639402112235220675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18158949759601408156813783 27238424639402112235220675)
      ·
        refine ⟨40857636959103168352831013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27238424639402112235220675 40857636959103168352831013)
        ·
          refine ⟨7660806929831844066155815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40857636959103168352831013 7660806929831844066155815)
          ·
            refine ⟨11491210394747766099233723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7660806929831844066155815 11491210394747766099233723)
            ·
              refine ⟨17236815592121649148850585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11491210394747766099233723 17236815592121649148850585)
              ·
                refine ⟨12927611694091236861637939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17236815592121649148850585 12927611694091236861637939)
                ·
                  refine ⟨19391417541136855292456909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12927611694091236861637939 19391417541136855292456909)
                  ·
                    refine ⟨7271781577926320734671341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19391417541136855292456909 7271781577926320734671341)
                    ·
                      refine ⟨2726918091722370275501753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7271781577926320734671341 2726918091722370275501753)
                      ·
                        rfl

theorem cell23_5310654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_5310654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310654 prefixEnd_5310654 := by exact prefixLift 5310654
  have htrace : WordTrace (prefixWord ++ tailWord_5310654) baseStart_5310654 baseEnd_5310654 := by
    simpa [prefixWord, tailWord_5310654, baseEnd_5310654] using wordTrace_append hprefix tailTrace_5310654
  have hstable : (prefixWord ++ tailWord_5310654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310654).length < 2 ^ (prefixWord ++ tailWord_5310654).sum := by decide
  have hdescent : baseEnd_5310654 < baseStart_5310654 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310700 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 7]
def baseStart_5310700 : Nat := 118140960795 + 5310700 * 2 ^ 59
def prefixEnd_5310700 : Nat := 4983230072969 + 3 ^ 40 * 5310700 * 2
def baseEnd_5310700 : Nat := 302993523536941899502949

theorem tailTrace_5310700 : CollatzResearch.WordTrace tailWord_5310700 prefixEnd_5310700 302993523536941899502949 := by
  unfold tailWord_5310700
  simp only [CollatzResearch.WordTrace]
  refine ⟨96848570930124185097760777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129131427906832246797014369 96848570930124185097760777)
  ·
    refine ⟨72636428197593138823320583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96848570930124185097760777 72636428197593138823320583)
    ·
      refine ⟨108954642296389708234980875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72636428197593138823320583 108954642296389708234980875)
      ·
        refine ⟨163431963444584562352471313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108954642296389708234980875 163431963444584562352471313)
        ·
          refine ⟨122573972583438421764353485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163431963444584562352471313 122573972583438421764353485)
          ·
            refine ⟨45965239718789408161632557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122573972583438421764353485 45965239718789408161632557)
            ·
              refine ⟨17236964894546028060612209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45965239718789408161632557 17236964894546028060612209)
              ·
                refine ⟨12927723670909521045459157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17236964894546028060612209 12927723670909521045459157)
                ·
                  refine ⟨302993523536941899502949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12927723670909521045459157 302993523536941899502949)
                  ·
                    rfl

theorem cell23_5310700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 7].length) (baseStart_5310700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310700 prefixEnd_5310700 := by exact prefixLift 5310700
  have htrace : WordTrace (prefixWord ++ tailWord_5310700) baseStart_5310700 baseEnd_5310700 := by
    simpa [prefixWord, tailWord_5310700, baseEnd_5310700] using wordTrace_append hprefix tailTrace_5310700
  have hstable : (prefixWord ++ tailWord_5310700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310700).length < 2 ^ (prefixWord ++ tailWord_5310700).sum := by decide
  have hdescent : baseEnd_5310700 < baseStart_5310700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310728 : List Nat := [2, 1, 3, 2, 3, 3, 1, 2, 2, 2, 2]
def baseStart_5310728 : Nat := 118140960795 + 5310728 * 2 ^ 59
def prefixEnd_5310728 : Nat := 4983230072969 + 3 ^ 40 * 5310728 * 2
def baseEnd_5310728 : Nat := 2726956089290802985976413

theorem tailTrace_5310728 : CollatzResearch.WordTrace tailWord_5310728 prefixEnd_5310728 2726956089290802985976413 := by
  unfold tailWord_5310728
  simp only [CollatzResearch.WordTrace]
  refine ⟨96849081552073465488770419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129132108736097953985027225 96849081552073465488770419)
  ·
    refine ⟨145273622328110198233155629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96849081552073465488770419 145273622328110198233155629)
    ·
      refine ⟨54477608373041324337433361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145273622328110198233155629 54477608373041324337433361)
      ·
        refine ⟨40858206279780993253075021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54477608373041324337433361 40858206279780993253075021)
        ·
          refine ⟨15321827354917872469903133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40858206279780993253075021 15321827354917872469903133)
          ·
            refine ⟨5745685258094202176213675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15321827354917872469903133 5745685258094202176213675)
            ·
              refine ⟨8618527887141303264320513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5745685258094202176213675 8618527887141303264320513)
              ·
                refine ⟨6463895915355977448240385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8618527887141303264320513 6463895915355977448240385)
                ·
                  refine ⟨4847921936516983086180289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6463895915355977448240385 4847921936516983086180289)
                  ·
                    refine ⟨3635941452387737314635217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4847921936516983086180289 3635941452387737314635217)
                    ·
                      refine ⟨2726956089290802985976413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635941452387737314635217 2726956089290802985976413)
                      ·
                        rfl

theorem cell23_5310728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_5310728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310728 prefixEnd_5310728 := by exact prefixLift 5310728
  have htrace : WordTrace (prefixWord ++ tailWord_5310728) baseStart_5310728 baseEnd_5310728 := by
    simpa [prefixWord, tailWord_5310728, baseEnd_5310728] using wordTrace_append hprefix tailTrace_5310728
  have hstable : (prefixWord ++ tailWord_5310728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310728).length < 2 ^ (prefixWord ++ tailWord_5310728).sum := by decide
  have hdescent : baseEnd_5310728 < baseStart_5310728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310767 : List Nat := [1, 1, 2, 1, 2, 1, 4, 2, 1, 6, 2]
def baseStart_5310767 : Nat := 118140960795 + 5310767 * 2 ^ 59
def prefixEnd_5310767 : Nat := 4983230072969 + 3 ^ 40 * 5310767 * 2
def baseEnd_5310767 : Nat := 2726976115036328333388733

theorem tailTrace_5310767 : CollatzResearch.WordTrace tailWord_5310767 prefixEnd_5310767 2726976115036328333388733 := by
  unfold tailWord_5310767
  simp only [CollatzResearch.WordTrace]
  refine ⟨193699585551005640638210555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129133057034003760425473703 193699585551005640638210555)
  ·
    refine ⟨290549378326508460957315833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193699585551005640638210555 290549378326508460957315833)
    ·
      refine ⟨217912033744881345717986875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290549378326508460957315833 217912033744881345717986875)
      ·
        refine ⟨326868050617322018576980313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217912033744881345717986875 326868050617322018576980313)
        ·
          refine ⟨245151037962991513932735235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326868050617322018576980313 245151037962991513932735235)
          ·
            refine ⟨367726556944487270899102853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245151037962991513932735235 367726556944487270899102853)
            ·
              refine ⟨68948729427091363293581785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 367726556944487270899102853 68948729427091363293581785)
              ·
                refine ⟨51711547070318522470186339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68948729427091363293581785 51711547070318522470186339)
                ·
                  refine ⟨77567320605477783705279509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51711547070318522470186339 77567320605477783705279509)
                  ·
                    refine ⟨3635968153381771111184977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77567320605477783705279509 3635968153381771111184977)
                    ·
                      refine ⟨2726976115036328333388733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3635968153381771111184977 2726976115036328333388733)
                      ·
                        rfl

theorem cell23_5310767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 2, 1, 6, 2].length) (baseStart_5310767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310767 prefixEnd_5310767 := by exact prefixLift 5310767
  have htrace : WordTrace (prefixWord ++ tailWord_5310767) baseStart_5310767 baseEnd_5310767 := by
    simpa [prefixWord, tailWord_5310767, baseEnd_5310767] using wordTrace_append hprefix tailTrace_5310767
  have hstable : (prefixWord ++ tailWord_5310767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310767).length < 2 ^ (prefixWord ++ tailWord_5310767).sum := by decide
  have hdescent : baseEnd_5310767 < baseStart_5310767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310787 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 3]
def baseStart_5310787 : Nat := 118140960795 + 5310787 * 2 ^ 59
def prefixEnd_5310787 : Nat := 4983230072969 + 3 ^ 40 * 5310787 * 2
def baseEnd_5310787 : Nat := 2726986384649418255138641

theorem tailTrace_5310787 : CollatzResearch.WordTrace tailWord_5310787 prefixEnd_5310787 2726986384649418255138641 := by
  unfold tailWord_5310787
  simp only [CollatzResearch.WordTrace]
  refine ⟨193700315010933184053938615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129133543340622122702625743 193700315010933184053938615)
  ·
    refine ⟨290550472516399776080907923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193700315010933184053938615 290550472516399776080907923)
    ·
      refine ⟨435825708774599664121361885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290550472516399776080907923 435825708774599664121361885)
      ·
        refine ⟨163434640790474874045510707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435825708774599664121361885 163434640790474874045510707)
        ·
          refine ⟨245151961185712311068266061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163434640790474874045510707 245151961185712311068266061)
          ·
            refine ⟨91931985444642116650599773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245151961185712311068266061 91931985444642116650599773)
            ·
              refine ⟨34474494541740793743974915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91931985444642116650599773 34474494541740793743974915)
              ·
                refine ⟨51711741812611190615962373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34474494541740793743974915 51711741812611190615962373)
                ·
                  refine ⟨9695951589864598240492945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51711741812611190615962373 9695951589864598240492945)
                  ·
                    refine ⟨7271963692398448680369709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9695951589864598240492945 7271963692398448680369709)
                    ·
                      refine ⟨2726986384649418255138641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7271963692398448680369709 2726986384649418255138641)
                      ·
                        rfl

theorem cell23_5310787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 3].length) (baseStart_5310787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310787 prefixEnd_5310787 := by exact prefixLift 5310787
  have htrace : WordTrace (prefixWord ++ tailWord_5310787) baseStart_5310787 baseEnd_5310787 := by
    simpa [prefixWord, tailWord_5310787, baseEnd_5310787] using wordTrace_append hprefix tailTrace_5310787
  have hstable : (prefixWord ++ tailWord_5310787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310787).length < 2 ^ (prefixWord ++ tailWord_5310787).sum := by decide
  have hdescent : baseEnd_5310787 < baseStart_5310787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310807 : List Nat := [1, 1, 3, 2, 3, 1, 3, 3, 6]
def baseStart_5310807 : Nat := 118140960795 + 5310807 * 2 ^ 59
def prefixEnd_5310807 : Nat := 4983230072969 + 3 ^ 40 * 5310807 * 2
def baseEnd_5310807 : Nat := 302999628251389797432061

theorem tailTrace_5310807 : CollatzResearch.WordTrace tailWord_5310807 prefixEnd_5310807 302999628251389797432061 := by
  unfold tailWord_5310807
  simp only [CollatzResearch.WordTrace]
  refine ⟨193701044470860727469666675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129134029647240484979777783 193701044470860727469666675)
  ·
    refine ⟨290551566706291091204500013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193701044470860727469666675 290551566706291091204500013)
    ·
      refine ⟨108956837514859159201687505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290551566706291091204500013 108956837514859159201687505)
      ·
        refine ⟨81717628136144369401265629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108956837514859159201687505 81717628136144369401265629)
        ·
          refine ⟨30644110551054138525474611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81717628136144369401265629 30644110551054138525474611)
          ·
            refine ⟨45966165826581207788211917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30644110551054138525474611 45966165826581207788211917)
            ·
              refine ⟨17237312184967952920579469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45966165826581207788211917 17237312184967952920579469)
              ·
                refine ⟨6463992069362982345217301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17237312184967952920579469 6463992069362982345217301)
                ·
                  refine ⟨302999628251389797432061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6463992069362982345217301 302999628251389797432061)
                  ·
                    rfl

theorem cell23_5310807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 3, 6].length) (baseStart_5310807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310807 prefixEnd_5310807 := by exact prefixLift 5310807
  have htrace : WordTrace (prefixWord ++ tailWord_5310807) baseStart_5310807 baseEnd_5310807 := by
    simpa [prefixWord, tailWord_5310807, baseEnd_5310807] using wordTrace_append hprefix tailTrace_5310807
  have hstable : (prefixWord ++ tailWord_5310807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310807).length < 2 ^ (prefixWord ++ tailWord_5310807).sum := by decide
  have hdescent : baseEnd_5310807 < baseStart_5310807 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310844 : List Nat := [2, 2, 2, 1, 1, 1, 2, 3, 4, 3, 2]
def baseStart_5310844 : Nat := 118140960795 + 5310844 * 2 ^ 59
def prefixEnd_5310844 : Nat := 4983230072969 + 3 ^ 40 * 5310844 * 2
def baseEnd_5310844 : Nat := 2727015653046724532125879

theorem tailTrace_5310844 : CollatzResearch.WordTrace tailWord_5310844 prefixEnd_5310844 2727015653046724532125879 := by
  unfold tailWord_5310844
  simp only [CollatzResearch.WordTrace]
  refine ⟨96851196985863341394381793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129134929314484455192509057 96851196985863341394381793)
  ·
    refine ⟨72638397739397506045786345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96851196985863341394381793 72638397739397506045786345)
    ·
      refine ⟨54478798304548129534339759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72638397739397506045786345 54478798304548129534339759)
      ·
        refine ⟨81718197456822194301509639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54478798304548129534339759 81718197456822194301509639)
        ·
          refine ⟨122577296185233291452264459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81718197456822194301509639 122577296185233291452264459)
          ·
            refine ⟨183865944277849937178396689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122577296185233291452264459 183865944277849937178396689)
            ·
              refine ⟨137899458208387452883797517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183865944277849937178396689 137899458208387452883797517)
              ·
                refine ⟨51712296828145294831424069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137899458208387452883797517 51712296828145294831424069)
                ·
                  refine ⟨9696055655277242780892013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51712296828145294831424069 9696055655277242780892013)
                  ·
                    refine ⟨3636020870728966042834505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9696055655277242780892013 3636020870728966042834505)
                    ·
                      refine ⟨2727015653046724532125879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636020870728966042834505 2727015653046724532125879)
                      ·
                        rfl

theorem cell23_5310844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 3, 4, 3, 2].length) (baseStart_5310844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310844 prefixEnd_5310844 := by exact prefixLift 5310844
  have htrace : WordTrace (prefixWord ++ tailWord_5310844) baseStart_5310844 baseEnd_5310844 := by
    simpa [prefixWord, tailWord_5310844, baseEnd_5310844] using wordTrace_append hprefix tailTrace_5310844
  have hstable : (prefixWord ++ tailWord_5310844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310844).length < 2 ^ (prefixWord ++ tailWord_5310844).sum := by decide
  have hdescent : baseEnd_5310844 < baseStart_5310844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310868 : List Nat := [2, 4, 2, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_5310868 : Nat := 118140960795 + 5310868 * 2 ^ 59
def prefixEnd_5310868 : Nat := 4983230072969 + 3 ^ 40 * 5310868 * 2
def baseEnd_5310868 : Nat := 2727027976582432438225769

theorem tailTrace_5310868 : CollatzResearch.WordTrace tailWord_5310868 prefixEnd_5310868 2727027976582432438225769 := by
  unfold tailWord_5310868
  simp only [CollatzResearch.WordTrace]
  refine ⟨96851634661819867443818629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129135512882426489925091505 96851634661819867443818629)
  ·
    refine ⟨18159681499091225145715993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96851634661819867443818629 18159681499091225145715993)
    ·
      refine ⟨13619761124318418859286995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18159681499091225145715993 13619761124318418859286995)
      ·
        refine ⟨20429641686477628288930493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13619761124318418859286995 20429641686477628288930493)
        ·
          refine ⟨7661115632429110608348935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20429641686477628288930493 7661115632429110608348935)
          ·
            refine ⟨11491673448643665912523403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661115632429110608348935 11491673448643665912523403)
            ·
              refine ⟨17237510172965498868785105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11491673448643665912523403 17237510172965498868785105)
              ·
                refine ⟨12928132629724124151588829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17237510172965498868785105 12928132629724124151588829)
                ·
                  refine ⟨4848049736146546556845811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12928132629724124151588829 4848049736146546556845811)
                  ·
                    refine ⟨7272074604219819835268717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4848049736146546556845811 7272074604219819835268717)
                    ·
                      refine ⟨2727027976582432438225769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7272074604219819835268717 2727027976582432438225769)
                      ·
                        rfl

theorem cell23_5310868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_5310868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310868 prefixEnd_5310868 := by exact prefixLift 5310868
  have htrace : WordTrace (prefixWord ++ tailWord_5310868) baseStart_5310868 baseEnd_5310868 := by
    simpa [prefixWord, tailWord_5310868, baseEnd_5310868] using wordTrace_append hprefix tailTrace_5310868
  have hstable : (prefixWord ++ tailWord_5310868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310868).length < 2 ^ (prefixWord ++ tailWord_5310868).sum := by decide
  have hdescent : baseEnd_5310868 < baseStart_5310868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310874 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5310874 : Nat := 118140960795 + 5310874 * 2 ^ 59
def prefixEnd_5310874 : Nat := 4983230072969 + 3 ^ 40 * 5310874 * 2
def baseEnd_5310874 : Nat := 2727031057466359414750741

theorem tailTrace_5310874 : CollatzResearch.WordTrace tailWord_5310874 prefixEnd_5310874 2727031057466359414750741 := by
  unfold tailWord_5310874
  simp only [CollatzResearch.WordTrace]
  refine ⟨48425872040404499478088919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129135658774411998608237117 48425872040404499478088919)
  ·
    refine ⟨72638808060606749217133379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48425872040404499478088919 72638808060606749217133379)
    ·
      refine ⟨108958212090910123825700069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72638808060606749217133379 108958212090910123825700069)
      ·
        refine ⟨20429664767045648217318763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108958212090910123825700069 20429664767045648217318763)
        ·
          refine ⟨30644497150568472325978145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20429664767045648217318763 30644497150568472325978145)
          ·
            refine ⟨22983372862926354244483609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30644497150568472325978145 22983372862926354244483609)
            ·
              refine ⟨17237529647194765683362707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22983372862926354244483609 17237529647194765683362707)
              ·
                refine ⟨25856294470792148525044061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17237529647194765683362707 25856294470792148525044061)
                ·
                  refine ⟨9696110426547055696891523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25856294470792148525044061 9696110426547055696891523)
                  ·
                    refine ⟨14544165639820583545337285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9696110426547055696891523 14544165639820583545337285)
                    ·
                      refine ⟨2727031057466359414750741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14544165639820583545337285 2727031057466359414750741)
                      ·
                        rfl

theorem cell23_5310874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5310874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310874 prefixEnd_5310874 := by exact prefixLift 5310874
  have htrace : WordTrace (prefixWord ++ tailWord_5310874) baseStart_5310874 baseEnd_5310874 := by
    simpa [prefixWord, tailWord_5310874, baseEnd_5310874] using wordTrace_append hprefix tailTrace_5310874
  have hstable : (prefixWord ++ tailWord_5310874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310874).length < 2 ^ (prefixWord ++ tailWord_5310874).sum := by decide
  have hdescent : baseEnd_5310874 < baseStart_5310874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310878 : List Nat := [4, 3, 1, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_5310878 : Nat := 118140960795 + 5310878 * 2 ^ 59
def prefixEnd_5310878 : Nat := 4983230072969 + 3 ^ 40 * 5310878 * 2
def baseEnd_5310878 : Nat := 2727033111388977399100723

theorem tailTrace_5310878 : CollatzResearch.WordTrace tailWord_5310878 prefixEnd_5310878 2727033111388977399100723 := by
  unfold tailWord_5310878
  simp only [CollatzResearch.WordTrace]
  refine ⟨24212954256700438324437661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129135756035735671063667525 24212954256700438324437661)
  ·
    refine ⟨9079857846262664371664123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24212954256700438324437661 9079857846262664371664123)
    ·
      refine ⟨13619786769393996557496185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9079857846262664371664123 13619786769393996557496185)
      ·
        refine ⟨10214840077045497418122139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13619786769393996557496185 10214840077045497418122139)
        ·
          refine ⟨15322260115568246127183209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10214840077045497418122139 15322260115568246127183209)
          ·
            refine ⟨11491695086676184595387407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15322260115568246127183209 11491695086676184595387407)
            ·
              refine ⟨17237542630014276893081111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11491695086676184595387407 17237542630014276893081111)
              ·
                refine ⟨25856313945021415339621667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17237542630014276893081111 25856313945021415339621667)
                ·
                  refine ⟨38784470917532123009432501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25856313945021415339621667 38784470917532123009432501)
                  ·
                    refine ⟨3636044148518636532134297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38784470917532123009432501 3636044148518636532134297)
                    ·
                      refine ⟨2727033111388977399100723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636044148518636532134297 2727033111388977399100723)
                      ·
                        rfl

theorem cell23_5310878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_5310878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310878 prefixEnd_5310878 := by exact prefixLift 5310878
  have htrace : WordTrace (prefixWord ++ tailWord_5310878) baseStart_5310878 baseEnd_5310878 := by
    simpa [prefixWord, tailWord_5310878, baseEnd_5310878] using wordTrace_append hprefix tailTrace_5310878
  have hstable : (prefixWord ++ tailWord_5310878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310878).length < 2 ^ (prefixWord ++ tailWord_5310878).sum := by decide
  have hdescent : baseEnd_5310878 < baseStart_5310878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310888 : List Nat := [2, 1, 6, 1, 1, 1, 4, 1, 1, 5]
def baseStart_5310888 : Nat := 118140960795 + 5310888 * 2 ^ 59
def prefixEnd_5310888 : Nat := 4983230072969 + 3 ^ 40 * 5310888 * 2
def baseEnd_5310888 : Nat := 909012748731840786658559

theorem tailTrace_5310888 : CollatzResearch.WordTrace tailWord_5310888 prefixEnd_5310888 909012748731840786658559 := by
  unfold tailWord_5310888
  simp only [CollatzResearch.WordTrace]
  refine ⟨96851999391783639151682659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129135999189044852202243545 96851999391783639151682659)
  ·
    refine ⟨145277999087675458727523989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96851999391783639151682659 145277999087675458727523989)
    ·
      refine ⟨6809906207234787127852687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 145277999087675458727523989 6809906207234787127852687)
      ·
        refine ⟨10214859310852180691779031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6809906207234787127852687 10214859310852180691779031)
        ·
          refine ⟨15322288966278271037668547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10214859310852180691779031 15322288966278271037668547)
          ·
            refine ⟨22983433449417406556502821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15322288966278271037668547 22983433449417406556502821)
            ·
              refine ⟨4309393771765763729344279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22983433449417406556502821 4309393771765763729344279)
              ·
                refine ⟨6464090657648645594016419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309393771765763729344279 6464090657648645594016419)
                ·
                  refine ⟨9696135986472968391024629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6464090657648645594016419 9696135986472968391024629)
                  ·
                    refine ⟨909012748731840786658559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9696135986472968391024629 909012748731840786658559)
                    ·
                      rfl

theorem cell23_5310888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_5310888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310888 prefixEnd_5310888 := by exact prefixLift 5310888
  have htrace : WordTrace (prefixWord ++ tailWord_5310888) baseStart_5310888 baseEnd_5310888 := by
    simpa [prefixWord, tailWord_5310888, baseEnd_5310888] using wordTrace_append hprefix tailTrace_5310888
  have hstable : (prefixWord ++ tailWord_5310888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310888).length < 2 ^ (prefixWord ++ tailWord_5310888).sum := by decide
  have hdescent : baseEnd_5310888 < baseStart_5310888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310897 : List Nat := [1, 2, 2, 4, 1, 3, 10]
def baseStart_5310897 : Nat := 118140960795 + 5310897 * 2 ^ 59
def prefixEnd_5310897 : Nat := 4983230072969 + 3 ^ 40 * 5310897 * 2
def baseEnd_5310897 : Nat := 33667195895326084256335

theorem tailTrace_5310897 : CollatzResearch.WordTrace tailWord_5310897 prefixEnd_5310897 33667195895326084256335 := by
  unfold tailWord_5310897
  simp only [CollatzResearch.WordTrace]
  refine ⟨193704327040534672840442945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129136218027023115226961963 193704327040534672840442945)
  ·
    refine ⟨145278245280401004630332209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193704327040534672840442945 145278245280401004630332209)
    ·
      refine ⟨108958683960300753472749157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145278245280401004630332209 108958683960300753472749157)
      ·
        refine ⟨20429753242556391276140467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108958683960300753472749157 20429753242556391276140467)
        ·
          refine ⟨30644629863834586914210701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20429753242556391276140467 30644629863834586914210701)
          ·
            refine ⟨11491736198937970092829013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30644629863834586914210701 11491736198937970092829013)
            ·
              refine ⟨33667195895326084256335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11491736198937970092829013 33667195895326084256335)
              ·
                rfl

theorem cell23_5310897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 10].length) (baseStart_5310897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310897 prefixEnd_5310897 := by exact prefixLift 5310897
  have htrace : WordTrace (prefixWord ++ tailWord_5310897) baseStart_5310897 baseEnd_5310897 := by
    simpa [prefixWord, tailWord_5310897, baseEnd_5310897] using wordTrace_append hprefix tailTrace_5310897
  have hstable : (prefixWord ++ tailWord_5310897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310897).length < 2 ^ (prefixWord ++ tailWord_5310897).sum := by decide
  have hdescent : baseEnd_5310897 < baseStart_5310897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310901 : List Nat := [1, 3, 3, 2, 3, 1, 1, 1, 4, 4]
def baseStart_5310901 : Nat := 118140960795 + 5310901 * 2 ^ 59
def prefixEnd_5310901 : Nat := 4983230072969 + 3 ^ 40 * 5310901 * 2
def baseEnd_5310901 : Nat := 909014973814676936371039

theorem tailTrace_5310901 : CollatzResearch.WordTrace tailWord_5310901 prefixEnd_5310901 909014973814676936371039 := by
  unfold tailWord_5310901
  simp only [CollatzResearch.WordTrace]
  refine ⟨193704472932520181523588557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129136315288346787682392371 193704472932520181523588557)
  ·
    refine ⟨72639177349695068071345709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193704472932520181523588557 72639177349695068071345709)
    ·
      refine ⟨27239691506135650526754641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72639177349695068071345709 27239691506135650526754641)
      ·
        refine ⟨20429768629601737895065981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27239691506135650526754641 20429768629601737895065981)
        ·
          refine ⟨7661163236100651710649743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20429768629601737895065981 7661163236100651710649743)
          ·
            refine ⟨11491744854150977565974615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661163236100651710649743 11491744854150977565974615)
            ·
              refine ⟨17237617281226466348961923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11491744854150977565974615 17237617281226466348961923)
              ·
                refine ⟨25856425921839699523442885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17237617281226466348961923 25856425921839699523442885)
                ·
                  refine ⟨4848079860344943660645541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25856425921839699523442885 4848079860344943660645541)
                  ·
                    refine ⟨909014973814676936371039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4848079860344943660645541 909014973814676936371039)
                    ·
                      rfl

theorem cell23_5310901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 1, 4, 4].length) (baseStart_5310901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310901 prefixEnd_5310901 := by exact prefixLift 5310901
  have htrace : WordTrace (prefixWord ++ tailWord_5310901) baseStart_5310901 baseEnd_5310901 := by
    simpa [prefixWord, tailWord_5310901, baseEnd_5310901] using wordTrace_append hprefix tailTrace_5310901
  have hstable : (prefixWord ++ tailWord_5310901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310901).length < 2 ^ (prefixWord ++ tailWord_5310901).sum := by decide
  have hdescent : baseEnd_5310901 < baseStart_5310901 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310908 : List Nat := [2, 2, 2, 4, 1, 1, 1, 3, 3, 2, 2]
def baseStart_5310908 : Nat := 118140960795 + 5310908 * 2 ^ 59
def prefixEnd_5310908 : Nat := 4983230072969 + 3 ^ 40 * 5310908 * 2
def baseEnd_5310908 : Nat := 2727048515808612281725585

theorem tailTrace_5310908 : CollatzResearch.WordTrace tailWord_5310908 prefixEnd_5310908 2727048515808612281725585 := by
  unfold tailWord_5310908
  simp only [CollatzResearch.WordTrace]
  refine ⟨96852364121747410859546689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129136485495663214479395585 96852364121747410859546689)
  ·
    refine ⟨72639273091310558144660017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96852364121747410859546689 72639273091310558144660017)
    ·
      refine ⟨54479454818482918608495013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72639273091310558144660017 54479454818482918608495013)
      ·
        refine ⟨10214897778465547239092815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54479454818482918608495013 10214897778465547239092815)
        ·
          refine ⟨15322346667698320858639223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10214897778465547239092815 15322346667698320858639223)
          ·
            refine ⟨22983520001547481287958835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15322346667698320858639223 22983520001547481287958835)
            ·
              refine ⟨34475280002321221931938253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22983520001547481287958835 34475280002321221931938253)
              ·
                refine ⟨12928230000870458224476845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34475280002321221931938253 12928230000870458224476845)
                ·
                  refine ⟨4848086250326421834178817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12928230000870458224476845 4848086250326421834178817)
                  ·
                    refine ⟨3636064687744816375634113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4848086250326421834178817 3636064687744816375634113)
                    ·
                      refine ⟨2727048515808612281725585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636064687744816375634113 2727048515808612281725585)
                      ·
                        rfl

theorem cell23_5310908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_5310908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310908 prefixEnd_5310908 := by exact prefixLift 5310908
  have htrace : WordTrace (prefixWord ++ tailWord_5310908) baseStart_5310908 baseEnd_5310908 := by
    simpa [prefixWord, tailWord_5310908, baseEnd_5310908] using wordTrace_append hprefix tailTrace_5310908
  have hstable : (prefixWord ++ tailWord_5310908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310908).length < 2 ^ (prefixWord ++ tailWord_5310908).sum := by decide
  have hdescent : baseEnd_5310908 < baseStart_5310908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310937 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 5]
def baseStart_5310937 : Nat := 118140960795 + 5310937 * 2 ^ 59
def prefixEnd_5310937 : Nat := 4983230072969 + 3 ^ 40 * 5310937 * 2
def baseEnd_5310937 : Nat := 2727063406747592668262951

theorem tailTrace_5310937 : CollatzResearch.WordTrace tailWord_5310937 prefixEnd_5310937 2727063406747592668262951 := by
  unfold tailWord_5310937
  simp only [CollatzResearch.WordTrace]
  refine ⟨193705785960389759671899065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129137190640259839781266043 193705785960389759671899065)
  ·
    refine ⟨145279339470292319753924299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193705785960389759671899065 145279339470292319753924299)
    ·
      refine ⟨217919009205438479630886449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145279339470292319753924299 217919009205438479630886449)
      ·
        refine ⟨163439256904078859723164837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217919009205438479630886449 163439256904078859723164837)
        ·
          refine ⟨30644860669514786198093407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163439256904078859723164837 30644860669514786198093407)
          ·
            refine ⟨45967291004272179297140111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30644860669514786198093407 45967291004272179297140111)
            ·
              refine ⟨68950936506408268945710167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45967291004272179297140111 68950936506408268945710167)
              ·
                refine ⟨103426404759612403418565251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68950936506408268945710167 103426404759612403418565251)
                ·
                  refine ⟨155139607139418605127847877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103426404759612403418565251 155139607139418605127847877)
                  ·
                    refine ⟨29088676338640988461471477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155139607139418605127847877 29088676338640988461471477)
                    ·
                      refine ⟨2727063406747592668262951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29088676338640988461471477 2727063406747592668262951)
                      ·
                        rfl

theorem cell23_5310937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 4, 5].length) (baseStart_5310937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310937 prefixEnd_5310937 := by exact prefixLift 5310937
  have htrace : WordTrace (prefixWord ++ tailWord_5310937) baseStart_5310937 baseEnd_5310937 := by
    simpa [prefixWord, tailWord_5310937, baseEnd_5310937] using wordTrace_append hprefix tailTrace_5310937
  have hstable : (prefixWord ++ tailWord_5310937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310937).length < 2 ^ (prefixWord ++ tailWord_5310937).sum := by decide
  have hdescent : baseEnd_5310937 < baseStart_5310937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5310941 : List Nat := [1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_5310941 : Nat := 118140960795 + 5310941 * 2 ^ 59
def prefixEnd_5310941 : Nat := 4983230072969 + 3 ^ 40 * 5310941 * 2
def baseEnd_5310941 : Nat := 2727065460670210652612933

theorem tailTrace_5310941 : CollatzResearch.WordTrace tailWord_5310941 prefixEnd_5310941 2727065460670210652612933 := by
  unfold tailWord_5310941
  simp only [CollatzResearch.WordTrace]
  refine ⟨193705931852375268355044677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129137287901583512236696451 193705931852375268355044677)
  ·
    refine ⟨36319862222320362816570877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193705931852375268355044677 36319862222320362816570877)
    ·
      refine ⟨13619948333370136056214079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36319862222320362816570877 13619948333370136056214079)
      ·
        refine ⟨20429922500055204084321119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13619948333370136056214079 20429922500055204084321119)
        ·
          refine ⟨30644883750082806126481679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20429922500055204084321119 30644883750082806126481679)
          ·
            refine ⟨45967325625124209189722519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30644883750082806126481679 45967325625124209189722519)
            ·
              refine ⟨68950988437686313784583779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45967325625124209189722519 68950988437686313784583779)
              ·
                refine ⟨103426482656529470676875669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68950988437686313784583779 103426482656529470676875669)
                ·
                  refine ⟨4848116374524818937978547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 103426482656529470676875669 4848116374524818937978547)
                  ·
                    refine ⟨7272174561787228406967821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4848116374524818937978547 7272174561787228406967821)
                    ·
                      refine ⟨2727065460670210652612933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7272174561787228406967821 2727065460670210652612933)
                      ·
                        rfl

theorem cell23_5310941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_5310941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5310941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5310941 prefixEnd_5310941 := by exact prefixLift 5310941
  have htrace : WordTrace (prefixWord ++ tailWord_5310941) baseStart_5310941 baseEnd_5310941 := by
    simpa [prefixWord, tailWord_5310941, baseEnd_5310941] using wordTrace_append hprefix tailTrace_5310941
  have hstable : (prefixWord ++ tailWord_5310941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5310941).length < 2 ^ (prefixWord ++ tailWord_5310941).sum := by decide
  have hdescent : baseEnd_5310941 < baseStart_5310941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5310941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311038 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_5311038 : Nat := 118140960795 + 5311038 * 2 ^ 59
def prefixEnd_5311038 : Nat := 4983230072969 + 3 ^ 40 * 5311038 * 2
def baseEnd_5311038 : Nat := 303012807588188530344443

theorem tailTrace_5311038 : CollatzResearch.WordTrace tailWord_5311038 prefixEnd_5311038 303012807588188530344443 := by
  unfold tailWord_5311038
  simp only [CollatzResearch.WordTrace]
  refine ⟨24213683716627981740165721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129139646488682569280883845 24213683716627981740165721)
  ·
    refine ⟨18160262787470986305124291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24213683716627981740165721 18160262787470986305124291)
    ·
      refine ⟨27240394181206479457686437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18160262787470986305124291 27240394181206479457686437)
      ·
        refine ⟨5107573908976214898316207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27240394181206479457686437 5107573908976214898316207)
        ·
          refine ⟨7661360863464322347474311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107573908976214898316207 7661360863464322347474311)
          ·
            refine ⟨11492041295196483521211467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661360863464322347474311 11492041295196483521211467)
            ·
              refine ⟨17238061942794725281817201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11492041295196483521211467 17238061942794725281817201)
              ·
                refine ⟨12928546457096043961362901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17238061942794725281817201 12928546457096043961362901)
                ·
                  refine ⟨303012807588188530344443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12928546457096043961362901 303012807588188530344443)
                  ·
                    rfl

theorem cell23_5311038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_5311038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311038 prefixEnd_5311038 := by exact prefixLift 5311038
  have htrace : WordTrace (prefixWord ++ tailWord_5311038) baseStart_5311038 baseEnd_5311038 := by
    simpa [prefixWord, tailWord_5311038, baseEnd_5311038] using wordTrace_append hprefix tailTrace_5311038
  have hstable : (prefixWord ++ tailWord_5311038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311038).length < 2 ^ (prefixWord ++ tailWord_5311038).sum := by decide
  have hdescent : baseEnd_5311038 < baseStart_5311038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311106 : List Nat := [3, 4, 3, 1, 2, 1, 1, 3, 5]
def baseStart_5311106 : Nat := 118140960795 + 5311106 * 2 ^ 59
def prefixEnd_5311106 : Nat := 4983230072969 + 3 ^ 40 * 5311106 * 2
def baseEnd_5311106 : Nat := 303016687219800278561075

theorem tailTrace_5311106 : CollatzResearch.WordTrace tailWord_5311106 prefixEnd_5311106 303016687219800278561075 := by
  unfold tailWord_5311106
  simp only [CollatzResearch.WordTrace]
  refine ⟨48427987474194375383700293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129141299931185001023200781 48427987474194375383700293)
  ·
    refine ⟨9080247651411445384443805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48427987474194375383700293 9080247651411445384443805)
    ·
      refine ⟨3405092869279292019166427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9080247651411445384443805 3405092869279292019166427)
      ·
        refine ⟨5107639303918938028749641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405092869279292019166427 5107639303918938028749641)
        ·
          refine ⟨3830729477939203521562231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5107639303918938028749641 3830729477939203521562231)
          ·
            refine ⟨5746094216908805282343347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3830729477939203521562231 5746094216908805282343347)
            ·
              refine ⟨8619141325363207923515021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5746094216908805282343347 8619141325363207923515021)
              ·
                refine ⟨3232177997011202971318133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8619141325363207923515021 3232177997011202971318133)
                ·
                  refine ⟨303016687219800278561075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3232177997011202971318133 303016687219800278561075)
                  ·
                    rfl

theorem cell23_5311106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_5311106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311106 prefixEnd_5311106 := by exact prefixLift 5311106
  have htrace : WordTrace (prefixWord ++ tailWord_5311106) baseStart_5311106 baseEnd_5311106 := by
    simpa [prefixWord, tailWord_5311106, baseEnd_5311106] using wordTrace_append hprefix tailTrace_5311106
  have hstable : (prefixWord ++ tailWord_5311106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311106).length < 2 ^ (prefixWord ++ tailWord_5311106).sum := by decide
  have hdescent : baseEnd_5311106 < baseStart_5311106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311132 : List Nat := [2, 2, 3, 2, 2, 2, 3, 2, 1, 4]
def baseStart_5311132 : Nat := 118140960795 + 5311132 * 2 ^ 59
def prefixEnd_5311132 : Nat := 4983230072969 + 3 ^ 40 * 5311132 * 2
def baseEnd_5311132 : Nat := 909054511825073135108185

theorem tailTrace_5311132 : CollatzResearch.WordTrace tailWord_5311132 prefixEnd_5311132 909054511825073135108185 := by
  unfold tailWord_5311132
  simp only [CollatzResearch.WordTrace]
  refine ⟨96856449097341653987623825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129141932129788871983498433 96856449097341653987623825)
  ·
    refine ⟨72642336823006240490717869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96856449097341653987623825 72642336823006240490717869)
    ·
      refine ⟨27240876308627340184019201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72642336823006240490717869 27240876308627340184019201)
      ·
        refine ⟨20430657231470505138014401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27240876308627340184019201 20430657231470505138014401)
        ·
          refine ⟨15322992923602878853510801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20430657231470505138014401 15322992923602878853510801)
          ·
            refine ⟨11492244692702159140133101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15322992923602878853510801 11492244692702159140133101)
            ·
              refine ⟨4309591759763309677549913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11492244692702159140133101 4309591759763309677549913)
              ·
                refine ⟨3232193819822482258162435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4309591759763309677549913 3232193819822482258162435)
                ·
                  refine ⟨4848290729733723387243653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232193819822482258162435 4848290729733723387243653)
                  ·
                    refine ⟨909054511825073135108185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4848290729733723387243653 909054511825073135108185)
                    ·
                      rfl

theorem cell23_5311132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_5311132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311132 prefixEnd_5311132 := by exact prefixLift 5311132
  have htrace : WordTrace (prefixWord ++ tailWord_5311132) baseStart_5311132 baseEnd_5311132 := by
    simpa [prefixWord, tailWord_5311132, baseEnd_5311132] using wordTrace_append hprefix tailTrace_5311132
  have hstable : (prefixWord ++ tailWord_5311132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311132).length < 2 ^ (prefixWord ++ tailWord_5311132).sum := by decide
  have hdescent : baseEnd_5311132 < baseStart_5311132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311165 : List Nat := [1, 4, 1, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_5311165 : Nat := 118140960795 + 5311165 * 2 ^ 59
def prefixEnd_5311165 : Nat := 4983230072969 + 3 ^ 40 * 5311165 * 2
def baseEnd_5311165 : Nat := 2727180480336817776211903

theorem tailTrace_5311165 : CollatzResearch.WordTrace tailWord_5311165 prefixEnd_5311165 2727180480336817776211903 := by
  unfold tailWord_5311165
  simp only [CollatzResearch.WordTrace]
  refine ⟨193714101803563754611198949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129142734535709169740799299 193714101803563754611198949)
  ·
    refine ⟨36321394088168203989599803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193714101803563754611198949 36321394088168203989599803)
    ·
      refine ⟨54482091132252305984399705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36321394088168203989599803 54482091132252305984399705)
      ·
        refine ⟨40861568349189229488299779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54482091132252305984399705 40861568349189229488299779)
        ·
          refine ⟨61292352523783844232449669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40861568349189229488299779 61292352523783844232449669)
          ·
            refine ⟨11492316098209470793584313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61292352523783844232449669 11492316098209470793584313)
            ·
              refine ⟨8619237073657103095188235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11492316098209470793584313 8619237073657103095188235)
              ·
                refine ⟨12928855610485654642782353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8619237073657103095188235 12928855610485654642782353)
                ·
                  refine ⟨9696641707864240982086765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12928855610485654642782353 9696641707864240982086765)
                  ·
                    refine ⟨3636240640449090368282537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9696641707864240982086765 3636240640449090368282537)
                    ·
                      refine ⟨2727180480336817776211903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636240640449090368282537 2727180480336817776211903)
                      ·
                        rfl

theorem cell23_5311165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_5311165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311165 prefixEnd_5311165 := by exact prefixLift 5311165
  have htrace : WordTrace (prefixWord ++ tailWord_5311165) baseStart_5311165 baseEnd_5311165 := by
    simpa [prefixWord, tailWord_5311165, baseEnd_5311165] using wordTrace_append hprefix tailTrace_5311165
  have hstable : (prefixWord ++ tailWord_5311165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311165).length < 2 ^ (prefixWord ++ tailWord_5311165).sum := by decide
  have hdescent : baseEnd_5311165 < baseStart_5311165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311189 : List Nat := [1, 3, 2, 5, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5311189 : Nat := 118140960795 + 5311189 * 2 ^ 59
def prefixEnd_5311189 : Nat := 4983230072969 + 3 ^ 40 * 5311189 * 2
def baseEnd_5311189 : Nat := 2727192803872525682311793

theorem tailTrace_5311189 : CollatzResearch.WordTrace tailWord_5311189 prefixEnd_5311189 2727192803872525682311793 := by
  unfold tailWord_5311189
  simp only [CollatzResearch.WordTrace]
  refine ⟨193714977155476806710072621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129143318103651204473381747 193714977155476806710072621)
  ·
    refine ⟨72643116433303802516277233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193714977155476806710072621 72643116433303802516277233)
    ·
      refine ⟨54482337324977851887207925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72643116433303802516277233 54482337324977851887207925)
      ·
        refine ⟨5107719124216673614425743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54482337324977851887207925 5107719124216673614425743)
        ·
          refine ⟨7661578686325010421638615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5107719124216673614425743 7661578686325010421638615)
          ·
            refine ⟨11492368029487515632457923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661578686325010421638615 11492368029487515632457923)
            ·
              refine ⟨17238552044231273448686885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11492368029487515632457923 17238552044231273448686885)
              ·
                refine ⟨3232228508293363771628791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17238552044231273448686885 3232228508293363771628791)
                ·
                  refine ⟨4848342762440045657443187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232228508293363771628791 4848342762440045657443187)
                  ·
                    refine ⟨7272514143660068486164781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4848342762440045657443187 7272514143660068486164781)
                    ·
                      refine ⟨2727192803872525682311793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7272514143660068486164781 2727192803872525682311793)
                      ·
                        rfl

theorem cell23_5311189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5311189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311189 prefixEnd_5311189 := by exact prefixLift 5311189
  have htrace : WordTrace (prefixWord ++ tailWord_5311189) baseStart_5311189 baseEnd_5311189 := by
    simpa [prefixWord, tailWord_5311189, baseEnd_5311189] using wordTrace_append hprefix tailTrace_5311189
  have hstable : (prefixWord ++ tailWord_5311189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311189).length < 2 ^ (prefixWord ++ tailWord_5311189).sum := by decide
  have hdescent : baseEnd_5311189 < baseStart_5311189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311201 : List Nat := [1, 2, 3, 1, 4, 1, 3, 8]
def baseStart_5311201 : Nat := 118140960795 + 5311201 * 2 ^ 59
def prefixEnd_5311201 : Nat := 4983230072969 + 3 ^ 40 * 5311201 * 2
def baseEnd_5311201 : Nat := 101007369097791838346731

theorem tailTrace_5311201 : CollatzResearch.WordTrace tailWord_5311201 prefixEnd_5311201 101007369097791838346731 := by
  unfold tailWord_5311201
  simp only [CollatzResearch.WordTrace]
  refine ⟨193715414831433332759509457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129143609887622221839672971 193715414831433332759509457)
  ·
    refine ⟨145286561123574999569632093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193715414831433332759509457 145286561123574999569632093)
    ·
      refine ⟨54482460421340624838612035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145286561123574999569632093 54482460421340624838612035)
      ·
        refine ⟨81723690632010937257918053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54482460421340624838612035 81723690632010937257918053)
        ·
          refine ⟨15323191993502050735859635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81723690632010937257918053 15323191993502050735859635)
          ·
            refine ⟨22984787990253076103789453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15323191993502050735859635 22984787990253076103789453)
            ·
              refine ⟨8619295496344903538921045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22984787990253076103789453 8619295496344903538921045)
              ·
                refine ⟨101007369097791838346731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8619295496344903538921045 101007369097791838346731)
                ·
                  rfl

theorem cell23_5311201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 8].length) (baseStart_5311201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311201 prefixEnd_5311201 := by exact prefixLift 5311201
  have htrace : WordTrace (prefixWord ++ tailWord_5311201) baseStart_5311201 baseEnd_5311201 := by
    simpa [prefixWord, tailWord_5311201, baseEnd_5311201] using wordTrace_append hprefix tailTrace_5311201
  have hstable : (prefixWord ++ tailWord_5311201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311201).length < 2 ^ (prefixWord ++ tailWord_5311201).sum := by decide
  have hdescent : baseEnd_5311201 < baseStart_5311201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311218 : List Nat := [3, 2, 1, 3, 1, 3, 3, 7]
def baseStart_5311218 : Nat := 118140960795 + 5311218 * 2 ^ 59
def prefixEnd_5311218 : Nat := 4983230072969 + 3 ^ 40 * 5311218 * 2
def baseEnd_5311218 : Nat := 101007692400426150698117

theorem tailTrace_5311218 : CollatzResearch.WordTrace tailWord_5311218 prefixEnd_5311218 101007692400426150698117 := by
  unfold tailWord_5311218
  simp only [CollatzResearch.WordTrace]
  refine ⟨48429008718092936165719577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129144023248247829775252205 48429008718092936165719577)
  ·
    refine ⟨36321756538569702124289683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48429008718092936165719577 36321756538569702124289683)
    ·
      refine ⟨54482634807854553186434525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36321756538569702124289683 54482634807854553186434525)
      ·
        refine ⟨20430988052945457444912947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54482634807854553186434525 20430988052945457444912947)
        ·
          refine ⟨30646482079418186167369421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20430988052945457444912947 30646482079418186167369421)
          ·
            refine ⟨11492430779781819812763533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30646482079418186167369421 11492430779781819812763533)
            ·
              refine ⟨4309661542418182429786325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11492430779781819812763533 4309661542418182429786325)
              ·
                refine ⟨101007692400426150698117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4309661542418182429786325 101007692400426150698117)
                ·
                  rfl

theorem cell23_5311218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 7].length) (baseStart_5311218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311218 prefixEnd_5311218 := by exact prefixLift 5311218
  have htrace : WordTrace (prefixWord ++ tailWord_5311218) baseStart_5311218 baseEnd_5311218 := by
    simpa [prefixWord, tailWord_5311218, baseEnd_5311218] using wordTrace_append hprefix tailTrace_5311218
  have hstable : (prefixWord ++ tailWord_5311218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311218).length < 2 ^ (prefixWord ++ tailWord_5311218).sum := by decide
  have hdescent : baseEnd_5311218 < baseStart_5311218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311228 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 1, 3, 3]
def baseStart_5311228 : Nat := 118140960795 + 5311228 * 2 ^ 59
def prefixEnd_5311228 : Nat := 4983230072969 + 3 ^ 40 * 5311228 * 2
def baseEnd_5311228 : Nat := 2727212829618051029724113

theorem tailTrace_5311228 : CollatzResearch.WordTrace tailWord_5311228 prefixEnd_5311228 2727212829618051029724113 := by
  unfold tailWord_5311228
  simp only [CollatzResearch.WordTrace]
  refine ⟨96858199801167758185371169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129144266401557010913828225 96858199801167758185371169)
  ·
    refine ⟨72643649850875818639028377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96858199801167758185371169 72643649850875818639028377)
    ·
      refine ⟨54482737388156863979271283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72643649850875818639028377 54482737388156863979271283)
      ·
        refine ⟨81724106082235295968906925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54482737388156863979271283 81724106082235295968906925)
        ·
          refine ⟨30646539780838235988340097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81724106082235295968906925 30646539780838235988340097)
          ·
            refine ⟨22984904835628676991255073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30646539780838235988340097 22984904835628676991255073)
            ·
              refine ⟨17238678626721507743441305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22984904835628676991255073 17238678626721507743441305)
              ·
                refine ⟨12929008970041130807580979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17238678626721507743441305 12929008970041130807580979)
                ·
                  refine ⟨19393513455061696211371469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12929008970041130807580979 19393513455061696211371469)
                  ·
                    refine ⟨7272567545648136079264301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19393513455061696211371469 7272567545648136079264301)
                    ·
                      refine ⟨2727212829618051029724113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7272567545648136079264301 2727212829618051029724113)
                      ·
                        rfl

theorem cell23_5311228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 1, 3, 3].length) (baseStart_5311228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311228 prefixEnd_5311228 := by exact prefixLift 5311228
  have htrace : WordTrace (prefixWord ++ tailWord_5311228) baseStart_5311228 baseEnd_5311228 := by
    simpa [prefixWord, tailWord_5311228, baseEnd_5311228] using wordTrace_append hprefix tailTrace_5311228
  have hstable : (prefixWord ++ tailWord_5311228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311228).length < 2 ^ (prefixWord ++ tailWord_5311228).sum := by decide
  have hdescent : baseEnd_5311228 < baseStart_5311228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311272 : List Nat := [2, 1, 5, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_5311272 : Nat := 118140960795 + 5311272 * 2 ^ 59
def prefixEnd_5311272 : Nat := 4983230072969 + 3 ^ 40 * 5311272 * 2
def baseEnd_5311272 : Nat := 2727235422766848857573911

theorem tailTrace_5311272 : CollatzResearch.WordTrace tailWord_5311272 prefixEnd_5311272 2727235422766848857573911 := by
  unfold tailWord_5311272
  simp only [CollatzResearch.WordTrace]
  refine ⟨96859002207088055942672035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129145336276117407923562713 96859002207088055942672035)
  ·
    refine ⟨145288503310632083914008053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96859002207088055942672035 145288503310632083914008053)
    ·
      refine ⟨13620797185371757866938255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145288503310632083914008053 13620797185371757866938255)
      ·
        refine ⟨20431195778057636800407383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13620797185371757866938255 20431195778057636800407383)
        ·
          refine ⟨30646793667086455200611075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20431195778057636800407383 30646793667086455200611075)
          ·
            refine ⟨45970190500629682800916613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30646793667086455200611075 45970190500629682800916613)
            ·
              refine ⟨8619410718868065525171865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45970190500629682800916613 8619410718868065525171865)
              ·
                refine ⟨6464558039151049143878899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8619410718868065525171865 6464558039151049143878899)
                ·
                  refine ⟨9696837058726573715818349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6464558039151049143878899 9696837058726573715818349)
                  ·
                    refine ⟨3636313897022465143431881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9696837058726573715818349 3636313897022465143431881)
                    ·
                      refine ⟨2727235422766848857573911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636313897022465143431881 2727235422766848857573911)
                      ·
                        rfl

theorem cell23_5311272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_5311272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311272 prefixEnd_5311272 := by exact prefixLift 5311272
  have htrace : WordTrace (prefixWord ++ tailWord_5311272) baseStart_5311272 baseEnd_5311272 := by
    simpa [prefixWord, tailWord_5311272, baseEnd_5311272] using wordTrace_append hprefix tailTrace_5311272
  have hstable : (prefixWord ++ tailWord_5311272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311272).length < 2 ^ (prefixWord ++ tailWord_5311272).sum := by decide
  have hdescent : baseEnd_5311272 < baseStart_5311272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311308 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 7]
def baseStart_5311308 : Nat := 118140960795 + 5311308 * 2 ^ 59
def prefixEnd_5311308 : Nat := 4983230072969 + 3 ^ 40 * 5311308 * 2
def baseEnd_5311308 : Nat := 303028212007823412969305

theorem tailTrace_5311308 : CollatzResearch.WordTrace tailWord_5311308 prefixEnd_5311308 303028212007823412969305 := by
  unfold tailWord_5311308
  simp only [CollatzResearch.WordTrace]
  refine ⟨96859658721022845016827289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129146211628030460022436385 96859658721022845016827289)
  ·
    refine ⟨72644744040767133762620467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96859658721022845016827289 72644744040767133762620467)
    ·
      refine ⟨108967116061150700643930701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72644744040767133762620467 108967116061150700643930701)
      ·
        refine ⟨40862668522931512741474013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108967116061150700643930701 40862668522931512741474013)
        ·
          refine ⟨15323500696099317278052755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40862668522931512741474013 15323500696099317278052755)
          ·
            refine ⟨22985251044148975917079133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15323500696099317278052755 22985251044148975917079133)
            ·
              refine ⟨8619469141555865968904675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22985251044148975917079133 8619469141555865968904675)
              ·
                refine ⟨12929203712333798953357013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8619469141555865968904675 12929203712333798953357013)
                ·
                  refine ⟨303028212007823412969305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12929203712333798953357013 303028212007823412969305)
                  ·
                    rfl

theorem cell23_5311308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 7].length) (baseStart_5311308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311308 prefixEnd_5311308 := by exact prefixLift 5311308
  have htrace : WordTrace (prefixWord ++ tailWord_5311308) baseStart_5311308 baseEnd_5311308 := by
    simpa [prefixWord, tailWord_5311308, baseEnd_5311308] using wordTrace_append hprefix tailTrace_5311308
  have hstable : (prefixWord ++ tailWord_5311308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311308).length < 2 ^ (prefixWord ++ tailWord_5311308).sum := by decide
  have hdescent : baseEnd_5311308 < baseStart_5311308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311319 : List Nat := [1, 1, 3, 2, 4, 1, 4, 1, 2, 2, 2]
def baseStart_5311319 : Nat := 118140960795 + 5311319 * 2 ^ 59
def prefixEnd_5311319 : Nat := 4983230072969 + 3 ^ 40 * 5311319 * 2
def baseEnd_5311319 : Nat := 2727259556357610173686195

theorem tailTrace_5311319 : CollatzResearch.WordTrace tailWord_5311319 prefixEnd_5311319 2727259556357610173686195 := by
  unfold tailWord_5311319
  simp only [CollatzResearch.WordTrace]
  refine ⟨193719718645005838912305011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129146479096670559274870007 193719718645005838912305011)
  ·
    refine ⟨290579577967508758368457517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193719718645005838912305011 290579577967508758368457517)
    ·
      refine ⟨108967341737815784388171569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290579577967508758368457517 108967341737815784388171569)
      ·
        refine ⟨81725506303361838291128677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108967341737815784388171569 81725506303361838291128677)
        ·
          refine ⟨15323532431880344679586627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81725506303361838291128677 15323532431880344679586627)
          ·
            refine ⟨22985298647820517019379941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15323532431880344679586627 22985298647820517019379941)
            ·
              refine ⟨4309743496466346941133739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22985298647820517019379941 4309743496466346941133739)
              ·
                refine ⟨6464615244699520411700609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309743496466346941133739 6464615244699520411700609)
                ·
                  refine ⟨4848461433524640308775457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6464615244699520411700609 4848461433524640308775457)
                  ·
                    refine ⟨3636346075143480231581593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4848461433524640308775457 3636346075143480231581593)
                    ·
                      refine ⟨2727259556357610173686195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636346075143480231581593 2727259556357610173686195)
                      ·
                        rfl

theorem cell23_5311319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 4, 1, 2, 2, 2].length) (baseStart_5311319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311319 prefixEnd_5311319 := by exact prefixLift 5311319
  have htrace : WordTrace (prefixWord ++ tailWord_5311319) baseStart_5311319 baseEnd_5311319 := by
    simpa [prefixWord, tailWord_5311319, baseEnd_5311319] using wordTrace_append hprefix tailTrace_5311319
  have hstable : (prefixWord ++ tailWord_5311319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311319).length < 2 ^ (prefixWord ++ tailWord_5311319).sum := by decide
  have hdescent : baseEnd_5311319 < baseStart_5311319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311395 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 3]
def baseStart_5311395 : Nat := 118140960795 + 5311395 * 2 ^ 59
def prefixEnd_5311395 : Nat := 4983230072969 + 3 ^ 40 * 5311395 * 2
def baseEnd_5311395 : Nat := 2727298580887351876335845

theorem tailTrace_5311395 : CollatzResearch.WordTrace tailWord_5311395 prefixEnd_5311395 2727298580887351876335845 := by
  unfold tailWord_5311395
  simp only [CollatzResearch.WordTrace]
  refine ⟨193722490592730503892071639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129148327061820335928047759 193722490592730503892071639)
  ·
    refine ⟨290583735889095755838107459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193722490592730503892071639 290583735889095755838107459)
    ·
      refine ⟨435875603833643633757161189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290583735889095755838107459 435875603833643633757161189)
      ·
        refine ⟨81726675718808181329467723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 435875603833643633757161189 81726675718808181329467723)
        ·
          refine ⟨122590013578212271994201585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81726675718808181329467723 122590013578212271994201585)
          ·
            refine ⟨91942510183659203995651189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122590013578212271994201585 91942510183659203995651189)
            ·
              refine ⟨8619610329718050374592299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 91942510183659203995651189 8619610329718050374592299)
              ·
                refine ⟨12929415494577075561888449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8619610329718050374592299 12929415494577075561888449)
                ·
                  refine ⟨9697061620932806671416337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12929415494577075561888449 9697061620932806671416337)
                  ·
                    refine ⟨7272796215699605003562253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9697061620932806671416337 7272796215699605003562253)
                    ·
                      refine ⟨2727298580887351876335845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7272796215699605003562253 2727298580887351876335845)
                      ·
                        rfl

theorem cell23_5311395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 2, 2, 3].length) (baseStart_5311395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311395 prefixEnd_5311395 := by exact prefixLift 5311395
  have htrace : WordTrace (prefixWord ++ tailWord_5311395) baseStart_5311395 baseEnd_5311395 := by
    simpa [prefixWord, tailWord_5311395, baseEnd_5311395] using wordTrace_append hprefix tailTrace_5311395
  have hstable : (prefixWord ++ tailWord_5311395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311395).length < 2 ^ (prefixWord ++ tailWord_5311395).sum := by decide
  have hdescent : baseEnd_5311395 < baseStart_5311395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311432 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 6]
def baseStart_5311432 : Nat := 118140960795 + 5311432 * 2 ^ 59
def prefixEnd_5311432 : Nat := 4983230072969 + 3 ^ 40 * 5311432 * 2
def baseEnd_5311432 : Nat := 303035286630174247952575

theorem tailTrace_5311432 : CollatzResearch.WordTrace tailWord_5311432 prefixEnd_5311432 303035286630174247952575 := by
  unfold tailWord_5311432
  simp only [CollatzResearch.WordTrace]
  refine ⟨96861920046798229605584275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129149226729064306140779033 96861920046798229605584275)
  ·
    refine ⟨145292880070197344408376413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96861920046798229605584275 145292880070197344408376413)
    ·
      refine ⟨54484830026324004153141155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145292880070197344408376413 54484830026324004153141155)
      ·
        refine ⟨81727245039486006229711733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54484830026324004153141155 81727245039486006229711733)
        ·
          refine ⟨7661929222451813084035475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 81727245039486006229711733 7661929222451813084035475)
          ·
            refine ⟨11492893833677719626053213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7661929222451813084035475 11492893833677719626053213)
            ·
              refine ⟨4309835187629144859769955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11492893833677719626053213 4309835187629144859769955)
              ·
                refine ⟨6464752781443717289654933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309835187629144859769955 6464752781443717289654933)
                ·
                  refine ⟨303035286630174247952575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6464752781443717289654933 303035286630174247952575)
                  ·
                    rfl

theorem cell23_5311432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 6].length) (baseStart_5311432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311432 prefixEnd_5311432 := by exact prefixLift 5311432
  have htrace : WordTrace (prefixWord ++ tailWord_5311432) baseStart_5311432 baseEnd_5311432 := by
    simpa [prefixWord, tailWord_5311432, baseEnd_5311432] using wordTrace_append hprefix tailTrace_5311432
  have hstable : (prefixWord ++ tailWord_5311432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311432).length < 2 ^ (prefixWord ++ tailWord_5311432).sum := by decide
  have hdescent : baseEnd_5311432 < baseStart_5311432 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311435 : List Nat := [1, 1, 1, 1, 3, 5, 1, 2, 1, 5, 2]
def baseStart_5311435 : Nat := 118140960795 + 5311435 * 2 ^ 59
def prefixEnd_5311435 : Nat := 4983230072969 + 3 ^ 40 * 5311435 * 2
def baseEnd_5311435 : Nat := 2727319120113531719835661

theorem tailTrace_5311435 : CollatzResearch.WordTrace tailWord_5311435 prefixEnd_5311435 2727319120113531719835661 := by
  unfold tailWord_5311435
  simp only [CollatzResearch.WordTrace]
  refine ⟨193723949512585590723527759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129149299675057060482351839 193723949512585590723527759)
  ·
    refine ⟨290585924268878386085291639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193723949512585590723527759 290585924268878386085291639)
    ·
      refine ⟨435878886403317579127937459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290585924268878386085291639 435878886403317579127937459)
      ·
        refine ⟨653818329604976368691906189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435878886403317579127937459 653818329604976368691906189)
        ·
          refine ⟨245181873601866138259464821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 653818329604976368691906189 245181873601866138259464821)
          ·
            refine ⟨22985800650174950461824827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245181873601866138259464821 22985800650174950461824827)
            ·
              refine ⟨34478700975262425692737241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22985800650174950461824827 34478700975262425692737241)
              ·
                refine ⟨25859025731446819269552931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34478700975262425692737241 25859025731446819269552931)
                ·
                  refine ⟨38788538597170228904329397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25859025731446819269552931 38788538597170228904329397)
                  ·
                    refine ⟨3636425493484708959780881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38788538597170228904329397 3636425493484708959780881)
                    ·
                      refine ⟨2727319120113531719835661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636425493484708959780881 2727319120113531719835661)
                      ·
                        rfl

theorem cell23_5311435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 2, 1, 5, 2].length) (baseStart_5311435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311435 prefixEnd_5311435 := by exact prefixLift 5311435
  have htrace : WordTrace (prefixWord ++ tailWord_5311435) baseStart_5311435 baseEnd_5311435 := by
    simpa [prefixWord, tailWord_5311435, baseEnd_5311435] using wordTrace_append hprefix tailTrace_5311435
  have hstable : (prefixWord ++ tailWord_5311435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311435).length < 2 ^ (prefixWord ++ tailWord_5311435).sum := by decide
  have hdescent : baseEnd_5311435 < baseStart_5311435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311485 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_5311485 : Nat := 118140960795 + 5311485 * 2 ^ 59
def prefixEnd_5311485 : Nat := 4983230072969 + 3 ^ 40 * 5311485 * 2
def baseEnd_5311485 : Nat := 2727344794146256524210431

theorem tailTrace_5311485 : CollatzResearch.WordTrace tailWord_5311485 prefixEnd_5311485 2727344794146256524210431 := by
  unfold tailWord_5311485
  simp only [CollatzResearch.WordTrace]
  refine ⟨193725773162404449262847909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129150515441602966175231939 193725773162404449262847909)
  ·
    refine ⟨36323582467950834236783983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193725773162404449262847909 36323582467950834236783983)
    ·
      refine ⟨54485373701926251355175975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36323582467950834236783983 54485373701926251355175975)
      ·
        refine ⟨81728060552889377032763963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54485373701926251355175975 81728060552889377032763963)
        ·
          refine ⟨122592090829334065549145945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81728060552889377032763963 122592090829334065549145945)
          ·
            refine ⟨91944068122000549161859459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122592090829334065549145945 91944068122000549161859459)
            ·
              refine ⟨137916102183000823742789189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91944068122000549161859459 137916102183000823742789189)
              ·
                refine ⟨25859269159312654451772973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137916102183000823742789189 25859269159312654451772973)
                ·
                  refine ⟨9697225934742245419414865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25859269159312654451772973 9697225934742245419414865)
                  ·
                    refine ⟨7272919451056684064561149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9697225934742245419414865 7272919451056684064561149)
                    ·
                      refine ⟨2727344794146256524210431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7272919451056684064561149 2727344794146256524210431)
                      ·
                        rfl

theorem cell23_5311485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_5311485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311485 prefixEnd_5311485 := by exact prefixLift 5311485
  have htrace : WordTrace (prefixWord ++ tailWord_5311485) baseStart_5311485 baseEnd_5311485 := by
    simpa [prefixWord, tailWord_5311485, baseEnd_5311485] using wordTrace_append hprefix tailTrace_5311485
  have hstable : (prefixWord ++ tailWord_5311485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311485).length < 2 ^ (prefixWord ++ tailWord_5311485).sum := by decide
  have hdescent : baseEnd_5311485 < baseStart_5311485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311495 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_5311495 : Nat := 118140960795 + 5311495 * 2 ^ 59
def prefixEnd_5311495 : Nat := 4983230072969 + 3 ^ 40 * 5311495 * 2
def baseEnd_5311495 : Nat := 2727349928952801485085385

theorem tailTrace_5311495 : CollatzResearch.WordTrace tailWord_5311495 prefixEnd_5311495 2727349928952801485085385 := by
  unfold tailWord_5311495
  simp only [CollatzResearch.WordTrace]
  refine ⟨193726137892368220970711939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129150758594912147313807959 193726137892368220970711939)
  ·
    refine ⟨290589206838552331456067909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193726137892368220970711939 290589206838552331456067909)
    ·
      refine ⟨54485476282228562148012733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290589206838552331456067909 54485476282228562148012733)
      ·
        refine ⟨20432053605835710805504775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54485476282228562148012733 20432053605835710805504775)
        ·
          refine ⟨30648080408753566208257163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20432053605835710805504775 30648080408753566208257163)
          ·
            refine ⟨45972120613130349312385745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30648080408753566208257163 45972120613130349312385745)
            ·
              refine ⟨34479090459847761984289309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45972120613130349312385745 34479090459847761984289309)
              ·
                refine ⟨12929658922442910744108491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34479090459847761984289309 12929658922442910744108491)
                ·
                  refine ⟨19394488383664366116162737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12929658922442910744108491 19394488383664366116162737)
                  ·
                    refine ⟨14545866287748274587122053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19394488383664366116162737 14545866287748274587122053)
                    ·
                      refine ⟨2727349928952801485085385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14545866287748274587122053 2727349928952801485085385)
                      ·
                        rfl

theorem cell23_5311495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_5311495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311495 prefixEnd_5311495 := by exact prefixLift 5311495
  have htrace : WordTrace (prefixWord ++ tailWord_5311495) baseStart_5311495 baseEnd_5311495 := by
    simpa [prefixWord, tailWord_5311495, baseEnd_5311495] using wordTrace_append hprefix tailTrace_5311495
  have hstable : (prefixWord ++ tailWord_5311495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311495).length < 2 ^ (prefixWord ++ tailWord_5311495).sum := by decide
  have hdescent : baseEnd_5311495 < baseStart_5311495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311502 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_5311502 : Nat := 118140960795 + 5311502 * 2 ^ 59
def prefixEnd_5311502 : Nat := 4983230072969 + 3 ^ 40 * 5311502 * 2
def baseEnd_5311502 : Nat := 2727353523317382957697853

theorem tailTrace_5311502 : CollatzResearch.WordTrace tailWord_5311502 prefixEnd_5311502 2727353523317382957697853 := by
  unfold tailWord_5311502
  simp only [CollatzResearch.WordTrace]
  refine ⟨24215799150417857645777095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129150928802228574110811173 24215799150417857645777095)
  ·
    refine ⟨36323698725626786468665643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24215799150417857645777095 36323698725626786468665643)
    ·
      refine ⟨54485548088440179702998465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36323698725626786468665643 54485548088440179702998465)
      ·
        refine ⟨40864161066330134777248849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54485548088440179702998465 40864161066330134777248849)
        ·
          refine ⟨30648120799747601082936637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40864161066330134777248849 30648120799747601082936637)
          ·
            refine ⟨11493045299905350406101239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30648120799747601082936637 11493045299905350406101239)
            ·
              refine ⟨17239567949858025609151859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11493045299905350406101239 17239567949858025609151859)
              ·
                refine ⟨25859351924787038413727789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17239567949858025609151859 25859351924787038413727789)
                ·
                  refine ⟨9697256971795139405147921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25859351924787038413727789 9697256971795139405147921)
                  ·
                    refine ⟨7272942728846354553860941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9697256971795139405147921 7272942728846354553860941)
                    ·
                      refine ⟨2727353523317382957697853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7272942728846354553860941 2727353523317382957697853)
                      ·
                        rfl

theorem cell23_5311502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_5311502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311502 prefixEnd_5311502 := by exact prefixLift 5311502
  have htrace : WordTrace (prefixWord ++ tailWord_5311502) baseStart_5311502 baseEnd_5311502 := by
    simpa [prefixWord, tailWord_5311502, baseEnd_5311502] using wordTrace_append hprefix tailTrace_5311502
  have hstable : (prefixWord ++ tailWord_5311502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311502).length < 2 ^ (prefixWord ++ tailWord_5311502).sum := by decide
  have hdescent : baseEnd_5311502 < baseStart_5311502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311519 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 1, 2, 3]
def baseStart_5311519 : Nat := 118140960795 + 5311519 * 2 ^ 59
def prefixEnd_5311519 : Nat := 4983230072969 + 3 ^ 40 * 5311519 * 2
def baseEnd_5311519 : Nat := 2727362252488509391185275

theorem tailTrace_5311519 : CollatzResearch.WordTrace tailWord_5311519 prefixEnd_5311519 2727362252488509391185275 := by
  unfold tailWord_5311519
  simp only [CollatzResearch.WordTrace]
  refine ⟨193727013244281273069585611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129151342162854182046390407 193727013244281273069585611)
  ·
    refine ⟨290590519866421909604378417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193727013244281273069585611 290590519866421909604378417)
    ·
      refine ⟨217942889899816432203283813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290590519866421909604378417 217942889899816432203283813)
      ·
        refine ⟨40864291856215581038115715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 217942889899816432203283813 40864291856215581038115715)
        ·
          refine ⟨61296437784323371557173573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40864291856215581038115715 61296437784323371557173573)
          ·
            refine ⟨11493082084560632166970045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61296437784323371557173573 11493082084560632166970045)
            ·
              refine ⟨4309905781710237062613767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11493082084560632166970045 4309905781710237062613767)
              ·
                refine ⟨6464858672565355593920651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4309905781710237062613767 6464858672565355593920651)
                ·
                  refine ⟨9697288008848033390880977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6464858672565355593920651 9697288008848033390880977)
                  ·
                    refine ⟨7272966006636025043160733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9697288008848033390880977 7272966006636025043160733)
                    ·
                      refine ⟨2727362252488509391185275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7272966006636025043160733 2727362252488509391185275)
                      ·
                        rfl

theorem cell23_5311519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_5311519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311519 prefixEnd_5311519 := by exact prefixLift 5311519
  have htrace : WordTrace (prefixWord ++ tailWord_5311519) baseStart_5311519 baseEnd_5311519 := by
    simpa [prefixWord, tailWord_5311519, baseEnd_5311519] using wordTrace_append hprefix tailTrace_5311519
  have hstable : (prefixWord ++ tailWord_5311519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311519).length < 2 ^ (prefixWord ++ tailWord_5311519).sum := by decide
  have hdescent : baseEnd_5311519 < baseStart_5311519 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311549 : List Nat := [1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_5311549 : Nat := 118140960795 + 5311549 * 2 ^ 59
def prefixEnd_5311549 : Nat := 4983230072969 + 3 ^ 40 * 5311549 * 2
def baseEnd_5311549 : Nat := 2727377656908144273810137

theorem tailTrace_5311549 : CollatzResearch.WordTrace tailWord_5311549 prefixEnd_5311549 2727377656908144273810137 := by
  unfold tailWord_5311549
  simp only [CollatzResearch.WordTrace]
  refine ⟨193728107434172588193177701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129152071622781725462118467 193728107434172588193177701)
  ·
    refine ⟨36324020143907360286220819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193728107434172588193177701 36324020143907360286220819)
    ·
      refine ⟨54486030215861040429331229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36324020143907360286220819 54486030215861040429331229)
      ·
        refine ⟨20432261330947890160999211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54486030215861040429331229 20432261330947890160999211)
        ·
          refine ⟨30648391996421835241498817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20432261330947890160999211 30648391996421835241498817)
          ·
            refine ⟨22986293997316376431124113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30648391996421835241498817 22986293997316376431124113)
            ·
              refine ⟨17239720497987282323343085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22986293997316376431124113 17239720497987282323343085)
              ·
                refine ⟨6464895186745230871253657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17239720497987282323343085 6464895186745230871253657)
                ·
                  refine ⟨4848671390058923153440243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6464895186745230871253657 4848671390058923153440243)
                  ·
                    refine ⟨7273007085088384730160365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4848671390058923153440243 7273007085088384730160365)
                    ·
                      refine ⟨2727377656908144273810137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7273007085088384730160365 2727377656908144273810137)
                      ·
                        rfl

theorem cell23_5311549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_5311549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311549 prefixEnd_5311549 := by exact prefixLift 5311549
  have htrace : WordTrace (prefixWord ++ tailWord_5311549) baseStart_5311549 baseEnd_5311549 := by
    simpa [prefixWord, tailWord_5311549, baseEnd_5311549] using wordTrace_append hprefix tailTrace_5311549
  have hstable : (prefixWord ++ tailWord_5311549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311549).length < 2 ^ (prefixWord ++ tailWord_5311549).sum := by decide
  have hdescent : baseEnd_5311549 < baseStart_5311549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311585 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 4]
def baseStart_5311585 : Nat := 118140960795 + 5311585 * 2 ^ 59
def prefixEnd_5311585 : Nat := 4983230072969 + 3 ^ 40 * 5311585 * 2
def baseEnd_5311585 : Nat := 2727396142211706132959971

theorem tailTrace_5311585 : CollatzResearch.WordTrace tailWord_5311585 prefixEnd_5311585 2727396142211706132959971 := by
  unfold tailWord_5311585
  simp only [CollatzResearch.WordTrace]
  refine ⟨193729420462042166341488209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129152946974694777560992139 193729420462042166341488209)
  ·
    refine ⟨145297065346531624756116157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193729420462042166341488209 145297065346531624756116157)
    ·
      refine ⟨54486399504949359283543559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145297065346531624756116157 54486399504949359283543559)
      ·
        refine ⟨81729599257424038925315339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54486399504949359283543559 81729599257424038925315339)
        ·
          refine ⟨122594398886136058387973009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81729599257424038925315339 122594398886136058387973009)
          ·
            refine ⟨91945799164602043790979757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122594398886136058387973009 91945799164602043790979757)
            ·
              refine ⟨34479674686725766421617409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91945799164602043790979757 34479674686725766421617409)
              ·
                refine ⟨25859756015044324816213057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34479674686725766421617409 25859756015044324816213057)
                ·
                  refine ⟨19394817011283243612159793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25859756015044324816213057 19394817011283243612159793)
                  ·
                    refine ⟨14546112758462432709119845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19394817011283243612159793 14546112758462432709119845)
                    ·
                      refine ⟨2727396142211706132959971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14546112758462432709119845 2727396142211706132959971)
                      ·
                        rfl

theorem cell23_5311585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_5311585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311585 prefixEnd_5311585 := by exact prefixLift 5311585
  have htrace : WordTrace (prefixWord ++ tailWord_5311585) baseStart_5311585 baseEnd_5311585 := by
    simpa [prefixWord, tailWord_5311585, baseEnd_5311585] using wordTrace_append hprefix tailTrace_5311585
  have hstable : (prefixWord ++ tailWord_5311585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311585).length < 2 ^ (prefixWord ++ tailWord_5311585).sum := by decide
  have hdescent : baseEnd_5311585 < baseStart_5311585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311589 : List Nat := [1, 3, 1, 3, 2, 1, 3, 1, 4, 2, 2]
def baseStart_5311589 : Nat := 118140960795 + 5311589 * 2 ^ 59
def prefixEnd_5311589 : Nat := 4983230072969 + 3 ^ 40 * 5311589 * 2
def baseEnd_5311589 : Nat := 2727398196134324117309953

theorem tailTrace_5311589 : CollatzResearch.WordTrace tailWord_5311589 prefixEnd_5311589 2727398196134324117309953 := by
  unfold tailWord_5311589
  simp only [CollatzResearch.WordTrace]
  refine ⟨193729566354027675024633821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129153044236018450016422547 193729566354027675024633821)
  ·
    refine ⟨72648587382760378134237683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193729566354027675024633821 72648587382760378134237683)
    ·
      refine ⟨108972881074140567201356525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72648587382760378134237683 108972881074140567201356525)
      ·
        refine ⟨40864830402802712700508697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108972881074140567201356525 40864830402802712700508697)
        ·
          refine ⟨30648622802102034525381523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40864830402802712700508697 30648622802102034525381523)
          ·
            refine ⟨45972934203153051788072285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30648622802102034525381523 45972934203153051788072285)
            ·
              refine ⟨17239850326182394420527107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45972934203153051788072285 17239850326182394420527107)
              ·
                refine ⟨25859775489273591630790661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17239850326182394420527107 25859775489273591630790661)
                ·
                  refine ⟨4848707904238798430773249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25859775489273591630790661 4848707904238798430773249)
                  ·
                    refine ⟨3636530928179098823079937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4848707904238798430773249 3636530928179098823079937)
                    ·
                      refine ⟨2727398196134324117309953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636530928179098823079937 2727398196134324117309953)
                      ·
                        rfl

theorem cell23_5311589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_5311589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311589 prefixEnd_5311589 := by exact prefixLift 5311589
  have htrace : WordTrace (prefixWord ++ tailWord_5311589) baseStart_5311589 baseEnd_5311589 := by
    simpa [prefixWord, tailWord_5311589, baseEnd_5311589] using wordTrace_append hprefix tailTrace_5311589
  have hstable : (prefixWord ++ tailWord_5311589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311589).length < 2 ^ (prefixWord ++ tailWord_5311589).sum := by decide
  have hdescent : baseEnd_5311589 < baseStart_5311589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311625 : List Nat := [1, 2, 1, 1, 4, 3, 2, 1, 1, 7]
def baseStart_5311625 : Nat := 118140960795 + 5311625 * 2 ^ 59
def prefixEnd_5311625 : Nat := 4983230072969 + 3 ^ 40 * 5311625 * 2
def baseEnd_5311625 : Nat := 909138893812628658819929

theorem tailTrace_5311625 : CollatzResearch.WordTrace tailWord_5311625 prefixEnd_5311625 909138893812628658819929 := by
  unfold tailWord_5311625
  simp only [CollatzResearch.WordTrace]
  refine ⟨193730879381897253172944329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129153919587931502115296219 193730879381897253172944329)
  ·
    refine ⟨145298159536422939879708247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193730879381897253172944329 145298159536422939879708247)
    ·
      refine ⟨217947239304634409819562371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145298159536422939879708247 217947239304634409819562371)
      ·
        refine ⟨326920858956951614729343557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217947239304634409819562371 326920858956951614729343557)
        ·
          refine ⟨61297661054428427761751917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 326920858956951614729343557 61297661054428427761751917)
          ·
            refine ⟨22986622895410660410656969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61297661054428427761751917 22986622895410660410656969)
            ·
              refine ⟨17239967171557995307992727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22986622895410660410656969 17239967171557995307992727)
              ·
                refine ⟨25859950757336992961989091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17239967171557995307992727 25859950757336992961989091)
                ·
                  refine ⟨38789926136005489442983637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25859950757336992961989091 38789926136005489442983637)
                  ·
                    refine ⟨909138893812628658819929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38789926136005489442983637 909138893812628658819929)
                    ·
                      rfl

theorem cell23_5311625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 7].length) (baseStart_5311625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311625 prefixEnd_5311625 := by exact prefixLift 5311625
  have htrace : WordTrace (prefixWord ++ tailWord_5311625) baseStart_5311625 baseEnd_5311625 := by
    simpa [prefixWord, tailWord_5311625, baseEnd_5311625] using wordTrace_append hprefix tailTrace_5311625
  have hstable : (prefixWord ++ tailWord_5311625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311625).length < 2 ^ (prefixWord ++ tailWord_5311625).sum := by decide
  have hdescent : baseEnd_5311625 < baseStart_5311625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311642 : List Nat := [3, 1, 1, 5, 1, 1, 1, 1, 4, 5]
def baseStart_5311642 : Nat := 118140960795 + 5311642 * 2 ^ 59
def prefixEnd_5311642 : Nat := 4983230072969 + 3 ^ 40 * 5311642 * 2
def baseEnd_5311642 : Nat := 909141803536337469982403

theorem tailTrace_5311642 : CollatzResearch.WordTrace tailWord_5311642 prefixEnd_5311642 909141803536337469982403 := by
  unfold tailWord_5311642
  simp only [CollatzResearch.WordTrace]
  refine ⟨48432874855708916269078295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129154332948557110050875453 48432874855708916269078295)
  ·
    refine ⟨72649312283563374403617443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48432874855708916269078295 72649312283563374403617443)
    ·
      refine ⟨108973968425345061605426165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72649312283563374403617443 108973968425345061605426165)
      ·
        refine ⟨10216309539876099525508703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 108973968425345061605426165 10216309539876099525508703)
        ·
          refine ⟨15324464309814149288263055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10216309539876099525508703 15324464309814149288263055)
          ·
            refine ⟨22986696464721223932394583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15324464309814149288263055 22986696464721223932394583)
            ·
              refine ⟨34480044697081835898591875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22986696464721223932394583 34480044697081835898591875)
              ·
                refine ⟨51720067045622753847887813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34480044697081835898591875 51720067045622753847887813)
                ·
                  refine ⟨9697512571054266346478965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51720067045622753847887813 9697512571054266346478965)
                  ·
                    refine ⟨909141803536337469982403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9697512571054266346478965 909141803536337469982403)
                    ·
                      rfl

theorem cell23_5311642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 1, 4, 5].length) (baseStart_5311642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311642 prefixEnd_5311642 := by exact prefixLift 5311642
  have htrace : WordTrace (prefixWord ++ tailWord_5311642) baseStart_5311642 baseEnd_5311642 := by
    simpa [prefixWord, tailWord_5311642, baseEnd_5311642] using wordTrace_append hprefix tailTrace_5311642
  have hstable : (prefixWord ++ tailWord_5311642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311642).length < 2 ^ (prefixWord ++ tailWord_5311642).sum := by decide
  have hdescent : baseEnd_5311642 < baseStart_5311642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311652 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_5311652 : Nat := 118140960795 + 5311652 * 2 ^ 59
def prefixEnd_5311652 : Nat := 4983230072969 + 3 ^ 40 * 5311652 * 2
def baseEnd_5311652 : Nat := 2727430545415557370822163

theorem tailTrace_5311652 : CollatzResearch.WordTrace tailWord_5311652 prefixEnd_5311652 2727430545415557370822163 := by
  unfold tailWord_5311652
  simp only [CollatzResearch.WordTrace]
  refine ⟨96865932076399718392088605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129154576101866291189451473 96865932076399718392088605)
  ·
    refine ⟨36324724528649894397033227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96865932076399718392088605 36324724528649894397033227)
    ·
      refine ⟨54487086792974841595549841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36324724528649894397033227 54487086792974841595549841)
      ·
        refine ⟨40865315094731131196662381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54487086792974841595549841 40865315094731131196662381)
        ·
          refine ⟨15324493160524174198748393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40865315094731131196662381 15324493160524174198748393)
          ·
            refine ⟨11493369870393130649061295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15324493160524174198748393 11493369870393130649061295)
            ·
              refine ⟨17240054805589695973591943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11493369870393130649061295 17240054805589695973591943)
              ·
                refine ⟨25860082208384543960387915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17240054805589695973591943 25860082208384543960387915)
                ·
                  refine ⟨38790123312576815940581873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25860082208384543960387915 38790123312576815940581873)
                  ·
                    refine ⟨29092592484432611955436405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38790123312576815940581873 29092592484432611955436405)
                    ·
                      refine ⟨2727430545415557370822163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29092592484432611955436405 2727430545415557370822163)
                      ·
                        rfl

theorem cell23_5311652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_5311652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311652 prefixEnd_5311652 := by exact prefixLift 5311652
  have htrace : WordTrace (prefixWord ++ tailWord_5311652) baseStart_5311652 baseEnd_5311652 := by
    simpa [prefixWord, tailWord_5311652, baseEnd_5311652] using wordTrace_append hprefix tailTrace_5311652
  have hstable : (prefixWord ++ tailWord_5311652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311652).length < 2 ^ (prefixWord ++ tailWord_5311652).sum := by decide
  have hdescent : baseEnd_5311652 < baseStart_5311652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311705 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 6]
def baseStart_5311705 : Nat := 118140960795 + 5311705 * 2 ^ 59
def prefixEnd_5311705 : Nat := 4983230072969 + 3 ^ 40 * 5311705 * 2
def baseEnd_5311705 : Nat := 2727457759890245663459419

theorem tailTrace_5311705 : CollatzResearch.WordTrace tailWord_5311705 prefixEnd_5311705 2727457759890245663459419 := by
  unfold tailWord_5311705
  simp only [CollatzResearch.WordTrace]
  refine ⟨193733797221607426835856569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129155864814404951223904379 193733797221607426835856569)
  ·
    refine ⟨145300347916205570126892427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193733797221607426835856569 145300347916205570126892427)
    ·
      refine ⟨217950521874308355190338641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145300347916205570126892427 217950521874308355190338641)
      ·
        refine ⟨163462891405731266392753981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217950521874308355190338641 163462891405731266392753981)
        ·
          refine ⟨61298584277149224897282743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163462891405731266392753981 61298584277149224897282743)
          ·
            refine ⟨91947876415723837345924115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61298584277149224897282743 91947876415723837345924115)
            ·
              refine ⟨137921814623585756018886173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91947876415723837345924115 137921814623585756018886173)
              ·
                refine ⟨51720680483844658507082315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137921814623585756018886173 51720680483844658507082315)
                ·
                  refine ⟨77581020725766987760623473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51720680483844658507082315 77581020725766987760623473)
                  ·
                    refine ⟨58185765544325240820467605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77581020725766987760623473 58185765544325240820467605)
                    ·
                      refine ⟨2727457759890245663459419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58185765544325240820467605 2727457759890245663459419)
                      ·
                        rfl

theorem cell23_5311705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 2, 6].length) (baseStart_5311705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311705 prefixEnd_5311705 := by exact prefixLift 5311705
  have htrace : WordTrace (prefixWord ++ tailWord_5311705) baseStart_5311705 baseEnd_5311705 := by
    simpa [prefixWord, tailWord_5311705, baseEnd_5311705] using wordTrace_append hprefix tailTrace_5311705
  have hstable : (prefixWord ++ tailWord_5311705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311705).length < 2 ^ (prefixWord ++ tailWord_5311705).sum := by decide
  have hdescent : baseEnd_5311705 < baseStart_5311705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311772 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 3, 1, 5]
def baseStart_5311772 : Nat := 118140960795 + 5311772 * 2 ^ 59
def prefixEnd_5311772 : Nat := 4983230072969 + 3 ^ 40 * 5311772 * 2
def baseEnd_5311772 : Nat := 2727492163094096901321611

theorem tailTrace_5311772 : CollatzResearch.WordTrace tailWord_5311772 prefixEnd_5311772 2727492163094096901321611 := by
  unfold tailWord_5311772
  simp only [CollatzResearch.WordTrace]
  refine ⟨96868120456182348639272785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129157493941576464852363713 96868120456182348639272785)
  ·
    refine ⟨72651090342136761479454589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96868120456182348639272785 72651090342136761479454589)
    ·
      refine ⟨27244158878301285554795471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72651090342136761479454589 27244158878301285554795471)
      ·
        refine ⟨40866238317451928332193207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27244158878301285554795471 40866238317451928332193207)
        ·
          refine ⟨61299357476177892498289811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40866238317451928332193207 61299357476177892498289811)
          ·
            refine ⟨91949036214266838747434717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61299357476177892498289811 91949036214266838747434717)
            ·
              refine ⟨34480888580350064530288019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91949036214266838747434717 34480888580350064530288019)
              ·
                refine ⟨51721332870525096795432029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34480888580350064530288019 51721332870525096795432029)
                ·
                  refine ⟨19395499826446911298287011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51721332870525096795432029 19395499826446911298287011)
                  ·
                    refine ⟨29093249739670366947430517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19395499826446911298287011 29093249739670366947430517)
                    ·
                      refine ⟨2727492163094096901321611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29093249739670366947430517 2727492163094096901321611)
                      ·
                        rfl

theorem cell23_5311772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_5311772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311772 prefixEnd_5311772 := by exact prefixLift 5311772
  have htrace : WordTrace (prefixWord ++ tailWord_5311772) baseStart_5311772 baseEnd_5311772 := by
    simpa [prefixWord, tailWord_5311772, baseEnd_5311772] using wordTrace_append hprefix tailTrace_5311772
  have hstable : (prefixWord ++ tailWord_5311772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311772).length < 2 ^ (prefixWord ++ tailWord_5311772).sum := by decide
  have hdescent : baseEnd_5311772 < baseStart_5311772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311779 : List Nat := [1, 1, 1, 4, 2, 5, 1, 1, 1, 6]
def baseStart_5311779 : Nat := 118140960795 + 5311779 * 2 ^ 59
def prefixEnd_5311779 : Nat := 4983230072969 + 3 ^ 40 * 5311779 * 2
def baseEnd_5311779 : Nat := 909165252486226124644693

theorem tailTrace_5311779 : CollatzResearch.WordTrace tailWord_5311779 prefixEnd_5311779 909165252486226124644693 := by
  unfold tailWord_5311779
  simp only [CollatzResearch.WordTrace]
  refine ⟨193736496223339337474050391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129157664148892891649366927 193736496223339337474050391)
  ·
    refine ⟨290604744335009006211075587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193736496223339337474050391 290604744335009006211075587)
    ·
      refine ⟨435907116502513509316613381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290604744335009006211075587 435907116502513509316613381)
      ·
        refine ⟨81732584344221282996865009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 435907116502513509316613381 81732584344221282996865009)
        ·
          refine ⟨61299438258165962247648757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81732584344221282996865009 61299438258165962247648757)
          ·
            refine ⟨5746822336703058960717071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61299438258165962247648757 5746822336703058960717071)
            ·
              refine ⟨8620233505054588441075607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5746822336703058960717071 8620233505054588441075607)
              ·
                refine ⟨12930350257581882661613411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8620233505054588441075607 12930350257581882661613411)
                ·
                  refine ⟨19395525386372823992420117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12930350257581882661613411 19395525386372823992420117)
                  ·
                    refine ⟨909165252486226124644693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19395525386372823992420117 909165252486226124644693)
                    ·
                      rfl

theorem cell23_5311779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 6].length) (baseStart_5311779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311779 prefixEnd_5311779 := by exact prefixLift 5311779
  have htrace : WordTrace (prefixWord ++ tailWord_5311779) baseStart_5311779 baseEnd_5311779 := by
    simpa [prefixWord, tailWord_5311779, baseEnd_5311779] using wordTrace_append hprefix tailTrace_5311779
  have hstable : (prefixWord ++ tailWord_5311779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311779).length < 2 ^ (prefixWord ++ tailWord_5311779).sum := by decide
  have hdescent : baseEnd_5311779 < baseStart_5311779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311786 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5311786 : Nat := 118140960795 + 5311786 * 2 ^ 59
def prefixEnd_5311786 : Nat := 4983230072969 + 3 ^ 40 * 5311786 * 2
def baseEnd_5311786 : Nat := 2727499351823259846546547

theorem tailTrace_5311786 : CollatzResearch.WordTrace tailWord_5311786 prefixEnd_5311786 2727499351823259846546547 := by
  unfold tailWord_5311786
  simp only [CollatzResearch.WordTrace]
  refine ⟨48434187883578494417388803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129157834356209318446370141 48434187883578494417388803)
  ·
    refine ⟨72651281825367741626083205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48434187883578494417388803 72651281825367741626083205)
    ·
      refine ⟨13622115342256451554890601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72651281825367741626083205 13622115342256451554890601)
      ·
        refine ⟨10216586506692338666167951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13622115342256451554890601 10216586506692338666167951)
        ·
          refine ⟨15324879760038507999251927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10216586506692338666167951 15324879760038507999251927)
          ·
            refine ⟨22987319640057761998877891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15324879760038507999251927 22987319640057761998877891)
            ·
              refine ⟨34480979460086642998316837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22987319640057761998877891 34480979460086642998316837)
              ·
                refine ⟨6465183648766245562184407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34480979460086642998316837 6465183648766245562184407)
                ·
                  refine ⟨9697775473149368343276611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6465183648766245562184407 9697775473149368343276611)
                  ·
                    refine ⟨14546663209724052514914917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9697775473149368343276611 14546663209724052514914917)
                    ·
                      refine ⟨2727499351823259846546547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14546663209724052514914917 2727499351823259846546547)
                      ·
                        rfl

theorem cell23_5311786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5311786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311786 prefixEnd_5311786 := by exact prefixLift 5311786
  have htrace : WordTrace (prefixWord ++ tailWord_5311786) baseStart_5311786 baseEnd_5311786 := by
    simpa [prefixWord, tailWord_5311786, baseEnd_5311786] using wordTrace_append hprefix tailTrace_5311786
  have hstable : (prefixWord ++ tailWord_5311786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311786).length < 2 ^ (prefixWord ++ tailWord_5311786).sum := by decide
  have hdescent : baseEnd_5311786 < baseStart_5311786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311806 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_5311806 : Nat := 118140960795 + 5311806 * 2 ^ 59
def prefixEnd_5311806 : Nat := 4983230072969 + 3 ^ 40 * 5311806 * 2
def baseEnd_5311806 : Nat := 2727509621436349768296455

theorem tailTrace_5311806 : CollatzResearch.WordTrace tailWord_5311806 prefixEnd_5311806 2727509621436349768296455 := by
  unfold tailWord_5311806
  simp only [CollatzResearch.WordTrace]
  refine ⟨24217185124280190135660409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129158320662827680723522181 24217185124280190135660409)
  ·
    refine ⟨18162888843210142601745307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24217185124280190135660409 18162888843210142601745307)
    ·
      refine ⟨27244333264815213902617961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18162888843210142601745307 27244333264815213902617961)
      ·
        refine ⟨20433249948611410426963471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27244333264815213902617961 20433249948611410426963471)
        ·
          refine ⟨30649874922917115640445207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20433249948611410426963471 30649874922917115640445207)
          ·
            refine ⟨45974812384375673460667811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30649874922917115640445207 45974812384375673460667811)
            ·
              refine ⟨68962218576563510191001717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45974812384375673460667811 68962218576563510191001717)
              ·
                refine ⟨6465207991552829080406411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68962218576563510191001717 6465207991552829080406411)
                ·
                  refine ⟨9697811987329243620609617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6465207991552829080406411 9697811987329243620609617)
                  ·
                    refine ⟨7273358990496932715457213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9697811987329243620609617 7273358990496932715457213)
                    ·
                      refine ⟨2727509621436349768296455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7273358990496932715457213 2727509621436349768296455)
                      ·
                        rfl

theorem cell23_5311806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_5311806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311806 prefixEnd_5311806 := by exact prefixLift 5311806
  have htrace : WordTrace (prefixWord ++ tailWord_5311806) baseStart_5311806 baseEnd_5311806 := by
    simpa [prefixWord, tailWord_5311806, baseEnd_5311806] using wordTrace_append hprefix tailTrace_5311806
  have hstable : (prefixWord ++ tailWord_5311806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311806).length < 2 ^ (prefixWord ++ tailWord_5311806).sum := by decide
  have hdescent : baseEnd_5311806 < baseStart_5311806 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311809 : List Nat := [1, 2, 5, 2, 1, 3, 9]
def baseStart_5311809 : Nat := 118140960795 + 5311809 * 2 ^ 59
def prefixEnd_5311809 : Nat := 4983230072969 + 3 ^ 40 * 5311809 * 2
def baseEnd_5311809 : Nat := 33672977307139669834061

theorem tailTrace_5311809 : CollatzResearch.WordTrace tailWord_5311809 prefixEnd_5311809 33672977307139669834061 := by
  unfold tailWord_5311809
  simp only [CollatzResearch.WordTrace]
  refine ⟨193737590413230652597642481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129158393608820435065094987 193737590413230652597642481)
  ·
    refine ⟨145303192809922989448231861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193737590413230652597642481 145303192809922989448231861)
    ·
      refine ⟨13622174325930280260771737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145303192809922989448231861 13622174325930280260771737)
      ·
        refine ⟨10216630744447710195578803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13622174325930280260771737 10216630744447710195578803)
        ·
          refine ⟨15324946116671565293368205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10216630744447710195578803 15324946116671565293368205)
          ·
            refine ⟨5746854793751836985013077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15324946116671565293368205 5746854793751836985013077)
            ·
              refine ⟨33672977307139669834061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5746854793751836985013077 33672977307139669834061)
              ·
                rfl

theorem cell23_5311809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 9].length) (baseStart_5311809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311809 prefixEnd_5311809 := by exact prefixLift 5311809
  have htrace : WordTrace (prefixWord ++ tailWord_5311809) baseStart_5311809 baseEnd_5311809 := by
    simpa [prefixWord, tailWord_5311809, baseEnd_5311809] using wordTrace_append hprefix tailTrace_5311809
  have hstable : (prefixWord ++ tailWord_5311809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311809).length < 2 ^ (prefixWord ++ tailWord_5311809).sum := by decide
  have hdescent : baseEnd_5311809 < baseStart_5311809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311814 : List Nat := [6, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5311814 : Nat := 118140960795 + 5311814 * 2 ^ 59
def prefixEnd_5311814 : Nat := 4983230072969 + 3 ^ 40 * 5311814 * 2
def baseEnd_5311814 : Nat := 2727513729281585736996419

theorem tailTrace_5311814 : CollatzResearch.WordTrace tailWord_5311814 prefixEnd_5311814 2727513729281585736996419 := by
  unfold tailWord_5311814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6054305399319141826611703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129158515185475025634382997 6054305399319141826611703)
  ·
    refine ⟨9081458098978712739917555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6054305399319141826611703 9081458098978712739917555)
    ·
      refine ⟨13622187148468069109876333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9081458098978712739917555 13622187148468069109876333)
      ·
        refine ⟨5108320180675525916203625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13622187148468069109876333 5108320180675525916203625)
        ·
          refine ⟨3831240135506644437152719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5108320180675525916203625 3831240135506644437152719)
          ·
            refine ⟨5746860203259966655729079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831240135506644437152719 5746860203259966655729079)
            ·
              refine ⟨8620290304889949983593619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5746860203259966655729079 8620290304889949983593619)
              ·
                refine ⟨12930435457334924975390429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8620290304889949983593619 12930435457334924975390429)
                ·
                  refine ⟨4848913296500596865771411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12930435457334924975390429 4848913296500596865771411)
                  ·
                    refine ⟨7273369944750895298657117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4848913296500596865771411 7273369944750895298657117)
                    ·
                      refine ⟨2727513729281585736996419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7273369944750895298657117 2727513729281585736996419)
                      ·
                        rfl

theorem cell23_5311814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5311814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311814 prefixEnd_5311814 := by exact prefixLift 5311814
  have htrace : WordTrace (prefixWord ++ tailWord_5311814) baseStart_5311814 baseEnd_5311814 := by
    simpa [prefixWord, tailWord_5311814, baseEnd_5311814] using wordTrace_append hprefix tailTrace_5311814
  have hstable : (prefixWord ++ tailWord_5311814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311814).length < 2 ^ (prefixWord ++ tailWord_5311814).sum := by decide
  have hdescent : baseEnd_5311814 < baseStart_5311814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311822 : List Nat := [4, 1, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_5311822 : Nat := 118140960795 + 5311822 * 2 ^ 59
def prefixEnd_5311822 : Nat := 4983230072969 + 3 ^ 40 * 5311822 * 2
def baseEnd_5311822 : Nat := 909172612375607235232127

theorem tailTrace_5311822 : CollatzResearch.WordTrace tailWord_5311822 prefixEnd_5311822 909172612375607235232127 := by
  unfold tailWord_5311822
  simp only [CollatzResearch.WordTrace]
  refine ⟨24217258070272944477233215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129158709708122370545243813 24217258070272944477233215)
  ·
    refine ⟨36325887105409416715849823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24217258070272944477233215 36325887105409416715849823)
    ·
      refine ⟨54488830658114125073774735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36325887105409416715849823 54488830658114125073774735)
      ·
        refine ⟨81733245987171187610662103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54488830658114125073774735 81733245987171187610662103)
        ·
          refine ⟨122599868980756781415993155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81733245987171187610662103 122599868980756781415993155)
          ·
            refine ⟨183899803471135172123989733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122599868980756781415993155 183899803471135172123989733)
            ·
              refine ⟨34481213150837844773248075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183899803471135172123989733 34481213150837844773248075)
              ·
                refine ⟨51721819726256767159872113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34481213150837844773248075 51721819726256767159872113)
                ·
                  refine ⟨38791364794692575369904085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51721819726256767159872113 38791364794692575369904085)
                  ·
                    refine ⟨909172612375607235232127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38791364794692575369904085 909172612375607235232127)
                    ·
                      rfl

theorem cell23_5311822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_5311822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311822 prefixEnd_5311822 := by exact prefixLift 5311822
  have htrace : WordTrace (prefixWord ++ tailWord_5311822) baseStart_5311822 baseEnd_5311822 := by
    simpa [prefixWord, tailWord_5311822, baseEnd_5311822] using wordTrace_append hprefix tailTrace_5311822
  have hstable : (prefixWord ++ tailWord_5311822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311822).length < 2 ^ (prefixWord ++ tailWord_5311822).sum := by decide
  have hdescent : baseEnd_5311822 < baseStart_5311822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311837 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5311837 : Nat := 118140960795 + 5311837 * 2 ^ 59
def prefixEnd_5311837 : Nat := 4983230072969 + 3 ^ 40 * 5311837 * 2
def baseEnd_5311837 : Nat := 2727525539336639147008813

theorem tailTrace_5311837 : CollatzResearch.WordTrace tailWord_5311837 prefixEnd_5311837 2727525539336639147008813 := by
  unfold tailWord_5311837
  simp only [CollatzResearch.WordTrace]
  refine ⟨193738611657129213379661765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129159074438086142253107843 193738611657129213379661765)
  ·
    refine ⟨36325989685711727508686581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193738611657129213379661765 36325989685711727508686581)
    ·
      refine ⟨3405561533035474453939367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36325989685711727508686581 3405561533035474453939367)
      ·
        refine ⟨5108342299553211680909051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405561533035474453939367 5108342299553211680909051)
        ·
          refine ⟨7662513449329817521363577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5108342299553211680909051 7662513449329817521363577)
          ·
            refine ⟨5746885086997363141022683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7662513449329817521363577 5746885086997363141022683)
            ·
              refine ⟨8620327630496044711534025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5746885086997363141022683 8620327630496044711534025)
              ·
                refine ⟨6465245722872033533650519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8620327630496044711534025 6465245722872033533650519)
                ·
                  refine ⟨9697868584308050300475779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6465245722872033533650519 9697868584308050300475779)
                  ·
                    refine ⟨14546802876462075450713669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9697868584308050300475779 14546802876462075450713669)
                    ·
                      refine ⟨2727525539336639147008813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14546802876462075450713669 2727525539336639147008813)
                      ·
                        rfl

theorem cell23_5311837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5311837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311837 prefixEnd_5311837 := by exact prefixLift 5311837
  have htrace : WordTrace (prefixWord ++ tailWord_5311837) baseStart_5311837 baseEnd_5311837 := by
    simpa [prefixWord, tailWord_5311837, baseEnd_5311837] using wordTrace_append hprefix tailTrace_5311837
  have hstable : (prefixWord ++ tailWord_5311837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311837).length < 2 ^ (prefixWord ++ tailWord_5311837).sum := by decide
  have hdescent : baseEnd_5311837 < baseStart_5311837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311863 : List Nat := [1, 1, 3, 1, 1, 2, 7, 1, 1, 3, 2]
def baseStart_5311863 : Nat := 118140960795 + 5311863 * 2 ^ 59
def prefixEnd_5311863 : Nat := 4983230072969 + 3 ^ 40 * 5311863 * 2
def baseEnd_5311863 : Nat := 2727538889833656045283693

theorem tailTrace_5311863 : CollatzResearch.WordTrace tailWord_5311863 prefixEnd_5311863 2727538889833656045283693 := by
  unfold tailWord_5311863
  simp only [CollatzResearch.WordTrace]
  refine ⟨193739559955035019820108243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129159706636690013213405495 193739559955035019820108243)
  ·
    refine ⟨290609339932552529730162365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193739559955035019820108243 290609339932552529730162365)
    ·
      refine ⟨108978502474707198648810887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290609339932552529730162365 108978502474707198648810887)
      ·
        refine ⟨163467753712060797973216331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108978502474707198648810887 163467753712060797973216331)
        ·
          refine ⟨245201630568091196959824497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163467753712060797973216331 245201630568091196959824497)
          ·
            refine ⟨183901222926068397719868373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245201630568091196959824497 183901222926068397719868373)
            ·
              refine ⟨4310184912329728071559415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 183901222926068397719868373 4310184912329728071559415)
              ·
                refine ⟨6465277368494592107339123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310184912329728071559415 6465277368494592107339123)
                ·
                  refine ⟨9697916052741888161008685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6465277368494592107339123 9697916052741888161008685)
                  ·
                    refine ⟨3636718519778208060378257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9697916052741888161008685 3636718519778208060378257)
                    ·
                      refine ⟨2727538889833656045283693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636718519778208060378257 2727538889833656045283693)
                      ·
                        rfl

theorem cell23_5311863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 7, 1, 1, 3, 2].length) (baseStart_5311863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311863 prefixEnd_5311863 := by exact prefixLift 5311863
  have htrace : WordTrace (prefixWord ++ tailWord_5311863) baseStart_5311863 baseEnd_5311863 := by
    simpa [prefixWord, tailWord_5311863, baseEnd_5311863] using wordTrace_append hprefix tailTrace_5311863
  have hstable : (prefixWord ++ tailWord_5311863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311863).length < 2 ^ (prefixWord ++ tailWord_5311863).sum := by decide
  have hdescent : baseEnd_5311863 < baseStart_5311863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311872 : List Nat := [2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 4]
def baseStart_5311872 : Nat := 118140960795 + 5311872 * 2 ^ 59
def prefixEnd_5311872 : Nat := 4983230072969 + 3 ^ 40 * 5311872 * 2
def baseEnd_5311872 : Nat := 2727543511159546510071151

theorem tailTrace_5311872 : CollatzResearch.WordTrace tailWord_5311872 prefixEnd_5311872 2727543511159546510071151 := by
  unfold tailWord_5311872
  simp only [CollatzResearch.WordTrace]
  refine ⟨96869944106001207178592935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129159925474668276238123913 96869944106001207178592935)
  ·
    refine ⟨145304916159001810767889403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96869944106001207178592935 145304916159001810767889403)
    ·
      refine ⟨217957374238502716151834105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145304916159001810767889403 217957374238502716151834105)
      ·
        refine ⟨163468030678877037113875579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217957374238502716151834105 163468030678877037113875579)
        ·
          refine ⟨245202046018315555670813369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163468030678877037113875579 245202046018315555670813369)
          ·
            refine ⟨183901534513736666753110027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245202046018315555670813369 183901534513736666753110027)
            ·
              refine ⟨275852301770605000129665041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183901534513736666753110027 275852301770605000129665041)
              ·
                refine ⟨206889226327953750097248781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275852301770605000129665041 206889226327953750097248781)
                ·
                  refine ⟨77583459872982656286468293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206889226327953750097248781 77583459872982656286468293)
                  ·
                    refine ⟨14546898726184248053712805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77583459872982656286468293 14546898726184248053712805)
                    ·
                      refine ⟨2727543511159546510071151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14546898726184248053712805 2727543511159546510071151)
                      ·
                        rfl

theorem cell23_5311872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 4].length) (baseStart_5311872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311872 prefixEnd_5311872 := by exact prefixLift 5311872
  have htrace : WordTrace (prefixWord ++ tailWord_5311872) baseStart_5311872 baseEnd_5311872 := by
    simpa [prefixWord, tailWord_5311872, baseEnd_5311872] using wordTrace_append hprefix tailTrace_5311872
  have hstable : (prefixWord ++ tailWord_5311872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311872).length < 2 ^ (prefixWord ++ tailWord_5311872).sum := by decide
  have hdescent : baseEnd_5311872 < baseStart_5311872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311879 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 3]
def baseStart_5311879 : Nat := 118140960795 + 5311879 * 2 ^ 59
def prefixEnd_5311879 : Nat := 4983230072969 + 3 ^ 40 * 5311879 * 2
def baseEnd_5311879 : Nat := 2727547105524127982683619

theorem tailTrace_5311879 : CollatzResearch.WordTrace tailWord_5311879 prefixEnd_5311879 2727547105524127982683619 := by
  unfold tailWord_5311879
  simp only [CollatzResearch.WordTrace]
  refine ⟨193740143522977054552690691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129160095681984703035127127 193740143522977054552690691)
  ·
    refine ⟨290610215284465581829036037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193740143522977054552690691 290610215284465581829036037)
    ·
      refine ⟨54489415365837296592944257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290610215284465581829036037 54489415365837296592944257)
      ·
        refine ⟨40867061524377972444708193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54489415365837296592944257 40867061524377972444708193)
        ·
          refine ⟨30650296143283479333531145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40867061524377972444708193 30650296143283479333531145)
          ·
            refine ⟨22987722107462609500148359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30650296143283479333531145 22987722107462609500148359)
            ·
              refine ⟨34481583161193914250222539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22987722107462609500148359 34481583161193914250222539)
              ·
                refine ⟨51722374741790871375333809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34481583161193914250222539 51722374741790871375333809)
                ·
                  refine ⟨38791781056343153531500357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51722374741790871375333809 38791781056343153531500357)
                  ·
                    refine ⟨7273458948064341287156317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38791781056343153531500357 7273458948064341287156317)
                    ·
                      refine ⟨2727547105524127982683619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7273458948064341287156317 2727547105524127982683619)
                      ·
                        rfl

theorem cell23_5311879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_5311879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311879 prefixEnd_5311879 := by exact prefixLift 5311879
  have htrace : WordTrace (prefixWord ++ tailWord_5311879) baseStart_5311879 baseEnd_5311879 := by
    simpa [prefixWord, tailWord_5311879, baseEnd_5311879] using wordTrace_append hprefix tailTrace_5311879
  have hstable : (prefixWord ++ tailWord_5311879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311879).length < 2 ^ (prefixWord ++ tailWord_5311879).sum := by decide
  have hdescent : baseEnd_5311879 < baseStart_5311879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311886 : List Nat := [4, 1, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_5311886 : Nat := 118140960795 + 5311886 * 2 ^ 59
def prefixEnd_5311886 : Nat := 4983230072969 + 3 ^ 40 * 5311886 * 2
def baseEnd_5311886 : Nat := 909183566629569818432029

theorem tailTrace_5311886 : CollatzResearch.WordTrace tailWord_5311886 prefixEnd_5311886 909183566629569818432029 := by
  unfold tailWord_5311886
  simp only [CollatzResearch.WordTrace]
  refine ⟨24217549854243961843524439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129160265889301129832130341 24217549854243961843524439)
  ·
    refine ⟨36326324781365942765286659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24217549854243961843524439 36326324781365942765286659)
    ·
      refine ⟨54489487172048914147929989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36326324781365942765286659 54489487172048914147929989)
      ·
        refine ⟨10216778844759171402736873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54489487172048914147929989 10216778844759171402736873)
        ·
          refine ⟨7662584133569378552052655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10216778844759171402736873 7662584133569378552052655)
          ·
            refine ⟨11493876200354067828078983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7662584133569378552052655 11493876200354067828078983)
            ·
              refine ⟨17240814300531101742118475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11493876200354067828078983 17240814300531101742118475)
              ·
                refine ⟨25861221450796652613177713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17240814300531101742118475 25861221450796652613177713)
                ·
                  refine ⟨19395916088097489459883285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25861221450796652613177713 19395916088097489459883285)
                  ·
                    refine ⟨909183566629569818432029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19395916088097489459883285 909183566629569818432029)
                    ·
                      rfl

theorem cell23_5311886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_5311886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311886 prefixEnd_5311886 := by exact prefixLift 5311886
  have htrace : WordTrace (prefixWord ++ tailWord_5311886) baseStart_5311886 baseEnd_5311886 := by
    simpa [prefixWord, tailWord_5311886, baseEnd_5311886] using wordTrace_append hprefix tailTrace_5311886
  have hstable : (prefixWord ++ tailWord_5311886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311886).length < 2 ^ (prefixWord ++ tailWord_5311886).sum := by decide
  have hdescent : baseEnd_5311886 < baseStart_5311886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311893 : List Nat := [1, 3, 2, 1, 1, 2, 4, 3, 2, 2, 2]
def baseStart_5311893 : Nat := 118140960795 + 5311893 * 2 ^ 59
def prefixEnd_5311893 : Nat := 4983230072969 + 3 ^ 40 * 5311893 * 2
def baseEnd_5311893 : Nat := 2727554294253290927908555

theorem tailTrace_5311893 : CollatzResearch.WordTrace tailWord_5311893 prefixEnd_5311893 2727554294253290927908555 := by
  unfold tailWord_5311893
  simp only [CollatzResearch.WordTrace]
  refine ⟨193740654144926334943700333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129160436096617556629133555 193740654144926334943700333)
  ·
    refine ⟨72652745304347375603887625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193740654144926334943700333 72652745304347375603887625)
    ·
      refine ⟨54489558978260531702915719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72652745304347375603887625 54489558978260531702915719)
      ·
        refine ⟨81734338467390797554373579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54489558978260531702915719 81734338467390797554373579)
        ·
          refine ⟨122601507701086196331560369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81734338467390797554373579 122601507701086196331560369)
          ·
            refine ⟨91951130775814647248670277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122601507701086196331560369 91951130775814647248670277)
            ·
              refine ⟨17240837020465246359125677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91951130775814647248670277 17240837020465246359125677)
              ·
                refine ⟨6465313882674467384672129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17240837020465246359125677 6465313882674467384672129)
                ·
                  refine ⟨4848985412005850538504097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6465313882674467384672129 4848985412005850538504097)
                  ·
                    refine ⟨3636739059004387903878073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4848985412005850538504097 3636739059004387903878073)
                    ·
                      refine ⟨2727554294253290927908555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636739059004387903878073 2727554294253290927908555)
                      ·
                        rfl

theorem cell23_5311893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 3, 2, 2, 2].length) (baseStart_5311893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311893 prefixEnd_5311893 := by exact prefixLift 5311893
  have htrace : WordTrace (prefixWord ++ tailWord_5311893) baseStart_5311893 baseEnd_5311893 := by
    simpa [prefixWord, tailWord_5311893, baseEnd_5311893] using wordTrace_append hprefix tailTrace_5311893
  have hstable : (prefixWord ++ tailWord_5311893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311893).length < 2 ^ (prefixWord ++ tailWord_5311893).sum := by decide
  have hdescent : baseEnd_5311893 < baseStart_5311893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5311999 : List Nat := [1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 3]
def baseStart_5311999 : Nat := 118140960795 + 5311999 * 2 ^ 59
def prefixEnd_5311999 : Nat := 4983230072969 + 3 ^ 40 * 5311999 * 2
def baseEnd_5311999 : Nat := 2727608723202667513183067

theorem tailTrace_5311999 : CollatzResearch.WordTrace tailWord_5311999 prefixEnd_5311999 2727608723202667513183067 := by
  unfold tailWord_5311999
  simp only [CollatzResearch.WordTrace]
  refine ⟨193744520282542315047059051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129163013521694876698039367 193744520282542315047059051)
  ·
    refine ⟨290616780423813472570588577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193744520282542315047059051 290616780423813472570588577)
    ·
      refine ⟨217962585317860104427941433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290616780423813472570588577 217962585317860104427941433)
      ·
        refine ⟨163471938988395078320956075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217962585317860104427941433 163471938988395078320956075)
        ·
          refine ⟨245207908482592617481434113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163471938988395078320956075 245207908482592617481434113)
          ·
            refine ⟨183905931361944463111075585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245207908482592617481434113 183905931361944463111075585)
            ·
              refine ⟨137929448521458347333306689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183905931361944463111075585 137929448521458347333306689)
              ·
                refine ⟨103447086391093760499980017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137929448521458347333306689 103447086391093760499980017)
                ·
                  refine ⟨77585314793320320374985013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103447086391093760499980017 77585314793320320374985013)
                  ·
                    refine ⟨7273623261873780035154845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 77585314793320320374985013 7273623261873780035154845)
                    ·
                      refine ⟨2727608723202667513183067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7273623261873780035154845 2727608723202667513183067)
                      ·
                        rfl

theorem cell23_5311999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_5311999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5311999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5311999 prefixEnd_5311999 := by exact prefixLift 5311999
  have htrace : WordTrace (prefixWord ++ tailWord_5311999) baseStart_5311999 baseEnd_5311999 := by
    simpa [prefixWord, tailWord_5311999, baseEnd_5311999] using wordTrace_append hprefix tailTrace_5311999
  have hstable : (prefixWord ++ tailWord_5311999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5311999).length < 2 ^ (prefixWord ++ tailWord_5311999).sum := by decide
  have hdescent : baseEnd_5311999 < baseStart_5311999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5311999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312049 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 5, 6]
def baseStart_5312049 : Nat := 118140960795 + 5312049 * 2 ^ 59
def prefixEnd_5312049 : Nat := 4983230072969 + 3 ^ 40 * 5312049 * 2
def baseEnd_5312049 : Nat := 909211465745130772519279

theorem tailTrace_5312049 : CollatzResearch.WordTrace tailWord_5312049 prefixEnd_5312049 909211465745130772519279 := by
  unfold tailWord_5312049
  simp only [CollatzResearch.WordTrace]
  refine ⟨193746343932361173586379201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129164229288240782390919467 193746343932361173586379201)
  ·
    refine ⟨145309757949270880189784401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193746343932361173586379201 145309757949270880189784401)
    ·
      refine ⟨108982318461953160142338301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145309757949270880189784401 108982318461953160142338301)
      ·
        refine ⟨40868369423232435053376863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108982318461953160142338301 40868369423232435053376863)
        ·
          refine ⟨61302554134848652580065295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40868369423232435053376863 61302554134848652580065295)
          ·
            refine ⟨91953831202272978870097943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61302554134848652580065295 91953831202272978870097943)
            ·
              refine ⟨137930746803409468305146915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91953831202272978870097943 137930746803409468305146915)
              ·
                refine ⟨206896120205114202457720373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137930746803409468305146915 206896120205114202457720373)
                ·
                  refine ⟨19396511269229456480411285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206896120205114202457720373 19396511269229456480411285)
                  ·
                    refine ⟨909211465745130772519279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19396511269229456480411285 909211465745130772519279)
                    ·
                      rfl

theorem cell23_5312049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 5, 6].length) (baseStart_5312049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312049 prefixEnd_5312049 := by exact prefixLift 5312049
  have htrace : WordTrace (prefixWord ++ tailWord_5312049) baseStart_5312049 baseEnd_5312049 := by
    simpa [prefixWord, tailWord_5312049, baseEnd_5312049] using wordTrace_append hprefix tailTrace_5312049
  have hstable : (prefixWord ++ tailWord_5312049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312049).length < 2 ^ (prefixWord ++ tailWord_5312049).sum := by decide
  have hdescent : baseEnd_5312049 < baseStart_5312049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312056 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 3, 1, 4]
def baseStart_5312056 : Nat := 118140960795 + 5312056 * 2 ^ 59
def prefixEnd_5312056 : Nat := 4983230072969 + 3 ^ 40 * 5312056 * 2
def baseEnd_5312056 : Nat := 2727637991599973790170305

theorem tailTrace_5312056 : CollatzResearch.WordTrace tailWord_5312056 prefixEnd_5312056 2727637991599973790170305 := by
  unfold tailWord_5312056
  simp only [CollatzResearch.WordTrace]
  refine ⟨96873299621667906890942011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129164399495557209187922681 96873299621667906890942011)
  ·
    refine ⟨145309949432501860336413017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96873299621667906890942011 145309949432501860336413017)
    ·
      refine ⟨108982462074376395252309763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145309949432501860336413017 108982462074376395252309763)
      ·
        refine ⟨163473693111564592878464645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108982462074376395252309763 163473693111564592878464645)
        ·
          refine ⟨30651317458418361164712121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163473693111564592878464645 30651317458418361164712121)
          ·
            refine ⟨22988488093813770873534091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30651317458418361164712121 22988488093813770873534091)
            ·
              refine ⟨34482732140720656310301137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22988488093813770873534091 34482732140720656310301137)
              ·
                refine ⟨25862049105540492232725853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34482732140720656310301137 25862049105540492232725853)
                ·
                  refine ⟨9698268414577684587272195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25862049105540492232725853 9698268414577684587272195)
                  ·
                    refine ⟨14547402621866526880908293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9698268414577684587272195 14547402621866526880908293)
                    ·
                      refine ⟨2727637991599973790170305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14547402621866526880908293 2727637991599973790170305)
                      ·
                        rfl

theorem cell23_5312056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_5312056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312056 prefixEnd_5312056 := by exact prefixLift 5312056
  have htrace : WordTrace (prefixWord ++ tailWord_5312056) baseStart_5312056 baseEnd_5312056 := by
    simpa [prefixWord, tailWord_5312056, baseEnd_5312056] using wordTrace_append hprefix tailTrace_5312056
  have hstable : (prefixWord ++ tailWord_5312056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312056).length < 2 ^ (prefixWord ++ tailWord_5312056).sum := by decide
  have hdescent : baseEnd_5312056 < baseStart_5312056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312100 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 2, 4]
def baseStart_5312100 : Nat := 118140960795 + 5312100 * 2 ^ 59
def prefixEnd_5312100 : Nat := 4983230072969 + 3 ^ 40 * 5312100 * 2
def baseEnd_5312100 : Nat := 909220194916257206006701

theorem tailTrace_5312100 : CollatzResearch.WordTrace tailWord_5312100 prefixEnd_5312100 909220194916257206006701 := by
  unfold tailWord_5312100
  simp only [CollatzResearch.WordTrace]
  refine ⟨96874102027588204648242877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129165469370117606197657169 96874102027588204648242877)
  ·
    refine ⟨36327788260345576743091079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96874102027588204648242877 36327788260345576743091079)
    ·
      refine ⟨54491682390518365114636619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36327788260345576743091079 54491682390518365114636619)
      ·
        refine ⟨81737523585777547671954929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54491682390518365114636619 81737523585777547671954929)
        ·
          refine ⟨61303142689333160753966197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81737523585777547671954929 61303142689333160753966197)
          ·
            refine ⟨5747169627124983820684331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61303142689333160753966197 5747169627124983820684331)
            ·
              refine ⟨8620754440687475731026497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5747169627124983820684331 8620754440687475731026497)
              ·
                refine ⟨6465565830515606798269873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8620754440687475731026497 6465565830515606798269873)
                ·
                  refine ⟨4849174372886705098702405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6465565830515606798269873 4849174372886705098702405)
                  ·
                    refine ⟨909220194916257206006701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4849174372886705098702405 909220194916257206006701)
                    ·
                      rfl

theorem cell23_5312100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_5312100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312100 prefixEnd_5312100 := by exact prefixLift 5312100
  have htrace : WordTrace (prefixWord ++ tailWord_5312100) baseStart_5312100 baseEnd_5312100 := by
    simpa [prefixWord, tailWord_5312100, baseEnd_5312100] using wordTrace_append hprefix tailTrace_5312100
  have hstable : (prefixWord ++ tailWord_5312100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312100).length < 2 ^ (prefixWord ++ tailWord_5312100).sum := by decide
  have hdescent : baseEnd_5312100 < baseStart_5312100 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312117 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_5312117 : Nat := 118140960795 + 5312117 * 2 ^ 59
def prefixEnd_5312117 : Nat := 4983230072969 + 3 ^ 40 * 5312117 * 2
def baseEnd_5312117 : Nat := 909223104639966017169175

theorem tailTrace_5312117 : CollatzResearch.WordTrace tailWord_5312117 prefixEnd_5312117 909223104639966017169175 := by
  unfold tailWord_5312117
  simp only [CollatzResearch.WordTrace]
  refine ⟨193748824096114821199854605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129165882730743214133236403 193748824096114821199854605)
  ·
    refine ⟨72655809036043057949945477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193748824096114821199854605 72655809036043057949945477)
    ·
      refine ⟨13622964194258073365614777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72655809036043057949945477 13622964194258073365614777)
      ·
        refine ⟨10217223145693555024211083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13622964194258073365614777 10217223145693555024211083)
        ·
          refine ⟨15325834718540332536316625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10217223145693555024211083 15325834718540332536316625)
          ·
            refine ⟨11494376038905249402237469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15325834718540332536316625 11494376038905249402237469)
            ·
              refine ⟨4310391014589468525839051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11494376038905249402237469 4310391014589468525839051)
              ·
                refine ⟨6465586521884202788758577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310391014589468525839051 6465586521884202788758577)
                ·
                  refine ⟨4849189891413152091568933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6465586521884202788758577 4849189891413152091568933)
                  ·
                    refine ⟨909223104639966017169175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4849189891413152091568933 909223104639966017169175)
                    ·
                      rfl

theorem cell23_5312117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_5312117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312117 prefixEnd_5312117 := by exact prefixLift 5312117
  have htrace : WordTrace (prefixWord ++ tailWord_5312117) baseStart_5312117 baseEnd_5312117 := by
    simpa [prefixWord, tailWord_5312117, baseEnd_5312117] using wordTrace_append hprefix tailTrace_5312117
  have hstable : (prefixWord ++ tailWord_5312117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312117).length < 2 ^ (prefixWord ++ tailWord_5312117).sum := by decide
  have hdescent : baseEnd_5312117 < baseStart_5312117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312168 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5312168 : Nat := 118140960795 + 5312168 * 2 ^ 59
def prefixEnd_5312168 : Nat := 4983230072969 + 3 ^ 40 * 5312168 * 2
def baseEnd_5312168 : Nat := 909231833811092450656597

theorem tailTrace_5312168 : CollatzResearch.WordTrace tailWord_5312168 prefixEnd_5312168 909231833811092450656597 := by
  unfold tailWord_5312168
  simp only [CollatzResearch.WordTrace]
  refine ⟨96875342109465028454980579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129167122812620037939974105 96875342109465028454980579)
  ·
    refine ⟨145313013164197542682470869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96875342109465028454980579 145313013164197542682470869)
    ·
      refine ⟨3405773746035879906620411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 145313013164197542682470869 3405773746035879906620411)
      ·
        refine ⟨5108660619053819859930617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3405773746035879906620411 5108660619053819859930617)
        ·
          refine ⟨3831495464290364894947963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5108660619053819859930617 3831495464290364894947963)
          ·
            refine ⟨5747243196435547342421945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831495464290364894947963 5747243196435547342421945)
            ·
              refine ⟨4310432397326660506816459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5747243196435547342421945 4310432397326660506816459)
              ·
                refine ⟨6465648595989990760224689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310432397326660506816459 6465648595989990760224689)
                ·
                  refine ⟨4849236446992493070168517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6465648595989990760224689 4849236446992493070168517)
                  ·
                    refine ⟨909231833811092450656597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4849236446992493070168517 909231833811092450656597)
                    ·
                      rfl

theorem cell23_5312168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5312168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312168 prefixEnd_5312168 := by exact prefixLift 5312168
  have htrace : WordTrace (prefixWord ++ tailWord_5312168) baseStart_5312168 baseEnd_5312168 := by
    simpa [prefixWord, tailWord_5312168, baseEnd_5312168] using wordTrace_append hprefix tailTrace_5312168
  have hstable : (prefixWord ++ tailWord_5312168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312168).length < 2 ^ (prefixWord ++ tailWord_5312168).sum := by decide
  have hdescent : baseEnd_5312168 < baseStart_5312168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312174 : List Nat := [4, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5312174 : Nat := 118140960795 + 5312174 * 2 ^ 59
def prefixEnd_5312174 : Nat := 4983230072969 + 3 ^ 40 * 5312174 * 2
def baseEnd_5312174 : Nat := 2727698582317204328494763

theorem tailTrace_5312174 : CollatzResearch.WordTrace tailWord_5312174 prefixEnd_5312174 2727698582317204328494763 := by
  unfold tailWord_5312174
  simp only [CollatzResearch.WordTrace]
  refine ⟨24218862882113539991834947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129167268704605546623119717 24218862882113539991834947)
  ·
    refine ⟨36328294323170309987752421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24218862882113539991834947 36328294323170309987752421)
    ·
      refine ⟨6811555185594433122703579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36328294323170309987752421 6811555185594433122703579)
      ·
        refine ⟨10217332778391649684055369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6811555185594433122703579 10217332778391649684055369)
        ·
          refine ⟨7662999583793737263041527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10217332778391649684055369 7662999583793737263041527)
          ·
            refine ⟨11494499375690605894562291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7662999583793737263041527 11494499375690605894562291)
            ·
              refine ⟨17241749063535908841843437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11494499375690605894562291 17241749063535908841843437)
              ·
                refine ⟨6465655898825965815691289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17241749063535908841843437 6465655898825965815691289)
                ·
                  refine ⟨4849241924119474361768467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6465655898825965815691289 4849241924119474361768467)
                  ·
                    refine ⟨7273862886179211542652701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4849241924119474361768467 7273862886179211542652701)
                    ·
                      refine ⟨2727698582317204328494763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7273862886179211542652701 2727698582317204328494763)
                      ·
                        rfl

theorem cell23_5312174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5312174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312174 prefixEnd_5312174 := by exact prefixLift 5312174
  have htrace : WordTrace (prefixWord ++ tailWord_5312174) baseStart_5312174 baseEnd_5312174 := by
    simpa [prefixWord, tailWord_5312174, baseEnd_5312174] using wordTrace_append hprefix tailTrace_5312174
  have hstable : (prefixWord ++ tailWord_5312174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312174).length < 2 ^ (prefixWord ++ tailWord_5312174).sum := by decide
  have hdescent : baseEnd_5312174 < baseStart_5312174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312176 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 4]
def baseStart_5312176 : Nat := 118140960795 + 5312176 * 2 ^ 59
def prefixEnd_5312176 : Nat := 4983230072969 + 3 ^ 40 * 5312176 * 2
def baseEnd_5312176 : Nat := 2727699609278513320669753

theorem tailTrace_5312176 : CollatzResearch.WordTrace tailWord_5312176 prefixEnd_5312176 2727699609278513320669753 := by
  unfold tailWord_5312176
  simp only [CollatzResearch.WordTrace]
  refine ⟨96875488001450537138126191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129167317335267382850834921 96875488001450537138126191)
  ·
    refine ⟨145313232002175805707189287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96875488001450537138126191 145313232002175805707189287)
    ·
      refine ⟨217969848003263708560783931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145313232002175805707189287 217969848003263708560783931)
      ·
        refine ⟨326954772004895562841175897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217969848003263708560783931 326954772004895562841175897)
        ·
          refine ⟨245216079003671672130881923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326954772004895562841175897 245216079003671672130881923)
          ·
            refine ⟨367824118505507508196322885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245216079003671672130881923 367824118505507508196322885)
            ·
              refine ⟨68967022219782657786810541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 367824118505507508196322885 68967022219782657786810541)
              ·
                refine ⟨25862633332418496670053953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68967022219782657786810541 25862633332418496670053953)
                ·
                  refine ⟨19396974999313872502540465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25862633332418496670053953 19396974999313872502540465)
                  ·
                    refine ⟨14547731249485404376905349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19396974999313872502540465 14547731249485404376905349)
                    ·
                      refine ⟨2727699609278513320669753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14547731249485404376905349 2727699609278513320669753)
                      ·
                        rfl

theorem cell23_5312176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 4].length) (baseStart_5312176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312176 prefixEnd_5312176 := by exact prefixLift 5312176
  have htrace : WordTrace (prefixWord ++ tailWord_5312176) baseStart_5312176 baseEnd_5312176 := by
    simpa [prefixWord, tailWord_5312176, baseEnd_5312176] using wordTrace_append hprefix tailTrace_5312176
  have hstable : (prefixWord ++ tailWord_5312176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312176).length < 2 ^ (prefixWord ++ tailWord_5312176).sum := by decide
  have hdescent : baseEnd_5312176 < baseStart_5312176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312223 : List Nat := [1, 1, 2, 3, 2, 2, 1, 1, 1, 7, 2]
def baseStart_5312223 : Nat := 118140960795 + 5312223 * 2 ^ 59
def prefixEnd_5312223 : Nat := 4983230072969 + 3 ^ 40 * 5312223 * 2
def baseEnd_5312223 : Nat := 2727723742869274636782037

theorem tailTrace_5312223 : CollatzResearch.WordTrace tailWord_5312223 prefixEnd_5312223 2727723742869274636782037 := by
  unfold tailWord_5312223
  simp only [CollatzResearch.WordTrace]
  refine ⟨193752690233730801303213323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129168460155820534202142215 193752690233730801303213323)
  ·
    refine ⟨290629035350596201954819985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193752690233730801303213323 290629035350596201954819985)
    ·
      refine ⟨217971776512947151466114989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290629035350596201954819985 217971776512947151466114989)
      ·
        refine ⟨81739416192355181799793121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217971776512947151466114989 81739416192355181799793121)
        ·
          refine ⟨61304562144266386349844841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81739416192355181799793121 61304562144266386349844841)
          ·
            refine ⟨45978421608199789762383631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61304562144266386349844841 45978421608199789762383631)
            ·
              refine ⟨68967632412299684643575447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45978421608199789762383631 68967632412299684643575447)
              ·
                refine ⟨103451448618449526965363171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68967632412299684643575447 103451448618449526965363171)
                ·
                  refine ⟨155177172927674290448044757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103451448618449526965363171 155177172927674290448044757)
                  ·
                    refine ⟨3636964990492366182376049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 155177172927674290448044757 3636964990492366182376049)
                    ·
                      refine ⟨2727723742869274636782037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636964990492366182376049 2727723742869274636782037)
                      ·
                        rfl

theorem cell23_5312223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_5312223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312223 prefixEnd_5312223 := by exact prefixLift 5312223
  have htrace : WordTrace (prefixWord ++ tailWord_5312223) baseStart_5312223 baseEnd_5312223 := by
    simpa [prefixWord, tailWord_5312223, baseEnd_5312223] using wordTrace_append hprefix tailTrace_5312223
  have hstable : (prefixWord ++ tailWord_5312223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312223).length < 2 ^ (prefixWord ++ tailWord_5312223).sum := by decide
  have hdescent : baseEnd_5312223 < baseStart_5312223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312253 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_5312253 : Nat := 118140960795 + 5312253 * 2 ^ 59
def prefixEnd_5312253 : Nat := 4983230072969 + 3 ^ 40 * 5312253 * 2
def baseEnd_5312253 : Nat := 2727739147288909519406899

theorem tailTrace_5312253 : CollatzResearch.WordTrace tailWord_5312253 prefixEnd_5312253 2727739147288909519406899 := by
  unfold tailWord_5312253
  simp only [CollatzResearch.WordTrace]
  refine ⟨193753784423622116426805413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129169189615748077617870275 193753784423622116426805413)
  ·
    refine ⟨36328834579429146830026015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193753784423622116426805413 36328834579429146830026015)
    ·
      refine ⟨54493251869143720245039023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36328834579429146830026015 54493251869143720245039023)
      ·
        refine ⟨81739877803715580367558535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54493251869143720245039023 81739877803715580367558535)
        ·
          refine ⟨122609816705573370551337803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81739877803715580367558535 122609816705573370551337803)
          ·
            refine ⟨183914725058360055827006705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122609816705573370551337803 183914725058360055827006705)
            ·
              refine ⟨137936043793770041870255029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183914725058360055827006705 137936043793770041870255029)
              ·
                refine ⟨12931504105665941425336409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137936043793770041870255029 12931504105665941425336409)
                ·
                  refine ⟨9698628079249456069002307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12931504105665941425336409 9698628079249456069002307)
                  ·
                    refine ⟨14547942118874184103503461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9698628079249456069002307 14547942118874184103503461)
                    ·
                      refine ⟨2727739147288909519406899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14547942118874184103503461 2727739147288909519406899)
                      ·
                        rfl

theorem cell23_5312253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_5312253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312253 prefixEnd_5312253 := by exact prefixLift 5312253
  have htrace : WordTrace (prefixWord ++ tailWord_5312253) baseStart_5312253 baseEnd_5312253 := by
    simpa [prefixWord, tailWord_5312253, baseEnd_5312253] using wordTrace_append hprefix tailTrace_5312253
  have hstable : (prefixWord ++ tailWord_5312253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312253).length < 2 ^ (prefixWord ++ tailWord_5312253).sum := by decide
  have hdescent : baseEnd_5312253 < baseStart_5312253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312270 : List Nat := [4, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_5312270 : Nat := 118140960795 + 5312270 * 2 ^ 59
def prefixEnd_5312270 : Nat := 4983230072969 + 3 ^ 40 * 5312270 * 2
def baseEnd_5312270 : Nat := 2727747876460035952894321

theorem tailTrace_5312270 : CollatzResearch.WordTrace tailWord_5312270 prefixEnd_5312270 2727747876460035952894321 := by
  unfold tailWord_5312270
  simp only [CollatzResearch.WordTrace]
  refine ⟨24219300558070066041271783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129169602976373685553449509 24219300558070066041271783)
  ·
    refine ⟨36328950837105099061907675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24219300558070066041271783 36328950837105099061907675)
    ·
      refine ⟨54493426255657648592861513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36328950837105099061907675 54493426255657648592861513)
      ·
        refine ⟨40870069691743236444646135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54493426255657648592861513 40870069691743236444646135)
        ·
          refine ⟨61305104537614854666969203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40870069691743236444646135 61305104537614854666969203)
          ·
            refine ⟨91957656806422282000453805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61305104537614854666969203 91957656806422282000453805)
            ·
              refine ⟨34484121302408355750170177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91957656806422282000453805 34484121302408355750170177)
              ·
                refine ⟨25863090976806266812627633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34484121302408355750170177 25863090976806266812627633)
                ·
                  refine ⟨19397318232604700109470725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25863090976806266812627633 19397318232604700109470725)
                  ·
                    refine ⟨3636997168613381270525761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19397318232604700109470725 3636997168613381270525761)
                    ·
                      refine ⟨2727747876460035952894321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3636997168613381270525761 2727747876460035952894321)
                      ·
                        rfl

theorem cell23_5312270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_5312270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312270 prefixEnd_5312270 := by exact prefixLift 5312270
  have htrace : WordTrace (prefixWord ++ tailWord_5312270) baseStart_5312270 baseEnd_5312270 := by
    simpa [prefixWord, tailWord_5312270, baseEnd_5312270] using wordTrace_append hprefix tailTrace_5312270
  have hstable : (prefixWord ++ tailWord_5312270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312270).length < 2 ^ (prefixWord ++ tailWord_5312270).sum := by decide
  have hdescent : baseEnd_5312270 < baseStart_5312270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312273 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 3]
def baseStart_5312273 : Nat := 118140960795 + 5312273 * 2 ^ 59
def prefixEnd_5312273 : Nat := 4983230072969 + 3 ^ 40 * 5312273 * 2
def baseEnd_5312273 : Nat := 2727749416901999441156807

theorem tailTrace_5312273 : CollatzResearch.WordTrace tailWord_5312273 prefixEnd_5312273 2727749416901999441156807 := by
  unfold tailWord_5312273
  simp only [CollatzResearch.WordTrace]
  refine ⟨193754513883549659842533473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129169675922366439895022315 193754513883549659842533473)
  ·
    refine ⟨145315885412662244881900105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193754513883549659842533473 145315885412662244881900105)
    ·
      refine ⟨108986914059496683661425079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145315885412662244881900105 108986914059496683661425079)
      ·
        refine ⟨163480371089245025492137619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108986914059496683661425079 163480371089245025492137619)
        ·
          refine ⟨245220556633867538238206429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163480371089245025492137619 245220556633867538238206429)
          ·
            refine ⟨91957708737700326839327411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245220556633867538238206429 91957708737700326839327411)
            ·
              refine ⟨137936563106550490258991117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91957708737700326839327411 137936563106550490258991117)
              ·
                refine ⟨51726211164956433847121669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137936563106550490258991117 51726211164956433847121669)
                ·
                  refine ⟨9698664593429331346335313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51726211164956433847121669 9698664593429331346335313)
                  ·
                    refine ⟨7273998445071998509751485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9698664593429331346335313 7273998445071998509751485)
                    ·
                      refine ⟨2727749416901999441156807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7273998445071998509751485 2727749416901999441156807)
                      ·
                        rfl

theorem cell23_5312273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 3].length) (baseStart_5312273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312273 prefixEnd_5312273 := by exact prefixLift 5312273
  have htrace : WordTrace (prefixWord ++ tailWord_5312273) baseStart_5312273 baseEnd_5312273 := by
    simpa [prefixWord, tailWord_5312273, baseEnd_5312273] using wordTrace_append hprefix tailTrace_5312273
  have hstable : (prefixWord ++ tailWord_5312273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312273).length < 2 ^ (prefixWord ++ tailWord_5312273).sum := by decide
  have hdescent : baseEnd_5312273 < baseStart_5312273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312310 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 8]
def baseStart_5312310 : Nat := 118140960795 + 5312310 * 2 ^ 59
def prefixEnd_5312310 : Nat := 4983230072969 + 3 ^ 40 * 5312310 * 2
def baseEnd_5312310 : Nat := 303085379520690644043793

theorem tailTrace_5312310 : CollatzResearch.WordTrace tailWord_5312310 prefixEnd_5312310 303085379520690644043793 := by
  unfold tailWord_5312310
  simp only [CollatzResearch.WordTrace]
  refine ⟨12109741461525975947601899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129170575589610410107753589 12109741461525975947601899)
  ·
    refine ⟨18164612192288963921402849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12109741461525975947601899 18164612192288963921402849)
    ·
      refine ⟨13623459144216722941052137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18164612192288963921402849 13623459144216722941052137)
      ·
        refine ⟨10217594358162542205789103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13623459144216722941052137 10217594358162542205789103)
        ·
          refine ⟨15326391537243813308683655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10217594358162542205789103 15326391537243813308683655)
          ·
            refine ⟨22989587305865719963025483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15326391537243813308683655 22989587305865719963025483)
            ·
              refine ⟨34484380958798579944538225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22989587305865719963025483 34484380958798579944538225)
              ·
                refine ⟨25863285719098934958403669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34484380958798579944538225 25863285719098934958403669)
                ·
                  refine ⟨303085379520690644043793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25863285719098934958403669 303085379520690644043793)
                  ·
                    rfl

theorem cell23_5312310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 8].length) (baseStart_5312310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312310 prefixEnd_5312310 := by exact prefixLift 5312310
  have htrace : WordTrace (prefixWord ++ tailWord_5312310) baseStart_5312310 baseEnd_5312310 := by
    simpa [prefixWord, tailWord_5312310, baseEnd_5312310] using wordTrace_append hprefix tailTrace_5312310
  have hstable : (prefixWord ++ tailWord_5312310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312310).length < 2 ^ (prefixWord ++ tailWord_5312310).sum := by decide
  have hdescent : baseEnd_5312310 < baseStart_5312310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312314 : List Nat := [3, 1, 1, 1, 5, 3, 1, 3, 1, 4]
def baseStart_5312314 : Nat := 118140960795 + 5312314 * 2 ^ 59
def prefixEnd_5312314 : Nat := 4983230072969 + 3 ^ 40 * 5312314 * 2
def baseEnd_5312314 : Nat := 909256823202944593581373

theorem tailTrace_5312314 : CollatzResearch.WordTrace tailWord_5312314 prefixEnd_5312314 909256823202944593581373 := by
  unfold tailWord_5312314
  simp only [CollatzResearch.WordTrace]
  refine ⟨48439002319100280961193999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129170672850934082563183997 48439002319100280961193999)
  ·
    refine ⟨72658503478650421441790999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48439002319100280961193999 72658503478650421441790999)
    ·
      refine ⟨108987755217975632162686499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72658503478650421441790999 108987755217975632162686499)
      ·
        refine ⟨163481632826963448244029749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108987755217975632162686499 163481632826963448244029749)
        ·
          refine ⟨15326403077527823272877789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163481632826963448244029749 15326403077527823272877789)
          ·
            refine ⟨5747401154072933727329171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15326403077527823272877789 5747401154072933727329171)
            ·
              refine ⟨8621101731109400590993757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5747401154072933727329171 8621101731109400590993757)
              ·
                refine ⟨3232913149166025221622659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8621101731109400590993757 3232913149166025221622659)
                ·
                  refine ⟨4849369723749037832433989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3232913149166025221622659 4849369723749037832433989)
                  ·
                    refine ⟨909256823202944593581373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4849369723749037832433989 909256823202944593581373)
                    ·
                      rfl

theorem cell23_5312314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 1, 3, 1, 4].length) (baseStart_5312314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312314 prefixEnd_5312314 := by exact prefixLift 5312314
  have htrace : WordTrace (prefixWord ++ tailWord_5312314) baseStart_5312314 baseEnd_5312314 := by
    simpa [prefixWord, tailWord_5312314, baseEnd_5312314] using wordTrace_append hprefix tailTrace_5312314
  have hstable : (prefixWord ++ tailWord_5312314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312314).length < 2 ^ (prefixWord ++ tailWord_5312314).sum := by decide
  have hdescent : baseEnd_5312314 < baseStart_5312314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312337 : List Nat := [1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 3]
def baseStart_5312337 : Nat := 118140960795 + 5312337 * 2 ^ 59
def prefixEnd_5312337 : Nat := 4983230072969 + 3 ^ 40 * 5312337 * 2
def baseEnd_5312337 : Nat := 2727782279663887190756513

theorem tailTrace_5312337 : CollatzResearch.WordTrace tailWord_5312337 prefixEnd_5312337 2727782279663887190756513 := by
  unfold tailWord_5312337
  simp only [CollatzResearch.WordTrace]
  refine ⟨193756848155317798772863265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129171232103545199181908843 193756848155317798772863265)
  ·
    refine ⟨145317636116488349079647449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193756848155317798772863265 145317636116488349079647449)
    ·
      refine ⟨108988227087366261809735587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145317636116488349079647449 108988227087366261809735587)
      ·
        refine ⟨163482340631049392714603381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108988227087366261809735587 163482340631049392714603381)
        ·
          refine ⟨15326469434160880566994067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163482340631049392714603381 15326469434160880566994067)
          ·
            refine ⟨22989704151241320850491101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15326469434160880566994067 22989704151241320850491101)
            ·
              refine ⟨8621139056715495318934163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22989704151241320850491101 8621139056715495318934163)
              ·
                refine ⟨12931708585073242978401245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8621139056715495318934163 12931708585073242978401245)
                ·
                  refine ⟨4849390719402466116900467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12931708585073242978401245 4849390719402466116900467)
                  ·
                    refine ⟨7274086079103699175350701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4849390719402466116900467 7274086079103699175350701)
                    ·
                      refine ⟨2727782279663887190756513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7274086079103699175350701 2727782279663887190756513)
                      ·
                        rfl

theorem cell23_5312337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 1, 3, 1, 3].length) (baseStart_5312337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312337 prefixEnd_5312337 := by exact prefixLift 5312337
  have htrace : WordTrace (prefixWord ++ tailWord_5312337) baseStart_5312337 baseEnd_5312337 := by
    simpa [prefixWord, tailWord_5312337, baseEnd_5312337] using wordTrace_append hprefix tailTrace_5312337
  have hstable : (prefixWord ++ tailWord_5312337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312337).length < 2 ^ (prefixWord ++ tailWord_5312337).sum := by decide
  have hdescent : baseEnd_5312337 < baseStart_5312337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312353 : List Nat := [1, 2, 3, 1, 1, 1, 4, 3, 1, 6]
def baseStart_5312353 : Nat := 118140960795 + 5312353 * 2 ^ 59
def prefixEnd_5312353 : Nat := 4983230072969 + 3 ^ 40 * 5312353 * 2
def baseEnd_5312353 : Nat := 909263498451453042718813

theorem tailTrace_5312353 : CollatzResearch.WordTrace tailWord_5312353 prefixEnd_5312353 909263498451453042718813 := by
  unfold tailWord_5312353
  simp only [CollatzResearch.WordTrace]
  refine ⟨193757431723259833505445713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129171621148839889003630475 193757431723259833505445713)
  ·
    refine ⟨145318073792444875129084285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193757431723259833505445713 145318073792444875129084285)
    ·
      refine ⟨54494277672166828173406607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145318073792444875129084285 54494277672166828173406607)
      ·
        refine ⟨81741416508250242260109911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54494277672166828173406607 81741416508250242260109911)
        ·
          refine ⟨122612124762375363390164867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81741416508250242260109911 122612124762375363390164867)
          ·
            refine ⟨183918187143563045085247301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122612124762375363390164867 183918187143563045085247301)
            ·
              refine ⟨34484660089418070953483869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 183918187143563045085247301 34484660089418070953483869)
              ·
                refine ⟨12931747533531776607556451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34484660089418070953483869 12931747533531776607556451)
                ·
                  refine ⟨19397621300297664911334677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12931747533531776607556451 19397621300297664911334677)
                  ·
                    refine ⟨909263498451453042718813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19397621300297664911334677 909263498451453042718813)
                    ·
                      rfl

theorem cell23_5312353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 6].length) (baseStart_5312353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312353 prefixEnd_5312353 := by exact prefixLift 5312353
  have htrace : WordTrace (prefixWord ++ tailWord_5312353) baseStart_5312353 baseEnd_5312353 := by
    simpa [prefixWord, tailWord_5312353, baseEnd_5312353] using wordTrace_append hprefix tailTrace_5312353
  have hstable : (prefixWord ++ tailWord_5312353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312353).length < 2 ^ (prefixWord ++ tailWord_5312353).sum := by decide
  have hdescent : baseEnd_5312353 < baseStart_5312353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312360 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_5312360 : Nat := 118140960795 + 5312360 * 2 ^ 59
def prefixEnd_5312360 : Nat := 4983230072969 + 3 ^ 40 * 5312360 * 2
def baseEnd_5312360 : Nat := 2727794089718940600768907

theorem tailTrace_5312360 : CollatzResearch.WordTrace tailWord_5312360 prefixEnd_5312360 2727794089718940600768907 := by
  unfold tailWord_5312360
  simp only [CollatzResearch.WordTrace]
  refine ⟨96878843517117236850475267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129171791356156315800633689 96878843517117236850475267)
  ·
    refine ⟨145318265275675855275712901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96878843517117236850475267 145318265275675855275712901)
    ·
      refine ⟨27247174739189222864196169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145318265275675855275712901 27247174739189222864196169)
      ·
        refine ⟨20435381054391917148147127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27247174739189222864196169 20435381054391917148147127)
        ·
          refine ⟨30653071581587875722220691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20435381054391917148147127 30653071581587875722220691)
          ·
            refine ⟨45979607372381813583331037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30653071581587875722220691 45979607372381813583331037)
            ·
              refine ⟨17242352764643180093749139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45979607372381813583331037 17242352764643180093749139)
              ·
                refine ⟨25863529146964770140623709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17242352764643180093749139 25863529146964770140623709)
                ·
                  refine ⟨9698823430111788802733891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25863529146964770140623709 9698823430111788802733891)
                  ·
                    refine ⟨14548235145167683204100837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9698823430111788802733891 14548235145167683204100837)
                    ·
                      refine ⟨2727794089718940600768907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14548235145167683204100837 2727794089718940600768907)
                      ·
                        rfl

theorem cell23_5312360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_5312360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312360 prefixEnd_5312360 := by exact prefixLift 5312360
  have htrace : WordTrace (prefixWord ++ tailWord_5312360) baseStart_5312360 baseEnd_5312360 := by
    simpa [prefixWord, tailWord_5312360, baseEnd_5312360] using wordTrace_append hprefix tailTrace_5312360
  have hstable : (prefixWord ++ tailWord_5312360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312360).length < 2 ^ (prefixWord ++ tailWord_5312360).sum := by decide
  have hdescent : baseEnd_5312360 < baseStart_5312360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312377 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 1, 1, 4]
def baseStart_5312377 : Nat := 118140960795 + 5312377 * 2 ^ 59
def prefixEnd_5312377 : Nat := 4983230072969 + 3 ^ 40 * 5312377 * 2
def baseEnd_5312377 : Nat := 2727802818890067034256329

theorem tailTrace_5312377 : CollatzResearch.WordTrace tailWord_5312377 prefixEnd_5312377 2727802818890067034256329 := by
  unfold tailWord_5312377
  simp only [CollatzResearch.WordTrace]
  refine ⟨193758307075172885604319385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129172204716781923736212923 193758307075172885604319385)
  ·
    refine ⟨145318730306379664203239539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193758307075172885604319385 145318730306379664203239539)
    ·
      refine ⟨217978095459569496304859309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145318730306379664203239539 217978095459569496304859309)
      ·
        refine ⟨81741785797338561114322241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 217978095459569496304859309 81741785797338561114322241)
        ·
          refine ⟨61306339348003920835741681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81741785797338561114322241 61306339348003920835741681)
          ·
            refine ⟨45979754511002940626806261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61306339348003920835741681 45979754511002940626806261)
            ·
              refine ⟨4310601985406525683763087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45979754511002940626806261 4310601985406525683763087)
              ·
                refine ⟨6465902978109788525644631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310601985406525683763087 6465902978109788525644631)
                ·
                  refine ⟨9698854467164682788466947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6465902978109788525644631 9698854467164682788466947)
                  ·
                    refine ⟨14548281700747024182700421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9698854467164682788466947 14548281700747024182700421)
                    ·
                      refine ⟨2727802818890067034256329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14548281700747024182700421 2727802818890067034256329)
                      ·
                        rfl

theorem cell23_5312377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 1, 1, 4].length) (baseStart_5312377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312377 prefixEnd_5312377 := by exact prefixLift 5312377
  have htrace : WordTrace (prefixWord ++ tailWord_5312377) baseStart_5312377 baseEnd_5312377 := by
    simpa [prefixWord, tailWord_5312377, baseEnd_5312377] using wordTrace_append hprefix tailTrace_5312377
  have hstable : (prefixWord ++ tailWord_5312377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312377).length < 2 ^ (prefixWord ++ tailWord_5312377).sum := by decide
  have hdescent : baseEnd_5312377 < baseStart_5312377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312387 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 2, 4]
def baseStart_5312387 : Nat := 118140960795 + 5312387 * 2 ^ 59
def prefixEnd_5312387 : Nat := 4983230072969 + 3 ^ 40 * 5312387 * 2
def baseEnd_5312387 : Nat := 909269317898870665043761

theorem tailTrace_5312387 : CollatzResearch.WordTrace tailWord_5312387 prefixEnd_5312387 909269317898870665043761 := by
  unfold tailWord_5312387
  simp only [CollatzResearch.WordTrace]
  refine ⟨193758671805136657312183415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129172447870091104874788943 193758671805136657312183415)
  ·
    refine ⟨290638007707704985968275123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193758671805136657312183415 290638007707704985968275123)
    ·
      refine ⟨435957011561557478952412685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290638007707704985968275123 435957011561557478952412685)
      ·
        refine ⟨163483879335584054607154757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435957011561557478952412685 163483879335584054607154757)
        ·
          refine ⟨30653227375422010238841517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163483879335584054607154757 30653227375422010238841517)
          ·
            refine ⟨11494960265783253839565569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30653227375422010238841517 11494960265783253839565569)
            ·
              refine ⟨8621220199337440379674177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11494960265783253839565569 8621220199337440379674177)
              ·
                refine ⟨6465915149503080284755633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8621220199337440379674177 6465915149503080284755633)
                ·
                  refine ⟨4849436362127310213566725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6465915149503080284755633 4849436362127310213566725)
                  ·
                    refine ⟨909269317898870665043761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4849436362127310213566725 909269317898870665043761)
                    ·
                      rfl

theorem cell23_5312387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 2, 4].length) (baseStart_5312387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312387 prefixEnd_5312387 := by exact prefixLift 5312387
  have htrace : WordTrace (prefixWord ++ tailWord_5312387) baseStart_5312387 baseEnd_5312387 := by
    simpa [prefixWord, tailWord_5312387, baseEnd_5312387] using wordTrace_append hprefix tailTrace_5312387
  have hstable : (prefixWord ++ tailWord_5312387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312387).length < 2 ^ (prefixWord ++ tailWord_5312387).sum := by decide
  have hdescent : baseEnd_5312387 < baseStart_5312387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312417 : List Nat := [1, 2, 3, 4, 2, 1, 3, 7]
def baseStart_5312417 : Nat := 118140960795 + 5312417 * 2 ^ 59
def prefixEnd_5312417 : Nat := 4983230072969 + 3 ^ 40 * 5312417 * 2
def baseEnd_5312417 : Nat := 101030494745046180657635

theorem tailTrace_5312417 : CollatzResearch.WordTrace tailWord_5312417 prefixEnd_5312417 101030494745046180657635 := by
  unfold tailWord_5312417
  simp only [CollatzResearch.WordTrace]
  refine ⟨193759765995027972435775505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129173177330018648290517003 193759765995027972435775505)
  ·
    refine ⟨145319824496270979326831629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193759765995027972435775505 145319824496270979326831629)
    ·
      refine ⟨54494934186101617247561861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145319824496270979326831629 54494934186101617247561861)
      ·
        refine ⟨10217800159894053233917849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54494934186101617247561861 10217800159894053233917849)
        ·
          refine ⟨7663350119920539925438387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10217800159894053233917849 7663350119920539925438387)
          ·
            refine ⟨11495025179880809888157581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663350119920539925438387 11495025179880809888157581)
            ·
              refine ⟨4310634442455303708059093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11495025179880809888157581 4310634442455303708059093)
              ·
                refine ⟨101030494745046180657635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4310634442455303708059093 101030494745046180657635)
                ·
                  rfl

theorem cell23_5312417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 7].length) (baseStart_5312417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312417 prefixEnd_5312417 := by exact prefixLift 5312417
  have htrace : WordTrace (prefixWord ++ tailWord_5312417) baseStart_5312417 baseEnd_5312417 := by
    simpa [prefixWord, tailWord_5312417, baseEnd_5312417] using wordTrace_append hprefix tailTrace_5312417
  have hstable : (prefixWord ++ tailWord_5312417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312417).length < 2 ^ (prefixWord ++ tailWord_5312417).sum := by decide
  have hdescent : baseEnd_5312417 < baseStart_5312417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312443 : List Nat := [1, 1, 1, 1, 1, 2, 2, 6, 2, 6]
def baseStart_5312443 : Nat := 118140960795 + 5312443 * 2 ^ 59
def prefixEnd_5312443 : Nat := 4983230072969 + 3 ^ 40 * 5312443 * 2
def baseEnd_5312443 : Nat := 909278902871087925343675

theorem tailTrace_5312443 : CollatzResearch.WordTrace tailWord_5312443 prefixEnd_5312443 909278902871087925343675 := by
  unfold tailWord_5312443
  simp only [CollatzResearch.WordTrace]
  refine ⟨193760714292933778876221983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129173809528622519250814655 193760714292933778876221983)
  ·
    refine ⟨290641071439400668314332975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193760714292933778876221983 290641071439400668314332975)
    ·
      refine ⟨435961607159101002471499463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290641071439400668314332975 435961607159101002471499463)
      ·
        refine ⟨653942410738651503707249195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435961607159101002471499463 653942410738651503707249195)
        ·
          refine ⟨980913616107977255560873793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 653942410738651503707249195 980913616107977255560873793)
          ·
            refine ⟨735685212080982941670655345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 980913616107977255560873793 735685212080982941670655345)
            ·
              refine ⟨551763909060737206252991509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735685212080982941670655345 551763909060737206252991509)
              ·
                refine ⟨25863933237222056543108977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 551763909060737206252991509 25863933237222056543108977)
                ·
                  refine ⟨19397949927916542407331733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25863933237222056543108977 19397949927916542407331733)
                  ·
                    refine ⟨909278902871087925343675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19397949927916542407331733 909278902871087925343675)
                    ·
                      rfl

theorem cell23_5312443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 6, 2, 6].length) (baseStart_5312443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312443 prefixEnd_5312443 := by exact prefixLift 5312443
  have htrace : WordTrace (prefixWord ++ tailWord_5312443) baseStart_5312443 baseEnd_5312443 := by
    simpa [prefixWord, tailWord_5312443, baseEnd_5312443] using wordTrace_append hprefix tailTrace_5312443
  have hstable : (prefixWord ++ tailWord_5312443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312443).length < 2 ^ (prefixWord ++ tailWord_5312443).sum := by decide
  have hdescent : baseEnd_5312443 < baseStart_5312443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312453 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 5]
def baseStart_5312453 : Nat := 118140960795 + 5312453 * 2 ^ 59
def prefixEnd_5312453 : Nat := 4983230072969 + 3 ^ 40 * 5312453 * 2
def baseEnd_5312453 : Nat := 2727841843419808736905979

theorem tailTrace_5312453 : CollatzResearch.WordTrace tailWord_5312453 prefixEnd_5312453 2727841843419808736905979 := by
  unfold tailWord_5312453
  simp only [CollatzResearch.WordTrace]
  refine ⟨193761079022897550584086013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129174052681931700389390675 193761079022897550584086013)
  ·
    refine ⟨72660404633586581469032255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193761079022897550584086013 72660404633586581469032255)
    ·
      refine ⟨108990606950379872203548383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72660404633586581469032255 108990606950379872203548383)
      ·
        refine ⟨163485910425569808305322575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108990606950379872203548383 163485910425569808305322575)
        ·
          refine ⟨245228865638354712457983863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163485910425569808305322575 245228865638354712457983863)
          ·
            refine ⟨367843298457532068686975795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245228865638354712457983863 367843298457532068686975795)
            ·
              refine ⟨551764947686298103030463693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367843298457532068686975795 551764947686298103030463693)
              ·
                refine ⟨206911855382361788636423885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 551764947686298103030463693 206911855382361788636423885)
                ·
                  refine ⟨77591945768385670738658957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206911855382361788636423885 77591945768385670738658957)
                  ·
                    refine ⟨29096979663144626526997109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 77591945768385670738658957 29096979663144626526997109)
                    ·
                      refine ⟨2727841843419808736905979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29096979663144626526997109 2727841843419808736905979)
                      ·
                        rfl

theorem cell23_5312453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 3, 5].length) (baseStart_5312453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312453 prefixEnd_5312453 := by exact prefixLift 5312453
  have htrace : WordTrace (prefixWord ++ tailWord_5312453) baseStart_5312453 baseEnd_5312453 := by
    simpa [prefixWord, tailWord_5312453, baseEnd_5312453] using wordTrace_append hprefix tailTrace_5312453
  have hstable : (prefixWord ++ tailWord_5312453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312453).length < 2 ^ (prefixWord ++ tailWord_5312453).sum := by decide
  have hdescent : baseEnd_5312453 < baseStart_5312453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312460 : List Nat := [2, 2, 1, 4, 1, 2, 2, 1, 2, 6]
def baseStart_5312460 : Nat := 118140960795 + 5312460 * 2 ^ 59
def prefixEnd_5312460 : Nat := 4983230072969 + 3 ^ 40 * 5312460 * 2
def baseEnd_5312460 : Nat := 909281812594796736506149

theorem tailTrace_5312460 : CollatzResearch.WordTrace tailWord_5312460 prefixEnd_5312460 909281812594796736506149 := by
  unfold tailWord_5312460
  simp only [CollatzResearch.WordTrace]
  refine ⟨96880667166936095389795417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129174222889248127186393889 96880667166936095389795417)
  ·
    refine ⟨72660500375202071542346563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96880667166936095389795417 72660500375202071542346563)
    ·
      refine ⟨108990750562803107313519845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72660500375202071542346563 108990750562803107313519845)
      ·
        refine ⟨20435765730525582621284971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108990750562803107313519845 20435765730525582621284971)
        ·
          refine ⟨30653648595788373931927457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20435765730525582621284971 30653648595788373931927457)
          ·
            refine ⟨22990236446841280448945593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30653648595788373931927457 22990236446841280448945593)
            ·
              refine ⟨17242677335130960336709195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22990236446841280448945593 17242677335130960336709195)
              ·
                refine ⟨25864016002696440505063793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17242677335130960336709195 25864016002696440505063793)
                ·
                  refine ⟨19398012002022330378797845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25864016002696440505063793 19398012002022330378797845)
                  ·
                    refine ⟨909281812594796736506149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19398012002022330378797845 909281812594796736506149)
                    ·
                      rfl

theorem cell23_5312460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 2, 2, 1, 2, 6].length) (baseStart_5312460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312460 prefixEnd_5312460 := by exact prefixLift 5312460
  have htrace : WordTrace (prefixWord ++ tailWord_5312460) baseStart_5312460 baseEnd_5312460 := by
    simpa [prefixWord, tailWord_5312460, baseEnd_5312460] using wordTrace_append hprefix tailTrace_5312460
  have hstable : (prefixWord ++ tailWord_5312460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312460).length < 2 ^ (prefixWord ++ tailWord_5312460).sum := by decide
  have hdescent : baseEnd_5312460 < baseStart_5312460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312487 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 5]
def baseStart_5312487 : Nat := 118140960795 + 5312487 * 2 ^ 59
def prefixEnd_5312487 : Nat := 4983230072969 + 3 ^ 40 * 5312487 * 2
def baseEnd_5312487 : Nat := 2727859301762061603880823

theorem tailTrace_5312487 : CollatzResearch.WordTrace tailWord_5312487 prefixEnd_5312487 2727859301762061603880823 := by
  unfold tailWord_5312487
  simp only [CollatzResearch.WordTrace]
  refine ⟨193762319104774374390823715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129174879403182916260549143 193762319104774374390823715)
  ·
    refine ⟨290643478657161561586235573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193762319104774374390823715 290643478657161561586235573)
    ·
      refine ⟨27247826124108896398709585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 290643478657161561586235573 27247826124108896398709585)
      ·
        refine ⟨20435869593081672299032189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27247826124108896398709585 20435869593081672299032189)
        ·
          refine ⟨7663451097405627112137071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20435869593081672299032189 7663451097405627112137071)
          ·
            refine ⟨11495176646108440668205607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663451097405627112137071 11495176646108440668205607)
            ·
              refine ⟨17242764969162661002308411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11495176646108440668205607 17242764969162661002308411)
              ·
                refine ⟨25864147453743991503462617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17242764969162661002308411 25864147453743991503462617)
                ·
                  refine ⟨19398110590307993627596963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25864147453743991503462617 19398110590307993627596963)
                  ·
                    refine ⟨29097165885461990441395445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19398110590307993627596963 29097165885461990441395445)
                    ·
                      refine ⟨2727859301762061603880823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29097165885461990441395445 2727859301762061603880823)
                      ·
                        rfl

theorem cell23_5312487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_5312487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312487 prefixEnd_5312487 := by exact prefixLift 5312487
  have htrace : WordTrace (prefixWord ++ tailWord_5312487) baseStart_5312487 baseEnd_5312487 := by
    simpa [prefixWord, tailWord_5312487, baseEnd_5312487] using wordTrace_append hprefix tailTrace_5312487
  have hstable : (prefixWord ++ tailWord_5312487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312487).length < 2 ^ (prefixWord ++ tailWord_5312487).sum := by decide
  have hdescent : baseEnd_5312487 < baseStart_5312487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312503 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 2, 11]
def baseStart_5312503 : Nat := 118140960795 + 5312503 * 2 ^ 59
def prefixEnd_5312503 : Nat := 4983230072969 + 3 ^ 40 * 5312503 * 2
def baseEnd_5312503 : Nat := 909289172484177847093583

theorem tailTrace_5312503 : CollatzResearch.WordTrace tailWord_5312503 prefixEnd_5312503 909289172484177847093583 := by
  unfold tailWord_5312503
  simp only [CollatzResearch.WordTrace]
  refine ⟨193762902672716409123406163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129175268448477606082270775 193762902672716409123406163)
  ·
    refine ⟨290644354009074613685109245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193762902672716409123406163 290644354009074613685109245)
    ·
      refine ⟨108991632753402980131915967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290644354009074613685109245 108991632753402980131915967)
      ·
        refine ⟨163487449130104470197873951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108991632753402980131915967 163487449130104470197873951)
        ·
          refine ⟨245231173695156705296810927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163487449130104470197873951 245231173695156705296810927)
          ·
            refine ⟨367846760542735057945216391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245231173695156705296810927 367846760542735057945216391)
            ·
              refine ⟨551770140814102586917824587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367846760542735057945216391 551770140814102586917824587)
              ·
                refine ⟨827655211221153880376736881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551770140814102586917824587 827655211221153880376736881)
                ·
                  refine ⟨620741408415865410282552661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 827655211221153880376736881 620741408415865410282552661)
                  ·
                    refine ⟨909289172484177847093583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 620741408415865410282552661 909289172484177847093583)
                    ·
                      rfl

theorem cell23_5312503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_5312503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312503 prefixEnd_5312503 := by exact prefixLift 5312503
  have htrace : WordTrace (prefixWord ++ tailWord_5312503) baseStart_5312503 baseEnd_5312503 := by
    simpa [prefixWord, tailWord_5312503, baseEnd_5312503] using wordTrace_append hprefix tailTrace_5312503
  have hstable : (prefixWord ++ tailWord_5312503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312503).length < 2 ^ (prefixWord ++ tailWord_5312503).sum := by decide
  have hdescent : baseEnd_5312503 < baseStart_5312503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312520 : List Nat := [2, 1, 3, 2, 1, 2, 1, 2, 4, 5]
def baseStart_5312520 : Nat := 118140960795 + 5312520 * 2 ^ 59
def prefixEnd_5312520 : Nat := 4983230072969 + 3 ^ 40 * 5312520 * 2
def baseEnd_5312520 : Nat := 909292082207886658256057

theorem tailTrace_5312520 : CollatzResearch.WordTrace tailWord_5312520 prefixEnd_5312520 909292082207886658256057 := by
  unfold tailWord_5312520
  simp only [CollatzResearch.WordTrace]
  refine ⟨96881761356827410513387507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129175681809103214017850009 96881761356827410513387507)
  ·
    refine ⟨145322642035241115770081261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96881761356827410513387507 145322642035241115770081261)
    ·
      refine ⟨54495990763215418413780473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145322642035241115770081261 54495990763215418413780473)
      ·
        refine ⟨40871993072411563810335355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54495990763215418413780473 40871993072411563810335355)
        ·
          refine ⟨61307989608617345715503033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40871993072411563810335355 61307989608617345715503033)
          ·
            refine ⟨45980992206463009286627275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61307989608617345715503033 45980992206463009286627275)
            ·
              refine ⟨68971488309694513929940913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45980992206463009286627275 68971488309694513929940913)
              ·
                refine ⟨51728616232270885447455685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68971488309694513929940913 51728616232270885447455685)
                ·
                  refine ⟨9699115543550791021397941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51728616232270885447455685 9699115543550791021397941)
                  ·
                    refine ⟨909292082207886658256057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9699115543550791021397941 909292082207886658256057)
                    ·
                      rfl

theorem cell23_5312520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 4, 5].length) (baseStart_5312520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312520 prefixEnd_5312520 := by exact prefixLift 5312520
  have htrace : WordTrace (prefixWord ++ tailWord_5312520) baseStart_5312520 baseEnd_5312520 := by
    simpa [prefixWord, tailWord_5312520, baseEnd_5312520] using wordTrace_append hprefix tailTrace_5312520
  have hstable : (prefixWord ++ tailWord_5312520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312520).length < 2 ^ (prefixWord ++ tailWord_5312520).sum := by decide
  have hdescent : baseEnd_5312520 < baseStart_5312520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312570 : List Nat := [3, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4]
def baseStart_5312570 : Nat := 118140960795 + 5312570 * 2 ^ 59
def prefixEnd_5312570 : Nat := 4983230072969 + 3 ^ 40 * 5312570 * 2
def baseEnd_5312570 : Nat := 2727901920656384779142941

theorem tailTrace_5312570 : CollatzResearch.WordTrace tailWord_5312570 prefixEnd_5312570 2727901920656384779142941 := by
  unfold tailWord_5312570
  simp only [CollatzResearch.WordTrace]
  refine ⟨48441336590868419891523791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129176897575649119710730109 48441336590868419891523791)
  ·
    refine ⟨72662004886302629837285687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48441336590868419891523791 72662004886302629837285687)
    ·
      refine ⟨108993007329453944755928531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72662004886302629837285687 108993007329453944755928531)
      ·
        refine ⟨163489510994180917133892797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108993007329453944755928531 163489510994180917133892797)
        ·
          refine ⟨61308566622817843925209799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163489510994180917133892797 61308566622817843925209799)
          ·
            refine ⟨91962849934226765887814699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61308566622817843925209799 91962849934226765887814699)
            ·
              refine ⟨137944274901340148831722049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91962849934226765887814699 137944274901340148831722049)
              ·
                refine ⟨103458206176005111623791537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137944274901340148831722049 103458206176005111623791537)
                ·
                  refine ⟨77593654632003833717843653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 103458206176005111623791537 77593654632003833717843653)
                  ·
                    refine ⟨14548810243500718822095685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77593654632003833717843653 14548810243500718822095685)
                    ·
                      refine ⟨2727901920656384779142941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14548810243500718822095685 2727901920656384779142941)
                      ·
                        rfl

theorem cell23_5312570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 2, 2, 4, 4].length) (baseStart_5312570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312570 prefixEnd_5312570 := by exact prefixLift 5312570
  have htrace : WordTrace (prefixWord ++ tailWord_5312570) baseStart_5312570 baseEnd_5312570 := by
    simpa [prefixWord, tailWord_5312570, baseEnd_5312570] using wordTrace_append hprefix tailTrace_5312570
  have hstable : (prefixWord ++ tailWord_5312570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312570).length < 2 ^ (prefixWord ++ tailWord_5312570).sum := by decide
  have hdescent : baseEnd_5312570 < baseStart_5312570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312594 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_5312594 : Nat := 118140960795 + 5312594 * 2 ^ 59
def prefixEnd_5312594 : Nat := 4983230072969 + 3 ^ 40 * 5312594 * 2
def baseEnd_5312594 : Nat := 2727914244192092685242831

theorem tailTrace_5312594 : CollatzResearch.WordTrace tailWord_5312594 prefixEnd_5312594 2727914244192092685242831 := by
  unfold tailWord_5312594
  simp only [CollatzResearch.WordTrace]
  refine ⟨48441555428846682916242209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129177481143591154443312557 48441555428846682916242209)
  ·
    refine ⟨36331166571635012187181657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48441555428846682916242209 36331166571635012187181657)
    ·
      refine ⟨27248374928726259140386243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36331166571635012187181657 27248374928726259140386243)
      ·
        refine ⟨40872562393089388710579365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27248374928726259140386243 40872562393089388710579365)
        ·
          refine ⟨7663605448704260383233631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40872562393089388710579365 7663605448704260383233631)
          ·
            refine ⟨11495408173056390574850447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663605448704260383233631 11495408173056390574850447)
            ·
              refine ⟨17243112259584585862275671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11495408173056390574850447 17243112259584585862275671)
              ·
                refine ⟨25864668389376878793413507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17243112259584585862275671 25864668389376878793413507)
                ·
                  refine ⟨38797002584065318190120261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25864668389376878793413507 38797002584065318190120261)
                  ·
                    refine ⟨7274437984512247160647549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38797002584065318190120261 7274437984512247160647549)
                    ·
                      refine ⟨2727914244192092685242831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7274437984512247160647549 2727914244192092685242831)
                      ·
                        rfl

theorem cell23_5312594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_5312594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312594 prefixEnd_5312594 := by exact prefixLift 5312594
  have htrace : WordTrace (prefixWord ++ tailWord_5312594) baseStart_5312594 baseEnd_5312594 := by
    simpa [prefixWord, tailWord_5312594, baseEnd_5312594] using wordTrace_append hprefix tailTrace_5312594
  have hstable : (prefixWord ++ tailWord_5312594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312594).length < 2 ^ (prefixWord ++ tailWord_5312594).sum := by decide
  have hdescent : baseEnd_5312594 < baseStart_5312594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312624 : List Nat := [2, 1, 1, 1, 5, 2, 1, 3, 3, 1, 3]
def baseStart_5312624 : Nat := 118140960795 + 5312624 * 2 ^ 59
def prefixEnd_5312624 : Nat := 4983230072969 + 3 ^ 40 * 5312624 * 2
def baseEnd_5312624 : Nat := 2727929648611727567867693

theorem tailTrace_5312624 : CollatzResearch.WordTrace tailWord_5312624 prefixEnd_5312624 2727929648611727567867693 := by
  unfold tailWord_5312624
  simp only [CollatzResearch.WordTrace]
  refine ⟨96883657952639023394280463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129178210603518697859040617 96883657952639023394280463)
  ·
    refine ⟨145325486928958535091420695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96883657952639023394280463 145325486928958535091420695)
    ·
      refine ⟨217988230393437802637131043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145325486928958535091420695 217988230393437802637131043)
      ·
        refine ⟨326982345590156703955696565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217988230393437802637131043 326982345590156703955696565)
        ·
          refine ⟨30654594899077190995846553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 326982345590156703955696565 30654594899077190995846553)
          ·
            refine ⟨22990946174307893246884915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30654594899077190995846553 22990946174307893246884915)
            ·
              refine ⟨34486419261461839870327373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22990946174307893246884915 34486419261461839870327373)
              ·
                refine ⟨12932407223048189951372765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34486419261461839870327373 12932407223048189951372765)
                ·
                  refine ⟨4849652708643071231764787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12932407223048189951372765 4849652708643071231764787)
                  ·
                    refine ⟨7274479062964606847647181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4849652708643071231764787 7274479062964606847647181)
                    ·
                      refine ⟨2727929648611727567867693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7274479062964606847647181 2727929648611727567867693)
                      ·
                        rfl

theorem cell23_5312624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 3, 1, 3].length) (baseStart_5312624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312624 prefixEnd_5312624 := by exact prefixLift 5312624
  have htrace : WordTrace (prefixWord ++ tailWord_5312624) baseStart_5312624 baseEnd_5312624 := by
    simpa [prefixWord, tailWord_5312624, baseEnd_5312624] using wordTrace_append hprefix tailTrace_5312624
  have hstable : (prefixWord ++ tailWord_5312624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312624).length < 2 ^ (prefixWord ++ tailWord_5312624).sum := by decide
  have hdescent : baseEnd_5312624 < baseStart_5312624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312644 : List Nat := [2, 3, 2, 1, 2, 1, 4, 2, 1, 5]
def baseStart_5312644 : Nat := 118140960795 + 5312644 * 2 ^ 59
def prefixEnd_5312644 : Nat := 4983230072969 + 3 ^ 40 * 5312644 * 2
def baseEnd_5312644 : Nat := 909313306074939163205867

theorem tailTrace_5312644 : CollatzResearch.WordTrace tailWord_5312644 prefixEnd_5312644 909313306074939163205867 := by
  unfold tailWord_5312644
  simp only [CollatzResearch.WordTrace]
  refine ⟨96884022682602795102144493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129178696910137060136192657 96884022682602795102144493)
  ·
    refine ⟨36331508505976048163304185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96884022682602795102144493 36331508505976048163304185)
    ·
      refine ⟨27248631379482036122478139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36331508505976048163304185 27248631379482036122478139)
      ·
        refine ⟨40872947069223054183717209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27248631379482036122478139 40872947069223054183717209)
        ·
          refine ⟨30654710301917290637787907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40872947069223054183717209 30654710301917290637787907)
          ·
            refine ⟨45982065452875935956681861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30654710301917290637787907 45982065452875935956681861)
            ·
              refine ⟨8621637272414237991877849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45982065452875935956681861 8621637272414237991877849)
              ·
                refine ⟨6466227954310678493908387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8621637272414237991877849 6466227954310678493908387)
                ·
                  refine ⟨9699341931466017740862581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6466227954310678493908387 9699341931466017740862581)
                  ·
                    refine ⟨909313306074939163205867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9699341931466017740862581 909313306074939163205867)
                    ·
                      rfl

theorem cell23_5312644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_5312644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312644 prefixEnd_5312644 := by exact prefixLift 5312644
  have htrace : WordTrace (prefixWord ++ tailWord_5312644) baseStart_5312644 baseEnd_5312644 := by
    simpa [prefixWord, tailWord_5312644, baseEnd_5312644] using wordTrace_append hprefix tailTrace_5312644
  have hstable : (prefixWord ++ tailWord_5312644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312644).length < 2 ^ (prefixWord ++ tailWord_5312644).sum := by decide
  have hdescent : baseEnd_5312644 < baseStart_5312644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312647 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_5312647 : Nat := 118140960795 + 5312647 * 2 ^ 59
def prefixEnd_5312647 : Nat := 4983230072969 + 3 ^ 40 * 5312647 * 2
def baseEnd_5312647 : Nat := 2727941458666780977880087

theorem tailTrace_5312647 : CollatzResearch.WordTrace tailWord_5312647 prefixEnd_5312647 2727941458666780977880087 := by
  unfold tailWord_5312647
  simp only [CollatzResearch.WordTrace]
  refine ⟨193768154784194721716648195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129178769856129814477765463 193768154784194721716648195)
  ·
    refine ⟨290652232176292082574972293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193768154784194721716648195 290652232176292082574972293)
    ·
      refine ⟨54497293533054765482807305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290652232176292082574972293 54497293533054765482807305)
      ·
        refine ⟨40872970149791074112105479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54497293533054765482807305 40872970149791074112105479)
        ·
          refine ⟨61309455224686611168158219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40872970149791074112105479 61309455224686611168158219)
          ·
            refine ⟨91964182837029916752237329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61309455224686611168158219 91964182837029916752237329)
            ·
              refine ⟨68973137127772437564177997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91964182837029916752237329 68973137127772437564177997)
              ·
                refine ⟨25864926422914664086566749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68973137127772437564177997 25864926422914664086566749)
                ·
                  refine ⟨9699347408592999032462531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25864926422914664086566749 9699347408592999032462531)
                  ·
                    refine ⟨14549021112889498548693797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9699347408592999032462531 14549021112889498548693797)
                    ·
                      refine ⟨2727941458666780977880087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14549021112889498548693797 2727941458666780977880087)
                      ·
                        rfl

theorem cell23_5312647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_5312647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312647 prefixEnd_5312647 := by exact prefixLift 5312647
  have htrace : WordTrace (prefixWord ++ tailWord_5312647) baseStart_5312647 baseEnd_5312647 := by
    simpa [prefixWord, tailWord_5312647, baseEnd_5312647] using wordTrace_append hprefix tailTrace_5312647
  have hstable : (prefixWord ++ tailWord_5312647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312647).length < 2 ^ (prefixWord ++ tailWord_5312647).sum := by decide
  have hdescent : baseEnd_5312647 < baseStart_5312647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312662 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5312662 : Nat := 118140960795 + 5312662 * 2 ^ 59
def prefixEnd_5312662 : Nat := 4983230072969 + 3 ^ 40 * 5312662 * 2
def baseEnd_5312662 : Nat := 2727949160876598419192519

theorem tailTrace_5312662 : CollatzResearch.WordTrace tailWord_5312662 prefixEnd_5312662 2727949160876598419192519 := by
  unfold tailWord_5312662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12110543867446273704902765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129179134586093586185629493 12110543867446273704902765)
  ·
    refine ⟨4541453950292352639338537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12110543867446273704902765 4541453950292352639338537)
    ·
      refine ⟨3406090462719264479503903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4541453950292352639338537 3406090462719264479503903)
      ·
        refine ⟨5109135694078896719255855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3406090462719264479503903 5109135694078896719255855)
        ·
          refine ⟨7663703541118345078883783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5109135694078896719255855 7663703541118345078883783)
          ·
            refine ⟨11495555311677517618325675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663703541118345078883783 11495555311677517618325675)
            ·
              refine ⟨17243332967516276427488513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11495555311677517618325675 17243332967516276427488513)
              ·
                refine ⟨12932499725637207320616385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17243332967516276427488513 12932499725637207320616385)
                ·
                  refine ⟨9699374794227905490462289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12932499725637207320616385 9699374794227905490462289)
                  ·
                    refine ⟨7274531095670929117846717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9699374794227905490462289 7274531095670929117846717)
                    ·
                      refine ⟨2727949160876598419192519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7274531095670929117846717 2727949160876598419192519)
                      ·
                        rfl

theorem cell23_5312662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5312662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312662 prefixEnd_5312662 := by exact prefixLift 5312662
  have htrace : WordTrace (prefixWord ++ tailWord_5312662) baseStart_5312662 baseEnd_5312662 := by
    simpa [prefixWord, tailWord_5312662, baseEnd_5312662] using wordTrace_append hprefix tailTrace_5312662
  have hstable : (prefixWord ++ tailWord_5312662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312662).length < 2 ^ (prefixWord ++ tailWord_5312662).sum := by decide
  have hdescent : baseEnd_5312662 < baseStart_5312662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312714 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3]
def baseStart_5312714 : Nat := 118140960795 + 5312714 * 2 ^ 59
def prefixEnd_5312714 : Nat := 4983230072969 + 3 ^ 40 * 5312714 * 2
def baseEnd_5312714 : Nat := 2727975861870632215742279

theorem tailTrace_5312714 : CollatzResearch.WordTrace tailWord_5312714 prefixEnd_5312714 2727975861870632215742279 := by
  unfold tailWord_5312714
  simp only [CollatzResearch.WordTrace]
  refine ⟨48442649618737998039834299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129180398983301328106224797 48442649618737998039834299)
  ·
    refine ⟨72663974428106997059751449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48442649618737998039834299 72663974428106997059751449)
    ·
      refine ⟨54497980821080247794813587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72663974428106997059751449 54497980821080247794813587)
      ·
        refine ⟨81746971231620371692220381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54497980821080247794813587 81746971231620371692220381)
        ·
          refine ⟨30655114211857639384582643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81746971231620371692220381 30655114211857639384582643)
          ·
            refine ⟨45982671317786459076873965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30655114211857639384582643 45982671317786459076873965)
            ·
              refine ⟨17243501744169922153827737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45982671317786459076873965 17243501744169922153827737)
              ·
                refine ⟨12932626308127441615370803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17243501744169922153827737 12932626308127441615370803)
                ·
                  refine ⟨19398939462191162423056205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12932626308127441615370803 19398939462191162423056205)
                  ·
                    refine ⟨7274602298321685908646077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19398939462191162423056205 7274602298321685908646077)
                    ·
                      refine ⟨2727975861870632215742279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7274602298321685908646077 2727975861870632215742279)
                      ·
                        rfl

theorem cell23_5312714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_5312714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312714 prefixEnd_5312714 := by exact prefixLift 5312714
  have htrace : WordTrace (prefixWord ++ tailWord_5312714) baseStart_5312714 baseEnd_5312714 := by
    simpa [prefixWord, tailWord_5312714, baseEnd_5312714] using wordTrace_append hprefix tailTrace_5312714
  have hstable : (prefixWord ++ tailWord_5312714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312714).length < 2 ^ (prefixWord ++ tailWord_5312714).sum := by decide
  have hdescent : baseEnd_5312714 < baseStart_5312714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312718 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_5312718 : Nat := 118140960795 + 5312718 * 2 ^ 59
def prefixEnd_5312718 : Nat := 4983230072969 + 3 ^ 40 * 5312718 * 2
def baseEnd_5312718 : Nat := 2727977915793250200092261

theorem tailTrace_5312718 : CollatzResearch.WordTrace tailWord_5312718 prefixEnd_5312718 2727977915793250200092261 := by
  unfold tailWord_5312718
  simp only [CollatzResearch.WordTrace]
  refine ⟨24221343045867187605310351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129180496244625000561655205 24221343045867187605310351)
  ·
    refine ⟨36332014568800781407965527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24221343045867187605310351 36332014568800781407965527)
    ·
      refine ⟨54498021853201172111948291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36332014568800781407965527 54498021853201172111948291)
      ·
        refine ⟨81747032779801758167922437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54498021853201172111948291 81747032779801758167922437)
        ·
          refine ⟨15327568646212829656485457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81747032779801758167922437 15327568646212829656485457)
          ·
            refine ⟨11495676484659622242364093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15327568646212829656485457 11495676484659622242364093)
            ·
              refine ⟨4310878681747358340886535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11495676484659622242364093 4310878681747358340886535)
              ·
                refine ⟨6466318022621037511329803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4310878681747358340886535 6466318022621037511329803)
                ·
                  refine ⟨9699477033931556266994705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6466318022621037511329803 9699477033931556266994705)
                  ·
                    refine ⟨7274607775448667200246029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9699477033931556266994705 7274607775448667200246029)
                    ·
                      refine ⟨2727977915793250200092261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7274607775448667200246029 2727977915793250200092261)
                      ·
                        rfl

theorem cell23_5312718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_5312718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312718 prefixEnd_5312718 := by exact prefixLift 5312718
  have htrace : WordTrace (prefixWord ++ tailWord_5312718) baseStart_5312718 baseEnd_5312718 := by
    simpa [prefixWord, tailWord_5312718, baseEnd_5312718] using wordTrace_append hprefix tailTrace_5312718
  have hstable : (prefixWord ++ tailWord_5312718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312718).length < 2 ^ (prefixWord ++ tailWord_5312718).sum := by decide
  have hdescent : baseEnd_5312718 < baseStart_5312718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312737 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 4]
def baseStart_5312737 : Nat := 118140960795 + 5312737 * 2 ^ 59
def prefixEnd_5312737 : Nat := 4983230072969 + 3 ^ 40 * 5312737 * 2
def baseEnd_5312737 : Nat := 2727987671925685625754673

theorem tailTrace_5312737 : CollatzResearch.WordTrace tailWord_5312737 prefixEnd_5312737 2727987671925685625754673 := by
  unfold tailWord_5312737
  simp only [CollatzResearch.WordTrace]
  refine ⟨193771437353868667087424465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129180958235912444724949643 193771437353868667087424465)
  ·
    refine ⟨145328578015401500315568349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193771437353868667087424465 145328578015401500315568349)
    ·
      refine ⟨54498216755775562618338131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145328578015401500315568349 54498216755775562618338131)
      ·
        refine ⟨81747325133663343927507197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54498216755775562618338131 81747325133663343927507197)
        ·
          refine ⟨30655246925123753972815199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81747325133663343927507197 30655246925123753972815199)
          ·
            refine ⟨45982870387685630959222799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30655246925123753972815199 45982870387685630959222799)
            ·
              refine ⟨68974305581528446438834199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45982870387685630959222799 68974305581528446438834199)
              ·
                refine ⟨103461458372292669658251299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68974305581528446438834199 103461458372292669658251299)
                ·
                  refine ⟨155192187558439004487376949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103461458372292669658251299 155192187558439004487376949)
                  ·
                    refine ⟨14549267583603656670691589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 155192187558439004487376949 14549267583603656670691589)
                    ·
                      refine ⟨2727987671925685625754673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14549267583603656670691589 2727987671925685625754673)
                      ·
                        rfl

theorem cell23_5312737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_5312737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312737 prefixEnd_5312737 := by exact prefixLift 5312737
  have htrace : WordTrace (prefixWord ++ tailWord_5312737) baseStart_5312737 baseEnd_5312737 := by
    simpa [prefixWord, tailWord_5312737, baseEnd_5312737] using wordTrace_append hprefix tailTrace_5312737
  have hstable : (prefixWord ++ tailWord_5312737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312737).length < 2 ^ (prefixWord ++ tailWord_5312737).sum := by decide
  have hdescent : baseEnd_5312737 < baseStart_5312737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312741 : List Nat := [1, 3, 1, 4, 2, 1, 1, 2, 3, 3, 2]
def baseStart_5312741 : Nat := 118140960795 + 5312741 * 2 ^ 59
def prefixEnd_5312741 : Nat := 4983230072969 + 3 ^ 40 * 5312741 * 2
def baseEnd_5312741 : Nat := 2727989725848303610104655

theorem tailTrace_5312741 : CollatzResearch.WordTrace tailWord_5312741 prefixEnd_5312741 2727989725848303610104655 := by
  unfold tailWord_5312741
  simp only [CollatzResearch.WordTrace]
  refine ⟨193771583245854175770570077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129181055497236117180380051 193771583245854175770570077)
  ·
    refine ⟨72664343717195315913963779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193771583245854175770570077 72664343717195315913963779)
    ·
      refine ⟨108996515575792973870945669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72664343717195315913963779 108996515575792973870945669)
      ·
        refine ⟨20436846670461182600802313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108996515575792973870945669 20436846670461182600802313)
        ·
          refine ⟨15327635002845886950601735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20436846670461182600802313 15327635002845886950601735)
          ·
            refine ⟨22991452504268830425902603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15327635002845886950601735 22991452504268830425902603)
            ·
              refine ⟨34487178756403245638853905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22991452504268830425902603 34487178756403245638853905)
              ·
                refine ⟨25865384067302434229140429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34487178756403245638853905 25865384067302434229140429)
                ·
                  refine ⟨9699519025238412835927661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25865384067302434229140429 9699519025238412835927661)
                  ·
                    refine ⟨3637319634464404813472873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9699519025238412835927661 3637319634464404813472873)
                    ·
                      refine ⟨2727989725848303610104655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3637319634464404813472873 2727989725848303610104655)
                      ·
                        rfl

theorem cell23_5312741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_5312741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312741 prefixEnd_5312741 := by exact prefixLift 5312741
  have htrace : WordTrace (prefixWord ++ tailWord_5312741) baseStart_5312741 baseEnd_5312741 := by
    simpa [prefixWord, tailWord_5312741, baseEnd_5312741] using wordTrace_append hprefix tailTrace_5312741
  have hstable : (prefixWord ++ tailWord_5312741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312741).length < 2 ^ (prefixWord ++ tailWord_5312741).sum := by decide
  have hdescent : baseEnd_5312741 < baseStart_5312741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312747 : List Nat := [1, 1, 1, 1, 2, 5, 3, 1, 2, 6]
def baseStart_5312747 : Nat := 118140960795 + 5312747 * 2 ^ 59
def prefixEnd_5312747 : Nat := 4983230072969 + 3 ^ 40 * 5312747 * 2
def baseEnd_5312747 : Nat := 909330935577410195543209

theorem tailTrace_5312747 : CollatzResearch.WordTrace tailWord_5312747 prefixEnd_5312747 909330935577410195543209 := by
  unfold tailWord_5312747
  simp only [CollatzResearch.WordTrace]
  refine ⟨193771802083832438795288495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129181201389221625863525663 193771802083832438795288495)
  ·
    refine ⟨290657703125748658192932743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193771802083832438795288495 290657703125748658192932743)
    ·
      refine ⟨435986554688622987289399115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290657703125748658192932743 435986554688622987289399115)
      ·
        refine ⟨653979832032934480934098673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 435986554688622987289399115 653979832032934480934098673)
        ·
          refine ⟨490484874024700860700574005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 653979832032934480934098673 490484874024700860700574005)
          ·
            refine ⟨45982956939815705690678813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 490484874024700860700574005 45982956939815705690678813)
            ·
              refine ⟨17243608852430889634004555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45982956939815705690678813 17243608852430889634004555)
              ·
                refine ⟨25865413278646334451006833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17243608852430889634004555 25865413278646334451006833)
                ·
                  refine ⟨19399059958984750838255125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25865413278646334451006833 19399059958984750838255125)
                  ·
                    refine ⟨909330935577410195543209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19399059958984750838255125 909330935577410195543209)
                    ·
                      rfl

theorem cell23_5312747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 6].length) (baseStart_5312747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312747 prefixEnd_5312747 := by exact prefixLift 5312747
  have htrace : WordTrace (prefixWord ++ tailWord_5312747) baseStart_5312747 baseEnd_5312747 := by
    simpa [prefixWord, tailWord_5312747, baseEnd_5312747] using wordTrace_append hprefix tailTrace_5312747
  have hstable : (prefixWord ++ tailWord_5312747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312747).length < 2 ^ (prefixWord ++ tailWord_5312747).sum := by decide
  have hdescent : baseEnd_5312747 < baseStart_5312747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312767 : List Nat := [1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_5312767 : Nat := 118140960795 + 5312767 * 2 ^ 59
def prefixEnd_5312767 : Nat := 4983230072969 + 3 ^ 40 * 5312767 * 2
def baseEnd_5312767 : Nat := 2728003076345320508379535

theorem tailTrace_5312767 : CollatzResearch.WordTrace tailWord_5312767 prefixEnd_5312767 2728003076345320508379535 := by
  unfold tailWord_5312767
  simp only [CollatzResearch.WordTrace]
  refine ⟨193772531543759982211016555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129181687695839988140677703 193772531543759982211016555)
  ·
    refine ⟨290658797315639973316524833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193772531543759982211016555 290658797315639973316524833)
    ·
      refine ⟨217994097986729979987393625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290658797315639973316524833 217994097986729979987393625)
      ·
        refine ⟨163495573490047484990545219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 217994097986729979987393625 163495573490047484990545219)
        ·
          refine ⟨245243360235071227485817829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163495573490047484990545219 245243360235071227485817829)
          ·
            refine ⟨45983130044075855153590843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245243360235071227485817829 45983130044075855153590843)
            ·
              refine ⟨68974695066113782730386265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45983130044075855153590843 68974695066113782730386265)
              ·
                refine ⟨51731021299585337047789699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68974695066113782730386265 51731021299585337047789699)
                ·
                  refine ⟨77596531949378005571684549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51731021299585337047789699 77596531949378005571684549)
                  ·
                    refine ⟨14549349740508376044690853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 77596531949378005571684549 14549349740508376044690853)
                    ·
                      refine ⟨2728003076345320508379535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14549349740508376044690853 2728003076345320508379535)
                      ·
                        rfl

theorem cell23_5312767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_5312767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312767 prefixEnd_5312767 := by exact prefixLift 5312767
  have htrace : WordTrace (prefixWord ++ tailWord_5312767) baseStart_5312767 baseEnd_5312767 := by
    simpa [prefixWord, tailWord_5312767, baseEnd_5312767] using wordTrace_append hprefix tailTrace_5312767
  have hstable : (prefixWord ++ tailWord_5312767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312767).length < 2 ^ (prefixWord ++ tailWord_5312767).sum := by decide
  have hdescent : baseEnd_5312767 < baseStart_5312767 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312771 : List Nat := [1, 1, 1, 3, 2, 3, 2, 2, 4, 2, 2]
def baseStart_5312771 : Nat := 118140960795 + 5312771 * 2 ^ 59
def prefixEnd_5312771 : Nat := 4983230072969 + 3 ^ 40 * 5312771 * 2
def baseEnd_5312771 : Nat := 2728005130267938492729517

theorem tailTrace_5312771 : CollatzResearch.WordTrace tailWord_5312771 prefixEnd_5312771 2728005130267938492729517 := by
  unfold tailWord_5312771
  simp only [CollatzResearch.WordTrace]
  refine ⟨193772677435745490894162167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129181784957163660596108111 193772677435745490894162167)
  ·
    refine ⟨290659016153618236341243251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193772677435745490894162167 290659016153618236341243251)
    ·
      refine ⟨435988524230427354511864877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290659016153618236341243251 435988524230427354511864877)
      ·
        refine ⟨163495696586410257941949329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 435988524230427354511864877 163495696586410257941949329)
        ·
          refine ⟨122621772439807693456461997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163495696586410257941949329 122621772439807693456461997)
          ·
            refine ⟨45983164664927885046173249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122621772439807693456461997 45983164664927885046173249)
            ·
              refine ⟨34487373498695913784629937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45983164664927885046173249 34487373498695913784629937)
              ·
                refine ⟨25865530124021935338472453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34487373498695913784629937 25865530124021935338472453)
                ·
                  refine ⟨4849786898254112875963585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25865530124021935338472453 4849786898254112875963585)
                  ·
                    refine ⟨3637340173690584656972689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4849786898254112875963585 3637340173690584656972689)
                    ·
                      refine ⟨2728005130267938492729517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3637340173690584656972689 2728005130267938492729517)
                      ·
                        rfl

theorem cell23_5312771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 2, 4, 2, 2].length) (baseStart_5312771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312771 prefixEnd_5312771 := by exact prefixLift 5312771
  have htrace : WordTrace (prefixWord ++ tailWord_5312771) baseStart_5312771 baseEnd_5312771 := by
    simpa [prefixWord, tailWord_5312771, baseEnd_5312771] using wordTrace_append hprefix tailTrace_5312771
  have hstable : (prefixWord ++ tailWord_5312771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312771).length < 2 ^ (prefixWord ++ tailWord_5312771).sum := by decide
  have hdescent : baseEnd_5312771 < baseStart_5312771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312775 : List Nat := [1, 1, 4, 5, 1, 1, 1, 3, 1, 3, 2]
def baseStart_5312775 : Nat := 118140960795 + 5312775 * 2 ^ 59
def prefixEnd_5312775 : Nat := 4983230072969 + 3 ^ 40 * 5312775 * 2
def baseEnd_5312775 : Nat := 2728007184190556477079499

theorem tailTrace_5312775 : CollatzResearch.WordTrace tailWord_5312775 prefixEnd_5312775 2728007184190556477079499 := by
  unfold tailWord_5312775
  simp only [CollatzResearch.WordTrace]
  refine ⟨193772823327730999577307779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129181882218487333051538519 193772823327730999577307779)
  ·
    refine ⟨290659234991596499365961669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193772823327730999577307779 290659234991596499365961669)
    ·
      refine ⟨54498606560924343631117813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290659234991596499365961669 54498606560924343631117813)
      ·
        refine ⟨5109244365086657215417295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54498606560924343631117813 5109244365086657215417295)
        ·
          refine ⟨7663866547629985823125943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5109244365086657215417295 7663866547629985823125943)
          ·
            refine ⟨11495799821444978734688915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7663866547629985823125943 11495799821444978734688915)
            ·
              refine ⟨17243699732167468102033373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11495799821444978734688915 17243699732167468102033373)
              ·
                refine ⟨6466387399562800538262515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17243699732167468102033373 6466387399562800538262515)
                ·
                  refine ⟨9699581099344200807393773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6466387399562800538262515 9699581099344200807393773)
                  ·
                    refine ⟨3637342912254075302772665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9699581099344200807393773 3637342912254075302772665)
                    ·
                      refine ⟨2728007184190556477079499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3637342912254075302772665 2728007184190556477079499)
                      ·
                        rfl

theorem cell23_5312775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_5312775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312775 prefixEnd_5312775 := by exact prefixLift 5312775
  have htrace : WordTrace (prefixWord ++ tailWord_5312775) baseStart_5312775 baseEnd_5312775 := by
    simpa [prefixWord, tailWord_5312775, baseEnd_5312775] using wordTrace_append hprefix tailTrace_5312775
  have hstable : (prefixWord ++ tailWord_5312775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312775).length < 2 ^ (prefixWord ++ tailWord_5312775).sum := by decide
  have hdescent : baseEnd_5312775 < baseStart_5312775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312805 : List Nat := [1, 3, 1, 2, 6, 1, 1, 1, 1, 4, 2]
def baseStart_5312805 : Nat := 118140960795 + 5312805 * 2 ^ 59
def prefixEnd_5312805 : Nat := 4983230072969 + 3 ^ 40 * 5312805 * 2
def baseEnd_5312805 : Nat := 2728022588610191359704361

theorem tailTrace_5312805 : CollatzResearch.WordTrace tailWord_5312805 prefixEnd_5312805 2728022588610191359704361 := by
  unfold tailWord_5312805
  simp only [CollatzResearch.WordTrace]
  refine ⟨193773917517622314700899869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129182611678414876467266579 193773917517622314700899869)
  ·
    refine ⟨72665219069108368012837451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193773917517622314700899869 72665219069108368012837451)
    ·
      refine ⟨108997828603662552019256177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72665219069108368012837451 108997828603662552019256177)
      ·
        refine ⟨81748371452746914014442133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108997828603662552019256177 81748371452746914014442133)
        ·
          refine ⟨3831954911847511594426975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81748371452746914014442133 3831954911847511594426975)
          ·
            refine ⟨5747932367771267391640463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3831954911847511594426975 5747932367771267391640463)
            ·
              refine ⟨8621898551656901087460695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5747932367771267391640463 8621898551656901087460695)
              ·
                refine ⟨12932847827485351631191043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8621898551656901087460695 12932847827485351631191043)
                ·
                  refine ⟨19399271741228027446786565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12932847827485351631191043 19399271741228027446786565)
                  ·
                    refine ⟨3637363451480255146272481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19399271741228027446786565 3637363451480255146272481)
                    ·
                      refine ⟨2728022588610191359704361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3637363451480255146272481 2728022588610191359704361)
                      ·
                        rfl

theorem cell23_5312805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_5312805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312805 prefixEnd_5312805 := by exact prefixLift 5312805
  have htrace : WordTrace (prefixWord ++ tailWord_5312805) baseStart_5312805 baseEnd_5312805 := by
    simpa [prefixWord, tailWord_5312805, baseEnd_5312805] using wordTrace_append hprefix tailTrace_5312805
  have hstable : (prefixWord ++ tailWord_5312805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312805).length < 2 ^ (prefixWord ++ tailWord_5312805).sum := by decide
  have hdescent : baseEnd_5312805 < baseStart_5312805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312847 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_5312847 : Nat := 118140960795 + 5312847 * 2 ^ 59
def prefixEnd_5312847 : Nat := 4983230072969 + 3 ^ 40 * 5312847 * 2
def baseEnd_5312847 : Nat := 2728044154797680195379167

theorem tailTrace_5312847 : CollatzResearch.WordTrace tailWord_5312847 prefixEnd_5312847 2728044154797680195379167 := by
  unfold tailWord_5312847
  simp only [CollatzResearch.WordTrace]
  refine ⟨193775449383470155873928795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129183632922313437249285863 193775449383470155873928795)
  ·
    refine ⟨290663174075205233810893193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193775449383470155873928795 290663174075205233810893193)
    ·
      refine ⟨217997380556403925358169895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290663174075205233810893193 217997380556403925358169895)
      ·
        refine ⟨326996070834605888037254843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217997380556403925358169895 326996070834605888037254843)
        ·
          refine ⟨490494106251908832055882265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326996070834605888037254843 490494106251908832055882265)
          ·
            refine ⟨367870579688931624041911699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490494106251908832055882265 367870579688931624041911699)
            ·
              refine ⟨551805869533397436062867549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367870579688931624041911699 551805869533397436062867549)
              ·
                refine ⟨206927201075024038523575331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 551805869533397436062867549 206927201075024038523575331)
                ·
                  refine ⟨310390801612536057785362997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206927201075024038523575331 310390801612536057785362997)
                  ·
                    refine ⟨29099137651175255417377781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 310390801612536057785362997 29099137651175255417377781)
                    ·
                      refine ⟨2728044154797680195379167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29099137651175255417377781 2728044154797680195379167)
                      ·
                        rfl

theorem cell23_5312847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_5312847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312847 prefixEnd_5312847 := by exact prefixLift 5312847
  have htrace : WordTrace (prefixWord ++ tailWord_5312847) baseStart_5312847 baseEnd_5312847 := by
    simpa [prefixWord, tailWord_5312847, baseEnd_5312847] using wordTrace_append hprefix tailTrace_5312847
  have hstable : (prefixWord ++ tailWord_5312847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312847).length < 2 ^ (prefixWord ++ tailWord_5312847).sum := by decide
  have hdescent : baseEnd_5312847 < baseStart_5312847 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312904 : List Nat := [2, 1, 3, 3, 1, 1, 2, 1, 1, 2, 6]
def baseStart_5312904 : Nat := 118140960795 + 5312904 * 2 ^ 59
def prefixEnd_5312904 : Nat := 4983230072969 + 3 ^ 40 * 5312904 * 2
def baseEnd_5312904 : Nat := 2728073423194986472366405

theorem tailTrace_5312904 : CollatzResearch.WordTrace tailWord_5312904 prefixEnd_5312904 2728073423194986472366405 := by
  unfold tailWord_5312904
  simp only [CollatzResearch.WordTrace]
  refine ⟨96888764172131827304376883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129185018896175769739169177 96888764172131827304376883)
  ·
    refine ⟨145333146258197740956565325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96888764172131827304376883 145333146258197740956565325)
    ·
      refine ⟨54499929846824152858711997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145333146258197740956565325 54499929846824152858711997)
      ·
        refine ⟨20437473692559057322016999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54499929846824152858711997 20437473692559057322016999)
        ·
          refine ⟨30656210538838585983025499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20437473692559057322016999 30656210538838585983025499)
          ·
            refine ⟨45984315808257878974538249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30656210538838585983025499 45984315808257878974538249)
            ·
              refine ⟨34488236856193409230903687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45984315808257878974538249 34488236856193409230903687)
              ·
                refine ⟨51732355284290113846355531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34488236856193409230903687 51732355284290113846355531)
                ·
                  refine ⟨77598532926435170769533297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51732355284290113846355531 77598532926435170769533297)
                  ·
                    refine ⟨58198899694826378077149973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 77598532926435170769533297 58198899694826378077149973)
                    ·
                      refine ⟨2728073423194986472366405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58198899694826378077149973 2728073423194986472366405)
                      ·
                        rfl

theorem cell23_5312904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_5312904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312904 prefixEnd_5312904 := by exact prefixLift 5312904
  have htrace : WordTrace (prefixWord ++ tailWord_5312904) baseStart_5312904 baseEnd_5312904 := by
    simpa [prefixWord, tailWord_5312904, baseEnd_5312904] using wordTrace_append hprefix tailTrace_5312904
  have hstable : (prefixWord ++ tailWord_5312904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312904).length < 2 ^ (prefixWord ++ tailWord_5312904).sum := by decide
  have hdescent : baseEnd_5312904 < baseStart_5312904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312905 : List Nat := [1, 2, 1, 1, 6, 1, 4, 2, 1, 4]
def baseStart_5312905 : Nat := 118140960795 + 5312905 * 2 ^ 59
def prefixEnd_5312905 : Nat := 4983230072969 + 3 ^ 40 * 5312905 * 2
def baseEnd_5312905 : Nat := 909357978891880322817967

theorem tailTrace_5312905 : CollatzResearch.WordTrace tailWord_5312905 prefixEnd_5312905 909357978891880322817967 := by
  unfold tailWord_5312905
  simp only [CollatzResearch.WordTrace]
  refine ⟨193777564817260031779540169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129185043211506687853026779 193777564817260031779540169)
  ·
    refine ⟨145333173612945023834655127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193777564817260031779540169 145333173612945023834655127)
    ·
      refine ⟨217999760419417535751982691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145333173612945023834655127 217999760419417535751982691)
      ·
        refine ⟨326999640629126303627974037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217999760419417535751982691 326999640629126303627974037)
        ·
          refine ⟨15328108154490295482561283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 326999640629126303627974037 15328108154490295482561283)
          ·
            refine ⟨22992162231735443223841925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15328108154490295482561283 22992162231735443223841925)
            ·
              refine ⟨4311030418450395604470361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22992162231735443223841925 4311030418450395604470361)
              ·
                refine ⟨3233272813837796703352771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4311030418450395604470361 3233272813837796703352771)
                ·
                  refine ⟨4849909220756695055029157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233272813837796703352771 4849909220756695055029157)
                  ·
                    refine ⟨909357978891880322817967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4849909220756695055029157 909357978891880322817967)
                    ·
                      rfl

theorem cell23_5312905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 4, 2, 1, 4].length) (baseStart_5312905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312905 prefixEnd_5312905 := by exact prefixLift 5312905
  have htrace : WordTrace (prefixWord ++ tailWord_5312905) baseStart_5312905 baseEnd_5312905 := by
    simpa [prefixWord, tailWord_5312905, baseEnd_5312905] using wordTrace_append hprefix tailTrace_5312905
  have hstable : (prefixWord ++ tailWord_5312905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312905).length < 2 ^ (prefixWord ++ tailWord_5312905).sum := by decide
  have hdescent : baseEnd_5312905 < baseStart_5312905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312921 : List Nat := [1, 2, 1, 2, 1, 4, 2, 2, 1, 5, 2]
def baseStart_5312921 : Nat := 118140960795 + 5312921 * 2 ^ 59
def prefixEnd_5312921 : Nat := 4983230072969 + 3 ^ 40 * 5312921 * 2
def baseEnd_5312921 : Nat := 2728082152366112905853827

theorem tailTrace_5312921 : CollatzResearch.WordTrace tailWord_5312921 prefixEnd_5312921 2728082152366112905853827 := by
  unfold tailWord_5312921
  simp only [CollatzResearch.WordTrace]
  refine ⟨193778148385202066512122617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129185432256801377674748411 193778148385202066512122617)
  ·
    refine ⟨145333611288901549884091963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193778148385202066512122617 145333611288901549884091963)
    ·
      refine ⟨218000416933352324826137945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145333611288901549884091963 218000416933352324826137945)
      ·
        refine ⟨163500312700014243619603459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218000416933352324826137945 163500312700014243619603459)
        ·
          refine ⟨245250469050021365429405189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163500312700014243619603459 245250469050021365429405189)
          ·
            refine ⟨45984462946879006018013473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245250469050021365429405189 45984462946879006018013473)
            ·
              refine ⟨34488347210159254513510105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45984462946879006018013473 34488347210159254513510105)
              ·
                refine ⟨25866260407619440885132579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34488347210159254513510105 25866260407619440885132579)
                ·
                  refine ⟨38799390611429161327698869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25866260407619440885132579 38799390611429161327698869)
                  ·
                    refine ⟨3637442869821483874471769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38799390611429161327698869 3637442869821483874471769)
                    ·
                      refine ⟨2728082152366112905853827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3637442869821483874471769 2728082152366112905853827)
                      ·
                        rfl

theorem cell23_5312921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 5, 2].length) (baseStart_5312921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312921 prefixEnd_5312921 := by exact prefixLift 5312921
  have htrace : WordTrace (prefixWord ++ tailWord_5312921) baseStart_5312921 baseEnd_5312921 := by
    simpa [prefixWord, tailWord_5312921, baseEnd_5312921] using wordTrace_append hprefix tailTrace_5312921
  have hstable : (prefixWord ++ tailWord_5312921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312921).length < 2 ^ (prefixWord ++ tailWord_5312921).sum := by decide
  have hdescent : baseEnd_5312921 < baseStart_5312921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312928 : List Nat := [2, 1, 1, 4, 1, 4, 1, 2, 3, 1, 3]
def baseStart_5312928 : Nat := 118140960795 + 5312928 * 2 ^ 59
def prefixEnd_5312928 : Nat := 4983230072969 + 3 ^ 40 * 5312928 * 2
def baseEnd_5312928 : Nat := 2728085746730694378466295

theorem tailTrace_5312928 : CollatzResearch.WordTrace tailWord_5312928 prefixEnd_5312928 2728085746730694378466295 := by
  unfold tailWord_5312928
  simp only [CollatzResearch.WordTrace]
  refine ⟨96889201848088353353813719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129185602464117804471751625 96889201848088353353813719)
  ·
    refine ⟨145333802772132530030720579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96889201848088353353813719 145333802772132530030720579)
    ·
      refine ⟨218000704158198795046080869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145333802772132530030720579 218000704158198795046080869)
      ·
        refine ⟨40875132029662274071140163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218000704158198795046080869 40875132029662274071140163)
        ·
          refine ⟨61312698044493411106710245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40875132029662274071140163 61312698044493411106710245)
          ·
            refine ⟨11496130883342514582508171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61312698044493411106710245 11496130883342514582508171)
            ·
              refine ⟨17244196325013771873762257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11496130883342514582508171 17244196325013771873762257)
              ·
                refine ⟨12933147243760328905321693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17244196325013771873762257 12933147243760328905321693)
                ·
                  refine ⟨4849930216410123339495635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12933147243760328905321693 4849930216410123339495635)
                  ·
                    refine ⟨7274895324615185009243453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4849930216410123339495635 7274895324615185009243453)
                    ·
                      refine ⟨2728085746730694378466295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7274895324615185009243453 2728085746730694378466295)
                      ·
                        rfl

theorem cell23_5312928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 2, 3, 1, 3].length) (baseStart_5312928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312928 prefixEnd_5312928 := by exact prefixLift 5312928
  have htrace : WordTrace (prefixWord ++ tailWord_5312928) baseStart_5312928 baseEnd_5312928 := by
    simpa [prefixWord, tailWord_5312928, baseEnd_5312928] using wordTrace_append hprefix tailTrace_5312928
  have hstable : (prefixWord ++ tailWord_5312928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312928).length < 2 ^ (prefixWord ++ tailWord_5312928).sum := by decide
  have hdescent : baseEnd_5312928 < baseStart_5312928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312945 : List Nat := [1, 2, 2, 4, 1, 2, 1, 5, 1, 1, 3]
def baseStart_5312945 : Nat := 118140960795 + 5312945 * 2 ^ 59
def prefixEnd_5312945 : Nat := 4983230072969 + 3 ^ 40 * 5312945 * 2
def baseEnd_5312945 : Nat := 2728094475901820811953717

theorem tailTrace_5312945 : CollatzResearch.WordTrace tailWord_5312945 prefixEnd_5312945 2728094475901820811953717 := by
  unfold tailWord_5312945
  simp only [CollatzResearch.WordTrace]
  refine ⟨193779023737115118610996289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129186015824743412407330859 193779023737115118610996289)
  ·
    refine ⟨145334267802836338958247217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193779023737115118610996289 145334267802836338958247217)
    ·
      refine ⟨109000700852127254218685413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145334267802836338958247217 109000700852127254218685413)
      ·
        refine ⟨20437631409773860166003515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109000700852127254218685413 20437631409773860166003515)
        ·
          refine ⟨30656447114660790249005273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20437631409773860166003515 30656447114660790249005273)
          ·
            refine ⟨22992335335995592686753955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30656447114660790249005273 22992335335995592686753955)
            ·
              refine ⟨34488503003993389030130933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22992335335995592686753955 34488503003993389030130933)
              ·
                refine ⟨3233297156624380221574775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34488503003993389030130933 3233297156624380221574775)
                ·
                  refine ⟨4849945734936570332362163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233297156624380221574775 4849945734936570332362163)
                  ·
                    refine ⟨7274918602404855498543245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4849945734936570332362163 7274918602404855498543245)
                    ·
                      refine ⟨2728094475901820811953717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7274918602404855498543245 2728094475901820811953717)
                      ·
                        rfl

theorem cell23_5312945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_5312945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312945 prefixEnd_5312945 := by exact prefixLift 5312945
  have htrace : WordTrace (prefixWord ++ tailWord_5312945) baseStart_5312945 baseEnd_5312945 := by
    simpa [prefixWord, tailWord_5312945, baseEnd_5312945] using wordTrace_append hprefix tailTrace_5312945
  have hstable : (prefixWord ++ tailWord_5312945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312945).length < 2 ^ (prefixWord ++ tailWord_5312945).sum := by decide
  have hdescent : baseEnd_5312945 < baseStart_5312945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312954 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5]
def baseStart_5312954 : Nat := 118140960795 + 5312954 * 2 ^ 59
def prefixEnd_5312954 : Nat := 4983230072969 + 3 ^ 40 * 5312954 * 2
def baseEnd_5312954 : Nat := 2728099097227711276741175

theorem tailTrace_5312954 : CollatzResearch.WordTrace tailWord_5312954 prefixEnd_5312954 2728099097227711276741175 := by
  unfold tailWord_5312954
  simp only [CollatzResearch.WordTrace]
  refine ⟨48444837998520628287018479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129186234662721675432049277 48444837998520628287018479)
  ·
    refine ⟨72667256997780942430527719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48444837998520628287018479 72667256997780942430527719)
    ·
      refine ⟨109000885496671413645791579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72667256997780942430527719 109000885496671413645791579)
      ·
        refine ⟨163501328245007120468687369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109000885496671413645791579 163501328245007120468687369)
        ·
          refine ⟨122625996183755340351515527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163501328245007120468687369 122625996183755340351515527)
          ·
            refine ⟨183938994275633010527273291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122625996183755340351515527 183938994275633010527273291)
            ·
              refine ⟨275908491413449515790909937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183938994275633010527273291 275908491413449515790909937)
              ·
                refine ⟨206931368560087136843182453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 275908491413449515790909937 206931368560087136843182453)
                ·
                  refine ⟨19399815802508169079048355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 206931368560087136843182453 19399815802508169079048355)
                  ·
                    refine ⟨29099723703762253618572533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19399815802508169079048355 29099723703762253618572533)
                    ·
                      refine ⟨2728099097227711276741175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29099723703762253618572533 2728099097227711276741175)
                      ·
                        rfl

theorem cell23_5312954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5].length) (baseStart_5312954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312954 prefixEnd_5312954 := by exact prefixLift 5312954
  have htrace : WordTrace (prefixWord ++ tailWord_5312954) baseStart_5312954 baseEnd_5312954 := by
    simpa [prefixWord, tailWord_5312954, baseEnd_5312954] using wordTrace_append hprefix tailTrace_5312954
  have hstable : (prefixWord ++ tailWord_5312954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312954).length < 2 ^ (prefixWord ++ tailWord_5312954).sum := by decide
  have hdescent : baseEnd_5312954 < baseStart_5312954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312974 : List Nat := [4, 1, 1, 1, 2, 1, 1, 12]
def baseStart_5312974 : Nat := 118140960795 + 5312974 * 2 ^ 59
def prefixEnd_5312974 : Nat := 4983230072969 + 3 ^ 40 * 5312974 * 2
def baseEnd_5312974 : Nat := 101041087660770414758929

theorem tailTrace_5312974 : CollatzResearch.WordTrace tailWord_5312974 prefixEnd_5312974 101041087660770414758929 := by
  unfold tailWord_5312974
  simp only [CollatzResearch.WordTrace]
  refine ⟨24222510181751257070475247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129186720969340037709201317 24222510181751257070475247)
  ·
    refine ⟨36333765272626885605712871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24222510181751257070475247 36333765272626885605712871)
    ·
      refine ⟨54500647908940328408569307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36333765272626885605712871 54500647908940328408569307)
      ·
        refine ⟨81750971863410492612853961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54500647908940328408569307 81750971863410492612853961)
        ·
          refine ⟨61313228897557869459640471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81750971863410492612853961 61313228897557869459640471)
          ·
            refine ⟨91969843346336804189460707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61313228897557869459640471 91969843346336804189460707)
            ·
              refine ⟨137954765019505206284191061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91969843346336804189460707 137954765019505206284191061)
              ·
                refine ⟨101041087660770414758929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 137954765019505206284191061 101041087660770414758929)
                ·
                  rfl

theorem cell23_5312974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 12].length) (baseStart_5312974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312974 prefixEnd_5312974 := by exact prefixLift 5312974
  have htrace : WordTrace (prefixWord ++ tailWord_5312974) baseStart_5312974 baseEnd_5312974 := by
    simpa [prefixWord, tailWord_5312974, baseEnd_5312974] using wordTrace_append hprefix tailTrace_5312974
  have hstable : (prefixWord ++ tailWord_5312974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312974).length < 2 ^ (prefixWord ++ tailWord_5312974).sum := by decide
  have hdescent : baseEnd_5312974 < baseStart_5312974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312981 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 6]
def baseStart_5312981 : Nat := 118140960795 + 5312981 * 2 ^ 59
def prefixEnd_5312981 : Nat := 4983230072969 + 3 ^ 40 * 5312981 * 2
def baseEnd_5312981 : Nat := 2728112961205382671103551

theorem tailTrace_5312981 : CollatzResearch.WordTrace tailWord_5312981 prefixEnd_5312981 2728112961205382671103551 := by
  unfold tailWord_5312981
  simp only [CollatzResearch.WordTrace]
  refine ⟨193780336764984696759306797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129186891176656464506204531 193780336764984696759306797)
  ·
    refine ⟨72667626286869261284740049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193780336764984696759306797 72667626286869261284740049)
    ·
      refine ⟨54500719715151945963555037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72667626286869261284740049 54500719715151945963555037)
      ·
        refine ⟨20437769893181979736333139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54500719715151945963555037 20437769893181979736333139)
        ·
          refine ⟨30656654839772969604499709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20437769893181979736333139 30656654839772969604499709)
          ·
            refine ⟨11496245564914863601687391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30656654839772969604499709 11496245564914863601687391)
            ·
              refine ⟨17244368347372295402531087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11496245564914863601687391 17244368347372295402531087)
              ·
                refine ⟨25866552521058443103796631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17244368347372295402531087 25866552521058443103796631)
                ·
                  refine ⟨38799828781587664655694947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25866552521058443103796631 38799828781587664655694947)
                  ·
                    refine ⟨58199743172381496983542421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38799828781587664655694947 58199743172381496983542421)
                    ·
                      refine ⟨2728112961205382671103551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58199743172381496983542421 2728112961205382671103551)
                      ·
                        rfl

theorem cell23_5312981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_5312981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312981 prefixEnd_5312981 := by exact prefixLift 5312981
  have htrace : WordTrace (prefixWord ++ tailWord_5312981) baseStart_5312981 baseEnd_5312981 := by
    simpa [prefixWord, tailWord_5312981, baseEnd_5312981] using wordTrace_append hprefix tailTrace_5312981
  have hstable : (prefixWord ++ tailWord_5312981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312981).length < 2 ^ (prefixWord ++ tailWord_5312981).sum := by decide
  have hdescent : baseEnd_5312981 < baseStart_5312981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5312991 : List Nat := [1, 1, 2, 3, 3, 2, 4, 7]
def baseStart_5312991 : Nat := 118140960795 + 5312991 * 2 ^ 59
def prefixEnd_5312991 : Nat := 4983230072969 + 3 ^ 40 * 5312991 * 2
def baseEnd_5312991 : Nat := 101041410963404727110315

theorem tailTrace_5312991 : CollatzResearch.WordTrace tailWord_5312991 prefixEnd_5312991 101041410963404727110315 := by
  unfold tailWord_5312991
  simp only [CollatzResearch.WordTrace]
  refine ⟨193780701494948468467170827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129187134329965645644780551 193780701494948468467170827)
  ·
    refine ⟨290671052242422702700756241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193780701494948468467170827 290671052242422702700756241)
    ·
      refine ⟨218003289181817027025567181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290671052242422702700756241 218003289181817027025567181)
      ·
        refine ⟨81751233443181385134587693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218003289181817027025567181 81751233443181385134587693)
        ·
          refine ⟨30656712541193019425470385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81751233443181385134587693 30656712541193019425470385)
          ·
            refine ⟨22992534405894764569102789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30656712541193019425470385 22992534405894764569102789)
            ·
              refine ⟨4311100201105268356706773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22992534405894764569102789 4311100201105268356706773)
              ·
                refine ⟨101041410963404727110315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4311100201105268356706773 101041410963404727110315)
                ·
                  rfl

theorem cell23_5312991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 4, 7].length) (baseStart_5312991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5312991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5312991 prefixEnd_5312991 := by exact prefixLift 5312991
  have htrace : WordTrace (prefixWord ++ tailWord_5312991) baseStart_5312991 baseEnd_5312991 := by
    simpa [prefixWord, tailWord_5312991, baseEnd_5312991] using wordTrace_append hprefix tailTrace_5312991
  have hstable : (prefixWord ++ tailWord_5312991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5312991).length < 2 ^ (prefixWord ++ tailWord_5312991).sum := by decide
  have hdescent : baseEnd_5312991 < baseStart_5312991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5312991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313005 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 3]
def baseStart_5313005 : Nat := 118140960795 + 5313005 * 2 ^ 59
def prefixEnd_5313005 : Nat := 4983230072969 + 3 ^ 40 * 5313005 * 2
def baseEnd_5313005 : Nat := 2728125284741090577203441

theorem tailTrace_5313005 : CollatzResearch.WordTrace tailWord_5313005 prefixEnd_5313005 2728125284741090577203441 := by
  unfold tailWord_5313005
  simp only [CollatzResearch.WordTrace]
  refine ⟨193781212116897748858180469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129187474744598499238786979 193781212116897748858180469)
  ·
    refine ⟨18166988635959163955454419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193781212116897748858180469 18166988635959163955454419)
    ·
      refine ⟨27250482953938745933181629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18166988635959163955454419 27250482953938745933181629)
      ·
        refine ⟨10218931107727029724943111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27250482953938745933181629 10218931107727029724943111)
        ·
          refine ⟨15328396661590544587414667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10218931107727029724943111 15328396661590544587414667)
          ·
            refine ⟨22992594992385816881122001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15328396661590544587414667 22992594992385816881122001)
            ·
              refine ⟨17244446244289362660841501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22992594992385816881122001 17244446244289362660841501)
              ·
                refine ⟨6466667341608510997815563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17244446244289362660841501 6466667341608510997815563)
                ·
                  refine ⟨9700001012412766496723345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6466667341608510997815563 9700001012412766496723345)
                  ·
                    refine ⟨7275000759309574872542509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9700001012412766496723345 7275000759309574872542509)
                    ·
                      refine ⟨2728125284741090577203441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7275000759309574872542509 2728125284741090577203441)
                      ·
                        rfl

theorem cell23_5313005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_5313005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313005 prefixEnd_5313005 := by exact prefixLift 5313005
  have htrace : WordTrace (prefixWord ++ tailWord_5313005) baseStart_5313005 baseEnd_5313005 := by
    simpa [prefixWord, tailWord_5313005, baseEnd_5313005] using wordTrace_append hprefix tailTrace_5313005
  have hstable : (prefixWord ++ tailWord_5313005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313005).length < 2 ^ (prefixWord ++ tailWord_5313005).sum := by decide
  have hdescent : baseEnd_5313005 < baseStart_5313005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313035 : List Nat := [1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 3]
def baseStart_5313035 : Nat := 118140960795 + 5313035 * 2 ^ 59
def prefixEnd_5313035 : Nat := 4983230072969 + 3 ^ 40 * 5313035 * 2
def baseEnd_5313035 : Nat := 2728140689160725459828303

theorem tailTrace_5313035 : CollatzResearch.WordTrace tailWord_5313035 prefixEnd_5313035 2728140689160725459828303 := by
  unfold tailWord_5313035
  simp only [CollatzResearch.WordTrace]
  refine ⟨193782306306789063981772559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129188204204526042654515039 193782306306789063981772559)
  ·
    refine ⟨290673459460183595972658839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193782306306789063981772559 290673459460183595972658839)
    ·
      refine ⟨436010189190275393958988259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290673459460183595972658839 436010189190275393958988259)
      ·
        refine ⟨654015283785413090938482389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436010189190275393958988259 654015283785413090938482389)
        ·
          refine ⟨15328483213720619318870681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 654015283785413090938482389 15328483213720619318870681)
          ·
            refine ⟨11496362410290464489153011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15328483213720619318870681 11496362410290464489153011)
            ·
              refine ⟨17244543615435696733729517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11496362410290464489153011 17244543615435696733729517)
              ·
                refine ⟨6466703855788386275148569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17244543615435696733729517 6466703855788386275148569)
                ·
                  refine ⟨4850027891841289706361427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6466703855788386275148569 4850027891841289706361427)
                  ·
                    refine ⟨7275041837761934559542141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4850027891841289706361427 7275041837761934559542141)
                    ·
                      refine ⟨2728140689160725459828303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7275041837761934559542141 2728140689160725459828303)
                      ·
                        rfl

theorem cell23_5313035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 2, 1, 3].length) (baseStart_5313035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313035 prefixEnd_5313035 := by exact prefixLift 5313035
  have htrace : WordTrace (prefixWord ++ tailWord_5313035) baseStart_5313035 baseEnd_5313035 := by
    simpa [prefixWord, tailWord_5313035, baseEnd_5313035] using wordTrace_append hprefix tailTrace_5313035
  have hstable : (prefixWord ++ tailWord_5313035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313035).length < 2 ^ (prefixWord ++ tailWord_5313035).sum := by decide
  have hdescent : baseEnd_5313035 < baseStart_5313035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313061 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 5]
def baseStart_5313061 : Nat := 118140960795 + 5313061 * 2 ^ 59
def prefixEnd_5313061 : Nat := 4983230072969 + 3 ^ 40 * 5313061 * 2
def baseEnd_5313061 : Nat := 2728154039657742358103183

theorem tailTrace_5313061 : CollatzResearch.WordTrace tailWord_5313061 prefixEnd_5313061 2728154039657742358103183 := by
  unfold tailWord_5313061
  simp only [CollatzResearch.WordTrace]
  refine ⟨193783254604694870422219037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129188836403129913614812691 193783254604694870422219037)
  ·
    refine ⟨72668720476760576408332139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193783254604694870422219037 72668720476760576408332139)
    ·
      refine ⟨109003080715140864612498209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72668720476760576408332139 109003080715140864612498209)
      ·
        refine ⟨81752310536355648459373657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109003080715140864612498209 81752310536355648459373657)
        ·
          refine ⟨61314232902266736344530243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81752310536355648459373657 61314232902266736344530243)
          ·
            refine ⟨91971349353400104516795365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61314232902266736344530243 91971349353400104516795365)
            ·
              refine ⟨17244628003762519596899131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91971349353400104516795365 17244628003762519596899131)
              ·
                refine ⟨25866942005643779395348697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17244628003762519596899131 25866942005643779395348697)
                ·
                  refine ⟨19400206504232834546511523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25866942005643779395348697 19400206504232834546511523)
                  ·
                    refine ⟨29100309756349251819767285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19400206504232834546511523 29100309756349251819767285)
                    ·
                      refine ⟨2728154039657742358103183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29100309756349251819767285 2728154039657742358103183)
                      ·
                        rfl

theorem cell23_5313061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_5313061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313061 prefixEnd_5313061 := by exact prefixLift 5313061
  have htrace : WordTrace (prefixWord ++ tailWord_5313061) baseStart_5313061 baseEnd_5313061 := by
    simpa [prefixWord, tailWord_5313061, baseEnd_5313061] using wordTrace_append hprefix tailTrace_5313061
  have hstable : (prefixWord ++ tailWord_5313061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313061).length < 2 ^ (prefixWord ++ tailWord_5313061).sum := by decide
  have hdescent : baseEnd_5313061 < baseStart_5313061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313081 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 7]
def baseStart_5313081 : Nat := 118140960795 + 5313081 * 2 ^ 59
def prefixEnd_5313081 : Nat := 4983230072969 + 3 ^ 40 * 5313081 * 2
def baseEnd_5313081 : Nat := 303129367696759142205899

theorem tailTrace_5313081 : CollatzResearch.WordTrace tailWord_5313081 prefixEnd_5313081 303129367696759142205899 := by
  unfold tailWord_5313081
  simp only [CollatzResearch.WordTrace]
  refine ⟨193783984064622413837947097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129189322709748275891964731 193783984064622413837947097)
  ·
    refine ⟨145337988048466810378460323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193783984064622413837947097 145337988048466810378460323)
    ·
      refine ⟨218006982072700215567690485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145337988048466810378460323 218006982072700215567690485)
      ·
        refine ⟨20438154569315645209470983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 218006982072700215567690485 20438154569315645209470983)
        ·
          refine ⟨30657231853973467814206475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20438154569315645209470983 30657231853973467814206475)
          ·
            refine ⟨45985847780960201721309713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30657231853973467814206475 45985847780960201721309713)
            ·
              refine ⟨34489385835720151290982285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45985847780960201721309713 34489385835720151290982285)
              ·
                refine ⟨12933519688395056734118357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34489385835720151290982285 12933519688395056734118357)
                ·
                  refine ⟨303129367696759142205899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12933519688395056734118357 303129367696759142205899)
                  ·
                    rfl

theorem cell23_5313081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 7].length) (baseStart_5313081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313081 prefixEnd_5313081 := by exact prefixLift 5313081
  have htrace : WordTrace (prefixWord ++ tailWord_5313081) baseStart_5313081 baseEnd_5313081 := by
    simpa [prefixWord, tailWord_5313081, baseEnd_5313081] using wordTrace_append hprefix tailTrace_5313081
  have hstable : (prefixWord ++ tailWord_5313081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313081).length < 2 ^ (prefixWord ++ tailWord_5313081).sum := by decide
  have hdescent : baseEnd_5313081 < baseStart_5313081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313111 : List Nat := [1, 1, 3, 2, 2, 2, 3, 1, 1, 7]
def baseStart_5313111 : Nat := 118140960795 + 5313111 * 2 ^ 59
def prefixEnd_5313111 : Nat := 4983230072969 + 3 ^ 40 * 5313111 * 2
def baseEnd_5313111 : Nat := 909393237896822387492651

theorem tailTrace_5313111 : CollatzResearch.WordTrace tailWord_5313111 prefixEnd_5313111 909393237896822387492651 := by
  unfold tailWord_5313111
  simp only [CollatzResearch.WordTrace]
  refine ⟨193785078254513728961539187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129190052169675819307692791 193785078254513728961539187)
  ·
    refine ⟨290677617381770593442308781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193785078254513728961539187 290677617381770593442308781)
    ·
      refine ⟨109004106518163972540865793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290677617381770593442308781 109004106518163972540865793)
      ·
        refine ⟨81753079888622979405649345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109004106518163972540865793 81753079888622979405649345)
        ·
          refine ⟨61314809916467234554237009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81753079888622979405649345 61314809916467234554237009)
          ·
            refine ⟨45986107437350425915677757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61314809916467234554237009 45986107437350425915677757)
            ·
              refine ⟨17244790289006409718379159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45986107437350425915677757 17244790289006409718379159)
              ·
                refine ⟨25867185433509614577568739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17244790289006409718379159 25867185433509614577568739)
                ·
                  refine ⟨38800778150264421866353109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25867185433509614577568739 38800778150264421866353109)
                  ·
                    refine ⟨909393237896822387492651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38800778150264421866353109 909393237896822387492651)
                    ·
                      rfl

theorem cell23_5313111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_5313111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313111 prefixEnd_5313111 := by exact prefixLift 5313111
  have htrace : WordTrace (prefixWord ++ tailWord_5313111) baseStart_5313111 baseEnd_5313111 := by
    simpa [prefixWord, tailWord_5313111, baseEnd_5313111] using wordTrace_append hprefix tailTrace_5313111
  have hstable : (prefixWord ++ tailWord_5313111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313111).length < 2 ^ (prefixWord ++ tailWord_5313111).sum := by decide
  have hdescent : baseEnd_5313111 < baseStart_5313111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313161 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 4]
def baseStart_5313161 : Nat := 118140960795 + 5313161 * 2 ^ 59
def prefixEnd_5313161 : Nat := 4983230072969 + 3 ^ 40 * 5313161 * 2
def baseEnd_5313161 : Nat := 2728205387723191966852723

theorem tailTrace_5313161 : CollatzResearch.WordTrace tailWord_5313161 prefixEnd_5313161 2728205387723191966852723 := by
  unfold tailWord_5313161
  simp only [CollatzResearch.WordTrace]
  refine ⟨193786901904332587500859337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129191267936221725000572891 193786901904332587500859337)
  ·
    refine ⟨145340176428249440625644503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193786901904332587500859337 145340176428249440625644503)
    ·
      refine ⟨218010264642374160938466755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145340176428249440625644503 218010264642374160938466755)
      ·
        refine ⟨327015396963561241407700133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218010264642374160938466755 327015396963561241407700133)
        ·
          refine ⟨61315386930667732763943775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 327015396963561241407700133 61315386930667732763943775)
          ·
            refine ⟨91973080396001599145915663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61315386930667732763943775 91973080396001599145915663)
            ·
              refine ⟨137959620594002398718873495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91973080396001599145915663 137959620594002398718873495)
              ·
                refine ⟨206939430891003598078310243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137959620594002398718873495 206939430891003598078310243)
                ·
                  refine ⟨310409146336505397117465365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 206939430891003598078310243 310409146336505397117465365)
                  ·
                    refine ⟨14550428734523690489881189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 310409146336505397117465365 14550428734523690489881189)
                    ·
                      refine ⟨2728205387723191966852723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14550428734523690489881189 2728205387723191966852723)
                      ·
                        rfl

theorem cell23_5313161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 6, 4].length) (baseStart_5313161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313161 prefixEnd_5313161 := by exact prefixLift 5313161
  have htrace : WordTrace (prefixWord ++ tailWord_5313161) baseStart_5313161 baseEnd_5313161 := by
    simpa [prefixWord, tailWord_5313161, baseEnd_5313161] using wordTrace_append hprefix tailTrace_5313161
  have hstable : (prefixWord ++ tailWord_5313161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313161).length < 2 ^ (prefixWord ++ tailWord_5313161).sum := by decide
  have hdescent : baseEnd_5313161 < baseStart_5313161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313188 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 6]
def baseStart_5313188 : Nat := 118140960795 + 5313188 * 2 ^ 59
def prefixEnd_5313188 : Nat := 4983230072969 + 3 ^ 40 * 5313188 * 2
def baseEnd_5313188 : Nat := 303135472411207040135011

theorem tailTrace_5313188 : CollatzResearch.WordTrace tailWord_5313188 prefixEnd_5313188 303135472411207040135011 := by
  unfold tailWord_5313188
  simp only [CollatzResearch.WordTrace]
  refine ⟨96893943337617385556046109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129191924450156514074728145 96893943337617385556046109)
  ·
    refine ⟨36335228751606519583517291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96893943337617385556046109 36335228751606519583517291)
    ·
      refine ⟨54502843127409779375275937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36335228751606519583517291 54502843127409779375275937)
      ·
        refine ⟨40877132345557334531456953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54502843127409779375275937 40877132345557334531456953)
        ·
          refine ⟨30657849259168000898592715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40877132345557334531456953 30657849259168000898592715)
          ·
            refine ⟨45986773888752001347889073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30657849259168000898592715 45986773888752001347889073)
            ·
              refine ⟨34490080416564001010916805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45986773888752001347889073 34490080416564001010916805)
              ·
                refine ⟨6466890078105750189546901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34490080416564001010916805 6466890078105750189546901)
                ·
                  refine ⟨303135472411207040135011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6466890078105750189546901 303135472411207040135011)
                  ·
                    rfl

theorem cell23_5313188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_5313188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313188 prefixEnd_5313188 := by exact prefixLift 5313188
  have htrace : WordTrace (prefixWord ++ tailWord_5313188) baseStart_5313188 baseEnd_5313188 := by
    simpa [prefixWord, tailWord_5313188, baseEnd_5313188] using wordTrace_append hprefix tailTrace_5313188
  have hstable : (prefixWord ++ tailWord_5313188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313188).length < 2 ^ (prefixWord ++ tailWord_5313188).sum := by decide
  have hdescent : baseEnd_5313188 < baseStart_5313188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313205 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 6]
def baseStart_5313205 : Nat := 118140960795 + 5313205 * 2 ^ 59
def prefixEnd_5313205 : Nat := 4983230072969 + 3 ^ 40 * 5313205 * 2
def baseEnd_5313205 : Nat := 303136442319109977189169

theorem tailTrace_5313205 : CollatzResearch.WordTrace tailWord_5313205 prefixEnd_5313205 303136442319109977189169 := by
  unfold tailWord_5313205
  simp only [CollatzResearch.WordTrace]
  refine ⟨193788506716173183015461069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129192337810782122010307379 193788506716173183015461069)
  ·
    refine ⟨72670690018564943630797901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193788506716173183015461069 72670690018564943630797901)
    ·
      refine ⟨27251508756961853861549213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72670690018564943630797901 27251508756961853861549213)
      ·
        refine ⟨10219315783860695198080955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27251508756961853861549213 10219315783860695198080955)
        ·
          refine ⟨15328973675791042797121433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10219315783860695198080955 15328973675791042797121433)
          ·
            refine ⟨11496730256843282097841075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15328973675791042797121433 11496730256843282097841075)
            ·
              refine ⟨17245095385264923146761613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11496730256843282097841075 17245095385264923146761613)
              ·
                refine ⟨6466910769474346180035605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17245095385264923146761613 6466910769474346180035605)
                ·
                  refine ⟨303136442319109977189169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6466910769474346180035605 303136442319109977189169)
                  ·
                    rfl

theorem cell23_5313205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 6].length) (baseStart_5313205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313205 prefixEnd_5313205 := by exact prefixLift 5313205
  have htrace : WordTrace (prefixWord ++ tailWord_5313205) baseStart_5313205 baseEnd_5313205 := by
    simpa [prefixWord, tailWord_5313205, baseEnd_5313205] using wordTrace_append hprefix tailTrace_5313205
  have hstable : (prefixWord ++ tailWord_5313205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313205).length < 2 ^ (prefixWord ++ tailWord_5313205).sum := by decide
  have hdescent : baseEnd_5313205 < baseStart_5313205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313249 : List Nat := [1, 2, 3, 1, 4, 2, 1, 4, 1, 1, 3]
def baseStart_5313249 : Nat := 118140960795 + 5313249 * 2 ^ 59
def prefixEnd_5313249 : Nat := 4983230072969 + 3 ^ 40 * 5313249 * 2
def baseEnd_5313249 : Nat := 2728250574020787622552319

theorem tailTrace_5313249 : CollatzResearch.WordTrace tailWord_5313249 prefixEnd_5313249 2728250574020787622552319 := by
  unfold tailWord_5313249
  simp only [CollatzResearch.WordTrace]
  refine ⟨193790111528013778530062801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129193407685342519020041867 193790111528013778530062801)
  ·
    refine ⟨145342583646010333897547101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193790111528013778530062801 145342583646010333897547101)
    ·
      refine ⟨54503468867253875211580163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145342583646010333897547101 54503468867253875211580163)
      ·
        refine ⟨81755203300880812817370245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54503468867253875211580163 81755203300880812817370245)
        ·
          refine ⟨15329100618915152403256921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 81755203300880812817370245 15329100618915152403256921)
          ·
            refine ⟨11496825464186364302442691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15329100618915152403256921 11496825464186364302442691)
            ·
              refine ⟨17245238196279546453664037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11496825464186364302442691 17245238196279546453664037)
              ·
                refine ⟨3233482161802414960062007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17245238196279546453664037 3233482161802414960062007)
                ·
                  refine ⟨4850223242703622440093011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233482161802414960062007 4850223242703622440093011)
                  ·
                    refine ⟨7275334864055433660139517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4850223242703622440093011 7275334864055433660139517)
                    ·
                      refine ⟨2728250574020787622552319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7275334864055433660139517 2728250574020787622552319)
                      ·
                        rfl

theorem cell23_5313249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_5313249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313249 prefixEnd_5313249 := by exact prefixLift 5313249
  have htrace : WordTrace (prefixWord ++ tailWord_5313249) baseStart_5313249 baseEnd_5313249 := by
    simpa [prefixWord, tailWord_5313249, baseEnd_5313249] using wordTrace_append hprefix tailTrace_5313249
  have hstable : (prefixWord ++ tailWord_5313249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313249).length < 2 ^ (prefixWord ++ tailWord_5313249).sum := by decide
  have hdescent : baseEnd_5313249 < baseStart_5313249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313258 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_5313258 : Nat := 118140960795 + 5313258 * 2 ^ 59
def prefixEnd_5313258 : Nat := 4983230072969 + 3 ^ 40 * 5313258 * 2
def baseEnd_5313258 : Nat := 2728255195346678087339777

theorem tailTrace_5313258 : CollatzResearch.WordTrace tailWord_5313258 prefixEnd_5313258 2728255195346678087339777 := by
  unfold tailWord_5313258
  simp only [CollatzResearch.WordTrace]
  refine ⟨48447609946245293266785107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129193626523320782044760285 48447609946245293266785107)
  ·
    refine ⟨72671414919367939900177661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48447609946245293266785107 72671414919367939900177661)
    ·
      refine ⟨27251780594762977462566623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72671414919367939900177661 27251780594762977462566623)
      ·
        refine ⟨40877670892144466193849935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27251780594762977462566623 40877670892144466193849935)
        ·
          refine ⟨61316506338216699290774903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40877670892144466193849935 61316506338216699290774903)
          ·
            refine ⟨91974759507325048936162355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61316506338216699290774903 91974759507325048936162355)
            ·
              refine ⟨137962139260987573404243533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91974759507325048936162355 137962139260987573404243533)
              ·
                refine ⟨51735802222870340026591325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137962139260987573404243533 51735802222870340026591325)
                ·
                  refine ⟨19400925833576377509971747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51735802222870340026591325 19400925833576377509971747)
                  ·
                    refine ⟨29101388750364566264957621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19400925833576377509971747 29101388750364566264957621)
                    ·
                      refine ⟨2728255195346678087339777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29101388750364566264957621 2728255195346678087339777)
                      ·
                        rfl

theorem cell23_5313258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_5313258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313258 prefixEnd_5313258 := by exact prefixLift 5313258
  have htrace : WordTrace (prefixWord ++ tailWord_5313258) baseStart_5313258 baseEnd_5313258 := by
    simpa [prefixWord, tailWord_5313258, baseEnd_5313258] using wordTrace_append hprefix tailTrace_5313258
  have hstable : (prefixWord ++ tailWord_5313258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313258).length < 2 ^ (prefixWord ++ tailWord_5313258).sum := by decide
  have hdescent : baseEnd_5313258 < baseStart_5313258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313265 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 2, 4]
def baseStart_5313265 : Nat := 118140960795 + 5313265 * 2 ^ 59
def prefixEnd_5313265 : Nat := 4983230072969 + 3 ^ 40 * 5313265 * 2
def baseEnd_5313265 : Nat := 909419596570419853317415

theorem tailTrace_5313265 : CollatzResearch.WordTrace tailWord_5313265 prefixEnd_5313265 909419596570419853317415 := by
  unfold tailWord_5313265
  simp only [CollatzResearch.WordTrace]
  refine ⟨193790695095955813262645249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129193796730637208841763499 193790695095955813262645249)
  ·
    refine ⟨145343021321966859946983937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193790695095955813262645249 145343021321966859946983937)
    ·
      refine ⟨109007265991475144960237953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145343021321966859946983937 109007265991475144960237953)
      ·
        refine ⟨81755449493606358720178465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109007265991475144960237953 81755449493606358720178465)
        ·
          refine ⟨61316587120204769040133849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81755449493606358720178465 61316587120204769040133849)
          ·
            refine ⟨45987440340153576780100387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61316587120204769040133849 45987440340153576780100387)
            ·
              refine ⟨68981160510230365170150581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45987440340153576780100387 68981160510230365170150581)
              ·
                refine ⟨6466983797834096734701617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68981160510230365170150581 6466983797834096734701617)
                ·
                  refine ⟨4850237848375572551026213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6466983797834096734701617 4850237848375572551026213)
                  ·
                    refine ⟨909419596570419853317415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4850237848375572551026213 909419596570419853317415)
                    ·
                      rfl

theorem cell23_5313265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 2, 4].length) (baseStart_5313265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313265 prefixEnd_5313265 := by exact prefixLift 5313265
  have htrace : WordTrace (prefixWord ++ tailWord_5313265) baseStart_5313265 baseEnd_5313265 := by
    simpa [prefixWord, tailWord_5313265, baseEnd_5313265] using wordTrace_append hprefix tailTrace_5313265
  have hstable : (prefixWord ++ tailWord_5313265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313265).length < 2 ^ (prefixWord ++ tailWord_5313265).sum := by decide
  have hdescent : baseEnd_5313265 < baseStart_5313265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313272 : List Nat := [2, 1, 2, 1, 1, 2, 5, 2, 3, 2, 2]
def baseStart_5313272 : Nat := 118140960795 + 5313272 * 2 ^ 59
def prefixEnd_5313272 : Nat := 4983230072969 + 3 ^ 40 * 5313272 * 2
def baseEnd_5313272 : Nat := 2728262384075841032564713

theorem tailTrace_5313272 : CollatzResearch.WordTrace tailWord_5313272 prefixEnd_5313272 2728262384075841032564713 := by
  unfold tailWord_5313272
  simp only [CollatzResearch.WordTrace]
  refine ⟨96895475203465226729075035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129193966937953635638766713 96895475203465226729075035)
  ·
    refine ⟨145343212805197840093612553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96895475203465226729075035 145343212805197840093612553)
    ·
      refine ⟨109007409603898380070209415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145343212805197840093612553 109007409603898380070209415)
      ·
        refine ⟨163511114405847570105314123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109007409603898380070209415 163511114405847570105314123)
        ·
          refine ⟨245266671608771355157971185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163511114405847570105314123 245266671608771355157971185)
          ·
            refine ⟨183950003706578516368478389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245266671608771355157971185 183950003706578516368478389)
            ·
              refine ⟨17245312847491735909544849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 183950003706578516368478389 17245312847491735909544849)
              ·
                refine ⟨12933984635618801932158637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17245312847491735909544849 12933984635618801932158637)
                ·
                  refine ⟨4850244238357050724559489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12933984635618801932158637 4850244238357050724559489)
                  ·
                    refine ⟨3637683178767788043419617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4850244238357050724559489 3637683178767788043419617)
                    ·
                      refine ⟨2728262384075841032564713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3637683178767788043419617 2728262384075841032564713)
                      ·
                        rfl

theorem cell23_5313272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 2, 3, 2, 2].length) (baseStart_5313272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313272 prefixEnd_5313272 := by exact prefixLift 5313272
  have htrace : WordTrace (prefixWord ++ tailWord_5313272) baseStart_5313272 baseEnd_5313272 := by
    simpa [prefixWord, tailWord_5313272, baseEnd_5313272] using wordTrace_append hprefix tailTrace_5313272
  have hstable : (prefixWord ++ tailWord_5313272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313272).length < 2 ^ (prefixWord ++ tailWord_5313272).sum := by decide
  have hdescent : baseEnd_5313272 < baseStart_5313272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313289 : List Nat := [1, 2, 1, 1, 3, 2, 3, 5, 1, 2, 2]
def baseStart_5313289 : Nat := 118140960795 + 5313289 * 2 ^ 59
def prefixEnd_5313289 : Nat := 4983230072969 + 3 ^ 40 * 5313289 * 2
def baseEnd_5313289 : Nat := 2728271113246967466052135

theorem tailTrace_5313289 : CollatzResearch.WordTrace tailWord_5313289 prefixEnd_5313289 2728271113246967466052135 := by
  unfold tailWord_5313289
  simp only [CollatzResearch.WordTrace]
  refine ⟨193791570447868865361518921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129194380298579243574345947 193791570447868865361518921)
  ·
    refine ⟨145343677835901649021139191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193791570447868865361518921 145343677835901649021139191)
    ·
      refine ⟨218015516753852473531708787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145343677835901649021139191 218015516753852473531708787)
      ·
        refine ⟨327023275130778710297563181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218015516753852473531708787 327023275130778710297563181)
        ·
          refine ⟨122633728174042016361586193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327023275130778710297563181 122633728174042016361586193)
          ·
            refine ⟨91975296130531512271189645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122633728174042016361586193 91975296130531512271189645)
            ·
              refine ⟨34490736048949317101696117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91975296130531512271189645 34490736048949317101696117)
              ·
                refine ⟨3233506504588998478284011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34490736048949317101696117 3233506504588998478284011)
                ·
                  refine ⟨4850259756883497717426017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233506504588998478284011 4850259756883497717426017)
                  ·
                    refine ⟨3637694817662623288069513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4850259756883497717426017 3637694817662623288069513)
                    ·
                      refine ⟨2728271113246967466052135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3637694817662623288069513 2728271113246967466052135)
                      ·
                        rfl

theorem cell23_5313289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 5, 1, 2, 2].length) (baseStart_5313289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313289 prefixEnd_5313289 := by exact prefixLift 5313289
  have htrace : WordTrace (prefixWord ++ tailWord_5313289) baseStart_5313289 baseEnd_5313289 := by
    simpa [prefixWord, tailWord_5313289, baseEnd_5313289] using wordTrace_append hprefix tailTrace_5313289
  have hstable : (prefixWord ++ tailWord_5313289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313289).length < 2 ^ (prefixWord ++ tailWord_5313289).sum := by decide
  have hdescent : baseEnd_5313289 < baseStart_5313289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313328 : List Nat := [2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 4]
def baseStart_5313328 : Nat := 118140960795 + 5313328 * 2 ^ 59
def prefixEnd_5313328 : Nat := 4983230072969 + 3 ^ 40 * 5313328 * 2
def baseEnd_5313328 : Nat := 2728291138992492813464455

theorem tailTrace_5313328 : CollatzResearch.WordTrace tailWord_5313328 prefixEnd_5313328 2728291138992492813464455 := by
  unfold tailWord_5313328
  simp only [CollatzResearch.WordTrace]
  refine ⟨96896496447363787511094319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129195328596485050014792425 96896496447363787511094319)
  ·
    refine ⟨145344744671045681266641479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96896496447363787511094319 145344744671045681266641479)
    ·
      refine ⟨218017117006568521899962219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145344744671045681266641479 218017117006568521899962219)
      ·
        refine ⟨327025675509852782849943329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218017117006568521899962219 327025675509852782849943329)
        ·
          refine ⟨245269256632389587137457497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327025675509852782849943329 245269256632389587137457497)
          ·
            refine ⟨183951942474292190353093123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245269256632389587137457497 183951942474292190353093123)
            ·
              refine ⟨275927913711438285529639685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 183951942474292190353093123 275927913711438285529639685)
              ·
                refine ⟨51736483820894678536807441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 275927913711438285529639685 51736483820894678536807441)
                ·
                  refine ⟨38802362865671008902605581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51736483820894678536807441 38802362865671008902605581)
                  ·
                    refine ⟨14550886074626628338477093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38802362865671008902605581 14550886074626628338477093)
                    ·
                      refine ⟨2728291138992492813464455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14550886074626628338477093 2728291138992492813464455)
                      ·
                        rfl

theorem cell23_5313328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 4].length) (baseStart_5313328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313328 prefixEnd_5313328 := by exact prefixLift 5313328
  have htrace : WordTrace (prefixWord ++ tailWord_5313328) baseStart_5313328 baseEnd_5313328 := by
    simpa [prefixWord, tailWord_5313328, baseEnd_5313328] using wordTrace_append hprefix tailTrace_5313328
  have hstable : (prefixWord ++ tailWord_5313328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313328).length < 2 ^ (prefixWord ++ tailWord_5313328).sum := by decide
  have hdescent : baseEnd_5313328 < baseStart_5313328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313365 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 3]
def baseStart_5313365 : Nat := 118140960795 + 5313365 * 2 ^ 59
def prefixEnd_5313365 : Nat := 4983230072969 + 3 ^ 40 * 5313365 * 2
def baseEnd_5313365 : Nat := 2728310137776709168701785

theorem tailTrace_5313365 : CollatzResearch.WordTrace tailWord_5313365 prefixEnd_5313365 2728310137776709168701785 := by
  unfold tailWord_5313365
  simp only [CollatzResearch.WordTrace]
  refine ⟨193794342395593530341285549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129196228263729020227523699 193794342395593530341285549)
  ·
    refine ⟨72672878398347573877982081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193794342395593530341285549 72672878398347573877982081)
    ·
      refine ⟨54504658798760680408486561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72672878398347573877982081 54504658798760680408486561)
      ·
        refine ⟨40878494099070510306364921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54504658798760680408486561 40878494099070510306364921)
        ·
          refine ⟨30658870574302882729773691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40878494099070510306364921 30658870574302882729773691)
          ·
            refine ⟨45988305861454324094660537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30658870574302882729773691 45988305861454324094660537)
            ·
              refine ⟨34491229396090743070995403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45988305861454324094660537 34491229396090743070995403)
              ·
                refine ⟨51736844094136114606493105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34491229396090743070995403 51736844094136114606493105)
                ·
                  refine ⟨38802633070602085954869829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51736844094136114606493105 38802633070602085954869829)
                  ·
                    refine ⟨7275493700737891116538093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38802633070602085954869829 7275493700737891116538093)
                    ·
                      refine ⟨2728310137776709168701785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7275493700737891116538093 2728310137776709168701785)
                      ·
                        rfl

theorem cell23_5313365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_5313365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313365 prefixEnd_5313365 := by exact prefixLift 5313365
  have htrace : WordTrace (prefixWord ++ tailWord_5313365) baseStart_5313365 baseEnd_5313365 := by
    simpa [prefixWord, tailWord_5313365, baseEnd_5313365] using wordTrace_append hprefix tailTrace_5313365
  have hstable : (prefixWord ++ tailWord_5313365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313365).length < 2 ^ (prefixWord ++ tailWord_5313365).sum := by decide
  have hdescent : baseEnd_5313365 < baseStart_5313365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313430 : List Nat := [5, 3, 1, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_5313430 : Nat := 118140960795 + 5313430 * 2 ^ 59
def prefixEnd_5313430 : Nat := 4983230072969 + 3 ^ 40 * 5313430 * 2
def baseEnd_5313430 : Nat := 2728343514019251414388987

theorem tailTrace_5313430 : CollatzResearch.WordTrace tailWord_5313430 prefixEnd_5313430 2728343514019251414388987 := by
  unfold tailWord_5313430
  simp only [CollatzResearch.WordTrace]
  refine ⟨12112294571272377902650109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129197808760238697628267829 12112294571272377902650109)
  ·
    refine ⟨4542110464227141713493791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12112294571272377902650109 4542110464227141713493791)
    ·
      refine ⟨6813165696340712570240687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4542110464227141713493791 6813165696340712570240687)
      ·
        refine ⟨10219748544511068855361031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6813165696340712570240687 10219748544511068855361031)
        ·
          refine ⟨15329622816766603283041547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10219748544511068855361031 15329622816766603283041547)
          ·
            refine ⟨22994434225149904924562321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15329622816766603283041547 22994434225149904924562321)
            ·
              refine ⟨17245825668862428693421741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22994434225149904924562321 17245825668862428693421741)
              ·
                refine ⟨6467184625823410760033153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17245825668862428693421741 6467184625823410760033153)
                ·
                  refine ⟨4850388469367558070024865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6467184625823410760033153 4850388469367558070024865)
                  ·
                    refine ⟨3637791352025668552518649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4850388469367558070024865 3637791352025668552518649)
                    ·
                      refine ⟨2728343514019251414388987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3637791352025668552518649 2728343514019251414388987)
                      ·
                        rfl

theorem cell23_5313430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_5313430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313430 prefixEnd_5313430 := by exact prefixLift 5313430
  have htrace : WordTrace (prefixWord ++ tailWord_5313430) baseStart_5313430 baseEnd_5313430 := by
    simpa [prefixWord, tailWord_5313430, baseEnd_5313430] using wordTrace_append hprefix tailTrace_5313430
  have hstable : (prefixWord ++ tailWord_5313430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313430).length < 2 ^ (prefixWord ++ tailWord_5313430).sum := by decide
  have hdescent : baseEnd_5313430 < baseStart_5313430 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313465 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 6]
def baseStart_5313465 : Nat := 118140960795 + 5313465 * 2 ^ 59
def prefixEnd_5313465 : Nat := 4983230072969 + 3 ^ 40 * 5313465 * 2
def baseEnd_5313465 : Nat := 2728361485842158777451325

theorem tailTrace_5313465 : CollatzResearch.WordTrace tailWord_5313465 prefixEnd_5313465 2728361485842158777451325 := by
  unfold tailWord_5313465
  simp only [CollatzResearch.WordTrace]
  refine ⟨193797989695231247419925849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129198659796820831613283899 193797989695231247419925849)
  ·
    refine ⟨145348492271423435564944387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193797989695231247419925849 145348492271423435564944387)
    ·
      refine ⟨218022738407135153347416581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145348492271423435564944387 218022738407135153347416581)
      ·
        refine ⟨40879263451337841252640609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218022738407135153347416581 40879263451337841252640609)
        ·
          refine ⟨30659447588503380939480457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40879263451337841252640609 30659447588503380939480457)
          ·
            refine ⟨22994585691377535704610343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30659447588503380939480457 22994585691377535704610343)
            ·
              refine ⟨34491878537066303556915515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22994585691377535704610343 34491878537066303556915515)
              ·
                refine ⟨51737817805599455335373273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34491878537066303556915515 51737817805599455335373273)
                ·
                  refine ⟨38803363354199591501529955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51737817805599455335373273 38803363354199591501529955)
                  ·
                    refine ⟨58205045031299387252294933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38803363354199591501529955 58205045031299387252294933)
                    ·
                      refine ⟨2728361485842158777451325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58205045031299387252294933 2728361485842158777451325)
                      ·
                        rfl

theorem cell23_5313465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_5313465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313465 prefixEnd_5313465 := by exact prefixLift 5313465
  have htrace : WordTrace (prefixWord ++ tailWord_5313465) baseStart_5313465 baseEnd_5313465 := by
    simpa [prefixWord, tailWord_5313465, baseEnd_5313465] using wordTrace_append hprefix tailTrace_5313465
  have hstable : (prefixWord ++ tailWord_5313465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313465).length < 2 ^ (prefixWord ++ tailWord_5313465).sum := by decide
  have hdescent : baseEnd_5313465 < baseStart_5313465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313479 : List Nat := [1, 1, 4, 1, 1, 2, 4, 4, 1, 4]
def baseStart_5313479 : Nat := 118140960795 + 5313479 * 2 ^ 59
def prefixEnd_5313479 : Nat := 4983230072969 + 3 ^ 40 * 5313479 * 2
def baseEnd_5313479 : Nat := 909456224857107240892087

theorem tailTrace_5313479 : CollatzResearch.WordTrace tailWord_5313479 prefixEnd_5313479 909456224857107240892087 := by
  unfold tailWord_5313479
  simp only [CollatzResearch.WordTrace]
  refine ⟨193798500317180527810935491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129199000211453685207290327 193798500317180527810935491)
  ·
    refine ⟨290697750475770791716403237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193798500317180527810935491 290697750475770791716403237)
    ·
      refine ⟨54505828214207023446825607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290697750475770791716403237 54505828214207023446825607)
      ·
        refine ⟨81758742321310535170238411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54505828214207023446825607 81758742321310535170238411)
        ·
          refine ⟨122638113481965802755357617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81758742321310535170238411 122638113481965802755357617)
          ·
            refine ⟨91978585111474352066518213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122638113481965802755357617 91978585111474352066518213)
            ·
              refine ⟨17245984708401441012472165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91978585111474352066518213 17245984708401441012472165)
              ·
                refine ⟨3233622132825270189838531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17245984708401441012472165 3233622132825270189838531)
                ·
                  refine ⟨4850433199237905284757797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233622132825270189838531 4850433199237905284757797)
                  ·
                    refine ⟨909456224857107240892087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4850433199237905284757797 909456224857107240892087)
                    ·
                      rfl

theorem cell23_5313479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 4, 1, 4].length) (baseStart_5313479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313479 prefixEnd_5313479 := by exact prefixLift 5313479
  have htrace : WordTrace (prefixWord ++ tailWord_5313479) baseStart_5313479 baseEnd_5313479 := by
    simpa [prefixWord, tailWord_5313479, baseEnd_5313479] using wordTrace_append hprefix tailTrace_5313479
  have hstable : (prefixWord ++ tailWord_5313479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313479).length < 2 ^ (prefixWord ++ tailWord_5313479).sum := by decide
  have hdescent : baseEnd_5313479 < baseStart_5313479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313529 : List Nat := [1, 2, 1, 3, 1, 3, 3, 2, 2, 3, 2]
def baseStart_5313529 : Nat := 118140960795 + 5313529 * 2 ^ 59
def prefixEnd_5313529 : Nat := 4983230072969 + 3 ^ 40 * 5313529 * 2
def baseEnd_5313529 : Nat := 2728394348604046527051031

theorem tailTrace_5313529 : CollatzResearch.WordTrace tailWord_5313529 prefixEnd_5313529 2728394348604046527051031 := by
  unfold tailWord_5313529
  simp only [CollatzResearch.WordTrace]
  refine ⟨193800323966999386350255641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129200215977999590900170427 193800323966999386350255641)
  ·
    refine ⟨145350242975249539762691731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193800323966999386350255641 145350242975249539762691731)
    ·
      refine ⟨218025364462874309644037597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145350242975249539762691731 218025364462874309644037597)
      ·
        refine ⟨81759511673577866116514099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218025364462874309644037597 81759511673577866116514099)
        ·
          refine ⟨122639267510366799174771149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81759511673577866116514099 122639267510366799174771149)
          ·
            refine ⟨45989725316387549690539181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122639267510366799174771149 45989725316387549690539181)
            ·
              refine ⟨17246146993645331133952193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45989725316387549690539181 17246146993645331133952193)
              ·
                refine ⟨12934610245233998350464145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17246146993645331133952193 12934610245233998350464145)
                ·
                  refine ⟨9700957683925498762848109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12934610245233998350464145 9700957683925498762848109)
                  ·
                    refine ⟨3637859131472062036068041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9700957683925498762848109 3637859131472062036068041)
                    ·
                      refine ⟨2728394348604046527051031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3637859131472062036068041 2728394348604046527051031)
                      ·
                        rfl

theorem cell23_5313529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 2, 2, 3, 2].length) (baseStart_5313529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313529 prefixEnd_5313529 := by exact prefixLift 5313529
  have htrace : WordTrace (prefixWord ++ tailWord_5313529) baseStart_5313529 baseEnd_5313529 := by
    simpa [prefixWord, tailWord_5313529, baseEnd_5313529] using wordTrace_append hprefix tailTrace_5313529
  have hstable : (prefixWord ++ tailWord_5313529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313529).length < 2 ^ (prefixWord ++ tailWord_5313529).sum := by decide
  have hdescent : baseEnd_5313529 < baseStart_5313529 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313559 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 4]
def baseStart_5313559 : Nat := 118140960795 + 5313559 * 2 ^ 59
def prefixEnd_5313559 : Nat := 4983230072969 + 3 ^ 40 * 5313559 * 2
def baseEnd_5313559 : Nat := 2728409753023681409675893

theorem tailTrace_5313559 : CollatzResearch.WordTrace tailWord_5313559 prefixEnd_5313559 2728409753023681409675893 := by
  unfold tailWord_5313559
  simp only [CollatzResearch.WordTrace]
  refine ⟨193801418156890701473847731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129200945437927134315898487 193801418156890701473847731)
  ·
    refine ⟨290702127235336052210771597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193801418156890701473847731 290702127235336052210771597)
    ·
      refine ⟨109013297713251019579039349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290702127235336052210771597 109013297713251019579039349)
      ·
        refine ⟨10219996660617283085534939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109013297713251019579039349 10219996660617283085534939)
        ·
          refine ⟨15329994990925924628302409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10219996660617283085534939 15329994990925924628302409)
          ·
            refine ⟨11497496243194443471226807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15329994990925924628302409 11497496243194443471226807)
            ·
              refine ⟨17246244364791665206840211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11497496243194443471226807 17246244364791665206840211)
              ·
                refine ⟨25869366547187497810260317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17246244364791665206840211 25869366547187497810260317)
                ·
                  refine ⟨9701012455195311678847619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25869366547187497810260317 9701012455195311678847619)
                  ·
                    refine ⟨14551518682792967518271429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9701012455195311678847619 14551518682792967518271429)
                    ·
                      refine ⟨2728409753023681409675893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14551518682792967518271429 2728409753023681409675893)
                      ·
                        rfl

theorem cell23_5313559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_5313559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313559 prefixEnd_5313559 := by exact prefixLift 5313559
  have htrace : WordTrace (prefixWord ++ tailWord_5313559) baseStart_5313559 baseEnd_5313559 := by
    simpa [prefixWord, tailWord_5313559, baseEnd_5313559] using wordTrace_append hprefix tailTrace_5313559
  have hstable : (prefixWord ++ tailWord_5313559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313559).length < 2 ^ (prefixWord ++ tailWord_5313559).sum := by decide
  have hdescent : baseEnd_5313559 < baseStart_5313559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313606 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_5313606 : Nat := 118140960795 + 5313606 * 2 ^ 59
def prefixEnd_5313606 : Nat := 4983230072969 + 3 ^ 40 * 5313606 * 2
def baseEnd_5313606 : Nat := 2728433886614442725788177

theorem tailTrace_5313606 : CollatzResearch.WordTrace tailWord_5313606 prefixEnd_5313606 2728433886614442725788177 := by
  unfold tailWord_5313606
  simp only [CollatzResearch.WordTrace]
  refine ⟨6056347887116263390650271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129202088258480285667205781 6056347887116263390650271)
  ·
    refine ⟨9084521830674395085975407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6056347887116263390650271 9084521830674395085975407)
    ·
      refine ⟨13626782746011592628963111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9084521830674395085975407 13626782746011592628963111)
      ·
        refine ⟨20440174119017388943444667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13626782746011592628963111 20440174119017388943444667)
        ·
          refine ⟨30660261178526083415167001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20440174119017388943444667 30660261178526083415167001)
          ·
            refine ⟨22995195883894562561375251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30660261178526083415167001 22995195883894562561375251)
            ·
              refine ⟨34492793825841843842062877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22995195883894562561375251 34492793825841843842062877)
              ·
                refine ⟨12934797684690691440773579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34492793825841843842062877 12934797684690691440773579)
                ·
                  refine ⟨19402196527036037161160369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12934797684690691440773579 19402196527036037161160369)
                  ·
                    refine ⟨14551647395277027870870277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19402196527036037161160369 14551647395277027870870277)
                    ·
                      refine ⟨2728433886614442725788177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14551647395277027870870277 2728433886614442725788177)
                      ·
                        rfl

theorem cell23_5313606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_5313606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313606 prefixEnd_5313606 := by exact prefixLift 5313606
  have htrace : WordTrace (prefixWord ++ tailWord_5313606) baseStart_5313606 baseEnd_5313606 := by
    simpa [prefixWord, tailWord_5313606, baseEnd_5313606] using wordTrace_append hprefix tailTrace_5313606
  have hstable : (prefixWord ++ tailWord_5313606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313606).length < 2 ^ (prefixWord ++ tailWord_5313606).sum := by decide
  have hdescent : baseEnd_5313606 < baseStart_5313606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313615 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 10]
def baseStart_5313615 : Nat := 118140960795 + 5313615 * 2 ^ 59
def prefixEnd_5313615 : Nat := 4983230072969 + 3 ^ 40 * 5313615 * 2
def baseEnd_5313615 : Nat := 2728438507940333190575635

theorem tailTrace_5313615 : CollatzResearch.WordTrace tailWord_5313615 prefixEnd_5313615 2728438507940333190575635 := by
  unfold tailWord_5313615
  simp only [CollatzResearch.WordTrace]
  refine ⟨193803460644687823037886299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129202307096458548691924199 193803460644687823037886299)
  ·
    refine ⟨290705190967031734556829449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193803460644687823037886299 290705190967031734556829449)
    ·
      refine ⟨218028893225273800917622087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290705190967031734556829449 218028893225273800917622087)
      ·
        refine ⟨327043339837910701376433131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218028893225273800917622087 327043339837910701376433131)
        ·
          refine ⟨490565009756866052064649697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327043339837910701376433131 490565009756866052064649697)
          ·
            refine ⟨367923757317649539048487273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 490565009756866052064649697 367923757317649539048487273)
            ·
              refine ⟨275942817988237154286365455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367923757317649539048487273 275942817988237154286365455)
              ·
                refine ⟨413914226982355731429548183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275942817988237154286365455 413914226982355731429548183)
                ·
                  refine ⟨620871340473533597144322275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 413914226982355731429548183 620871340473533597144322275)
                  ·
                    refine ⟨931307010710300395716483413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 620871340473533597144322275 931307010710300395716483413)
                    ·
                      refine ⟨2728438507940333190575635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 931307010710300395716483413 2728438507940333190575635)
                      ·
                        rfl

theorem cell23_5313615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 1, 10].length) (baseStart_5313615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313615 prefixEnd_5313615 := by exact prefixLift 5313615
  have htrace : WordTrace (prefixWord ++ tailWord_5313615) baseStart_5313615 baseEnd_5313615 := by
    simpa [prefixWord, tailWord_5313615, baseEnd_5313615] using wordTrace_append hprefix tailTrace_5313615
  have hstable : (prefixWord ++ tailWord_5313615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313615).length < 2 ^ (prefixWord ++ tailWord_5313615).sum := by decide
  have hdescent : baseEnd_5313615 < baseStart_5313615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313630 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_5313630 : Nat := 118140960795 + 5313630 * 2 ^ 59
def prefixEnd_5313630 : Nat := 4983230072969 + 3 ^ 40 * 5313630 * 2
def baseEnd_5313630 : Nat := 2728446210150150631888067

theorem tailTrace_5313630 : CollatzResearch.WordTrace tailWord_5313630 prefixEnd_5313630 2728446210150150631888067 := by
  unfold tailWord_5313630
  simp only [CollatzResearch.WordTrace]
  refine ⟨24225500967454185074960293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129202671826422320399788229 24225500967454185074960293)
  ·
    refine ⟨4542281431397659701555055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24225500967454185074960293 4542281431397659701555055)
    ·
      refine ⟨6813422147096489552332583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4542281431397659701555055 6813422147096489552332583)
      ·
        refine ⟨10220133220644734328498875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6813422147096489552332583 10220133220644734328498875)
        ·
          refine ⟨15330199830967101492748313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220133220644734328498875 15330199830967101492748313)
          ·
            refine ⟨11497649873225326119561235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15330199830967101492748313 11497649873225326119561235)
            ·
              refine ⟨17246474809837989179341853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11497649873225326119561235 17246474809837989179341853)
              ·
                refine ⟨6467428053689245942253195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17246474809837989179341853 6467428053689245942253195)
                ·
                  refine ⟨9701142080533868913379793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6467428053689245942253195 9701142080533868913379793)
                  ·
                    refine ⟨7275856560400401685034845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9701142080533868913379793 7275856560400401685034845)
                    ·
                      refine ⟨2728446210150150631888067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7275856560400401685034845 2728446210150150631888067)
                      ·
                        rfl

theorem cell23_5313630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_5313630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313630 prefixEnd_5313630 := by exact prefixLift 5313630
  have htrace : WordTrace (prefixWord ++ tailWord_5313630) baseStart_5313630 baseEnd_5313630 := by
    simpa [prefixWord, tailWord_5313630, baseEnd_5313630] using wordTrace_append hprefix tailTrace_5313630
  have hstable : (prefixWord ++ tailWord_5313630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313630).length < 2 ^ (prefixWord ++ tailWord_5313630).sum := by decide
  have hdescent : baseEnd_5313630 < baseStart_5313630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313706 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 7]
def baseStart_5313706 : Nat := 118140960795 + 5313706 * 2 ^ 59
def prefixEnd_5313706 : Nat := 4983230072969 + 3 ^ 40 * 5313706 * 2
def baseEnd_5313706 : Nat := 303165026075543592726413

theorem tailTrace_5313706 : CollatzResearch.WordTrace tailWord_5313706 prefixEnd_5313706 303165026075543592726413 := by
  unfold tailWord_5313706
  simp only [CollatzResearch.WordTrace]
  refine ⟨48451694921839536394862243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129204519791572097052965981 48451694921839536394862243)
  ·
    refine ⟨72677542382759304592293365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48451694921839536394862243 72677542382759304592293365)
    ·
      refine ⟨6813519598383684805527503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72677542382759304592293365 6813519598383684805527503)
      ·
        refine ⟨10220279397575527208291255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6813519598383684805527503 10220279397575527208291255)
        ·
          refine ⟨15330419096363290812436883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220279397575527208291255 15330419096363290812436883)
          ·
            refine ⟨22995628644544936218655325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15330419096363290812436883 22995628644544936218655325)
            ·
              refine ⟨8623360741704351081995747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22995628644544936218655325 8623360741704351081995747)
              ·
                refine ⟨12935041112556526622993621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8623360741704351081995747 12935041112556526622993621)
                ·
                  refine ⟨303165026075543592726413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12935041112556526622993621 303165026075543592726413)
                  ·
                    rfl

theorem cell23_5313706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 7].length) (baseStart_5313706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313706 prefixEnd_5313706 := by exact prefixLift 5313706
  have htrace : WordTrace (prefixWord ++ tailWord_5313706) baseStart_5313706 baseEnd_5313706 := by
    simpa [prefixWord, tailWord_5313706, baseEnd_5313706] using wordTrace_append hprefix tailTrace_5313706
  have hstable : (prefixWord ++ tailWord_5313706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313706).length < 2 ^ (prefixWord ++ tailWord_5313706).sum := by decide
  have hdescent : baseEnd_5313706 < baseStart_5313706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313712 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 5]
def baseStart_5313712 : Nat := 118140960795 + 5313712 * 2 ^ 59
def prefixEnd_5313712 : Nat := 4983230072969 + 3 ^ 40 * 5313712 * 2
def baseEnd_5313712 : Nat := 2728488315563819311062689

theorem tailTrace_5313712 : CollatzResearch.WordTrace tailWord_5313712 prefixEnd_5313712 2728488315563819311062689 := by
  unfold tailWord_5313712
  simp only [CollatzResearch.WordTrace]
  refine ⟨96903499262668204302083695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129204665683557605736111593 96903499262668204302083695)
  ·
    refine ⟨145355248894002306453125543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96903499262668204302083695 145355248894002306453125543)
    ·
      refine ⟨218032873341003459679688315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145355248894002306453125543 218032873341003459679688315)
      ·
        refine ⟨327049310011505189519532473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218032873341003459679688315 327049310011505189519532473)
        ·
          refine ⟨245286982508628892139649355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327049310011505189519532473 245286982508628892139649355)
          ·
            refine ⟨367930473762943338209474033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245286982508628892139649355 367930473762943338209474033)
            ·
              refine ⟨275947855322207503657105525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367930473762943338209474033 275947855322207503657105525)
              ·
                refine ⟨25870111436456953467853643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275947855322207503657105525 25870111436456953467853643)
                ·
                  refine ⟨38805167154685430201780465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25870111436456953467853643 38805167154685430201780465)
                  ·
                    refine ⟨29103875366014072651335349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38805167154685430201780465 29103875366014072651335349)
                    ·
                      refine ⟨2728488315563819311062689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29103875366014072651335349 2728488315563819311062689)
                      ·
                        rfl

theorem cell23_5313712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 5].length) (baseStart_5313712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313712 prefixEnd_5313712 := by exact prefixLift 5313712
  have htrace : WordTrace (prefixWord ++ tailWord_5313712) baseStart_5313712 baseEnd_5313712 := by
    simpa [prefixWord, tailWord_5313712, baseEnd_5313712] using wordTrace_append hprefix tailTrace_5313712
  have hstable : (prefixWord ++ tailWord_5313712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313712).length < 2 ^ (prefixWord ++ tailWord_5313712).sum := by decide
  have hdescent : baseEnd_5313712 < baseStart_5313712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313739 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 3, 6, 2]
def baseStart_5313739 : Nat := 118140960795 + 5313739 * 2 ^ 59
def prefixEnd_5313739 : Nat := 4983230072969 + 3 ^ 40 * 5313739 * 2
def baseEnd_5313739 : Nat := 2728502179541490705425065

theorem tailTrace_5313739 : CollatzResearch.WordTrace tailWord_5313739 prefixEnd_5313739 2728502179541490705425065 := by
  unfold tailWord_5313739
  simp only [CollatzResearch.WordTrace]
  refine ⟨193807983296238592215400271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129205322197492394810266847 193807983296238592215400271)
  ·
    refine ⟨290711974944357888323100407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193807983296238592215400271 290711974944357888323100407)
    ·
      refine ⟨436067962416536832484650611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290711974944357888323100407 436067962416536832484650611)
      ·
        refine ⟨654101943624805248726975917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436067962416536832484650611 654101943624805248726975917)
        ·
          refine ⟨245288228859301968272615969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 654101943624805248726975917 245288228859301968272615969)
          ·
            refine ⟨183966171644476476204461977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245288228859301968272615969 183966171644476476204461977)
            ·
              refine ⟨137974628733357357153346483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183966171644476476204461977 137974628733357357153346483)
              ·
                refine ⟨206961943100036035730019725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137974628733357357153346483 206961943100036035730019725)
                ·
                  refine ⟨77610728662513513398757397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206961943100036035730019725 77610728662513513398757397)
                  ·
                    refine ⟨3638002906055320940566753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 77610728662513513398757397 3638002906055320940566753)
                    ·
                      refine ⟨2728502179541490705425065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638002906055320940566753 2728502179541490705425065)
                      ·
                        rfl

theorem cell23_5313739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 3, 6, 2].length) (baseStart_5313739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313739 prefixEnd_5313739 := by exact prefixLift 5313739
  have htrace : WordTrace (prefixWord ++ tailWord_5313739) baseStart_5313739 baseEnd_5313739 := by
    simpa [prefixWord, tailWord_5313739, baseEnd_5313739] using wordTrace_append hprefix tailTrace_5313739
  have hstable : (prefixWord ++ tailWord_5313739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313739).length < 2 ^ (prefixWord ++ tailWord_5313739).sum := by decide
  have hdescent : baseEnd_5313739 < baseStart_5313739 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313757 : List Nat := [1, 4, 3, 2, 3, 1, 2, 2, 5]
def baseStart_5313757 : Nat := 118140960795 + 5313757 * 2 ^ 59
def prefixEnd_5313757 : Nat := 4983230072969 + 3 ^ 40 * 5313757 * 2
def baseEnd_5313757 : Nat := 303167935799252403888887

theorem tailTrace_5313757 : CollatzResearch.WordTrace tailWord_5313757 prefixEnd_5313757 303167935799252403888887 := by
  unfold tailWord_5313757
  simp only [CollatzResearch.WordTrace]
  refine ⟨193808639810173381289555525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129205759873448920859703683 193808639810173381289555525)
  ·
    refine ⟨36339119964407508991791661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193808639810173381289555525 36339119964407508991791661)
    ·
      refine ⟨13627169986652815871921873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36339119964407508991791661 13627169986652815871921873)
      ·
        refine ⟨10220377489989611903941405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13627169986652815871921873 10220377489989611903941405)
        ·
          refine ⟨3832641558746104463978027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10220377489989611903941405 3832641558746104463978027)
          ·
            refine ⟨5748962338119156695967041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832641558746104463978027 5748962338119156695967041)
            ·
              refine ⟨4311721753589367521975281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5748962338119156695967041 4311721753589367521975281)
              ·
                refine ⟨3233791315192025641481461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4311721753589367521975281 3233791315192025641481461)
                ·
                  refine ⟨303167935799252403888887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3233791315192025641481461 303167935799252403888887)
                  ·
                    rfl

theorem cell23_5313757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 2, 2, 5].length) (baseStart_5313757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313757 prefixEnd_5313757 := by exact prefixLift 5313757
  have htrace : WordTrace (prefixWord ++ tailWord_5313757) baseStart_5313757 baseEnd_5313757 := by
    simpa [prefixWord, tailWord_5313757, baseEnd_5313757] using wordTrace_append hprefix tailTrace_5313757
  have hstable : (prefixWord ++ tailWord_5313757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313757).length < 2 ^ (prefixWord ++ tailWord_5313757).sum := by decide
  have hdescent : baseEnd_5313757 < baseStart_5313757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313773 : List Nat := [1, 5, 1, 2, 2, 2, 1, 1, 2, 4, 2]
def baseStart_5313773 : Nat := 118140960795 + 5313773 * 2 ^ 59
def prefixEnd_5313773 : Nat := 4983230072969 + 3 ^ 40 * 5313773 * 2
def baseEnd_5313773 : Nat := 2728519637883743572399909

theorem tailTrace_5313773 : CollatzResearch.WordTrace tailWord_5313773 prefixEnd_5313773 2728519637883743572399909 := by
  unfold tailWord_5313773
  simp only [CollatzResearch.WordTrace]
  refine ⟨193809223378115416022137973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129206148918743610681425315 193809223378115416022137973)
  ·
    refine ⟨18169614691698320252075435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193809223378115416022137973 18169614691698320252075435)
    ·
      refine ⟨27254422037547480378113153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18169614691698320252075435 27254422037547480378113153)
      ·
        refine ⟨20440816528160610283584865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27254422037547480378113153 20440816528160610283584865)
        ·
          refine ⟨15330612396120457712688649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20440816528160610283584865 15330612396120457712688649)
          ·
            refine ⟨11497959297090343284516487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15330612396120457712688649 11497959297090343284516487)
            ·
              refine ⟨17246938945635514926774731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11497959297090343284516487 17246938945635514926774731)
              ·
                refine ⟨25870408418453272390162097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17246938945635514926774731 25870408418453272390162097)
                ·
                  refine ⟨19402806313839954292621573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25870408418453272390162097 19402806313839954292621573)
                  ·
                    refine ⟨3638026183844991429866545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19402806313839954292621573 3638026183844991429866545)
                    ·
                      refine ⟨2728519637883743572399909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638026183844991429866545 2728519637883743572399909)
                      ·
                        rfl

theorem cell23_5313773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_5313773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313773 prefixEnd_5313773 := by exact prefixLift 5313773
  have htrace : WordTrace (prefixWord ++ tailWord_5313773) baseStart_5313773 baseEnd_5313773 := by
    simpa [prefixWord, tailWord_5313773, baseEnd_5313773] using wordTrace_append hprefix tailTrace_5313773
  have hstable : (prefixWord ++ tailWord_5313773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313773).length < 2 ^ (prefixWord ++ tailWord_5313773).sum := by decide
  have hdescent : baseEnd_5313773 < baseStart_5313773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313779 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 6]
def baseStart_5313779 : Nat := 118140960795 + 5313779 * 2 ^ 59
def prefixEnd_5313779 : Nat := 4983230072969 + 3 ^ 40 * 5313779 * 2
def baseEnd_5313779 : Nat := 303169190974185616547209

theorem tailTrace_5313779 : CollatzResearch.WordTrace tailWord_5313779 prefixEnd_5313779 303169190974185616547209 := by
  unfold tailWord_5313779
  simp only [CollatzResearch.WordTrace]
  refine ⟨193809442216093679046856391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129206294810729119364570927 193809442216093679046856391)
  ·
    refine ⟨290714163324140518570284587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193809442216093679046856391 290714163324140518570284587)
    ·
      refine ⟨436071244986210777855426881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290714163324140518570284587 436071244986210777855426881)
      ·
        refine ⟨327053433739658083391570161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436071244986210777855426881 327053433739658083391570161)
        ·
          refine ⟨245290075304743562543677621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327053433739658083391570161 245290075304743562543677621)
          ·
            refine ⟨22995944559819708988469777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 245290075304743562543677621 22995944559819708988469777)
            ·
              refine ⟨17246958419864781741352333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22995944559819708988469777 17246958419864781741352333)
              ·
                refine ⟨6467609407449293153007125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17246958419864781741352333 6467609407449293153007125)
                ·
                  refine ⟨303169190974185616547209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6467609407449293153007125 303169190974185616547209)
                  ·
                    rfl

theorem cell23_5313779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 6].length) (baseStart_5313779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313779 prefixEnd_5313779 := by exact prefixLift 5313779
  have htrace : WordTrace (prefixWord ++ tailWord_5313779) baseStart_5313779 baseEnd_5313779 := by
    simpa [prefixWord, tailWord_5313779, baseEnd_5313779] using wordTrace_append hprefix tailTrace_5313779
  have hstable : (prefixWord ++ tailWord_5313779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313779).length < 2 ^ (prefixWord ++ tailWord_5313779).sum := by decide
  have hdescent : baseEnd_5313779 < baseStart_5313779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313793 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_5313793 : Nat := 118140960795 + 5313793 * 2 ^ 59
def prefixEnd_5313793 : Nat := 4983230072969 + 3 ^ 40 * 5313793 * 2
def baseEnd_5313793 : Nat := 2728529907496833494149817

theorem tailTrace_5313793 : CollatzResearch.WordTrace tailWord_5313793 prefixEnd_5313793 2728529907496833494149817 := by
  unfold tailWord_5313793
  simp only [CollatzResearch.WordTrace]
  refine ⟨193809952838042959437866033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129206635225361972958577355 193809952838042959437866033)
  ·
    refine ⟨145357464628532219578399525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193809952838042959437866033 145357464628532219578399525)
    ·
      refine ⟨27254524617849791170949911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145357464628532219578399525 27254524617849791170949911)
      ·
        refine ⟨40881786926774686756424867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27254524617849791170949911 40881786926774686756424867)
        ·
          refine ⟨61322680390162030134637301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40881786926774686756424867 61322680390162030134637301)
          ·
            refine ⟨5749001286577690325122247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61322680390162030134637301 5749001286577690325122247)
            ·
              refine ⟨8623501929866535487683371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749001286577690325122247 8623501929866535487683371)
              ·
                refine ⟨12935252894799803231525057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8623501929866535487683371 12935252894799803231525057)
                ·
                  refine ⟨9701439671099852423643793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12935252894799803231525057 9701439671099852423643793)
                  ·
                    refine ⟨7276079753324889317732845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9701439671099852423643793 7276079753324889317732845)
                    ·
                      refine ⟨2728529907496833494149817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7276079753324889317732845 2728529907496833494149817)
                      ·
                        rfl

theorem cell23_5313793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_5313793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313793 prefixEnd_5313793 := by exact prefixLift 5313793
  have htrace : WordTrace (prefixWord ++ tailWord_5313793) baseStart_5313793 baseEnd_5313793 := by
    simpa [prefixWord, tailWord_5313793, baseEnd_5313793] using wordTrace_append hprefix tailTrace_5313793
  have hstable : (prefixWord ++ tailWord_5313793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313793).length < 2 ^ (prefixWord ++ tailWord_5313793).sum := by decide
  have hdescent : baseEnd_5313793 < baseStart_5313793 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313800 : List Nat := [2, 1, 3, 2, 4, 1, 2, 3, 1, 4]
def baseStart_5313800 : Nat := 118140960795 + 5313800 * 2 ^ 59
def prefixEnd_5313800 : Nat := 4983230072969 + 3 ^ 40 * 5313800 * 2
def baseEnd_5313800 : Nat := 909511167287138322254095

theorem tailTrace_5313800 : CollatzResearch.WordTrace tailWord_5313800 prefixEnd_5313800 909511167287138322254095 := by
  unfold tailWord_5313800
  simp only [CollatzResearch.WordTrace]
  refine ⟨96905104074508799816685427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129206805432678399755580569 96905104074508799816685427)
  ·
    refine ⟨145357656111763199725028141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96905104074508799816685427 145357656111763199725028141)
    ·
      refine ⟨54509121041911199896885553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145357656111763199725028141 54509121041911199896885553)
      ·
        refine ⟨40881840781433399922664165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54509121041911199896885553 40881840781433399922664165)
        ·
          refine ⟨7665345146518762485499531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40881840781433399922664165 7665345146518762485499531)
          ·
            refine ⟨11498017719778143728249297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7665345146518762485499531 11498017719778143728249297)
            ·
              refine ⟨8623513289833607796186973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11498017719778143728249297 8623513289833607796186973)
              ·
                refine ⟨3233817483687602923570115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8623513289833607796186973 3233817483687602923570115)
                ·
                  refine ⟨4850726225531404385355173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233817483687602923570115 4850726225531404385355173)
                  ·
                    refine ⟨909511167287138322254095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4850726225531404385355173 909511167287138322254095)
                    ·
                      rfl

theorem cell23_5313800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_5313800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313800 prefixEnd_5313800 := by exact prefixLift 5313800
  have htrace : WordTrace (prefixWord ++ tailWord_5313800) baseStart_5313800 baseEnd_5313800 := by
    simpa [prefixWord, tailWord_5313800, baseEnd_5313800] using wordTrace_append hprefix tailTrace_5313800
  have hstable : (prefixWord ++ tailWord_5313800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313800).length < 2 ^ (prefixWord ++ tailWord_5313800).sum := by decide
  have hdescent : baseEnd_5313800 < baseStart_5313800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313857 : List Nat := [1, 2, 5, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_5313857 : Nat := 118140960795 + 5313857 * 2 ^ 59
def prefixEnd_5313857 : Nat := 4983230072969 + 3 ^ 40 * 5313857 * 2
def baseEnd_5313857 : Nat := 2728562770258721243749523

theorem tailTrace_5313857 : CollatzResearch.WordTrace tailWord_5313857 prefixEnd_5313857 2728562770258721243749523 := by
  unfold tailWord_5313857
  simp only [CollatzResearch.WordTrace]
  refine ⟨193812287109811098368195825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129208191406540732245463883 193812287109811098368195825)
  ·
    refine ⟨145359215332358323776146869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193812287109811098368195825 145359215332358323776146869)
    ·
      refine ⟨13627426437408592854013769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145359215332358323776146869 13627426437408592854013769)
      ·
        refine ⟨10220569828056444640510327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13627426437408592854013769 10220569828056444640510327)
        ·
          refine ⟨15330854742084666960765491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220569828056444640510327 15330854742084666960765491)
          ·
            refine ⟨22996282113127000441148237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15330854742084666960765491 22996282113127000441148237)
            ·
              refine ⟨8623605792422625165430589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22996282113127000441148237 8623605792422625165430589)
              ·
                refine ⟨3233852172158484437036471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8623605792422625165430589 3233852172158484437036471)
                ·
                  refine ⟨4850778258237726655554707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3233852172158484437036471 4850778258237726655554707)
                  ·
                    refine ⟨7276167387356589983332061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4850778258237726655554707 7276167387356589983332061)
                    ·
                      refine ⟨2728562770258721243749523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7276167387356589983332061 2728562770258721243749523)
                      ·
                        rfl

theorem cell23_5313857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_5313857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313857 prefixEnd_5313857 := by exact prefixLift 5313857
  have htrace : WordTrace (prefixWord ++ tailWord_5313857) baseStart_5313857 baseEnd_5313857 := by
    simpa [prefixWord, tailWord_5313857, baseEnd_5313857] using wordTrace_append hprefix tailTrace_5313857
  have hstable : (prefixWord ++ tailWord_5313857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313857).length < 2 ^ (prefixWord ++ tailWord_5313857).sum := by decide
  have hdescent : baseEnd_5313857 < baseStart_5313857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313859 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 4]
def baseStart_5313859 : Nat := 118140960795 + 5313859 * 2 ^ 59
def prefixEnd_5313859 : Nat := 4983230072969 + 3 ^ 40 * 5313859 * 2
def baseEnd_5313859 : Nat := 2728563797220030235924513

theorem tailTrace_5313859 : CollatzResearch.WordTrace tailWord_5313859 prefixEnd_5313859 2728563797220030235924513 := by
  unfold tailWord_5313859
  simp only [CollatzResearch.WordTrace]
  refine ⟨193812360055803852709768631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129208240037202568473179087 193812360055803852709768631)
  ·
    refine ⟨290718540083705779064652947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193812360055803852709768631 290718540083705779064652947)
    ·
      refine ⟨436077810125558668596979421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290718540083705779064652947 436077810125558668596979421)
      ·
        refine ⟨163529178797084500723867283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436077810125558668596979421 163529178797084500723867283)
        ·
          refine ⟨245293768195626751085800925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163529178797084500723867283 245293768195626751085800925)
          ·
            refine ⟨91985163073360031657175347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245293768195626751085800925 91985163073360031657175347)
            ·
              refine ⟨137977744610040047485763021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91985163073360031657175347 137977744610040047485763021)
              ·
                refine ⟨51741654228765017807161133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 137977744610040047485763021 51741654228765017807161133)
                ·
                  refine ⟨19403120335786881677685425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51741654228765017807161133 19403120335786881677685425)
                  ·
                    refine ⟨14552340251840161258264069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19403120335786881677685425 14552340251840161258264069)
                    ·
                      refine ⟨2728563797220030235924513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14552340251840161258264069 2728563797220030235924513)
                      ·
                        rfl

theorem cell23_5313859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 3, 2, 4].length) (baseStart_5313859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313859 prefixEnd_5313859 := by exact prefixLift 5313859
  have htrace : WordTrace (prefixWord ++ tailWord_5313859) baseStart_5313859 baseEnd_5313859 := by
    simpa [prefixWord, tailWord_5313859, baseEnd_5313859] using wordTrace_append hprefix tailTrace_5313859
  have hstable : (prefixWord ++ tailWord_5313859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313859).length < 2 ^ (prefixWord ++ tailWord_5313859).sum := by decide
  have hdescent : baseEnd_5313859 < baseStart_5313859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313900 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 3]
def baseStart_5313900 : Nat := 118140960795 + 5313900 * 2 ^ 59
def prefixEnd_5313900 : Nat := 4983230072969 + 3 ^ 40 * 5313900 * 2
def baseEnd_5313900 : Nat := 2728584849926864575511825

theorem tailTrace_5313900 : CollatzResearch.WordTrace tailWord_5313900 prefixEnd_5313900 2728584849926864575511825 := by
  unfold tailWord_5313900
  simp only [CollatzResearch.WordTrace]
  refine ⟨96906927724327658356005577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129209236965770211141340769 96906927724327658356005577)
  ·
    refine ⟨72680195793245743767004183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 96906927724327658356005577 72680195793245743767004183)
    ·
      refine ⟨109020293689868615650506275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72680195793245743767004183 109020293689868615650506275)
      ·
        refine ⟨163530440534802923475759413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109020293689868615650506275 163530440534802923475759413)
        ·
          refine ⟨15330978800137774075852445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 163530440534802923475759413 15330978800137774075852445)
          ·
            refine ⟨5749117050051665278444667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15330978800137774075852445 5749117050051665278444667)
            ·
              refine ⟨8623675575077497917667001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749117050051665278444667 8623675575077497917667001)
              ·
                refine ⟨6467756681308123438250251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8623675575077497917667001 6467756681308123438250251)
                ·
                  refine ⟨9701635021962185157375377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6467756681308123438250251 9701635021962185157375377)
                  ·
                    refine ⟨7276226266471638868031533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9701635021962185157375377 7276226266471638868031533)
                    ·
                      refine ⟨2728584849926864575511825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7276226266471638868031533 2728584849926864575511825)
                      ·
                        rfl

theorem cell23_5313900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_5313900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313900 prefixEnd_5313900 := by exact prefixLift 5313900
  have htrace : WordTrace (prefixWord ++ tailWord_5313900) baseStart_5313900 baseEnd_5313900 := by
    simpa [prefixWord, tailWord_5313900, baseEnd_5313900] using wordTrace_append hprefix tailTrace_5313900
  have hstable : (prefixWord ++ tailWord_5313900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313900).length < 2 ^ (prefixWord ++ tailWord_5313900).sum := by decide
  have hdescent : baseEnd_5313900 < baseStart_5313900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313919 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 4]
def baseStart_5313919 : Nat := 118140960795 + 5313919 * 2 ^ 59
def prefixEnd_5313919 : Nat := 4983230072969 + 3 ^ 40 * 5313919 * 2
def baseEnd_5313919 : Nat := 2728594606059300001174237

theorem tailTrace_5313919 : CollatzResearch.WordTrace tailWord_5313919 prefixEnd_5313919 2728594606059300001174237 := by
  unfold tailWord_5313919
  simp only [CollatzResearch.WordTrace]
  refine ⟨193814548435586482956952811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129209698957057655304635207 193814548435586482956952811)
  ·
    refine ⟨290721822653379724435429217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193814548435586482956952811 290721822653379724435429217)
    ·
      refine ⟨218041366990034793326571913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290721822653379724435429217 218041366990034793326571913)
      ·
        refine ⟨163531025242526094994928935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218041366990034793326571913 163531025242526094994928935)
        ·
          refine ⟨245296537863789142492393403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163531025242526094994928935 245296537863789142492393403)
          ·
            refine ⟨367944806795683713738590105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245296537863789142492393403 367944806795683713738590105)
            ·
              refine ⟨275958605096762785303942579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367944806795683713738590105 275958605096762785303942579)
              ·
                refine ⟨413937907645144177955913869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275958605096762785303942579 413937907645144177955913869)
                ·
                  refine ⟨155226715366929066733467701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 413937907645144177955913869 155226715366929066733467701)
                  ·
                    refine ⟨14552504565649600006262597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 155226715366929066733467701 14552504565649600006262597)
                    ·
                      refine ⟨2728594606059300001174237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14552504565649600006262597 2728594606059300001174237)
                      ·
                        rfl

theorem cell23_5313919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_5313919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313919 prefixEnd_5313919 := by exact prefixLift 5313919
  have htrace : WordTrace (prefixWord ++ tailWord_5313919) baseStart_5313919 baseEnd_5313919 := by
    simpa [prefixWord, tailWord_5313919, baseEnd_5313919] using wordTrace_append hprefix tailTrace_5313919
  have hstable : (prefixWord ++ tailWord_5313919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313919).length < 2 ^ (prefixWord ++ tailWord_5313919).sum := by decide
  have hdescent : baseEnd_5313919 < baseStart_5313919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313936 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 1, 10, 2]
def baseStart_5313936 : Nat := 118140960795 + 5313936 * 2 ^ 59
def prefixEnd_5313936 : Nat := 4983230072969 + 3 ^ 40 * 5313936 * 2
def baseEnd_5313936 : Nat := 2728603335230426434661659

theorem tailTrace_5313936 : CollatzResearch.WordTrace tailWord_5313936 prefixEnd_5313936 2728603335230426434661659 := by
  unfold tailWord_5313936
  simp only [CollatzResearch.WordTrace]
  refine ⟨96907584238262447430160831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129210112317683263240214441 96907584238262447430160831)
  ·
    refine ⟨145361376357393671145241247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96907584238262447430160831 145361376357393671145241247)
    ·
      refine ⟨218042064536090506717861871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145361376357393671145241247 218042064536090506717861871)
      ·
        refine ⟨327063096804135760076792807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218042064536090506717861871 327063096804135760076792807)
        ·
          refine ⟨490594645206203640115189211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327063096804135760076792807 490594645206203640115189211)
          ·
            refine ⟨735891967809305460172783817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 490594645206203640115189211 735891967809305460172783817)
            ·
              refine ⟨551918975856979095129587863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735891967809305460172783817 551918975856979095129587863)
              ·
                refine ⟨827878463785468642694381795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551918975856979095129587863 827878463785468642694381795)
                ·
                  refine ⟨1241817695678202964041572693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827878463785468642694381795 1241817695678202964041572693)
                  ·
                    refine ⟨3638137780307235246215545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1241817695678202964041572693 3638137780307235246215545)
                    ·
                      refine ⟨2728603335230426434661659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638137780307235246215545 2728603335230426434661659)
                      ·
                        rfl

theorem cell23_5313936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 1, 10, 2].length) (baseStart_5313936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313936 prefixEnd_5313936 := by exact prefixLift 5313936
  have htrace : WordTrace (prefixWord ++ tailWord_5313936) baseStart_5313936 baseEnd_5313936 := by
    simpa [prefixWord, tailWord_5313936, baseEnd_5313936] using wordTrace_append hprefix tailTrace_5313936
  have hstable : (prefixWord ++ tailWord_5313936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313936).length < 2 ^ (prefixWord ++ tailWord_5313936).sum := by decide
  have hdescent : baseEnd_5313936 < baseStart_5313936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313940 : List Nat := [2, 4, 2, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_5313940 : Nat := 118140960795 + 5313940 * 2 ^ 59
def prefixEnd_5313940 : Nat := 4983230072969 + 3 ^ 40 * 5313940 * 2
def baseEnd_5313940 : Nat := 2728605389153044419011641

theorem tailTrace_5313940 : CollatzResearch.WordTrace tailWord_5313940 prefixEnd_5313940 2728605389153044419011641 := by
  unfold tailWord_5313940
  simp only [CollatzResearch.WordTrace]
  refine ⟨96907657184255201771733637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129210209579006935695644849 96907657184255201771733637)
  ·
    refine ⟨18170185722047850332200057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96907657184255201771733637 18170185722047850332200057)
    ·
      refine ⟨13627639291535887749150043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18170185722047850332200057 13627639291535887749150043)
      ·
        refine ⟨20441458937303831623725065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13627639291535887749150043 20441458937303831623725065)
        ·
          refine ⟨15331094202977873717793799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20441458937303831623725065 15331094202977873717793799)
          ·
            refine ⟨22996641304466810576690699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15331094202977873717793799 22996641304466810576690699)
            ·
              refine ⟨34494961956700215865036049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22996641304466810576690699 34494961956700215865036049)
              ·
                refine ⟨25871221467525161898777037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34494961956700215865036049 25871221467525161898777037)
                ·
                  refine ⟨9701708050321935712041389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25871221467525161898777037 9701708050321935712041389)
                  ·
                    refine ⟨3638140518870725892015521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9701708050321935712041389 3638140518870725892015521)
                    ·
                      refine ⟨2728605389153044419011641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638140518870725892015521 2728605389153044419011641)
                      ·
                        rfl

theorem cell23_5313940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_5313940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313940 prefixEnd_5313940 := by exact prefixLift 5313940
  have htrace : WordTrace (prefixWord ++ tailWord_5313940) baseStart_5313940 baseEnd_5313940 := by
    simpa [prefixWord, tailWord_5313940, baseEnd_5313940] using wordTrace_append hprefix tailTrace_5313940
  have hstable : (prefixWord ++ tailWord_5313940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313940).length < 2 ^ (prefixWord ++ tailWord_5313940).sum := by decide
  have hdescent : baseEnd_5313940 < baseStart_5313940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313946 : List Nat := [3, 1, 1, 4, 1, 1, 3, 1, 2, 6]
def baseStart_5313946 : Nat := 118140960795 + 5313946 * 2 ^ 59
def prefixEnd_5313946 : Nat := 4983230072969 + 3 ^ 40 * 5313946 * 2
def baseEnd_5313946 : Nat := 909536156678990465178871

theorem tailTrace_5313946 : CollatzResearch.WordTrace tailWord_5313946 prefixEnd_5313946 909536156678990465178871 := by
  unfold tailWord_5313946
  simp only [CollatzResearch.WordTrace]
  refine ⟨48453883301622166642046423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129210355470992444378790461 48453883301622166642046423)
  ·
    refine ⟨72680824952433249963069635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48453883301622166642046423 72680824952433249963069635)
    ·
      refine ⟨109021237428649874944604453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72680824952433249963069635 109021237428649874944604453)
      ·
        refine ⟨20441482017871851552113335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109021237428649874944604453 20441482017871851552113335)
        ·
          refine ⟨30662223026807777328170003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20441482017871851552113335 30662223026807777328170003)
          ·
            refine ⟨45993334540211665992255005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30662223026807777328170003 45993334540211665992255005)
            ·
              refine ⟨17247500452579374747095627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45993334540211665992255005 17247500452579374747095627)
              ·
                refine ⟨25871250678869062120643441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17247500452579374747095627 25871250678869062120643441)
                ·
                  refine ⟨19403438009151796590482581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25871250678869062120643441 19403438009151796590482581)
                  ·
                    refine ⟨909536156678990465178871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19403438009151796590482581 909536156678990465178871)
                    ·
                      rfl

theorem cell23_5313946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_5313946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313946 prefixEnd_5313946 := by exact prefixLift 5313946
  have htrace : WordTrace (prefixWord ++ tailWord_5313946) baseStart_5313946 baseEnd_5313946 := by
    simpa [prefixWord, tailWord_5313946, baseEnd_5313946] using wordTrace_append hprefix tailTrace_5313946
  have hstable : (prefixWord ++ tailWord_5313946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313946).length < 2 ^ (prefixWord ++ tailWord_5313946).sum := by decide
  have hdescent : baseEnd_5313946 < baseStart_5313946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313956 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_5313956 : Nat := 118140960795 + 5313956 * 2 ^ 59
def prefixEnd_5313956 : Nat := 4983230072969 + 3 ^ 40 * 5313956 * 2
def baseEnd_5313956 : Nat := 2728613604843516356411567

theorem tailTrace_5313956 : CollatzResearch.WordTrace tailWord_5313956 prefixEnd_5313956 2728613604843516356411567 := by
  unfold tailWord_5313956
  simp only [CollatzResearch.WordTrace]
  refine ⟨96907948968226219138024861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129210598624301625517366481 96907948968226219138024861)
  ·
    refine ⟨36340480863084832176759323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96907948968226219138024861 36340480863084832176759323)
    ·
      refine ⟨54510721294627248265138985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36340480863084832176759323 54510721294627248265138985)
      ·
        refine ⟨40883040970970436198854239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54510721294627248265138985 40883040970970436198854239)
        ·
          refine ⟨61324561456455654298281359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40883040970970436198854239 61324561456455654298281359)
          ·
            refine ⟨91986842184683481447422039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61324561456455654298281359 91986842184683481447422039)
            ·
              refine ⟨137980263277025222171133059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91986842184683481447422039 137980263277025222171133059)
              ·
                refine ⟨206970394915537833256699589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 137980263277025222171133059 206970394915537833256699589)
                ·
                  refine ⟨38806949046663343735631173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 206970394915537833256699589 38806949046663343735631173)
                  ·
                    refine ⟨7276302946249376950430845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 38806949046663343735631173 7276302946249376950430845)
                    ·
                      refine ⟨2728613604843516356411567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7276302946249376950430845 2728613604843516356411567)
                      ·
                        rfl

theorem cell23_5313956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_5313956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313956 prefixEnd_5313956 := by exact prefixLift 5313956
  have htrace : WordTrace (prefixWord ++ tailWord_5313956) baseStart_5313956 baseEnd_5313956 := by
    simpa [prefixWord, tailWord_5313956, baseEnd_5313956] using wordTrace_append hprefix tailTrace_5313956
  have hstable : (prefixWord ++ tailWord_5313956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313956).length < 2 ^ (prefixWord ++ tailWord_5313956).sum := by decide
  have hdescent : baseEnd_5313956 < baseStart_5313956 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5313979 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 6]
def baseStart_5313979 : Nat := 118140960795 + 5313979 * 2 ^ 59
def prefixEnd_5313979 : Nat := 4983230072969 + 3 ^ 40 * 5313979 * 2
def baseEnd_5313979 : Nat := 2728625414898569766423961

theorem tailTrace_5313979 : CollatzResearch.WordTrace tailWord_5313979 prefixEnd_5313979 2728625414898569766423961 := by
  unfold tailWord_5313979
  simp only [CollatzResearch.WordTrace]
  refine ⟨193816736815369113204136991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129211157876912742136091327 193816736815369113204136991)
  ·
    refine ⟨290725105223053669806205487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193816736815369113204136991 290725105223053669806205487)
    ·
      refine ⟨436087657834580504709308231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290725105223053669806205487 436087657834580504709308231)
      ·
        refine ⟨654131486751870757063962347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436087657834580504709308231 654131486751870757063962347)
        ·
          refine ⟨981197230127806135595943521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654131486751870757063962347 981197230127806135595943521)
          ·
            refine ⟨735897922595854601696957641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 981197230127806135595943521 735897922595854601696957641)
            ·
              refine ⟨551923441946890951272718231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 735897922595854601696957641 551923441946890951272718231)
              ·
                refine ⟨827885162920336426909077347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551923441946890951272718231 827885162920336426909077347)
                ·
                  refine ⟨1241827744380504640363616021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 827885162920336426909077347 1241827744380504640363616021)
                  ·
                    refine ⟨58210675517836155017044501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1241827744380504640363616021 58210675517836155017044501)
                    ·
                      refine ⟨2728625414898569766423961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58210675517836155017044501 2728625414898569766423961)
                      ·
                        rfl

theorem cell23_5313979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 6, 6].length) (baseStart_5313979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5313979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5313979 prefixEnd_5313979 := by exact prefixLift 5313979
  have htrace : WordTrace (prefixWord ++ tailWord_5313979) baseStart_5313979 baseEnd_5313979 := by
    simpa [prefixWord, tailWord_5313979, baseEnd_5313979] using wordTrace_append hprefix tailTrace_5313979
  have hstable : (prefixWord ++ tailWord_5313979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5313979).length < 2 ^ (prefixWord ++ tailWord_5313979).sum := by decide
  have hdescent : baseEnd_5313979 < baseStart_5313979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5313979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314004 : List Nat := [2, 4, 1, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_5314004 : Nat := 118140960795 + 5314004 * 2 ^ 59
def prefixEnd_5314004 : Nat := 4983230072969 + 3 ^ 40 * 5314004 * 2
def baseEnd_5314004 : Nat := 2728638251914932168611347

theorem tailTrace_5314004 : CollatzResearch.WordTrace tailWord_5314004 prefixEnd_5314004 2728638251914932168611347 := by
  unfold tailWord_5314004
  simp only [CollatzResearch.WordTrace]
  refine ⟨96908824320139271236898533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129211765760185694982531377 96908824320139271236898533)
  ·
    refine ⟨18170404560026113356918475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 96908824320139271236898533 18170404560026113356918475)
    ·
      refine ⟨27255606840039170035377713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18170404560026113356918475 27255606840039170035377713)
      ·
        refine ⟨20441705130029377526533285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27255606840039170035377713 20441705130029377526533285)
        ·
          refine ⟨3832819711880508286224991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20441705130029377526533285 3832819711880508286224991)
          ·
            refine ⟨5749229567820762429337487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832819711880508286224991 5749229567820762429337487)
            ·
              refine ⟨8623844351731143644006231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749229567820762429337487 8623844351731143644006231)
              ·
                refine ⟨12935766527596715466009347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8623844351731143644006231 12935766527596715466009347)
                ·
                  refine ⟨19403649791395073199014021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12935766527596715466009347 19403649791395073199014021)
                  ·
                    refine ⟨3638184335886576224815129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19403649791395073199014021 3638184335886576224815129)
                    ·
                      refine ⟨2728638251914932168611347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638184335886576224815129 2728638251914932168611347)
                      ·
                        rfl

theorem cell23_5314004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_5314004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314004 prefixEnd_5314004 := by exact prefixLift 5314004
  have htrace : WordTrace (prefixWord ++ tailWord_5314004) baseStart_5314004 baseEnd_5314004 := by
    simpa [prefixWord, tailWord_5314004, baseEnd_5314004] using wordTrace_append hprefix tailTrace_5314004
  have hstable : (prefixWord ++ tailWord_5314004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314004).length < 2 ^ (prefixWord ++ tailWord_5314004).sum := by decide
  have hdescent : baseEnd_5314004 < baseStart_5314004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314050 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5314050 : Nat := 118140960795 + 5314050 * 2 ^ 59
def prefixEnd_5314050 : Nat := 4983230072969 + 3 ^ 40 * 5314050 * 2
def baseEnd_5314050 : Nat := 2728661872025038988636135

theorem tailTrace_5314050 : CollatzResearch.WordTrace tailWord_5314050 prefixEnd_5314050 2728661872025038988636135 := by
  unfold tailWord_5314050
  simp only [CollatzResearch.WordTrace]
  refine ⟨48454831599527973082492901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129212884265407928219981069 48454831599527973082492901)
  ·
    refine ⟨9085280924911494952967419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48454831599527973082492901 9085280924911494952967419)
    ·
      refine ⟨13627921387367242429451129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9085280924911494952967419 13627921387367242429451129)
      ·
        refine ⟨10220941040525431822088347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13627921387367242429451129 10220941040525431822088347)
        ·
          refine ⟨15331411560788147733132521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220941040525431822088347 15331411560788147733132521)
          ·
            refine ⟨11498558670591110799849391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15331411560788147733132521 11498558670591110799849391)
            ·
              refine ⟨17247838005886666199774087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11498558670591110799849391 17247838005886666199774087)
              ·
                refine ⟨25871757008829999299661131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17247838005886666199774087 25871757008829999299661131)
                ·
                  refine ⟨38807635513244998949491697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25871757008829999299661131 38807635513244998949491697)
                  ·
                    refine ⟨29105726634933749212118773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38807635513244998949491697 29105726634933749212118773)
                    ·
                      refine ⟨2728661872025038988636135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29105726634933749212118773 2728661872025038988636135)
                      ·
                        rfl

theorem cell23_5314050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5314050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314050 prefixEnd_5314050 := by exact prefixLift 5314050
  have htrace : WordTrace (prefixWord ++ tailWord_5314050) baseStart_5314050 baseEnd_5314050 := by
    simpa [prefixWord, tailWord_5314050, baseEnd_5314050] using wordTrace_append hprefix tailTrace_5314050
  have hstable : (prefixWord ++ tailWord_5314050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314050).length < 2 ^ (prefixWord ++ tailWord_5314050).sum := by decide
  have hdescent : baseEnd_5314050 < baseStart_5314050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314056 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 2, 1, 6]
def baseStart_5314056 : Nat := 118140960795 + 5314056 * 2 ^ 59
def prefixEnd_5314056 : Nat := 4983230072969 + 3 ^ 40 * 5314056 * 2
def baseEnd_5314056 : Nat := 2728664952908965965161107

theorem tailTrace_5314056 : CollatzResearch.WordTrace tailWord_5314056 prefixEnd_5314056 2728664952908965965161107 := by
  unfold tailWord_5314056
  simp only [CollatzResearch.WordTrace]
  refine ⟨96909772618045077677345011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129213030157393436903126681 96909772618045077677345011)
  ·
    refine ⟨145364658927067616516017517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96909772618045077677345011 145364658927067616516017517)
    ·
      refine ⟨54511747097650356193506569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145364658927067616516017517 54511747097650356193506569)
      ·
        refine ⟨40883810323237767145129927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54511747097650356193506569 40883810323237767145129927)
        ·
          refine ⟨61325715484856650717694891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40883810323237767145129927 61325715484856650717694891)
          ·
            refine ⟨91988573227284976076542337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61325715484856650717694891 91988573227284976076542337)
            ·
              refine ⟨68991429920463732057406753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91988573227284976076542337 68991429920463732057406753)
              ·
                refine ⟨51743572440347799043055065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68991429920463732057406753 51743572440347799043055065)
                ·
                  refine ⟨38807679330260849282291299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51743572440347799043055065 38807679330260849282291299)
                  ·
                    refine ⟨58211518995391273923436949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38807679330260849282291299 58211518995391273923436949)
                    ·
                      refine ⟨2728664952908965965161107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58211518995391273923436949 2728664952908965965161107)
                      ·
                        rfl

theorem cell23_5314056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_5314056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314056 prefixEnd_5314056 := by exact prefixLift 5314056
  have htrace : WordTrace (prefixWord ++ tailWord_5314056) baseStart_5314056 baseEnd_5314056 := by
    simpa [prefixWord, tailWord_5314056, baseEnd_5314056] using wordTrace_append hprefix tailTrace_5314056
  have hstable : (prefixWord ++ tailWord_5314056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314056).length < 2 ^ (prefixWord ++ tailWord_5314056).sum := by decide
  have hdescent : baseEnd_5314056 < baseStart_5314056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314080 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 3]
def baseStart_5314080 : Nat := 118140960795 + 5314080 * 2 ^ 59
def prefixEnd_5314080 : Nat := 4983230072969 + 3 ^ 40 * 5314080 * 2
def baseEnd_5314080 : Nat := 2728677276444673871260997

theorem tailTrace_5314080 : CollatzResearch.WordTrace tailWord_5314080 prefixEnd_5314080 2728677276444673871260997 := by
  unfold tailWord_5314080
  simp only [CollatzResearch.WordTrace]
  refine ⟨96910210294001603726781847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129213613725335471635709129 96910210294001603726781847)
  ·
    refine ⟨145365315441002405590172771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96910210294001603726781847 145365315441002405590172771)
    ·
      refine ⟨218047973161503608385259157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145365315441002405590172771 218047973161503608385259157)
      ·
        refine ⟨10220998741945481643059023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 218047973161503608385259157 10220998741945481643059023)
        ·
          refine ⟨15331498112918222464588535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10220998741945481643059023 15331498112918222464588535)
          ·
            refine ⟨22997247169377333696882803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15331498112918222464588535 22997247169377333696882803)
            ·
              refine ⟨34495870754066000545324205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22997247169377333696882803 34495870754066000545324205)
              ·
                refine ⟨12935951532774750204496577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34495870754066000545324205 12935951532774750204496577)
                ·
                  refine ⟨9701963649581062653372433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12935951532774750204496577 9701963649581062653372433)
                  ·
                    refine ⟨7276472737185796990029325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9701963649581062653372433 7276472737185796990029325)
                    ·
                      refine ⟨2728677276444673871260997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7276472737185796990029325 2728677276444673871260997)
                      ·
                        rfl

theorem cell23_5314080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_5314080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314080 prefixEnd_5314080 := by exact prefixLift 5314080
  have htrace : WordTrace (prefixWord ++ tailWord_5314080) baseStart_5314080 baseEnd_5314080 := by
    simpa [prefixWord, tailWord_5314080, baseEnd_5314080] using wordTrace_append hprefix tailTrace_5314080
  have hstable : (prefixWord ++ tailWord_5314080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314080).length < 2 ^ (prefixWord ++ tailWord_5314080).sum := by decide
  have hdescent : baseEnd_5314080 < baseStart_5314080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314104 : List Nat := [2, 1, 2, 1, 4, 4, 2, 2, 1, 4]
def baseStart_5314104 : Nat := 118140960795 + 5314104 * 2 ^ 59
def prefixEnd_5314104 : Nat := 4983230072969 + 3 ^ 40 * 5314104 * 2
def baseEnd_5314104 : Nat := 909563199993460592453629

theorem tailTrace_5314104 : CollatzResearch.WordTrace tailWord_5314104 prefixEnd_5314104 909563199993460592453629 := by
  unfold tailWord_5314104
  simp only [CollatzResearch.WordTrace]
  refine ⟨96910647969958129776218683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129214197293277506368291577 96910647969958129776218683)
  ·
    refine ⟨145365971954937194664328025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96910647969958129776218683 145365971954937194664328025)
    ·
      refine ⟨109024478966202895998246019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145365971954937194664328025 109024478966202895998246019)
      ·
        refine ⟨163536718449304343997369029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109024478966202895998246019 163536718449304343997369029)
        ·
          refine ⟨30663134709244564499506693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163536718449304343997369029 30663134709244564499506693)
          ·
            refine ⟨5749337757983355843657505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30663134709244564499506693 5749337757983355843657505)
            ·
              refine ⟨4312003318487516882743129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5749337757983355843657505 4312003318487516882743129)
              ·
                refine ⟨3234002488865637662057347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4312003318487516882743129 3234002488865637662057347)
                ·
                  refine ⟨4851003733298456493086021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234002488865637662057347 4851003733298456493086021)
                  ·
                    refine ⟨909563199993460592453629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4851003733298456493086021 909563199993460592453629)
                    ·
                      rfl

theorem cell23_5314104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 2, 2, 1, 4].length) (baseStart_5314104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314104 prefixEnd_5314104 := by exact prefixLift 5314104
  have htrace : WordTrace (prefixWord ++ tailWord_5314104) baseStart_5314104 baseEnd_5314104 := by
    simpa [prefixWord, tailWord_5314104, baseEnd_5314104] using wordTrace_append hprefix tailTrace_5314104
  have hstable : (prefixWord ++ tailWord_5314104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314104).length < 2 ^ (prefixWord ++ tailWord_5314104).sum := by decide
  have hdescent : baseEnd_5314104 < baseStart_5314104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314113 : List Nat := [1, 2, 5, 1, 1, 1, 1, 1, 5, 5]
def baseStart_5314113 : Nat := 118140960795 + 5314113 * 2 ^ 59
def prefixEnd_5314113 : Nat := 4983230072969 + 3 ^ 40 * 5314113 * 2
def baseEnd_5314113 : Nat := 909564740435424080716115

theorem tailTrace_5314113 : CollatzResearch.WordTrace tailWord_5314113 prefixEnd_5314113 909564740435424080716115 := by
  unfold tailWord_5314113
  simp only [CollatzResearch.WordTrace]
  refine ⟨193821624196883654089514993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129214416131255769393009995 193821624196883654089514993)
  ·
    refine ⟨145366218147662740567136245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193821624196883654089514993 145366218147662740567136245)
    ·
      refine ⟨13628082951343381928169023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145366218147662740567136245 13628082951343381928169023)
      ·
        refine ⟨20442124427015072892253535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13628082951343381928169023 20442124427015072892253535)
        ·
          refine ⟨30663186640522609338380303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20442124427015072892253535 30663186640522609338380303)
          ·
            refine ⟨45994779960783914007570455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30663186640522609338380303 45994779960783914007570455)
            ·
              refine ⟨68992169941175871011355683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45994779960783914007570455 68992169941175871011355683)
              ·
                refine ⟨103488254911763806517033525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68992169941175871011355683 103488254911763806517033525)
                ·
                  refine ⟨9702023897977856860971893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 103488254911763806517033525 9702023897977856860971893)
                  ·
                    refine ⟨909564740435424080716115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9702023897977856860971893 909564740435424080716115)
                    ·
                      rfl

theorem cell23_5314113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_5314113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314113 prefixEnd_5314113 := by exact prefixLift 5314113
  have htrace : WordTrace (prefixWord ++ tailWord_5314113) baseStart_5314113 baseEnd_5314113 := by
    simpa [prefixWord, tailWord_5314113, baseEnd_5314113] using wordTrace_append hprefix tailTrace_5314113
  have hstable : (prefixWord ++ tailWord_5314113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314113).length < 2 ^ (prefixWord ++ tailWord_5314113).sum := by decide
  have hdescent : baseEnd_5314113 < baseStart_5314113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314147 : List Nat := [1, 1, 1, 5, 1, 5, 2, 1, 1, 5]
def baseStart_5314147 : Nat := 118140960795 + 5314147 * 2 ^ 59
def prefixEnd_5314147 : Nat := 4983230072969 + 3 ^ 40 * 5314147 * 2
def baseEnd_5314147 : Nat := 909570559882841703041063

theorem tailTrace_5314147 : CollatzResearch.WordTrace tailWord_5314147 prefixEnd_5314147 909570559882841703041063 := by
  unfold tailWord_5314147
  simp only [CollatzResearch.WordTrace]
  refine ⟨193822864278760477896252695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129215242852506985264168463 193822864278760477896252695)
  ·
    refine ⟨290734296418140716844379043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193822864278760477896252695 290734296418140716844379043)
    ·
      refine ⟨436101444627211075266568565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290734296418140716844379043 436101444627211075266568565)
      ·
        refine ⟨40884510433801038306240803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 436101444627211075266568565 40884510433801038306240803)
        ·
          refine ⟨61326765650701557459361205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40884510433801038306240803 61326765650701557459361205)
          ·
            refine ⟨5749384279753271011815113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61326765650701557459361205 5749384279753271011815113)
            ·
              refine ⟨4312038209814953258861335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5749384279753271011815113 4312038209814953258861335)
              ·
                refine ⟨6468057314722429888292003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312038209814953258861335 6468057314722429888292003)
                ·
                  refine ⟨9702085972083644832438005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6468057314722429888292003 9702085972083644832438005)
                  ·
                    refine ⟨909570559882841703041063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9702085972083644832438005 909570559882841703041063)
                    ·
                      rfl

theorem cell23_5314147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 2, 1, 1, 5].length) (baseStart_5314147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314147 prefixEnd_5314147 := by exact prefixLift 5314147
  have htrace : WordTrace (prefixWord ++ tailWord_5314147) baseStart_5314147 baseEnd_5314147 := by
    simpa [prefixWord, tailWord_5314147, baseEnd_5314147] using wordTrace_append hprefix tailTrace_5314147
  have hstable : (prefixWord ++ tailWord_5314147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314147).length < 2 ^ (prefixWord ++ tailWord_5314147).sum := by decide
  have hdescent : baseEnd_5314147 < baseStart_5314147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314160 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 4, 4]
def baseStart_5314160 : Nat := 118140960795 + 5314160 * 2 ^ 59
def prefixEnd_5314160 : Nat := 4983230072969 + 3 ^ 40 * 5314160 * 2
def baseEnd_5314160 : Nat := 909572784965677852753543

theorem tailTrace_5314160 : CollatzResearch.WordTrace tailWord_5314160 prefixEnd_5314160 909572784965677852753543 := by
  unfold tailWord_5314160
  simp only [CollatzResearch.WordTrace]
  refine ⟨96911669213856690558237967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129215558951808920744317289 96911669213856690558237967)
  ·
    refine ⟨145367503820785035837356951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96911669213856690558237967 145367503820785035837356951)
    ·
      refine ⟨218051255731177553756035427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145367503820785035837356951 218051255731177553756035427)
      ·
        refine ⟨327076883596766330634053141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218051255731177553756035427 327076883596766330634053141)
        ·
          refine ⟨15331728918598421748471241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 327076883596766330634053141 15331728918598421748471241)
          ·
            refine ⟨11498796688948816311353431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15331728918598421748471241 11498796688948816311353431)
            ·
              refine ⟨17248195033423224467030147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11498796688948816311353431 17248195033423224467030147)
              ·
                refine ⟨25872292550134836700545221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17248195033423224467030147 25872292550134836700545221)
                ·
                  refine ⟨4851054853150281881352229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25872292550134836700545221 4851054853150281881352229)
                  ·
                    refine ⟨909572784965677852753543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4851054853150281881352229 909572784965677852753543)
                    ·
                      rfl

theorem cell23_5314160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 4, 4].length) (baseStart_5314160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314160 prefixEnd_5314160 := by exact prefixLift 5314160
  have htrace : WordTrace (prefixWord ++ tailWord_5314160) baseStart_5314160 baseEnd_5314160 := by
    simpa [prefixWord, tailWord_5314160, baseEnd_5314160] using wordTrace_append hprefix tailTrace_5314160
  have hstable : (prefixWord ++ tailWord_5314160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314160).length < 2 ^ (prefixWord ++ tailWord_5314160).sum := by decide
  have hdescent : baseEnd_5314160 < baseStart_5314160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314180 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_5314180 : Nat := 118140960795 + 5314180 * 2 ^ 59
def prefixEnd_5314180 : Nat := 4983230072969 + 3 ^ 40 * 5314180 * 2
def baseEnd_5314180 : Nat := 2728728624510123480010537

theorem tailTrace_5314180 : CollatzResearch.WordTrace tailWord_5314180 prefixEnd_5314180 2728728624510123480010537 := by
  unfold tailWord_5314180
  simp only [CollatzResearch.WordTrace]
  refine ⟨96912033943820462266101997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129216045258427283021469329 96912033943820462266101997)
  ·
    refine ⟨36342012728932673349788249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96912033943820462266101997 36342012728932673349788249)
    ·
      refine ⟨27256509546699505012341187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36342012728932673349788249 27256509546699505012341187)
      ·
        refine ⟨40884764320049257518511781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27256509546699505012341187 40884764320049257518511781)
        ·
          refine ⟨7665893310009235784720959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40884764320049257518511781 7665893310009235784720959)
          ·
            refine ⟨11498839965013853677081439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7665893310009235784720959 11498839965013853677081439)
            ·
              refine ⟨17248259947520780515622159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11498839965013853677081439 17248259947520780515622159)
              ·
                refine ⟨25872389921281170773433239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17248259947520780515622159 25872389921281170773433239)
                ·
                  refine ⟨38808584881921756160149859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25872389921281170773433239 38808584881921756160149859)
                  ·
                    refine ⟨58212877322882634240224789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38808584881921756160149859 58212877322882634240224789)
                    ·
                      refine ⟨2728728624510123480010537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58212877322882634240224789 2728728624510123480010537)
                      ·
                        rfl

theorem cell23_5314180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_5314180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314180 prefixEnd_5314180 := by exact prefixLift 5314180
  have htrace : WordTrace (prefixWord ++ tailWord_5314180) baseStart_5314180 baseEnd_5314180 := by
    simpa [prefixWord, tailWord_5314180, baseEnd_5314180] using wordTrace_append hprefix tailTrace_5314180
  have hstable : (prefixWord ++ tailWord_5314180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314180).length < 2 ^ (prefixWord ++ tailWord_5314180).sum := by decide
  have hdescent : baseEnd_5314180 < baseStart_5314180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314184 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 1, 1, 4]
def baseStart_5314184 : Nat := 118140960795 + 5314184 * 2 ^ 59
def prefixEnd_5314184 : Nat := 4983230072969 + 3 ^ 40 * 5314184 * 2
def baseEnd_5314184 : Nat := 2728730678432741464360519

theorem tailTrace_5314184 : CollatzResearch.WordTrace tailWord_5314184 prefixEnd_5314184 2728730678432741464360519 := by
  unfold tailWord_5314184
  simp only [CollatzResearch.WordTrace]
  refine ⟨96912106889813216607674803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129216142519750955476899737 96912106889813216607674803)
  ·
    refine ⟨145368160334719824911512205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96912106889813216607674803 145368160334719824911512205)
    ·
      refine ⟨54513060125519934341817077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145368160334719824911512205 54513060125519934341817077)
      ·
        refine ⟨5110599386767493844545351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54513060125519934341817077 5110599386767493844545351)
        ·
          refine ⟨7665899080151240766818027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5110599386767493844545351 7665899080151240766818027)
          ·
            refine ⟨11498848620226861150227041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7665899080151240766818027 11498848620226861150227041)
            ·
              refine ⟨8624136465170145862670281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11498848620226861150227041 8624136465170145862670281)
              ·
                refine ⟨6468102348877609397002711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8624136465170145862670281 6468102348877609397002711)
                ·
                  refine ⟨9702153523316414095504067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6468102348877609397002711 9702153523316414095504067)
                  ·
                    refine ⟨14553230284974621143256101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9702153523316414095504067 14553230284974621143256101)
                    ·
                      refine ⟨2728730678432741464360519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14553230284974621143256101 2728730678432741464360519)
                      ·
                        rfl

theorem cell23_5314184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_5314184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314184 prefixEnd_5314184 := by exact prefixLift 5314184
  have htrace : WordTrace (prefixWord ++ tailWord_5314184) baseStart_5314184 baseEnd_5314184 := by
    simpa [prefixWord, tailWord_5314184, baseEnd_5314184] using wordTrace_append hprefix tailTrace_5314184
  have hstable : (prefixWord ++ tailWord_5314184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314184).length < 2 ^ (prefixWord ++ tailWord_5314184).sum := by decide
  have hdescent : baseEnd_5314184 < baseStart_5314184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314190 : List Nat := [4, 1, 1, 3, 1, 2, 4, 7]
def baseStart_5314190 : Nat := 118140960795 + 5314190 * 2 ^ 59
def prefixEnd_5314190 : Nat := 4983230072969 + 3 ^ 40 * 5314190 * 2
def baseEnd_5314190 : Nat := 101064213308024757069833

theorem tailTrace_5314190 : CollatzResearch.WordTrace tailWord_5314190 prefixEnd_5314190 101064213308024757069833 := by
  unfold tailWord_5314190
  simp only [CollatzResearch.WordTrace]
  refine ⟨24228054077200587030008503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129216288411736464160045349 24228054077200587030008503)
  ·
    refine ⟨36342081115800880545012755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24228054077200587030008503 36342081115800880545012755)
    ·
      refine ⟨54513121673701320817519133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36342081115800880545012755 54513121673701320817519133)
      ·
        refine ⟨20442420627637995306569675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54513121673701320817519133 20442420627637995306569675)
        ·
          refine ⟨30663630941456992959854513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20442420627637995306569675 30663630941456992959854513)
          ·
            refine ⟨22997723206092744719890885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30663630941456992959854513 22997723206092744719890885)
            ·
              refine ⟨4312073101142389634979541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22997723206092744719890885 4312073101142389634979541)
              ·
                refine ⟨101064213308024757069833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4312073101142389634979541 101064213308024757069833)
                ·
                  rfl

theorem cell23_5314190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 7].length) (baseStart_5314190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314190 prefixEnd_5314190 := by exact prefixLift 5314190
  have htrace : WordTrace (prefixWord ++ tailWord_5314190) baseStart_5314190 baseEnd_5314190 := by
    simpa [prefixWord, tailWord_5314190, baseEnd_5314190] using wordTrace_append hprefix tailTrace_5314190
  have hstable : (prefixWord ++ tailWord_5314190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314190).length < 2 ^ (prefixWord ++ tailWord_5314190).sum := by decide
  have hdescent : baseEnd_5314190 < baseStart_5314190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314207 : List Nat := [1, 1, 2, 7, 2, 1, 9]
def baseStart_5314207 : Nat := 118140960795 + 5314207 * 2 ^ 59
def prefixEnd_5314207 : Nat := 4983230072969 + 3 ^ 40 * 5314207 * 2
def baseEnd_5314207 : Nat := 33688178870219689807073

theorem tailTrace_5314207 : CollatzResearch.WordTrace tailWord_5314207 prefixEnd_5314207 33688178870219689807073 := by
  unfold tailWord_5314207
  simp only [CollatzResearch.WordTrace]
  refine ⟨193825052658543108143436875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129216701772362072095624583 193825052658543108143436875)
  ·
    refine ⟨290737578987814662215155313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193825052658543108143436875 290737578987814662215155313)
    ·
      refine ⟨218053184240860996661366485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290737578987814662215155313 218053184240860996661366485)
      ·
        refine ⟨5110621505645179609250777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 218053184240860996661366485 5110621505645179609250777)
        ·
          refine ⟨3832966129233884706938083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5110621505645179609250777 3832966129233884706938083)
          ·
            refine ⟨5749449193850827060407125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3832966129233884706938083 5749449193850827060407125)
            ·
              refine ⟨33688178870219689807073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5749449193850827060407125 33688178870219689807073)
              ·
                rfl

theorem cell23_5314207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 9].length) (baseStart_5314207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314207 prefixEnd_5314207 := by exact prefixLift 5314207
  have htrace : WordTrace (prefixWord ++ tailWord_5314207) baseStart_5314207 baseEnd_5314207 := by
    simpa [prefixWord, tailWord_5314207, baseEnd_5314207] using wordTrace_append hprefix tailTrace_5314207
  have hstable : (prefixWord ++ tailWord_5314207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314207).length < 2 ^ (prefixWord ++ tailWord_5314207).sum := by decide
  have hdescent : baseEnd_5314207 < baseStart_5314207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314223 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 4]
def baseStart_5314223 : Nat := 118140960795 + 5314223 * 2 ^ 59
def prefixEnd_5314223 : Nat := 4983230072969 + 3 ^ 40 * 5314223 * 2
def baseEnd_5314223 : Nat := 2728750704178266811772839

theorem tailTrace_5314223 : CollatzResearch.WordTrace tailWord_5314223 prefixEnd_5314223 2728750704178266811772839 := by
  unfold tailWord_5314223
  simp only [CollatzResearch.WordTrace]
  refine ⟨193825636226485142876019323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129217090817656761917346215 193825636226485142876019323)
  ·
    refine ⟨290738454339727714314028985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193825636226485142876019323 290738454339727714314028985)
    ·
      refine ⟨218053840754795785735521739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290738454339727714314028985 218053840754795785735521739)
      ·
        refine ⟨327080761132193678603282609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218053840754795785735521739 327080761132193678603282609)
        ·
          refine ⟨245310570849145258952461957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327080761132193678603282609 245310570849145258952461957)
          ·
            refine ⟨45995732034214736053586617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245310570849145258952461957 45995732034214736053586617)
            ·
              refine ⟨34496799025661052040189963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45995732034214736053586617 34496799025661052040189963)
              ·
                refine ⟨51745198538491578060284945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34496799025661052040189963 51745198538491578060284945)
                ·
                  refine ⟨38808898903868683545213709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51745198538491578060284945 38808898903868683545213709)
                  ·
                    refine ⟨14553337088950756329455141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38808898903868683545213709 14553337088950756329455141)
                    ·
                      refine ⟨2728750704178266811772839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14553337088950756329455141 2728750704178266811772839)
                      ·
                        rfl

theorem cell23_5314223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 2, 3, 4].length) (baseStart_5314223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314223 prefixEnd_5314223 := by exact prefixLift 5314223
  have htrace : WordTrace (prefixWord ++ tailWord_5314223) baseStart_5314223 baseEnd_5314223 := by
    simpa [prefixWord, tailWord_5314223, baseEnd_5314223] using wordTrace_append hprefix tailTrace_5314223
  have hstable : (prefixWord ++ tailWord_5314223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314223).length < 2 ^ (prefixWord ++ tailWord_5314223).sum := by decide
  have hdescent : baseEnd_5314223 < baseStart_5314223 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314233 : List Nat := [1, 2, 1, 4, 1, 1, 2, 3, 2, 6]
def baseStart_5314233 : Nat := 118140960795 + 5314233 * 2 ^ 59
def prefixEnd_5314233 : Nat := 4983230072969 + 3 ^ 40 * 5314233 * 2
def baseEnd_5314233 : Nat := 909585279661603924215931

theorem tailTrace_5314233 : CollatzResearch.WordTrace tailWord_5314233 prefixEnd_5314233 909585279661603924215931 := by
  unfold tailWord_5314233
  simp only [CollatzResearch.WordTrace]
  refine ⟨193826000956448914583883353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129217333970965943055922235 193826000956448914583883353)
  ·
    refine ⟨145369500717336685937912515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193826000956448914583883353 145369500717336685937912515)
    ·
      refine ⟨218054251076005028906868773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145369500717336685937912515 218054251076005028906868773)
      ·
        refine ⟨40885172076750942920037895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218054251076005028906868773 40885172076750942920037895)
        ·
          refine ⟨61327758115126414380056843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40885172076750942920037895 61327758115126414380056843)
          ·
            refine ⟨91991637172689621570085265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61327758115126414380056843 91991637172689621570085265)
            ·
              refine ⟨68993727879517216177563949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91991637172689621570085265 68993727879517216177563949)
              ·
                refine ⟨25872647954818956066586481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68993727879517216177563949 25872647954818956066586481)
                ·
                  refine ⟨19404485966114217049939861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25872647954818956066586481 19404485966114217049939861)
                  ·
                    refine ⟨909585279661603924215931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19404485966114217049939861 909585279661603924215931)
                    ·
                      rfl

theorem cell23_5314233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 3, 2, 6].length) (baseStart_5314233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314233 prefixEnd_5314233 := by exact prefixLift 5314233
  have htrace : WordTrace (prefixWord ++ tailWord_5314233) baseStart_5314233 baseEnd_5314233 := by
    simpa [prefixWord, tailWord_5314233, baseEnd_5314233] using wordTrace_append hprefix tailTrace_5314233
  have hstable : (prefixWord ++ tailWord_5314233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314233).length < 2 ^ (prefixWord ++ tailWord_5314233).sum := by decide
  have hdescent : baseEnd_5314233 < baseStart_5314233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314234 : List Nat := [3, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3]
def baseStart_5314234 : Nat := 118140960795 + 5314234 * 2 ^ 59
def prefixEnd_5314234 : Nat := 4983230072969 + 3 ^ 40 * 5314234 * 2
def baseEnd_5314234 : Nat := 2728756352465466268735289

theorem tailTrace_5314234 : CollatzResearch.WordTrace tailWord_5314234 prefixEnd_5314234 2728756352465466268735289 := by
  unfold tailWord_5314234
  simp only [CollatzResearch.WordTrace]
  refine ⟨48456509357361322938667439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129217358286296861169779837 48456509357361322938667439)
  ·
    refine ⟨72684764036041984408001159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48456509357361322938667439 72684764036041984408001159)
    ·
      refine ⟨109027146054062976612001739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72684764036041984408001159 109027146054062976612001739)
      ·
        refine ⟨163540719081094464918002609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109027146054062976612001739 163540719081094464918002609)
        ·
          refine ⟨122655539310820848688501957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163540719081094464918002609 122655539310820848688501957)
          ·
            refine ⟨22997913620778909129094117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 122655539310820848688501957 22997913620778909129094117)
            ·
              refine ⟨4312108803896045461705147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22997913620778909129094117 4312108803896045461705147)
              ·
                refine ⟨6468163205844068192557721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312108803896045461705147 6468163205844068192557721)
                ·
                  refine ⟨4851122404383051144418291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6468163205844068192557721 4851122404383051144418291)
                  ·
                    refine ⟨7276683606574576716627437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4851122404383051144418291 7276683606574576716627437)
                    ·
                      refine ⟨2728756352465466268735289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7276683606574576716627437 2728756352465466268735289)
                      ·
                        rfl

theorem cell23_5314234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3].length) (baseStart_5314234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314234 prefixEnd_5314234 := by exact prefixLift 5314234
  have htrace : WordTrace (prefixWord ++ tailWord_5314234) baseStart_5314234 baseEnd_5314234 := by
    simpa [prefixWord, tailWord_5314234, baseEnd_5314234] using wordTrace_append hprefix tailTrace_5314234
  have hstable : (prefixWord ++ tailWord_5314234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314234).length < 2 ^ (prefixWord ++ tailWord_5314234).sum := by decide
  have hdescent : baseEnd_5314234 < baseStart_5314234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314257 : List Nat := [1, 2, 2, 1, 2, 5, 1, 2, 1, 4, 2]
def baseStart_5314257 : Nat := 118140960795 + 5314257 * 2 ^ 59
def prefixEnd_5314257 : Nat := 4983230072969 + 3 ^ 40 * 5314257 * 2
def baseEnd_5314257 : Nat := 2728768162520519678747683

theorem tailTrace_5314257 : CollatzResearch.WordTrace tailWord_5314257 prefixEnd_5314257 2728768162520519678747683 := by
  unfold tailWord_5314257
  simp only [CollatzResearch.WordTrace]
  refine ⟨193826876308361966682757025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129217917538907977788504683 193826876308361966682757025)
  ·
    refine ⟨145370157231271475012067769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193826876308361966682757025 145370157231271475012067769)
    ·
      refine ⟨109027617923453606259050827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145370157231271475012067769 109027617923453606259050827)
      ·
        refine ⟨163541426885180409388576241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109027617923453606259050827 163541426885180409388576241)
        ·
          refine ⟨122656070163885307041432181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163541426885180409388576241 122656070163885307041432181)
          ·
            refine ⟨11499006577864247535134267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 122656070163885307041432181 11499006577864247535134267)
            ·
              refine ⟨17248509866796371302701401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11499006577864247535134267 17248509866796371302701401)
              ·
                refine ⟨12936382400097278477026051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17248509866796371302701401 12936382400097278477026051)
                ·
                  refine ⟨19404573600145917715539077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12936382400097278477026051 19404573600145917715539077)
                  ·
                    refine ⟨3638357550027359571663577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19404573600145917715539077 3638357550027359571663577)
                    ·
                      refine ⟨2728768162520519678747683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638357550027359571663577 2728768162520519678747683)
                      ·
                        rfl

theorem cell23_5314257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 2, 1, 4, 2].length) (baseStart_5314257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314257 prefixEnd_5314257 := by exact prefixLift 5314257
  have htrace : WordTrace (prefixWord ++ tailWord_5314257) baseStart_5314257 baseEnd_5314257 := by
    simpa [prefixWord, tailWord_5314257, baseEnd_5314257] using wordTrace_append hprefix tailTrace_5314257
  have hstable : (prefixWord ++ tailWord_5314257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314257).length < 2 ^ (prefixWord ++ tailWord_5314257).sum := by decide
  have hdescent : baseEnd_5314257 < baseStart_5314257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314303 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 7]
def baseStart_5314303 : Nat := 118140960795 + 5314303 * 2 ^ 59
def prefixEnd_5314303 : Nat := 4983230072969 + 3 ^ 40 * 5314303 * 2
def baseEnd_5314303 : Nat := 2728791782630626498772471

theorem tailTrace_5314303 : CollatzResearch.WordTrace tailWord_5314303 prefixEnd_5314303 2728791782630626498772471 := by
  unfold tailWord_5314303
  simp only [CollatzResearch.WordTrace]
  refine ⟨193828554066195316538931563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129219036044130211025954375 193828554066195316538931563)
  ·
    refine ⟨290742831099292974808397345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193828554066195316538931563 290742831099292974808397345)
    ·
      refine ⟨218057123324469731106298009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290742831099292974808397345 218057123324469731106298009)
      ·
        refine ⟨163542842493352298329723507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218057123324469731106298009 163542842493352298329723507)
        ·
          refine ⟨245314263740028447494585261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163542842493352298329723507 245314263740028447494585261)
          ·
            refine ⟨91992848902510667810469473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245314263740028447494585261 91992848902510667810469473)
            ·
              refine ⟨68994636676883000857852105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91992848902510667810469473 68994636676883000857852105)
              ·
                refine ⟨51745977507662250643389079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68994636676883000857852105 51745977507662250643389079)
                ·
                  refine ⟨77618966261493375965083619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51745977507662250643389079 77618966261493375965083619)
                  ·
                    refine ⟨116428449392240063947625429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 77618966261493375965083619 116428449392240063947625429)
                    ·
                      refine ⟨2728791782630626498772471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 116428449392240063947625429 2728791782630626498772471)
                      ·
                        rfl

theorem cell23_5314303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_5314303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314303 prefixEnd_5314303 := by exact prefixLift 5314303
  have htrace : WordTrace (prefixWord ++ tailWord_5314303) baseStart_5314303 baseEnd_5314303 := by
    simpa [prefixWord, tailWord_5314303, baseEnd_5314303] using wordTrace_append hprefix tailTrace_5314303
  have hstable : (prefixWord ++ tailWord_5314303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314303).length < 2 ^ (prefixWord ++ tailWord_5314303).sum := by decide
  have hdescent : baseEnd_5314303 < baseStart_5314303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314391 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 3, 4]
def baseStart_5314391 : Nat := 118140960795 + 5314391 * 2 ^ 59
def prefixEnd_5314391 : Nat := 4983230072969 + 3 ^ 40 * 5314391 * 2
def baseEnd_5314391 : Nat := 909612322976074051490689

theorem tailTrace_5314391 : CollatzResearch.WordTrace tailWord_5314391 prefixEnd_5314391 909612322976074051490689 := by
  unfold tailWord_5314391
  simp only [CollatzResearch.WordTrace]
  refine ⟨193831763689876507568135027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129221175793251005045423351 193831763689876507568135027)
  ·
    refine ⟨290747645534814761352202541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193831763689876507568135027 290747645534814761352202541)
    ·
      refine ⟨109030367075555535507075953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290747645534814761352202541 109030367075555535507075953)
      ·
        refine ⟨81772775306666651630306965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109030367075555535507075953 81772775306666651630306965)
        ·
          refine ⟨3833098842499999295170639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 81772775306666651630306965 3833098842499999295170639)
          ·
            refine ⟨5749648263749998942755959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833098842499999295170639 5749648263749998942755959)
            ·
              refine ⟨8624472395624998414133939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749648263749998942755959 8624472395624998414133939)
              ·
                refine ⟨12936708593437497621200909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624472395624998414133939 12936708593437497621200909)
                ·
                  refine ⟨4851265722539061607950341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12936708593437497621200909 4851265722539061607950341)
                  ·
                    refine ⟨909612322976074051490689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4851265722539061607950341 909612322976074051490689)
                    ·
                      rfl

theorem cell23_5314391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 3, 4].length) (baseStart_5314391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314391 prefixEnd_5314391 := by exact prefixLift 5314391
  have htrace : WordTrace (prefixWord ++ tailWord_5314391) baseStart_5314391 baseEnd_5314391 := by
    simpa [prefixWord, tailWord_5314391, baseEnd_5314391] using wordTrace_append hprefix tailTrace_5314391
  have hstable : (prefixWord ++ tailWord_5314391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314391).length < 2 ^ (prefixWord ++ tailWord_5314391).sum := by decide
  have hdescent : baseEnd_5314391 < baseStart_5314391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314457 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 3]
def baseStart_5314457 : Nat := 118140960795 + 5314457 * 2 ^ 59
def prefixEnd_5314457 : Nat := 4983230072969 + 3 ^ 40 * 5314457 * 2
def baseEnd_5314457 : Nat := 2728870858651418896246763

theorem tailTrace_5314457 : CollatzResearch.WordTrace tailWord_5314457 prefixEnd_5314457 2728870858651418896246763 := by
  unfold tailWord_5314457
  simp only [CollatzResearch.WordTrace]
  refine ⟨193834170907637400840037625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129222780605091600560025083 193834170907637400840037625)
  ·
    refine ⟨145375628180728050630028219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193834170907637400840037625 145375628180728050630028219)
    ·
      refine ⟨218063442271092075945042329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145375628180728050630028219 218063442271092075945042329)
      ·
        refine ⟨163547581703319056958781747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218063442271092075945042329 163547581703319056958781747)
        ·
          refine ⟨245321372554978585438172621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163547581703319056958781747 245321372554978585438172621)
          ·
            refine ⟨91995514708116969539314733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 245321372554978585438172621 91995514708116969539314733)
            ·
              refine ⟨34498318015543863577243025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91995514708116969539314733 34498318015543863577243025)
              ·
                refine ⟨25873738511657897682932269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34498318015543863577243025 25873738511657897682932269)
                ·
                  refine ⟨9702651941871711631099601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25873738511657897682932269 9702651941871711631099601)
                  ·
                    refine ⟨7276988956403783723324701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9702651941871711631099601 7276988956403783723324701)
                    ·
                      refine ⟨2728870858651418896246763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7276988956403783723324701 2728870858651418896246763)
                      ·
                        rfl

theorem cell23_5314457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_5314457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314457 prefixEnd_5314457 := by exact prefixLift 5314457
  have htrace : WordTrace (prefixWord ++ tailWord_5314457) baseStart_5314457 baseEnd_5314457 := by
    simpa [prefixWord, tailWord_5314457, baseEnd_5314457] using wordTrace_append hprefix tailTrace_5314457
  have hstable : (prefixWord ++ tailWord_5314457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314457).length < 2 ^ (prefixWord ++ tailWord_5314457).sum := by decide
  have hdescent : baseEnd_5314457 < baseStart_5314457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314471 : List Nat := [1, 1, 6, 1, 2, 1, 1, 1, 5, 2, 2]
def baseStart_5314471 : Nat := 118140960795 + 5314471 * 2 ^ 59
def prefixEnd_5314471 : Nat := 4983230072969 + 3 ^ 40 * 5314471 * 2
def baseEnd_5314471 : Nat := 2728878047380581841471699

theorem tailTrace_5314471 : CollatzResearch.WordTrace tailWord_5314471 prefixEnd_5314471 2728878047380581841471699 := by
  unfold tailWord_5314471
  simp only [CollatzResearch.WordTrace]
  refine ⟨193834681529586681231047267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129223121019724454154031511 193834681529586681231047267)
  ·
    refine ⟨290752022294380021846570901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193834681529586681231047267 290752022294380021846570901)
    ·
      refine ⟨13629001045049063524058011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 290752022294380021846570901 13629001045049063524058011)
      ·
        refine ⟨20443501567573595286087017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13629001045049063524058011 20443501567573595286087017)
        ·
          refine ⟨15332626175680196464565263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20443501567573595286087017 15332626175680196464565263)
          ·
            refine ⟨22998939263520294696847895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15332626175680196464565263 22998939263520294696847895)
            ·
              refine ⟨34498408895280442045271843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22998939263520294696847895 34498408895280442045271843)
              ·
                refine ⟨51747613342920663067907765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34498408895280442045271843 51747613342920663067907765)
                ·
                  refine ⟨4851338750898812162616353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51747613342920663067907765 4851338750898812162616353)
                  ·
                    refine ⟨3638504063174109121962265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4851338750898812162616353 3638504063174109121962265)
                    ·
                      refine ⟨2728878047380581841471699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638504063174109121962265 2728878047380581841471699)
                      ·
                        rfl

theorem cell23_5314471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_5314471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314471 prefixEnd_5314471 := by exact prefixLift 5314471
  have htrace : WordTrace (prefixWord ++ tailWord_5314471) baseStart_5314471 baseEnd_5314471 := by
    simpa [prefixWord, tailWord_5314471, baseEnd_5314471] using wordTrace_append hprefix tailTrace_5314471
  have hstable : (prefixWord ++ tailWord_5314471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314471).length < 2 ^ (prefixWord ++ tailWord_5314471).sum := by decide
  have hdescent : baseEnd_5314471 < baseStart_5314471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314488 : List Nat := [2, 1, 2, 1, 2, 3, 4, 3, 1, 2, 2]
def baseStart_5314488 : Nat := 118140960795 + 5314488 * 2 ^ 59
def prefixEnd_5314488 : Nat := 4983230072969 + 3 ^ 40 * 5314488 * 2
def baseEnd_5314488 : Nat := 2728886776551708274959121

theorem tailTrace_5314488 : CollatzResearch.WordTrace tailWord_5314488 prefixEnd_5314488 2728886776551708274959121 := by
  unfold tailWord_5314488
  simp only [CollatzResearch.WordTrace]
  refine ⟨96917650785262546567208059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129223534380350062089610745 96917650785262546567208059)
  ·
    refine ⟨145376476177893819850812089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96917650785262546567208059 145376476177893819850812089)
    ·
      refine ⟨109032357133420364888109067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145376476177893819850812089 109032357133420364888109067)
      ·
        refine ⟨163548535700130547332163601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109032357133420364888109067 163548535700130547332163601)
        ·
          refine ⟨122661401775097910499122701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163548535700130547332163601 122661401775097910499122701)
          ·
            refine ⟨45998025665661716437171013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 122661401775097910499122701 45998025665661716437171013)
            ·
              refine ⟨8624629812311571831969565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45998025665661716437171013 8624629812311571831969565)
              ·
                refine ⟨3234236179616839436988587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8624629812311571831969565 3234236179616839436988587)
                ·
                  refine ⟨4851354269425259155482881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234236179616839436988587 4851354269425259155482881)
                  ·
                    refine ⟨3638515702068944366612161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4851354269425259155482881 3638515702068944366612161)
                    ·
                      refine ⟨2728886776551708274959121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638515702068944366612161 2728886776551708274959121)
                      ·
                        rfl

theorem cell23_5314488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 4, 3, 1, 2, 2].length) (baseStart_5314488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314488 prefixEnd_5314488 := by exact prefixLift 5314488
  have htrace : WordTrace (prefixWord ++ tailWord_5314488) baseStart_5314488 baseEnd_5314488 := by
    simpa [prefixWord, tailWord_5314488, baseEnd_5314488] using wordTrace_append hprefix tailTrace_5314488
  have hstable : (prefixWord ++ tailWord_5314488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314488).length < 2 ^ (prefixWord ++ tailWord_5314488).sum := by decide
  have hdescent : baseEnd_5314488 < baseStart_5314488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314490 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_5314490 : Nat := 118140960795 + 5314490 * 2 ^ 59
def prefixEnd_5314490 : Nat := 4983230072969 + 3 ^ 40 * 5314490 * 2
def baseEnd_5314490 : Nat := 909629267837672422378037

theorem tailTrace_5314490 : CollatzResearch.WordTrace tailWord_5314490 prefixEnd_5314490 909629267837672422378037 := by
  unfold tailWord_5314490
  simp only [CollatzResearch.WordTrace]
  refine ⟨48458843629129461868997231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129223583011011898317325949 48458843629129461868997231)
  ·
    refine ⟨72688265443694192803495847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48458843629129461868997231 72688265443694192803495847)
    ·
      refine ⟨109032398165541289205243771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72688265443694192803495847 109032398165541289205243771)
      ·
        refine ⟨163548597248311933807865657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109032398165541289205243771 163548597248311933807865657)
        ·
          refine ⟨122661447936233950355899243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163548597248311933807865657 122661447936233950355899243)
          ·
            refine ⟨183992171904350925533848865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122661447936233950355899243 183992171904350925533848865)
            ·
              refine ⟨137994128928263194150386649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 183992171904350925533848865 137994128928263194150386649)
              ·
                refine ⟨103495596696197395612789987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137994128928263194150386649 103495596696197395612789987)
                ·
                  refine ⟨155243395044296093419184981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103495596696197395612789987 155243395044296093419184981)
                  ·
                    refine ⟨909629267837672422378037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 155243395044296093419184981 909629267837672422378037)
                    ·
                      rfl

theorem cell23_5314490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_5314490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314490 prefixEnd_5314490 := by exact prefixLift 5314490
  have htrace : WordTrace (prefixWord ++ tailWord_5314490) baseStart_5314490 baseEnd_5314490 := by
    simpa [prefixWord, tailWord_5314490, baseEnd_5314490] using wordTrace_append hprefix tailTrace_5314490
  have hstable : (prefixWord ++ tailWord_5314490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314490).length < 2 ^ (prefixWord ++ tailWord_5314490).sum := by decide
  have hdescent : baseEnd_5314490 < baseStart_5314490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314518 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_5314518 : Nat := 118140960795 + 5314518 * 2 ^ 59
def prefixEnd_5314518 : Nat := 4983230072969 + 3 ^ 40 * 5314518 * 2
def baseEnd_5314518 : Nat := 2728902180971343157583983

theorem tailTrace_5314518 : CollatzResearch.WordTrace tailWord_5314518 prefixEnd_5314518 2728902180971343157583983 := by
  unfold tailWord_5314518
  simp only [CollatzResearch.WordTrace]
  refine ⟨12114774735026025516125513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129224263840277605505338805 12114774735026025516125513)
  ·
    refine ⟨9086081051269519137094135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12114774735026025516125513 9086081051269519137094135)
    ·
      refine ⟨13629121576904278705641203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9086081051269519137094135 13629121576904278705641203)
      ·
        refine ⟨20443682365356418058461805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13629121576904278705641203 20443682365356418058461805)
        ·
          refine ⟨7666380887008656771923177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20443682365356418058461805 7666380887008656771923177)
          ·
            refine ⟨5749785665256492578942383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7666380887008656771923177 5749785665256492578942383)
            ·
              refine ⟨8624678497884738868413575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749785665256492578942383 8624678497884738868413575)
              ·
                refine ⟨12937017746827108302620363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624678497884738868413575 12937017746827108302620363)
                ·
                  refine ⟨19405526620240662453930545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12937017746827108302620363 19405526620240662453930545)
                  ·
                    refine ⟨14554144965180496840447909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19405526620240662453930545 14554144965180496840447909)
                    ·
                      refine ⟨2728902180971343157583983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14554144965180496840447909 2728902180971343157583983)
                      ·
                        rfl

theorem cell23_5314518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_5314518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314518 prefixEnd_5314518 := by exact prefixLift 5314518
  have htrace : WordTrace (prefixWord ++ tailWord_5314518) baseStart_5314518 baseEnd_5314518 := by
    simpa [prefixWord, tailWord_5314518, baseEnd_5314518] using wordTrace_append hprefix tailTrace_5314518
  have hstable : (prefixWord ++ tailWord_5314518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314518).length < 2 ^ (prefixWord ++ tailWord_5314518).sum := by decide
  have hdescent : baseEnd_5314518 < baseStart_5314518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314521 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 3]
def baseStart_5314521 : Nat := 118140960795 + 5314521 * 2 ^ 59
def prefixEnd_5314521 : Nat := 4983230072969 + 3 ^ 40 * 5314521 * 2
def baseEnd_5314521 : Nat := 2728903721413306645846469

theorem tailTrace_5314521 : CollatzResearch.WordTrace tailWord_5314521 prefixEnd_5314521 2728903721413306645846469 := by
  unfold tailWord_5314521
  simp only [CollatzResearch.WordTrace]
  refine ⟨193836505179405539770367417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129224336786270359846911611 193836505179405539770367417)
  ·
    refine ⟨145377378884554154827775563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193836505179405539770367417 145377378884554154827775563)
    ·
      refine ⟨218066068326831232241663345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145377378884554154827775563 218066068326831232241663345)
      ·
        refine ⟨163549551245123424181247509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218066068326831232241663345 163549551245123424181247509)
        ·
          refine ⟨7666385214615160508495977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 163549551245123424181247509 7666385214615160508495977)
          ·
            refine ⟨5749788910961370381371983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7666385214615160508495977 5749788910961370381371983)
            ·
              refine ⟨8624683366442055572057975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749788910961370381371983 8624683366442055572057975)
              ·
                refine ⟨12937025049663083358086963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624683366442055572057975 12937025049663083358086963)
                ·
                  refine ⟨19405537574494625037130445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12937025049663083358086963 19405537574494625037130445)
                  ·
                    refine ⟨7277076590435484388923917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19405537574494625037130445 7277076590435484388923917)
                    ·
                      refine ⟨2728903721413306645846469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7277076590435484388923917 2728903721413306645846469)
                      ·
                        rfl

theorem cell23_5314521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_5314521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314521 prefixEnd_5314521 := by exact prefixLift 5314521
  have htrace : WordTrace (prefixWord ++ tailWord_5314521) baseStart_5314521 baseEnd_5314521 := by
    simpa [prefixWord, tailWord_5314521, baseEnd_5314521] using wordTrace_append hprefix tailTrace_5314521
  have hstable : (prefixWord ++ tailWord_5314521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314521).length < 2 ^ (prefixWord ++ tailWord_5314521).sum := by decide
  have hdescent : baseEnd_5314521 < baseStart_5314521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314531 : List Nat := [1, 1, 1, 6, 1, 2, 1, 4, 1, 3, 2]
def baseStart_5314531 : Nat := 118140960795 + 5314531 * 2 ^ 59
def prefixEnd_5314531 : Nat := 4983230072969 + 3 ^ 40 * 5314531 * 2
def baseEnd_5314531 : Nat := 2728908856219851606721423

theorem tailTrace_5314531 : CollatzResearch.WordTrace tailWord_5314531 prefixEnd_5314531 2728908856219851606721423 := by
  unfold tailWord_5314531
  simp only [CollatzResearch.WordTrace]
  refine ⟨193836869909369311478231447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129224579939579540985487631 193836869909369311478231447)
  ·
    refine ⟨290755304864053967217347171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193836869909369311478231447 290755304864053967217347171)
    ·
      refine ⟨436132957296080950826020757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290755304864053967217347171 436132957296080950826020757)
      ·
        refine ⟨20443732373253794569969723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 436132957296080950826020757 20443732373253794569969723)
        ·
          refine ⟨30665598559880691854954585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20443732373253794569969723 30665598559880691854954585)
          ·
            refine ⟨22999198919910518891215939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30665598559880691854954585 22999198919910518891215939)
            ·
              refine ⟨34498798379865778336823909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22999198919910518891215939 34498798379865778336823909)
              ·
                refine ⟨6468524696224833438154483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34498798379865778336823909 6468524696224833438154483)
                ·
                  refine ⟨9702787044337250157231725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6468524696224833438154483 9702787044337250157231725)
                  ·
                    refine ⟨3638545141626468808961897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9702787044337250157231725 3638545141626468808961897)
                    ·
                      refine ⟨2728908856219851606721423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638545141626468808961897 2728908856219851606721423)
                      ·
                        rfl

theorem cell23_5314531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_5314531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314531 prefixEnd_5314531 := by exact prefixLift 5314531
  have htrace : WordTrace (prefixWord ++ tailWord_5314531) baseStart_5314531 baseEnd_5314531 := by
    simpa [prefixWord, tailWord_5314531, baseEnd_5314531] using wordTrace_append hprefix tailTrace_5314531
  have hstable : (prefixWord ++ tailWord_5314531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314531).length < 2 ^ (prefixWord ++ tailWord_5314531).sum := by decide
  have hdescent : baseEnd_5314531 < baseStart_5314531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314544 : List Nat := [2, 1, 1, 1, 3, 2, 2, 4, 1, 4, 2]
def baseStart_5314544 : Nat := 118140960795 + 5314544 * 2 ^ 59
def prefixEnd_5314544 : Nat := 4983230072969 + 3 ^ 40 * 5314544 * 2
def baseEnd_5314544 : Nat := 2728915531468360055858863

theorem tailTrace_5314544 : CollatzResearch.WordTrace tailWord_5314544 prefixEnd_5314544 2728915531468360055858863 := by
  unfold tailWord_5314544
  simp only [CollatzResearch.WordTrace]
  refine ⟨96918672029161107349227343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129224896038881476465636457 96918672029161107349227343)
  ·
    refine ⟨145378008043741661023841015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96918672029161107349227343 145378008043741661023841015)
    ·
      refine ⟨218067012065612491535761523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145378008043741661023841015 218067012065612491535761523)
      ·
        refine ⟨327100518098418737303642285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218067012065612491535761523 327100518098418737303642285)
        ·
          refine ⟨122662694286907026488865857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 327100518098418737303642285 122662694286907026488865857)
          ·
            refine ⟨91997020715180269866649393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122662694286907026488865857 91997020715180269866649393)
            ·
              refine ⟨68997765536385202399987045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91997020715180269866649393 68997765536385202399987045)
              ·
                refine ⟨12937081038072225449997571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68997765536385202399987045 12937081038072225449997571)
                ·
                  refine ⟨19405621557108338174996357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12937081038072225449997571 19405621557108338174996357)
                  ·
                    refine ⟨3638554041957813407811817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19405621557108338174996357 3638554041957813407811817)
                    ·
                      refine ⟨2728915531468360055858863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638554041957813407811817 2728915531468360055858863)
                      ·
                        rfl

theorem cell23_5314544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 4, 1, 4, 2].length) (baseStart_5314544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314544 prefixEnd_5314544 := by exact prefixLift 5314544
  have htrace : WordTrace (prefixWord ++ tailWord_5314544) baseStart_5314544 baseEnd_5314544 := by
    simpa [prefixWord, tailWord_5314544, baseEnd_5314544] using wordTrace_append hprefix tailTrace_5314544
  have hstable : (prefixWord ++ tailWord_5314544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314544).length < 2 ^ (prefixWord ++ tailWord_5314544).sum := by decide
  have hdescent : baseEnd_5314544 < baseStart_5314544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314557 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_5314557 : Nat := 118140960795 + 5314557 * 2 ^ 59
def prefixEnd_5314557 : Nat := 4983230072969 + 3 ^ 40 * 5314557 * 2
def baseEnd_5314557 : Nat := 2728922206716868504996303

theorem tailTrace_5314557 : CollatzResearch.WordTrace tailWord_5314557 prefixEnd_5314557 2728922206716868504996303 := by
  unfold tailWord_5314557
  simp only [CollatzResearch.WordTrace]
  refine ⟨193837818207275117918677925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129225212138183411945785283 193837818207275117918677925)
  ·
    refine ⟨36344590913864084609752111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 193837818207275117918677925 36344590913864084609752111)
    ·
      refine ⟨54516886370796126914628167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36344590913864084609752111 54516886370796126914628167)
      ·
        refine ⟨81775329556194190371942251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54516886370796126914628167 81775329556194190371942251)
        ·
          refine ⟨122662994334291285557913377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81775329556194190371942251 122662994334291285557913377)
          ·
            refine ⟨91997245750718464168435033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122662994334291285557913377 91997245750718464168435033)
            ·
              refine ⟨68997934313038848126326275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91997245750718464168435033 68997934313038848126326275)
              ·
                refine ⟨103496901469558272189489413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68997934313038848126326275 103496901469558272189489413)
                ·
                  refine ⟨19405669025542176035529265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 103496901469558272189489413 19405669025542176035529265)
                  ·
                    refine ⟨14554251769156632026646949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19405669025542176035529265 14554251769156632026646949)
                    ·
                      refine ⟨2728922206716868504996303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14554251769156632026646949 2728922206716868504996303)
                      ·
                        rfl

theorem cell23_5314557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_5314557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314557 prefixEnd_5314557 := by exact prefixLift 5314557
  have htrace : WordTrace (prefixWord ++ tailWord_5314557) baseStart_5314557 baseEnd_5314557 := by
    simpa [prefixWord, tailWord_5314557, baseEnd_5314557] using wordTrace_append hprefix tailTrace_5314557
  have hstable : (prefixWord ++ tailWord_5314557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314557).length < 2 ^ (prefixWord ++ tailWord_5314557).sum := by decide
  have hdescent : baseEnd_5314557 < baseStart_5314557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314561 : List Nat := [1, 2, 4, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_5314561 : Nat := 118140960795 + 5314561 * 2 ^ 59
def prefixEnd_5314561 : Nat := 4983230072969 + 3 ^ 40 * 5314561 * 2
def baseEnd_5314561 : Nat := 2728924260639486489346285

theorem tailTrace_5314561 : CollatzResearch.WordTrace tailWord_5314561 prefixEnd_5314561 2728924260639486489346285 := by
  unfold tailWord_5314561
  simp only [CollatzResearch.WordTrace]
  refine ⟨193837964099260626601823537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129225309399507084401215691 193837964099260626601823537)
  ·
    refine ⟨145378473074445469951367653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193837964099260626601823537 145378473074445469951367653)
    ·
      refine ⟨27258463701458525615881435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145378473074445469951367653 27258463701458525615881435)
      ·
        refine ⟨40887695552187788423822153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27258463701458525615881435 40887695552187788423822153)
        ·
          refine ⟨30665771664140841317866615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40887695552187788423822153 30665771664140841317866615)
          ·
            refine ⟨45998657496211261976799923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30665771664140841317866615 45998657496211261976799923)
            ·
              refine ⟨68997986244316892965199885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45998657496211261976799923 68997986244316892965199885)
              ·
                refine ⟨25874244841618834861949957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68997986244316892965199885 25874244841618834861949957)
                ·
                  refine ⟨4851420907803531536615617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25874244841618834861949957 4851420907803531536615617)
                  ·
                    refine ⟨3638565680852648652461713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4851420907803531536615617 3638565680852648652461713)
                    ·
                      refine ⟨2728924260639486489346285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638565680852648652461713 2728924260639486489346285)
                      ·
                        rfl

theorem cell23_5314561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_5314561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314561 prefixEnd_5314561 := by exact prefixLift 5314561
  have htrace : WordTrace (prefixWord ++ tailWord_5314561) baseStart_5314561 baseEnd_5314561 := by
    simpa [prefixWord, tailWord_5314561, baseEnd_5314561] using wordTrace_append hprefix tailTrace_5314561
  have hstable : (prefixWord ++ tailWord_5314561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314561).length < 2 ^ (prefixWord ++ tailWord_5314561).sum := by decide
  have hdescent : baseEnd_5314561 < baseStart_5314561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314566 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_5314566 : Nat := 118140960795 + 5314566 * 2 ^ 59
def prefixEnd_5314566 : Nat := 4983230072969 + 3 ^ 40 * 5314566 * 2
def baseEnd_5314566 : Nat := 909642276014252989927921

theorem tailTrace_5314566 : CollatzResearch.WordTrace tailWord_5314566 prefixEnd_5314566 909642276014252989927921 := by
  unfold tailWord_5314566
  simp only [CollatzResearch.WordTrace]
  refine ⟨6057442077007578514242361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 129225430976161674970503701 6057442077007578514242361)
  ·
    refine ⟨4543081557755683885681771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6057442077007578514242361 4543081557755683885681771)
    ·
      refine ⟨6814622336633525828522657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4543081557755683885681771 6814622336633525828522657)
      ·
        refine ⟨5110966752475144371391993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6814622336633525828522657 5110966752475144371391993)
        ·
          refine ⟨3833225064356358278543995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5110966752475144371391993 3833225064356358278543995)
          ·
            refine ⟨5749837596534537417815993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833225064356358278543995 5749837596534537417815993)
            ·
              refine ⟨4312378197400903063361995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5749837596534537417815993 4312378197400903063361995)
              ·
                refine ⟨6468567296101354595042993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312378197400903063361995 6468567296101354595042993)
                ·
                  refine ⟨4851425472076015946282245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6468567296101354595042993 4851425472076015946282245)
                  ·
                    refine ⟨909642276014252989927921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4851425472076015946282245 909642276014252989927921)
                    ·
                      rfl

theorem cell23_5314566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_5314566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314566 prefixEnd_5314566 := by exact prefixLift 5314566
  have htrace : WordTrace (prefixWord ++ tailWord_5314566) baseStart_5314566 baseEnd_5314566 := by
    simpa [prefixWord, tailWord_5314566, baseEnd_5314566] using wordTrace_append hprefix tailTrace_5314566
  have hstable : (prefixWord ++ tailWord_5314566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314566).length < 2 ^ (prefixWord ++ tailWord_5314566).sum := by decide
  have hdescent : baseEnd_5314566 < baseStart_5314566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314612 : List Nat := [2, 5, 1, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_5314612 : Nat := 118140960795 + 5314612 * 2 ^ 59
def prefixEnd_5314612 : Nat := 4983230072969 + 3 ^ 40 * 5314612 * 2
def baseEnd_5314612 : Nat := 2728950448152865789808551

theorem tailTrace_5314612 : CollatzResearch.WordTrace tailWord_5314612 prefixEnd_5314612 2728950448152865789808551 := by
  unfold tailWord_5314612
  simp only [CollatzResearch.WordTrace]
  refine ⟨96919912111037931155965045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129226549481383908207953393 96919912111037931155965045)
  ·
    refine ⟨9086241760409806045871723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 96919912111037931155965045 9086241760409806045871723)
    ·
      refine ⟨13629362640614709068807585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9086241760409806045871723 13629362640614709068807585)
      ·
        refine ⟨10222021980461031801605689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13629362640614709068807585 10222021980461031801605689)
        ·
          refine ⟨7666516485345773851204267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10222021980461031801605689 7666516485345773851204267)
          ·
            refine ⟨11499774728018660776806401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666516485345773851204267 11499774728018660776806401)
            ·
              refine ⟨8624831046013995582604801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11499774728018660776806401 8624831046013995582604801)
              ·
                refine ⟨6468623284510496686953601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8624831046013995582604801 6468623284510496686953601)
                ·
                  refine ⟨4851467463382872515215201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6468623284510496686953601 4851467463382872515215201)
                  ·
                    refine ⟨3638600597537154386411401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4851467463382872515215201 3638600597537154386411401)
                    ·
                      refine ⟨2728950448152865789808551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638600597537154386411401 2728950448152865789808551)
                      ·
                        rfl

theorem cell23_5314612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_5314612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314612 prefixEnd_5314612 := by exact prefixLift 5314612
  have htrace : WordTrace (prefixWord ++ tailWord_5314612) baseStart_5314612 baseEnd_5314612 := by
    simpa [prefixWord, tailWord_5314612, baseEnd_5314612] using wordTrace_append hprefix tailTrace_5314612
  have hstable : (prefixWord ++ tailWord_5314612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314612).length < 2 ^ (prefixWord ++ tailWord_5314612).sum := by decide
  have hdescent : baseEnd_5314612 < baseStart_5314612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314657 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 8]
def baseStart_5314657 : Nat := 118140960795 + 5314657 * 2 ^ 59
def prefixEnd_5314657 : Nat := 4983230072969 + 3 ^ 40 * 5314657 * 2
def baseEnd_5314657 : Nat := 303219283864702012638427

theorem tailTrace_5314657 : CollatzResearch.WordTrace tailWord_5314657 prefixEnd_5314657 303219283864702012638427 := by
  unfold tailWord_5314657
  simp only [CollatzResearch.WordTrace]
  refine ⟨193841465506912834997318225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129227643671275223331545483 193841465506912834997318225)
  ·
    refine ⟨145381099130184626247988669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193841465506912834997318225 145381099130184626247988669)
    ·
      refine ⟨54517912173819234842995751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145381099130184626247988669 54517912173819234842995751)
      ·
        refine ⟨81776868260728852264493627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54517912173819234842995751 81776868260728852264493627)
        ·
          refine ⟨122665302391093278396740441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81776868260728852264493627 122665302391093278396740441)
          ·
            refine ⟨91998976793319958797555331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122665302391093278396740441 91998976793319958797555331)
            ·
              refine ⟨137998465189979938196332997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91998976793319958797555331 137998465189979938196332997)
              ·
                refine ⟨25874712223121238411812437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 137998465189979938196332997 25874712223121238411812437)
                ·
                  refine ⟨303219283864702012638427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25874712223121238411812437 303219283864702012638427)
                  ·
                    rfl

theorem cell23_5314657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 8].length) (baseStart_5314657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314657 prefixEnd_5314657 := by exact prefixLift 5314657
  have htrace : WordTrace (prefixWord ++ tailWord_5314657) baseStart_5314657 baseEnd_5314657 := by
    simpa [prefixWord, tailWord_5314657, baseEnd_5314657] using wordTrace_append hprefix tailTrace_5314657
  have hstable : (prefixWord ++ tailWord_5314657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314657).length < 2 ^ (prefixWord ++ tailWord_5314657).sum := by decide
  have hdescent : baseEnd_5314657 < baseStart_5314657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314674 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 8]
def baseStart_5314674 : Nat := 118140960795 + 5314674 * 2 ^ 59
def prefixEnd_5314674 : Nat := 4983230072969 + 3 ^ 40 * 5314674 * 2
def baseEnd_5314674 : Nat := 303220253772604949692585

theorem tailTrace_5314674 : CollatzResearch.WordTrace tailWord_5314674 prefixEnd_5314674 303220253772604949692585 := by
  unfold tailWord_5314674
  simp only [CollatzResearch.WordTrace]
  refine ⟨48460521386962811725171769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129228057031900831267124717 48460521386962811725171769)
  ·
    refine ⟨36345391040222108793878827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48460521386962811725171769 36345391040222108793878827)
    ·
      refine ⟨54518086560333163190818241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36345391040222108793878827 54518086560333163190818241)
      ·
        refine ⟨40888564920249872393113681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54518086560333163190818241 40888564920249872393113681)
        ·
          refine ⟨30666423690187404294835261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40888564920249872393113681 30666423690187404294835261)
          ·
            refine ⟨11499908883820276610563223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30666423690187404294835261 11499908883820276610563223)
            ·
              refine ⟨17249863325730414915844835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11499908883820276610563223 17249863325730414915844835)
              ·
                refine ⟨25874794988595622373767253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17249863325730414915844835 25874794988595622373767253)
                ·
                  refine ⟨303220253772604949692585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 25874794988595622373767253 303220253772604949692585)
                  ·
                    rfl

theorem cell23_5314674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_5314674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314674 prefixEnd_5314674 := by exact prefixLift 5314674
  have htrace : WordTrace (prefixWord ++ tailWord_5314674) baseStart_5314674 baseEnd_5314674 := by
    simpa [prefixWord, tailWord_5314674, baseEnd_5314674] using wordTrace_append hprefix tailTrace_5314674
  have hstable : (prefixWord ++ tailWord_5314674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314674).length < 2 ^ (prefixWord ++ tailWord_5314674).sum := by decide
  have hdescent : baseEnd_5314674 < baseStart_5314674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314678 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_5314678 : Nat := 118140960795 + 5314678 * 2 ^ 59
def prefixEnd_5314678 : Nat := 4983230072969 + 3 ^ 40 * 5314678 * 2
def baseEnd_5314678 : Nat := 909661445958687510527749

theorem tailTrace_5314678 : CollatzResearch.WordTrace tailWord_5314678 prefixEnd_5314678 909661445958687510527749 := by
  unfold tailWord_5314678
  simp only [CollatzResearch.WordTrace]
  refine ⟨12115139464989797223989543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 129228154293224503722555125 12115139464989797223989543)
  ·
    refine ⟨18172709197484695835984315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12115139464989797223989543 18172709197484695835984315)
    ·
      refine ⟨27259063796227043753976473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18172709197484695835984315 27259063796227043753976473)
      ·
        refine ⟨20444297847170282815482355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27259063796227043753976473 20444297847170282815482355)
        ·
          refine ⟨30666446770755424223223533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20444297847170282815482355 30666446770755424223223533)
          ·
            refine ⟨11499917539033284083708825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30666446770755424223223533 11499917539033284083708825)
            ·
              refine ⟨8624938154274963062781619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11499917539033284083708825 8624938154274963062781619)
              ·
                refine ⟨12937407231412444594172429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8624938154274963062781619 12937407231412444594172429)
                ·
                  refine ⟨4851527711779666722814661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12937407231412444594172429 4851527711779666722814661)
                  ·
                    refine ⟨909661445958687510527749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4851527711779666722814661 909661445958687510527749)
                    ·
                      rfl

theorem cell23_5314678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_5314678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314678 prefixEnd_5314678 := by exact prefixLift 5314678
  have htrace : WordTrace (prefixWord ++ tailWord_5314678) baseStart_5314678 baseEnd_5314678 := by
    simpa [prefixWord, tailWord_5314678, baseEnd_5314678] using wordTrace_append hprefix tailTrace_5314678
  have hstable : (prefixWord ++ tailWord_5314678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314678).length < 2 ^ (prefixWord ++ tailWord_5314678).sum := by decide
  have hdescent : baseEnd_5314678 < baseStart_5314678 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314691 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 6]
def baseStart_5314691 : Nat := 118140960795 + 5314691 * 2 ^ 59
def prefixEnd_5314691 : Nat := 4983230072969 + 3 ^ 40 * 5314691 * 2
def baseEnd_5314691 : Nat := 303221223680507886746743

theorem tailTrace_5314691 : CollatzResearch.WordTrace tailWord_5314691 prefixEnd_5314691 303221223680507886746743 := by
  unfold tailWord_5314691
  simp only [CollatzResearch.WordTrace]
  refine ⟨193842705588789658804055927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129228470392526439202703951 193842705588789658804055927)
  ·
    refine ⟨290764058383184488206083891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193842705588789658804055927 290764058383184488206083891)
    ·
      refine ⟨436146087574776732309125837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290764058383184488206083891 436146087574776732309125837)
      ·
        refine ⟨163554782840541274615922189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436146087574776732309125837 163554782840541274615922189)
        ·
          refine ⟨61333043565202977980970821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163554782840541274615922189 61333043565202977980970821)
          ·
            refine ⟨11499945668475558371432029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61333043565202977980970821 11499945668475558371432029)
            ·
              refine ⟨4312479625678334389287011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11499945668475558371432029 4312479625678334389287011)
              ·
                refine ⟨6468719438517501583930517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312479625678334389287011 6468719438517501583930517)
                ·
                  refine ⟨303221223680507886746743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6468719438517501583930517 303221223680507886746743)
                  ·
                    rfl

theorem cell23_5314691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 6].length) (baseStart_5314691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314691 prefixEnd_5314691 := by exact prefixLift 5314691
  have htrace : WordTrace (prefixWord ++ tailWord_5314691) baseStart_5314691 baseEnd_5314691 := by
    simpa [prefixWord, tailWord_5314691, baseEnd_5314691] using wordTrace_append hprefix tailTrace_5314691
  have hstable : (prefixWord ++ tailWord_5314691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314691).length < 2 ^ (prefixWord ++ tailWord_5314691).sum := by decide
  have hdescent : baseEnd_5314691 < baseStart_5314691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314712 : List Nat := [2, 1, 2, 4, 4, 1, 1, 3, 1, 4]
def baseStart_5314712 : Nat := 118140960795 + 5314712 * 2 ^ 59
def prefixEnd_5314712 : Nat := 4983230072969 + 3 ^ 40 * 5314712 * 2
def baseEnd_5314712 : Nat := 909667265406105132852697

theorem tailTrace_5314712 : CollatzResearch.WordTrace tailWord_5314712 prefixEnd_5314712 909667265406105132852697 := by
  unfold tailWord_5314712
  simp only [CollatzResearch.WordTrace]
  refine ⟨96921735760856789695285195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129228981014475719593713593 96921735760856789695285195)
  ·
    refine ⟨145382603641285184542927793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96921735760856789695285195 145382603641285184542927793)
    ·
      refine ⟨109036952730963888407195845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145382603641285184542927793 109036952730963888407195845)
      ·
        refine ⟨20444428637055729076349221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109036952730963888407195845 20444428637055729076349221)
        ·
          refine ⟨3833330369447949201815479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20444428637055729076349221 3833330369447949201815479)
          ·
            refine ⟨5749995554171923802723219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833330369447949201815479 5749995554171923802723219)
            ·
              refine ⟨8624993331257885704084829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5749995554171923802723219 8624993331257885704084829)
              ·
                refine ⟨3234372499221707139031811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8624993331257885704084829 3234372499221707139031811)
                ·
                  refine ⟨4851558748832560708547717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234372499221707139031811 4851558748832560708547717)
                  ·
                    refine ⟨909667265406105132852697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4851558748832560708547717 909667265406105132852697)
                    ·
                      rfl

theorem cell23_5314712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_5314712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314712 prefixEnd_5314712 := by exact prefixLift 5314712
  have htrace : WordTrace (prefixWord ++ tailWord_5314712) baseStart_5314712 baseEnd_5314712 := by
    simpa [prefixWord, tailWord_5314712, baseEnd_5314712] using wordTrace_append hprefix tailTrace_5314712
  have hstable : (prefixWord ++ tailWord_5314712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314712).length < 2 ^ (prefixWord ++ tailWord_5314712).sum := by decide
  have hdescent : baseEnd_5314712 < baseStart_5314712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314721 : List Nat := [1, 2, 3, 3, 1, 2, 2, 3, 1, 5]
def baseStart_5314721 : Nat := 118140960795 + 5314721 * 2 ^ 59
def prefixEnd_5314721 : Nat := 4983230072969 + 3 ^ 40 * 5314721 * 2
def baseEnd_5314721 : Nat := 909668805848068621115183

theorem tailTrace_5314721 : CollatzResearch.WordTrace tailWord_5314721 prefixEnd_5314721 909668805848068621115183 := by
  unfold tailWord_5314721
  simp only [CollatzResearch.WordTrace]
  refine ⟨193843799778680973927648017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129229199852453982618432011 193843799778680973927648017)
  ·
    refine ⟨145382849834010730445736013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193843799778680973927648017 145382849834010730445736013)
    ·
      refine ⟨54518568687754023917151005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145382849834010730445736013 54518568687754023917151005)
      ·
        refine ⟨20444463257907758968931627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54518568687754023917151005 20444463257907758968931627)
        ·
          refine ⟨30666694886861638453397441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20444463257907758968931627 30666694886861638453397441)
          ·
            refine ⟨23000021165146228840048081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30666694886861638453397441 23000021165146228840048081)
            ·
              refine ⟨17250015873859671630036061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23000021165146228840048081 17250015873859671630036061)
              ·
                refine ⟨6468755952697376861263523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17250015873859671630036061 6468755952697376861263523)
                ·
                  refine ⟨9703133929046065291895285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6468755952697376861263523 9703133929046065291895285)
                  ·
                    refine ⟨909668805848068621115183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9703133929046065291895285 909668805848068621115183)
                    ·
                      rfl

theorem cell23_5314721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 3, 1, 5].length) (baseStart_5314721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314721 prefixEnd_5314721 := by exact prefixLift 5314721
  have htrace : WordTrace (prefixWord ++ tailWord_5314721) baseStart_5314721 baseEnd_5314721 := by
    simpa [prefixWord, tailWord_5314721, baseEnd_5314721] using wordTrace_append hprefix tailTrace_5314721
  have hstable : (prefixWord ++ tailWord_5314721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314721).length < 2 ^ (prefixWord ++ tailWord_5314721).sum := by decide
  have hdescent : baseEnd_5314721 < baseStart_5314721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314744 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 1, 1, 5]
def baseStart_5314744 : Nat := 118140960795 + 5314744 * 2 ^ 59
def prefixEnd_5314744 : Nat := 4983230072969 + 3 ^ 40 * 5314744 * 2
def baseEnd_5314744 : Nat := 2729018227599259273357943

theorem tailTrace_5314744 : CollatzResearch.WordTrace tailWord_5314744 prefixEnd_5314744 2729018227599259273357943 := by
  unfold tailWord_5314744
  simp only [CollatzResearch.WordTrace]
  refine ⟨96922319328798824427867643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129229759105065099237156857 96922319328798824427867643)
  ·
    refine ⟨145383478993198236641801465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96922319328798824427867643 145383478993198236641801465)
    ·
      refine ⟨109037609244898677481351099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145383478993198236641801465 109037609244898677481351099)
      ·
        refine ⟨163556413867348016222026649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109037609244898677481351099 163556413867348016222026649)
        ·
          refine ⟨122667310400511012166519987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163556413867348016222026649 122667310400511012166519987)
          ·
            refine ⟨184000965600766518249779981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122667310400511012166519987 184000965600766518249779981)
            ·
              refine ⟨69000362100287444343667493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184000965600766518249779981 69000362100287444343667493)
              ·
                refine ⟨12937567893803895814437655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69000362100287444343667493 12937567893803895814437655)
                ·
                  refine ⟨19406351840705843721656483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12937567893803895814437655 19406351840705843721656483)
                  ·
                    refine ⟨29109527761058765582484725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19406351840705843721656483 29109527761058765582484725)
                    ·
                      refine ⟨2729018227599259273357943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29109527761058765582484725 2729018227599259273357943)
                      ·
                        rfl

theorem cell23_5314744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 1, 5].length) (baseStart_5314744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314744 prefixEnd_5314744 := by exact prefixLift 5314744
  have htrace : WordTrace (prefixWord ++ tailWord_5314744) baseStart_5314744 baseEnd_5314744 := by
    simpa [prefixWord, tailWord_5314744, baseEnd_5314744] using wordTrace_append hprefix tailTrace_5314744
  have hstable : (prefixWord ++ tailWord_5314744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314744).length < 2 ^ (prefixWord ++ tailWord_5314744).sum := by decide
  have hdescent : baseEnd_5314744 < baseStart_5314744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314761 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 3]
def baseStart_5314761 : Nat := 118140960795 + 5314761 * 2 ^ 59
def prefixEnd_5314761 : Nat := 4983230072969 + 3 ^ 40 * 5314761 * 2
def baseEnd_5314761 : Nat := 2729026956770385706845365

theorem tailTrace_5314761 : CollatzResearch.WordTrace tailWord_5314761 prefixEnd_5314761 2729026956770385706845365 := by
  unfold tailWord_5314761
  simp only [CollatzResearch.WordTrace]
  refine ⟨193845258698536060759104137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129230172465690707172736091 193845258698536060759104137)
  ·
    refine ⟨145383944023902045569328103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193845258698536060759104137 145383944023902045569328103)
    ·
      refine ⟨218075916035853068353992155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145383944023902045569328103 218075916035853068353992155)
      ·
        refine ⟨327113874053779602530988233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218075916035853068353992155 327113874053779602530988233)
        ·
          refine ⟨245335405540334701898241175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 327113874053779602530988233 245335405540334701898241175)
          ·
            refine ⟨368003108310502052847361763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245335405540334701898241175 368003108310502052847361763)
            ·
              refine ⟨552004662465753079271042645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368003108310502052847361763 552004662465753079271042645)
              ·
                refine ⟨6468804638270543897707531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 552004662465753079271042645 6468804638270543897707531)
                ·
                  refine ⟨9703206957405815846561297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6468804638270543897707531 9703206957405815846561297)
                  ·
                    refine ⟨7277405218054361884920973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9703206957405815846561297 7277405218054361884920973)
                    ·
                      refine ⟨2729026956770385706845365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7277405218054361884920973 2729026956770385706845365)
                      ·
                        rfl

theorem cell23_5314761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 1, 2, 3].length) (baseStart_5314761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314761 prefixEnd_5314761 := by exact prefixLift 5314761
  have htrace : WordTrace (prefixWord ++ tailWord_5314761) baseStart_5314761 baseEnd_5314761 := by
    simpa [prefixWord, tailWord_5314761, baseEnd_5314761] using wordTrace_append hprefix tailTrace_5314761
  have hstable : (prefixWord ++ tailWord_5314761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314761).length < 2 ^ (prefixWord ++ tailWord_5314761).sum := by decide
  have hdescent : baseEnd_5314761 < baseStart_5314761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314775 : List Nat := [1, 1, 3, 2, 1, 2, 1, 7, 1, 2, 2]
def baseStart_5314775 : Nat := 118140960795 + 5314775 * 2 ^ 59
def prefixEnd_5314775 : Nat := 4983230072969 + 3 ^ 40 * 5314775 * 2
def baseEnd_5314775 : Nat := 2729034145499548652070301

theorem tailTrace_5314775 : CollatzResearch.WordTrace tailWord_5314775 prefixEnd_5314775 2729034145499548652070301 := by
  unfold tailWord_5314775
  simp only [CollatzResearch.WordTrace]
  refine ⟨193845769320485341150113779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129230512880323560766742519 193845769320485341150113779)
  ·
    refine ⟨290768653980728011725170669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193845769320485341150113779 290768653980728011725170669)
    ·
      refine ⟨109038245242773004396939001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290768653980728011725170669 109038245242773004396939001)
      ·
        refine ⟨81778683932079753297704251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109038245242773004396939001 81778683932079753297704251)
        ·
          refine ⟨122668025898119629946556377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81778683932079753297704251 122668025898119629946556377)
          ·
            refine ⟨92001019423589722459917283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122668025898119629946556377 92001019423589722459917283)
            ·
              refine ⟨138001529135384583689875925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92001019423589722459917283 138001529135384583689875925)
              ·
                refine ⟨3234410839110576180231467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 138001529135384583689875925 3234410839110576180231467)
                ·
                  refine ⟨4851616258665864270347201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234410839110576180231467 4851616258665864270347201)
                  ·
                    refine ⟨3638712193999398202760401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4851616258665864270347201 3638712193999398202760401)
                    ·
                      refine ⟨2729034145499548652070301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638712193999398202760401 2729034145499548652070301)
                      ·
                        rfl

theorem cell23_5314775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_5314775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314775 prefixEnd_5314775 := by exact prefixLift 5314775
  have htrace : WordTrace (prefixWord ++ tailWord_5314775) baseStart_5314775 baseEnd_5314775 := by
    simpa [prefixWord, tailWord_5314775, baseEnd_5314775] using wordTrace_append hprefix tailTrace_5314775
  have hstable : (prefixWord ++ tailWord_5314775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314775).length < 2 ^ (prefixWord ++ tailWord_5314775).sum := by decide
  have hdescent : baseEnd_5314775 < baseStart_5314775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314786 : List Nat := [3, 3, 4, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_5314786 : Nat := 118140960795 + 5314786 * 2 ^ 59
def prefixEnd_5314786 : Nat := 4983230072969 + 3 ^ 40 * 5314786 * 2
def baseEnd_5314786 : Nat := 2729039793786748109032751

theorem tailTrace_5314786 : CollatzResearch.WordTrace tailWord_5314786 prefixEnd_5314786 2729039793786748109032751 := by
  unfold tailWord_5314786
  simp only [CollatzResearch.WordTrace]
  refine ⟨48461542630861372507191053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129230780348963660019176141 48461542630861372507191053)
  ·
    refine ⟨18173078486573014690196645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48461542630861372507191053 18173078486573014690196645)
    ·
      refine ⟨3407452216232440254411871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18173078486573014690196645 3407452216232440254411871)
      ·
        refine ⟨5111178324348660381617807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407452216232440254411871 5111178324348660381617807)
        ·
          refine ⟨7666767486522990572426711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111178324348660381617807 7666767486522990572426711)
          ·
            refine ⟨11500151229784485858640067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7666767486522990572426711 11500151229784485858640067)
            ·
              refine ⟨17250226844676728787960101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11500151229784485858640067 17250226844676728787960101)
              ·
                refine ⟨3234417533376886647742519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17250226844676728787960101 3234417533376886647742519)
                ·
                  refine ⟨4851626300065329971613779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234417533376886647742519 4851626300065329971613779)
                  ·
                    refine ⟨7277439450097994957420669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4851626300065329971613779 7277439450097994957420669)
                    ·
                      refine ⟨2729039793786748109032751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7277439450097994957420669 2729039793786748109032751)
                      ·
                        rfl

theorem cell23_5314786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_5314786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314786 prefixEnd_5314786 := by exact prefixLift 5314786
  have htrace : WordTrace (prefixWord ++ tailWord_5314786) baseStart_5314786 baseEnd_5314786 := by
    simpa [prefixWord, tailWord_5314786, baseEnd_5314786] using wordTrace_append hprefix tailTrace_5314786
  have hstable : (prefixWord ++ tailWord_5314786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314786).length < 2 ^ (prefixWord ++ tailWord_5314786).sum := by decide
  have hdescent : baseEnd_5314786 < baseStart_5314786 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314792 : List Nat := [2, 1, 4, 1, 2, 3, 1, 4, 1, 2, 2]
def baseStart_5314792 : Nat := 118140960795 + 5314792 * 2 ^ 59
def prefixEnd_5314792 : Nat := 4983230072969 + 3 ^ 40 * 5314792 * 2
def baseEnd_5314792 : Nat := 2729042874670675085557723

theorem tailTrace_5314792 : CollatzResearch.WordTrace tailWord_5314792 prefixEnd_5314792 2729042874670675085557723 := by
  unfold tailWord_5314792
  simp only [CollatzResearch.WordTrace]
  refine ⟨96923194680711876526741315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129230926240949168702321753 96923194680711876526741315)
  ·
    refine ⟨145384792021067814790111973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96923194680711876526741315 145384792021067814790111973)
    ·
      refine ⟨27259648503950215273145995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 145384792021067814790111973 27259648503950215273145995)
      ·
        refine ⟨40889472755925322909718993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27259648503950215273145995 40889472755925322909718993)
        ·
          refine ⟨30667104566943992182289245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40889472755925322909718993 30667104566943992182289245)
          ·
            refine ⟨11500164212603997068358467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30667104566943992182289245 11500164212603997068358467)
            ·
              refine ⟨17250246318905995602537701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11500164212603997068358467 17250246318905995602537701)
              ·
                refine ⟨3234421184794874175475819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17250246318905995602537701 3234421184794874175475819)
                ·
                  refine ⟨4851631777192311263213729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3234421184794874175475819 4851631777192311263213729)
                  ·
                    refine ⟨3638723832894233447410297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4851631777192311263213729 3638723832894233447410297)
                    ·
                      refine ⟨2729042874670675085557723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638723832894233447410297 2729042874670675085557723)
                      ·
                        rfl

theorem cell23_5314792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_5314792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314792 prefixEnd_5314792 := by exact prefixLift 5314792
  have htrace : WordTrace (prefixWord ++ tailWord_5314792) baseStart_5314792 baseEnd_5314792 := by
    simpa [prefixWord, tailWord_5314792, baseEnd_5314792] using wordTrace_append hprefix tailTrace_5314792
  have hstable : (prefixWord ++ tailWord_5314792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314792).length < 2 ^ (prefixWord ++ tailWord_5314792).sum := by decide
  have hdescent : baseEnd_5314792 < baseStart_5314792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314794 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 1, 9]
def baseStart_5314794 : Nat := 118140960795 + 5314794 * 2 ^ 59
def prefixEnd_5314794 : Nat := 4983230072969 + 3 ^ 40 * 5314794 * 2
def baseEnd_5314794 : Nat := 909681300543994692577571

theorem tailTrace_5314794 : CollatzResearch.WordTrace tailWord_5314794 prefixEnd_5314794 909681300543994692577571 := by
  unfold tailWord_5314794
  simp only [CollatzResearch.WordTrace]
  refine ⟨48461615576854126848763859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129230974871611004930036957 48461615576854126848763859)
  ·
    refine ⟨72692423365281190273145789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48461615576854126848763859 72692423365281190273145789)
    ·
      refine ⟨27259658761980446352429671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72692423365281190273145789 27259658761980446352429671)
      ·
        refine ⟨40889488142970669528644507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27259658761980446352429671 40889488142970669528644507)
        ·
          refine ⟨61334232214456004292966761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40889488142970669528644507 61334232214456004292966761)
          ·
            refine ⟨46000674160842003219725071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61334232214456004292966761 46000674160842003219725071)
            ·
              refine ⟨69001011241263004829587607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46000674160842003219725071 69001011241263004829587607)
              ·
                refine ⟨103501516861894507244381411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69001011241263004829587607 103501516861894507244381411)
                ·
                  refine ⟨155252275292841760866572117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103501516861894507244381411 155252275292841760866572117)
                  ·
                    refine ⟨909681300543994692577571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 155252275292841760866572117 909681300543994692577571)
                    ·
                      rfl

theorem cell23_5314794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_5314794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314794 prefixEnd_5314794 := by exact prefixLift 5314794
  have htrace : WordTrace (prefixWord ++ tailWord_5314794) baseStart_5314794 baseEnd_5314794 := by
    simpa [prefixWord, tailWord_5314794, baseEnd_5314794] using wordTrace_append hprefix tailTrace_5314794
  have hstable : (prefixWord ++ tailWord_5314794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314794).length < 2 ^ (prefixWord ++ tailWord_5314794).sum := by decide
  have hdescent : baseEnd_5314794 < baseStart_5314794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314842 : List Nat := [3, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3]
def baseStart_5314842 : Nat := 118140960795 + 5314842 * 2 ^ 59
def prefixEnd_5314842 : Nat := 4983230072969 + 3 ^ 40 * 5314842 * 2
def baseEnd_5314842 : Nat := 2729068548703399889932493

theorem tailTrace_5314842 : CollatzResearch.WordTrace tailWord_5314842 prefixEnd_5314842 2729068548703399889932493 := by
  unfold tailWord_5314842
  simp only [CollatzResearch.WordTrace]
  refine ⟨48462053252810652898200695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129232142007495074395201853 48462053252810652898200695)
  ·
    refine ⟨72693079879215979347301043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48462053252810652898200695 72693079879215979347301043)
    ·
      refine ⟨109039619818823969020951565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72693079879215979347301043 109039619818823969020951565)
      ·
        refine ⟨40889857432058988382856837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109039619818823969020951565 40889857432058988382856837)
        ·
          refine ⟨7666848268511060321785657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40889857432058988382856837 7666848268511060321785657)
          ·
            refine ⟨5750136201383295241339243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7666848268511060321785657 5750136201383295241339243)
            ·
              refine ⟨8625204302074942862008865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750136201383295241339243 8625204302074942862008865)
              ·
                refine ⟨6468903226556207146506649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8625204302074942862008865 6468903226556207146506649)
                ·
                  refine ⟨4851677419917155359879987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6468903226556207146506649 4851677419917155359879987)
                  ·
                    refine ⟨7277516129875733039819981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4851677419917155359879987 7277516129875733039819981)
                    ·
                      refine ⟨2729068548703399889932493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7277516129875733039819981 2729068548703399889932493)
                      ·
                        rfl

theorem cell23_5314842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_5314842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314842 prefixEnd_5314842 := by exact prefixLift 5314842
  have htrace : WordTrace (prefixWord ++ tailWord_5314842) baseStart_5314842 baseEnd_5314842 := by
    simpa [prefixWord, tailWord_5314842, baseEnd_5314842] using wordTrace_append hprefix tailTrace_5314842
  have hstable : (prefixWord ++ tailWord_5314842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314842).length < 2 ^ (prefixWord ++ tailWord_5314842).sum := by decide
  have hdescent : baseEnd_5314842 < baseStart_5314842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314888 : List Nat := [2, 1, 3, 1, 1, 2, 5, 3, 5]
def baseStart_5314888 : Nat := 118140960795 + 5314888 * 2 ^ 59
def prefixEnd_5314888 : Nat := 4983230072969 + 3 ^ 40 * 5314888 * 2
def baseEnd_5314888 : Nat := 303232463201500745550809

theorem tailTrace_5314888 : CollatzResearch.WordTrace tailWord_5314888 prefixEnd_5314888 303232463201500745550809 := by
  unfold tailWord_5314888
  simp only [CollatzResearch.WordTrace]
  refine ⟨96924945384537980724488659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129233260512717307632651545 96924945384537980724488659)
  ·
    refine ⟨145387418076806971086732989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96924945384537980724488659 145387418076806971086732989)
    ·
      refine ⟨54520281778802614157524871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145387418076806971086732989 54520281778802614157524871)
      ·
        refine ⟨81780422668203921236287307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54520281778802614157524871 81780422668203921236287307)
        ·
          refine ⟨122670634002305881854430961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81780422668203921236287307 122670634002305881854430961)
          ·
            refine ⟨92002975501729411390823221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122670634002305881854430961 92002975501729411390823221)
            ·
              refine ⟨8625278953287132317889677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92002975501729411390823221 8625278953287132317889677)
              ·
                refine ⟨3234479607482674619208629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8625278953287132317889677 3234479607482674619208629)
                ·
                  refine ⟨303232463201500745550809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3234479607482674619208629 303232463201500745550809)
                  ·
                    rfl

theorem cell23_5314888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 5, 3, 5].length) (baseStart_5314888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314888 prefixEnd_5314888 := by exact prefixLift 5314888
  have htrace : WordTrace (prefixWord ++ tailWord_5314888) baseStart_5314888 baseEnd_5314888 := by
    simpa [prefixWord, tailWord_5314888, baseEnd_5314888] using wordTrace_append hprefix tailTrace_5314888
  have hstable : (prefixWord ++ tailWord_5314888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314888).length < 2 ^ (prefixWord ++ tailWord_5314888).sum := by decide
  have hdescent : baseEnd_5314888 < baseStart_5314888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314910 : List Nat := [4, 4, 2, 1, 1, 2, 2, 1, 2, 1, 3]
def baseStart_5314910 : Nat := 118140960795 + 5314910 * 2 ^ 59
def prefixEnd_5314910 : Nat := 4983230072969 + 3 ^ 40 * 5314910 * 2
def baseEnd_5314910 : Nat := 2729103465387905623882181

theorem tailTrace_5314910 : CollatzResearch.WordTrace tailWord_5314910 prefixEnd_5314910 2729103465387905623882181 := by
  unfold tailWord_5314910
  simp only [CollatzResearch.WordTrace]
  refine ⟨24231336646874532400784773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129233795449997506137518789 24231336646874532400784773)
  ·
    refine ⟨4543375621288974825147145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24231336646874532400784773 4543375621288974825147145)
    ·
      refine ⟨3407531715966731118860359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4543375621288974825147145 3407531715966731118860359)
      ·
        refine ⟨5111297573950096678290539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407531715966731118860359 5111297573950096678290539)
        ·
          refine ⟨7666946360925145017435809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111297573950096678290539 7666946360925145017435809)
          ·
            refine ⟨5750209770693858763076857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7666946360925145017435809 5750209770693858763076857)
            ·
              refine ⟨4312657328020394072307643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5750209770693858763076857 4312657328020394072307643)
              ·
                refine ⟨6468985992030591108461465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312657328020394072307643 6468985992030591108461465)
                ·
                  refine ⟨4851739494022943331346099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6468985992030591108461465 4851739494022943331346099)
                  ·
                    refine ⟨7277609241034414997019149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4851739494022943331346099 7277609241034414997019149)
                    ·
                      refine ⟨2729103465387905623882181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7277609241034414997019149 2729103465387905623882181)
                      ·
                        rfl

theorem cell23_5314910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_5314910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314910 prefixEnd_5314910 := by exact prefixLift 5314910
  have htrace : WordTrace (prefixWord ++ tailWord_5314910) baseStart_5314910 baseEnd_5314910 := by
    simpa [prefixWord, tailWord_5314910, baseEnd_5314910] using wordTrace_append hprefix tailTrace_5314910
  have hstable : (prefixWord ++ tailWord_5314910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314910).length < 2 ^ (prefixWord ++ tailWord_5314910).sum := by decide
  have hdescent : baseEnd_5314910 < baseStart_5314910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314921 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 4]
def baseStart_5314921 : Nat := 118140960795 + 5314921 * 2 ^ 59
def prefixEnd_5314921 : Nat := 4983230072969 + 3 ^ 40 * 5314921 * 2
def baseEnd_5314921 : Nat := 2729109113675105080844629

theorem tailTrace_5314921 : CollatzResearch.WordTrace tailWord_5314921 prefixEnd_5314921 2729109113675105080844629 := by
  unfold tailWord_5314921
  simp only [CollatzResearch.WordTrace]
  refine ⟨193851094377956408084928617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129234062918637605389952411 193851094377956408084928617)
  ·
    refine ⟨145388320783467306063696463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193851094377956408084928617 145388320783467306063696463)
    ·
      refine ⟨218082481175200959095544695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145388320783467306063696463 218082481175200959095544695)
      ·
        refine ⟨327123721762801438643317043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 218082481175200959095544695 327123721762801438643317043)
        ·
          refine ⟨490685582644202157964975565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 327123721762801438643317043 490685582644202157964975565)
          ·
            refine ⟨184007093491575809236865837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 490685582644202157964975565 184007093491575809236865837)
            ·
              refine ⟨69002660059340928463824689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 184007093491575809236865837 69002660059340928463824689)
              ·
                refine ⟨51751995044505696347868517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69002660059340928463824689 51751995044505696347868517)
                ·
                  refine ⟨9703499070844818065225347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51751995044505696347868517 9703499070844818065225347)
                  ·
                    refine ⟨14555248606267227097838021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9703499070844818065225347 14555248606267227097838021)
                    ·
                      refine ⟨2729109113675105080844629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14555248606267227097838021 2729109113675105080844629)
                      ·
                        rfl

theorem cell23_5314921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 4, 1, 4].length) (baseStart_5314921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314921 prefixEnd_5314921 := by exact prefixLift 5314921
  have htrace : WordTrace (prefixWord ++ tailWord_5314921) baseStart_5314921 baseEnd_5314921 := by
    simpa [prefixWord, tailWord_5314921, baseEnd_5314921] using wordTrace_append hprefix tailTrace_5314921
  have hstable : (prefixWord ++ tailWord_5314921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314921).length < 2 ^ (prefixWord ++ tailWord_5314921).sum := by decide
  have hdescent : baseEnd_5314921 < baseStart_5314921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314951 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 6]
def baseStart_5314951 : Nat := 118140960795 + 5314951 * 2 ^ 59
def prefixEnd_5314951 : Nat := 4983230072969 + 3 ^ 40 * 5314951 * 2
def baseEnd_5314951 : Nat := 2729124518094739963469491

theorem tailTrace_5314951 : CollatzResearch.WordTrace tailWord_5314951 prefixEnd_5314951 2729124518094739963469491 := by
  unfold tailWord_5314951
  simp only [CollatzResearch.WordTrace]
  refine ⟨193852188567847723208520707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129234792378565148805680471 193852188567847723208520707)
  ·
    refine ⟨290778282851771584812781061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193852188567847723208520707 290778282851771584812781061)
    ·
      refine ⟨54520928034707172152396449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 290778282851771584812781061 54520928034707172152396449)
      ·
        refine ⟨40890696026030379114297337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54520928034707172152396449 40890696026030379114297337)
        ·
          refine ⟨30668022019522784335723003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40890696026030379114297337 30668022019522784335723003)
          ·
            refine ⟨46002033029284176503584505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30668022019522784335723003 46002033029284176503584505)
            ·
              refine ⟨34501524771963132377688379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46002033029284176503584505 34501524771963132377688379)
              ·
                refine ⟨51752287157944698566532569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34501524771963132377688379 51752287157944698566532569)
                ·
                  refine ⟨38814215368458523924899427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51752287157944698566532569 38814215368458523924899427)
                  ·
                    refine ⟨58221323052687785887349141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 38814215368458523924899427 58221323052687785887349141)
                    ·
                      refine ⟨2729124518094739963469491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58221323052687785887349141 2729124518094739963469491)
                      ·
                        rfl

theorem cell23_5314951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_5314951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314951 prefixEnd_5314951 := by exact prefixLift 5314951
  have htrace : WordTrace (prefixWord ++ tailWord_5314951) baseStart_5314951 baseEnd_5314951 := by
    simpa [prefixWord, tailWord_5314951, baseEnd_5314951] using wordTrace_append hprefix tailTrace_5314951
  have hstable : (prefixWord ++ tailWord_5314951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314951).length < 2 ^ (prefixWord ++ tailWord_5314951).sum := by decide
  have hdescent : baseEnd_5314951 < baseStart_5314951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314978 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 6]
def baseStart_5314978 : Nat := 118140960795 + 5314978 * 2 ^ 59
def prefixEnd_5314978 : Nat := 4983230072969 + 3 ^ 40 * 5314978 * 2
def baseEnd_5314978 : Nat := 303237598008045706425763

theorem tailTrace_5314978 : CollatzResearch.WordTrace tailWord_5314978 prefixEnd_5314978 303237598008045706425763 := by
  unfold tailWord_5314978
  simp only [CollatzResearch.WordTrace]
  refine ⟨48463293334687476704938397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129235448892499937879835725 48463293334687476704938397)
  ·
    refine ⟨18173735000507803764351899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48463293334687476704938397 18173735000507803764351899)
    ·
      refine ⟨27260602500761705646527849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18173735000507803764351899 27260602500761705646527849)
      ·
        refine ⟨20445451875571279234895887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27260602500761705646527849 20445451875571279234895887)
        ·
          refine ⟨30668177813356918852343831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20445451875571279234895887 30668177813356918852343831)
          ·
            refine ⟨46002266720035378278515747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30668177813356918852343831 46002266720035378278515747)
            ·
              refine ⟨69003400080053067417773621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46002266720035378278515747 69003400080053067417773621)
              ·
                refine ⟨6469068757504975070416277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69003400080053067417773621 6469068757504975070416277)
                ·
                  refine ⟨303237598008045706425763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6469068757504975070416277 303237598008045706425763)
                  ·
                    rfl

theorem cell23_5314978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 6].length) (baseStart_5314978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314978 prefixEnd_5314978 := by exact prefixLift 5314978
  have htrace : WordTrace (prefixWord ++ tailWord_5314978) baseStart_5314978 baseEnd_5314978 := by
    simpa [prefixWord, tailWord_5314978, baseEnd_5314978] using wordTrace_append hprefix tailTrace_5314978
  have hstable : (prefixWord ++ tailWord_5314978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314978).length < 2 ^ (prefixWord ++ tailWord_5314978).sum := by decide
  have hdescent : baseEnd_5314978 < baseStart_5314978 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314986 : List Nat := [3, 1, 6, 1, 2, 1, 1, 1, 2, 5]
def baseStart_5314986 : Nat := 118140960795 + 5314986 * 2 ^ 59
def prefixEnd_5314986 : Nat := 4983230072969 + 3 ^ 40 * 5314986 * 2
def baseEnd_5314986 : Nat := 909714163305882442177277

theorem tailTrace_5314986 : CollatzResearch.WordTrace tailWord_5314986 prefixEnd_5314986 909714163305882442177277 := by
  unfold tailWord_5314986
  simp only [CollatzResearch.WordTrace]
  refine ⟨48463366280680231046511203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129235643415147282790696541 48463366280680231046511203)
  ·
    refine ⟨72695049421020346569766805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48463366280680231046511203 72695049421020346569766805)
    ·
      refine ⟨3407580441610328745457819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72695049421020346569766805 3407580441610328745457819)
      ·
        refine ⟨5111370662415493118186729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3407580441610328745457819 5111370662415493118186729)
        ·
          refine ⟨3833527996811619838640047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5111370662415493118186729 3833527996811619838640047)
          ·
            refine ⟨5750291995217429757960071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833527996811619838640047 5750291995217429757960071)
            ·
              refine ⟨8625437992826144636940107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750291995217429757960071 8625437992826144636940107)
              ·
                refine ⟨12938156989239216955410161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8625437992826144636940107 12938156989239216955410161)
                ·
                  refine ⟨9703617741929412716557621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12938156989239216955410161 9703617741929412716557621)
                  ·
                    refine ⟨909714163305882442177277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9703617741929412716557621 909714163305882442177277)
                    ·
                      rfl

theorem cell23_5314986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_5314986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314986 prefixEnd_5314986 := by exact prefixLift 5314986
  have htrace : WordTrace (prefixWord ++ tailWord_5314986) baseStart_5314986 baseEnd_5314986 := by
    simpa [prefixWord, tailWord_5314986, baseEnd_5314986] using wordTrace_append hprefix tailTrace_5314986
  have hstable : (prefixWord ++ tailWord_5314986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314986).length < 2 ^ (prefixWord ++ tailWord_5314986).sum := by decide
  have hdescent : baseEnd_5314986 < baseStart_5314986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5314989 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 2, 1, 4]
def baseStart_5314989 : Nat := 118140960795 + 5314989 * 2 ^ 59
def prefixEnd_5314989 : Nat := 4983230072969 + 3 ^ 40 * 5314989 * 2
def baseEnd_5314989 : Nat := 2729144030359610814794317

theorem tailTrace_5314989 : CollatzResearch.WordTrace tailWord_5314989 prefixEnd_5314989 2729144030359610814794317 := by
  unfold tailWord_5314989
  simp only [CollatzResearch.WordTrace]
  refine ⟨193853574541710055698404021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129235716361140037132269347 193853574541710055698404021)
  ·
    refine ⟨18173772613285317721725377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193853574541710055698404021 18173772613285317721725377)
    ·
      refine ⟨13630329459963988291294033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18173772613285317721725377 13630329459963988291294033)
      ·
        refine ⟨10222747094972991218470525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13630329459963988291294033 10222747094972991218470525)
        ·
          refine ⟨3833530160614871706926447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10222747094972991218470525 3833530160614871706926447)
          ·
            refine ⟨5750295240922307560389671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833530160614871706926447 5750295240922307560389671)
            ·
              refine ⟨8625442861383461340584507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750295240922307560389671 8625442861383461340584507)
              ·
                refine ⟨12938164292075192010876761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8625442861383461340584507 12938164292075192010876761)
                ·
                  refine ⟨9703623219056394008157571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12938164292075192010876761 9703623219056394008157571)
                  ·
                    refine ⟨14555434828584591012236357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9703623219056394008157571 14555434828584591012236357)
                    ·
                      refine ⟨2729144030359610814794317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14555434828584591012236357 2729144030359610814794317)
                      ·
                        rfl

theorem cell23_5314989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_5314989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5314989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5314989 prefixEnd_5314989 := by exact prefixLift 5314989
  have htrace : WordTrace (prefixWord ++ tailWord_5314989) baseStart_5314989 baseEnd_5314989 := by
    simpa [prefixWord, tailWord_5314989, baseEnd_5314989] using wordTrace_append hprefix tailTrace_5314989
  have hstable : (prefixWord ++ tailWord_5314989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5314989).length < 2 ^ (prefixWord ++ tailWord_5314989).sum := by decide
  have hdescent : baseEnd_5314989 < baseStart_5314989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5314989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315012 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 6]
def baseStart_5315012 : Nat := 118140960795 + 5315012 * 2 ^ 59
def prefixEnd_5315012 : Nat := 4983230072969 + 3 ^ 40 * 5315012 * 2
def baseEnd_5315012 : Nat := 303239537823851580534079

theorem tailTrace_5315012 : CollatzResearch.WordTrace tailWord_5315012 prefixEnd_5315012 303239537823851580534079 := by
  unfold tailWord_5315012
  simp only [CollatzResearch.WordTrace]
  refine ⟨96927206710313365313245645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129236275613751153750994193 96927206710313365313245645)
  ·
    refine ⟨36347702516367511992467117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96927206710313365313245645 36347702516367511992467117)
    ·
      refine ⟨13630388443637816997175169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36347702516367511992467117 13630388443637816997175169)
      ·
        refine ⟨10222791332728362747881377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13630388443637816997175169 10222791332728362747881377)
        ·
          refine ⟨7667093499546272060911033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10222791332728362747881377 7667093499546272060911033)
          ·
            refine ⟨5750320124659704045683275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7667093499546272060911033 5750320124659704045683275)
            ·
              refine ⟨8625480186989556068524913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750320124659704045683275 8625480186989556068524913)
              ·
                refine ⟨6469110140242167051393685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8625480186989556068524913 6469110140242167051393685)
                ·
                  refine ⟨303239537823851580534079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6469110140242167051393685 303239537823851580534079)
                  ·
                    rfl

theorem cell23_5315012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 6].length) (baseStart_5315012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315012 prefixEnd_5315012 := by exact prefixLift 5315012
  have htrace : WordTrace (prefixWord ++ tailWord_5315012) baseStart_5315012 baseEnd_5315012 := by
    simpa [prefixWord, tailWord_5315012, baseEnd_5315012] using wordTrace_append hprefix tailTrace_5315012
  have hstable : (prefixWord ++ tailWord_5315012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315012).length < 2 ^ (prefixWord ++ tailWord_5315012).sum := by decide
  have hdescent : baseEnd_5315012 < baseStart_5315012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315051 : List Nat := [1, 1, 1, 1, 2, 3, 5, 9]
def baseStart_5315051 : Nat := 118140960795 + 5315051 * 2 ^ 59
def prefixEnd_5315051 : Nat := 4983230072969 + 3 ^ 40 * 5315051 * 2
def baseEnd_5315051 : Nat := 101080587635562576748853

theorem tailTrace_5315051 : CollatzResearch.WordTrace tailWord_5315051 prefixEnd_5315051 101080587635562576748853 := by
  unfold tailWord_5315051
  simp only [CollatzResearch.WordTrace]
  refine ⟨193855835867485440287161007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129237223911656960191440671 193855835867485440287161007)
  ·
    refine ⟨290783753801228160430741511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193855835867485440287161007 290783753801228160430741511)
    ·
      refine ⟨436175630701842240646112267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290783753801228160430741511 436175630701842240646112267)
      ·
        refine ⟨654263446052763360969168401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436175630701842240646112267 654263446052763360969168401)
        ·
          refine ⟨490697584539572520726876301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 654263446052763360969168401 490697584539572520726876301)
          ·
            refine ⟨184011594202339695272578613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 490697584539572520726876301 184011594202339695272578613)
            ·
              refine ⟨17251086956469346431804245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 184011594202339695272578613 17251086956469346431804245)
              ·
                refine ⟨101080587635562576748853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17251086956469346431804245 101080587635562576748853)
                ·
                  rfl

theorem cell23_5315051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 9].length) (baseStart_5315051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315051 prefixEnd_5315051 := by exact prefixLift 5315051
  have htrace : WordTrace (prefixWord ++ tailWord_5315051) baseStart_5315051 baseEnd_5315051 := by
    simpa [prefixWord, tailWord_5315051, baseEnd_5315051] using wordTrace_append hprefix tailTrace_5315051
  have hstable : (prefixWord ++ tailWord_5315051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315051).length < 2 ^ (prefixWord ++ tailWord_5315051).sum := by decide
  have hdescent : baseEnd_5315051 < baseStart_5315051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315065 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 3]
def baseStart_5315065 : Nat := 118140960795 + 5315065 * 2 ^ 59
def prefixEnd_5315065 : Nat := 4983230072969 + 3 ^ 40 * 5315065 * 2
def baseEnd_5315065 : Nat := 2729183054889352517443967

theorem tailTrace_5315065 : CollatzResearch.WordTrace tailWord_5315065 prefixEnd_5315065 2729183054889352517443967 := by
  unfold tailWord_5315065
  simp only [CollatzResearch.WordTrace]
  refine ⟨193856346489434720678170649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129237564326289813785447099 193856346489434720678170649)
  ·
    refine ⟨145392259867076040508627987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193856346489434720678170649 145392259867076040508627987)
    ·
      refine ⟨218088389800614060762941981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145392259867076040508627987 218088389800614060762941981)
      ·
        refine ⟨81783146175230272786103243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 218088389800614060762941981 81783146175230272786103243)
        ·
          refine ⟨122674719262845409179154865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81783146175230272786103243 122674719262845409179154865)
          ·
            refine ⟨92006039447134056884366149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 122674719262845409179154865 92006039447134056884366149)
            ·
              refine ⟨17251132396337635665818653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92006039447134056884366149 17251132396337635665818653)
              ·
                refine ⟨6469174648626613374681995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17251132396337635665818653 6469174648626613374681995)
                ·
                  refine ⟨9703761972939920062022993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469174648626613374681995 9703761972939920062022993)
                  ·
                    refine ⟨7277821479704940046517245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9703761972939920062022993 7277821479704940046517245)
                    ·
                      refine ⟨2729183054889352517443967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7277821479704940046517245 2729183054889352517443967)
                      ·
                        rfl

theorem cell23_5315065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_5315065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315065 prefixEnd_5315065 := by exact prefixLift 5315065
  have htrace : WordTrace (prefixWord ++ tailWord_5315065) baseStart_5315065 baseEnd_5315065 := by
    simpa [prefixWord, tailWord_5315065, baseEnd_5315065] using wordTrace_append hprefix tailTrace_5315065
  have hstable : (prefixWord ++ tailWord_5315065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315065).length < 2 ^ (prefixWord ++ tailWord_5315065).sum := by decide
  have hdescent : baseEnd_5315065 < baseStart_5315065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315112 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 1, 3, 3]
def baseStart_5315112 : Nat := 118140960795 + 5315112 * 2 ^ 59
def prefixEnd_5315112 : Nat := 4983230072969 + 3 ^ 40 * 5315112 * 2
def baseEnd_5315112 : Nat := 2729207188480113833556251

theorem tailTrace_5315112 : CollatzResearch.WordTrace tailWord_5315112 prefixEnd_5315112 2729207188480113833556251 := by
  unfold tailWord_5315112
  simp only [CollatzResearch.WordTrace]
  refine ⟨96929030360132223852565795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129238707146842965136754393 96929030360132223852565795)
  ·
    refine ⟨145393545540198335778848693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96929030360132223852565795 145393545540198335778848693)
    ·
      refine ⟨13630644894393593979267065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 145393545540198335778848693 13630644894393593979267065)
      ·
        refine ⟨10222983670795195484450299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13630644894393593979267065 10222983670795195484450299)
        ·
          refine ⟨15334475506192793226675449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10222983670795195484450299 15334475506192793226675449)
          ·
            refine ⟨11500856629644594920006587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15334475506192793226675449 11500856629644594920006587)
            ·
              refine ⟨17251284944466892380009881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11500856629644594920006587 17251284944466892380009881)
              ·
                refine ⟨12938463708350169285007411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17251284944466892380009881 12938463708350169285007411)
                ·
                  refine ⟨19407695562525253927511117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12938463708350169285007411 19407695562525253927511117)
                  ·
                    refine ⟨7277885835946970222816669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19407695562525253927511117 7277885835946970222816669)
                    ·
                      refine ⟨2729207188480113833556251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7277885835946970222816669 2729207188480113833556251)
                      ·
                        rfl

theorem cell23_5315112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_5315112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315112 prefixEnd_5315112 := by exact prefixLift 5315112
  have htrace : WordTrace (prefixWord ++ tailWord_5315112) baseStart_5315112 baseEnd_5315112 := by
    simpa [prefixWord, tailWord_5315112, baseEnd_5315112] using wordTrace_append hprefix tailTrace_5315112
  have hstable : (prefixWord ++ tailWord_5315112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315112).length < 2 ^ (prefixWord ++ tailWord_5315112).sum := by decide
  have hdescent : baseEnd_5315112 < baseStart_5315112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315122 : List Nat := [3, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_5315122 : Nat := 118140960795 + 5315122 * 2 ^ 59
def prefixEnd_5315122 : Nat := 4983230072969 + 3 ^ 40 * 5315122 * 2
def baseEnd_5315122 : Nat := 2729212323286658794431205

theorem tailTrace_5315122 : CollatzResearch.WordTrace tailWord_5315122 prefixEnd_5315122 2729212323286658794431205 := by
  unfold tailWord_5315122
  simp only [CollatzResearch.WordTrace]
  refine ⟨48464606362557054853248905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129238950300152146275330413 48464606362557054853248905)
  ·
    refine ⟨36348454771917791139936679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48464606362557054853248905 36348454771917791139936679)
    ·
      refine ⟨54522682157876686709905019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36348454771917791139936679 54522682157876686709905019)
      ·
        refine ⟨81784023236815030064857529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54522682157876686709905019 81784023236815030064857529)
        ·
          refine ⟨61338017427611272548643147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81784023236815030064857529 61338017427611272548643147)
          ·
            refine ⟨92007026141416908822964721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61338017427611272548643147 92007026141416908822964721)
            ·
              refine ⟨69005269606062681617223541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92007026141416908822964721 69005269606062681617223541)
              ·
                refine ⟨6469244025568376401614707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69005269606062681617223541 6469244025568376401614707)
                ·
                  refine ⟨9703866038352564602422061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469244025568376401614707 9703866038352564602422061)
                  ·
                    refine ⟨3638949764382211725908273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9703866038352564602422061 3638949764382211725908273)
                    ·
                      refine ⟨2729212323286658794431205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638949764382211725908273 2729212323286658794431205)
                      ·
                        rfl

theorem cell23_5315122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_5315122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315122 prefixEnd_5315122 := by exact prefixLift 5315122
  have htrace : WordTrace (prefixWord ++ tailWord_5315122) baseStart_5315122 baseEnd_5315122 := by
    simpa [prefixWord, tailWord_5315122, baseEnd_5315122] using wordTrace_append hprefix tailTrace_5315122
  have hstable : (prefixWord ++ tailWord_5315122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315122).length < 2 ^ (prefixWord ++ tailWord_5315122).sum := by decide
  have hdescent : baseEnd_5315122 < baseStart_5315122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315128 : List Nat := [2, 1, 2, 1, 4, 1, 2, 2, 2, 6]
def baseStart_5315128 : Nat := 118140960795 + 5315128 * 2 ^ 59
def prefixEnd_5315128 : Nat := 4983230072969 + 3 ^ 40 * 5315128 * 2
def baseEnd_5315128 : Nat := 909738468056861923652059

theorem tailTrace_5315128 : CollatzResearch.WordTrace tailWord_5315128 prefixEnd_5315128 909738468056861923652059 := by
  unfold tailWord_5315128
  simp only [CollatzResearch.WordTrace]
  refine ⟨96929322144103241218857019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129239096192137654958476025 96929322144103241218857019)
  ·
    refine ⟨145393983216154861828285529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96929322144103241218857019 145393983216154861828285529)
    ·
      refine ⟨109045487412116146371214147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 145393983216154861828285529 109045487412116146371214147)
      ·
        refine ⟨163568231118174219556821221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109045487412116146371214147 163568231118174219556821221)
        ·
          refine ⟨30669043334657666166903979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 163568231118174219556821221 30669043334657666166903979)
          ·
            refine ⟨46003565001986499250355969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30669043334657666166903979 46003565001986499250355969)
            ·
              refine ⟨34502673751489874437766977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46003565001986499250355969 34502673751489874437766977)
              ·
                refine ⟨25877005313617405828325233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34502673751489874437766977 25877005313617405828325233)
                ·
                  refine ⟨19407753985213054371243925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25877005313617405828325233 19407753985213054371243925)
                  ·
                    refine ⟨909738468056861923652059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19407753985213054371243925 909738468056861923652059)
                    ·
                      rfl

theorem cell23_5315128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 2, 2, 6].length) (baseStart_5315128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315128 prefixEnd_5315128 := by exact prefixLift 5315128
  have htrace : WordTrace (prefixWord ++ tailWord_5315128) baseStart_5315128 baseEnd_5315128 := by
    simpa [prefixWord, tailWord_5315128, baseEnd_5315128] using wordTrace_append hprefix tailTrace_5315128
  have hstable : (prefixWord ++ tailWord_5315128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315128).length < 2 ^ (prefixWord ++ tailWord_5315128).sum := by decide
  have hdescent : baseEnd_5315128 < baseStart_5315128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315135 : List Nat := [1, 1, 2, 2, 3, 2, 1, 2, 3, 4, 2]
def baseStart_5315135 : Nat := 118140960795 + 5315135 * 2 ^ 59
def prefixEnd_5315135 : Nat := 4983230072969 + 3 ^ 40 * 5315135 * 2
def baseEnd_5315135 : Nat := 2729218998535167243568645

theorem tailTrace_5315135 : CollatzResearch.WordTrace tailWord_5315135 prefixEnd_5315135 2729218998535167243568645 := by
  unfold tailWord_5315135
  simp only [CollatzResearch.WordTrace]
  refine ⟨193858899599181122633218859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129239266399454081755479239 193858899599181122633218859)
  ·
    refine ⟨290788349398771683949828289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193858899599181122633218859 290788349398771683949828289)
    ·
      refine ⟨218091262049078762962371217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290788349398771683949828289 218091262049078762962371217)
      ·
        refine ⟨163568446536809072221778413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218091262049078762962371217 163568446536809072221778413)
        ·
          refine ⟨61338167451303402083166905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 163568446536809072221778413 61338167451303402083166905)
          ·
            refine ⟨46003625588477551562375179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61338167451303402083166905 46003625588477551562375179)
            ·
              refine ⟨69005438382716327343562769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46003625588477551562375179 69005438382716327343562769)
              ·
                refine ⟨51754078787037245507672077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69005438382716327343562769 51754078787037245507672077)
                ·
                  refine ⟨19407779545138967065377029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 51754078787037245507672077 19407779545138967065377029)
                  ·
                    refine ⟨3638958664713556324758193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19407779545138967065377029 3638958664713556324758193)
                    ·
                      refine ⟨2729218998535167243568645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638958664713556324758193 2729218998535167243568645)
                      ·
                        rfl

theorem cell23_5315135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_5315135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315135 prefixEnd_5315135 := by exact prefixLift 5315135
  have htrace : WordTrace (prefixWord ++ tailWord_5315135) baseStart_5315135 baseEnd_5315135 := by
    simpa [prefixWord, tailWord_5315135, baseEnd_5315135] using wordTrace_append hprefix tailTrace_5315135
  have hstable : (prefixWord ++ tailWord_5315135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315135).length < 2 ^ (prefixWord ++ tailWord_5315135).sum := by decide
  have hdescent : baseEnd_5315135 < baseStart_5315135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315173 : List Nat := [1, 3, 1, 3, 5, 1, 2, 1, 1, 3, 2]
def baseStart_5315173 : Nat := 118140960795 + 5315173 * 2 ^ 59
def prefixEnd_5315173 : Nat := 4983230072969 + 3 ^ 40 * 5315173 * 2
def baseEnd_5315173 : Nat := 2729238510800038094893471

theorem tailTrace_5315173 : CollatzResearch.WordTrace tailWord_5315173 prefixEnd_5315173 2729238510800038094893471 := by
  unfold tailWord_5315173
  simp only [CollatzResearch.WordTrace]
  refine ⟨193860285573043455123102173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129240190382028970082068115 193860285573043455123102173)
  ·
    refine ⟨72697607089891295671163315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193860285573043455123102173 72697607089891295671163315)
    ·
      refine ⟨109046410634836943506744973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72697607089891295671163315 109046410634836943506744973)
      ·
        refine ⟨40892403988063853815029365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109046410634836943506744973 40892403988063853815029365)
        ·
          refine ⟨3833662873880986295159003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40892403988063853815029365 3833662873880986295159003)
          ·
            refine ⟨5750494310821479442738505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3833662873880986295159003 5750494310821479442738505)
            ·
              refine ⟨4312870733116109582053879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5750494310821479442738505 4312870733116109582053879)
              ·
                refine ⟨6469306099674164373080819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4312870733116109582053879 6469306099674164373080819)
                ·
                  refine ⟨9703959149511246559621229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469306099674164373080819 9703959149511246559621229)
                  ·
                    refine ⟨3638984681066717459857961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9703959149511246559621229 3638984681066717459857961)
                    ·
                      refine ⟨2729238510800038094893471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638984681066717459857961 2729238510800038094893471)
                      ·
                        rfl

theorem cell23_5315173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_5315173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315173 prefixEnd_5315173 := by exact prefixLift 5315173
  have htrace : WordTrace (prefixWord ++ tailWord_5315173) baseStart_5315173 baseEnd_5315173 := by
    simpa [prefixWord, tailWord_5315173, baseEnd_5315173] using wordTrace_append hprefix tailTrace_5315173
  have hstable : (prefixWord ++ tailWord_5315173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315173).length < 2 ^ (prefixWord ++ tailWord_5315173).sum := by decide
  have hdescent : baseEnd_5315173 < baseStart_5315173 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315195 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 2, 5, 2]
def baseStart_5315195 : Nat := 118140960795 + 5315195 * 2 ^ 59
def prefixEnd_5315195 : Nat := 4983230072969 + 3 ^ 40 * 5315195 * 2
def baseEnd_5315195 : Nat := 2729249807374437008818369

theorem tailTrace_5315195 : CollatzResearch.WordTrace tailWord_5315195 prefixEnd_5315195 2729249807374437008818369 := by
  unfold tailWord_5315195
  simp only [CollatzResearch.WordTrace]
  refine ⟨193861087978963752880403039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129240725319309168586935359 193861087978963752880403039)
  ·
    refine ⟨290791631968445629320604559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193861087978963752880403039 290791631968445629320604559)
    ·
      refine ⟨436187447952668443980906839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290791631968445629320604559 436187447952668443980906839)
      ·
        refine ⟨654281171929002665971360259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 436187447952668443980906839 654281171929002665971360259)
        ·
          refine ⟨981421757893503998957040389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 654281171929002665971360259 981421757893503998957040389)
          ·
            refine ⟨184016579605031999804445073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 981421757893503998957040389 184016579605031999804445073)
            ·
              refine ⟨138012434703773999853333805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 184016579605031999804445073 138012434703773999853333805)
              ·
                refine ⟨51754663013915249945000177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138012434703773999853333805 51754663013915249945000177)
                ·
                  refine ⟨38815997260436437458750133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51754663013915249945000177 38815997260436437458750133)
                  ·
                    refine ⟨3638999743165916011757825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38815997260436437458750133 3638999743165916011757825)
                    ·
                      refine ⟨2729249807374437008818369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3638999743165916011757825 2729249807374437008818369)
                      ·
                        rfl

theorem cell23_5315195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 2, 5, 2].length) (baseStart_5315195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315195 prefixEnd_5315195 := by exact prefixLift 5315195
  have htrace : WordTrace (prefixWord ++ tailWord_5315195) baseStart_5315195 baseEnd_5315195 := by
    simpa [prefixWord, tailWord_5315195, baseEnd_5315195] using wordTrace_append hprefix tailTrace_5315195
  have hstable : (prefixWord ++ tailWord_5315195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315195).length < 2 ^ (prefixWord ++ tailWord_5315195).sum := by decide
  have hdescent : baseEnd_5315195 < baseStart_5315195 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315225 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 4]
def baseStart_5315225 : Nat := 118140960795 + 5315225 * 2 ^ 59
def prefixEnd_5315225 : Nat := 4983230072969 + 3 ^ 40 * 5315225 * 2
def baseEnd_5315225 : Nat := 2729265211794071891443231

theorem tailTrace_5315225 : CollatzResearch.WordTrace tailWord_5315225 prefixEnd_5315225 2729265211794071891443231 := by
  unfold tailWord_5315225
  simp only [CollatzResearch.WordTrace]
  refine ⟨193862182168855068003995129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129241454779236712002663419 193862182168855068003995129)
  ·
    refine ⟨145396636626641301002996347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 193862182168855068003995129 145396636626641301002996347)
    ·
      refine ⟨218094954939961951504494521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145396636626641301002996347 218094954939961951504494521)
      ·
        refine ⟨163571216204971463628370891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218094954939961951504494521 163571216204971463628370891)
        ·
          refine ⟨245356824307457195442556337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163571216204971463628370891 245356824307457195442556337)
          ·
            refine ⟨184017618230592896581917253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 245356824307457195442556337 184017618230592896581917253)
            ·
              refine ⟨34503303418236168109109485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 184017618230592896581917253 34503303418236168109109485)
              ·
                refine ⟨12938738781838563040916057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34503303418236168109109485 12938738781838563040916057)
                ·
                  refine ⟨9704054086378922280687043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12938738781838563040916057 9704054086378922280687043)
                  ·
                    refine ⟨14556081129568383421030565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9704054086378922280687043 14556081129568383421030565)
                    ·
                      refine ⟨2729265211794071891443231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14556081129568383421030565 2729265211794071891443231)
                      ·
                        rfl

theorem cell23_5315225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_5315225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315225 prefixEnd_5315225 := by exact prefixLift 5315225
  have htrace : WordTrace (prefixWord ++ tailWord_5315225) baseStart_5315225 baseEnd_5315225 := by
    simpa [prefixWord, tailWord_5315225, baseEnd_5315225] using wordTrace_append hprefix tailTrace_5315225
  have hstable : (prefixWord ++ tailWord_5315225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315225).length < 2 ^ (prefixWord ++ tailWord_5315225).sum := by decide
  have hdescent : baseEnd_5315225 < baseStart_5315225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315226 : List Nat := [3, 1, 1, 6, 1, 2, 1, 3, 5]
def baseStart_5315226 : Nat := 118140960795 + 5315226 * 2 ^ 59
def prefixEnd_5315226 : Nat := 4983230072969 + 3 ^ 40 * 5315226 * 2
def baseEnd_5315226 : Nat := 303251747252747376392303

theorem tailTrace_5315226 : CollatzResearch.WordTrace tailWord_5315226 prefixEnd_5315226 303251747252747376392303 := by
  unfold tailWord_5315226
  simp only [CollatzResearch.WordTrace]
  refine ⟨48465554660462861293695383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129241479094567630116521021 48465554660462861293695383)
  ·
    refine ⟨72698331990694291940543075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48465554660462861293695383 72698331990694291940543075)
    ·
      refine ⟨109047497986041437910814613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72698331990694291940543075 109047497986041437910814613)
      ·
        refine ⟨5111601468095692402069435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 109047497986041437910814613 5111601468095692402069435)
        ·
          refine ⟨7667402202143538603104153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111601468095692402069435 7667402202143538603104153)
          ·
            refine ⟨5750551651607653952328115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7667402202143538603104153 5750551651607653952328115)
            ·
              refine ⟨8625827477411480928492173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750551651607653952328115 8625827477411480928492173)
              ·
                refine ⟨3234685304029305348184565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8625827477411480928492173 3234685304029305348184565)
                ·
                  refine ⟨303251747252747376392303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3234685304029305348184565 303251747252747376392303)
                  ·
                    rfl

theorem cell23_5315226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 5].length) (baseStart_5315226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315226 prefixEnd_5315226 := by exact prefixLift 5315226
  have htrace : WordTrace (prefixWord ++ tailWord_5315226) baseStart_5315226 baseEnd_5315226 := by
    simpa [prefixWord, tailWord_5315226, baseEnd_5315226] using wordTrace_append hprefix tailTrace_5315226
  have hstable : (prefixWord ++ tailWord_5315226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315226).length < 2 ^ (prefixWord ++ tailWord_5315226).sum := by decide
  have hdescent : baseEnd_5315226 < baseStart_5315226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315239 : List Nat := [1, 1, 6, 3, 1, 1, 1, 2, 2, 5]
def baseStart_5315239 : Nat := 118140960795 + 5315239 * 2 ^ 59
def prefixEnd_5315239 : Nat := 4983230072969 + 3 ^ 40 * 5315239 * 2
def baseEnd_5315239 : Nat := 909757466841078278889389

theorem tailTrace_5315239 : CollatzResearch.WordTrace tailWord_5315239 prefixEnd_5315239 909757466841078278889389 := by
  unfold tailWord_5315239
  simp only [CollatzResearch.WordTrace]
  refine ⟨193862692790804348395004771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129241795193869565596669847 193862692790804348395004771)
  ·
    refine ⟨290794039186206522592507157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193862692790804348395004771 290794039186206522592507157)
    ·
      refine ⟨13630970586853430746523773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 290794039186206522592507157 13630970586853430746523773)
      ·
        refine ⟨5111613970070036529946415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13630970586853430746523773 5111613970070036529946415)
        ·
          refine ⟨7667420955105054794919623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5111613970070036529946415 7667420955105054794919623)
          ·
            refine ⟨11501131432657582192379435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7667420955105054794919623 11501131432657582192379435)
            ·
              refine ⟨17251697148986373288569153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11501131432657582192379435 17251697148986373288569153)
              ·
                refine ⟨12938772861739779966426865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17251697148986373288569153 12938772861739779966426865)
                ·
                  refine ⟨9704079646304834974820149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12938772861739779966426865 9704079646304834974820149)
                  ·
                    refine ⟨909757466841078278889389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9704079646304834974820149 909757466841078278889389)
                    ·
                      rfl

theorem cell23_5315239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_5315239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315239 prefixEnd_5315239 := by exact prefixLift 5315239
  have htrace : WordTrace (prefixWord ++ tailWord_5315239) baseStart_5315239 baseEnd_5315239 := by
    simpa [prefixWord, tailWord_5315239, baseEnd_5315239] using wordTrace_append hprefix tailTrace_5315239
  have hstable : (prefixWord ++ tailWord_5315239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315239).length < 2 ^ (prefixWord ++ tailWord_5315239).sum := by decide
  have hdescent : baseEnd_5315239 < baseStart_5315239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315262 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_5315262 : Nat := 118140960795 + 5315262 * 2 ^ 59
def prefixEnd_5315262 : Nat := 4983230072969 + 3 ^ 40 * 5315262 * 2
def baseEnd_5315262 : Nat := 2729284210578288246680561

theorem tailTrace_5315262 : CollatzResearch.WordTrace tailWord_5315262 prefixEnd_5315262 2729284210578288246680561 := by
  unfold tailWord_5315262
  simp only [CollatzResearch.WordTrace]
  refine ⟨24232941458715127915386505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129242354446480682215394693 24232941458715127915386505)
  ·
    refine ⟨18174706094036345936539879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24232941458715127915386505 18174706094036345936539879)
    ·
      refine ⟨27262059141054518904809819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18174706094036345936539879 27262059141054518904809819)
      ·
        refine ⟨40893088711581778357214729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27262059141054518904809819 40893088711581778357214729)
        ·
          refine ⟨30669816533686333767911047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40893088711581778357214729 30669816533686333767911047)
          ·
            refine ⟨46004724800529500651866571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30669816533686333767911047 46004724800529500651866571)
            ·
              refine ⟨69007087200794250977799857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46004724800529500651866571 69007087200794250977799857)
              ·
                refine ⟨51755315400595688233349893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69007087200794250977799857 51755315400595688233349893)
                ·
                  refine ⟨9704121637611691543753105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51755315400595688233349893 9704121637611691543753105)
                  ·
                    refine ⟨7278091228208768657814829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9704121637611691543753105 7278091228208768657814829)
                    ·
                      refine ⟨2729284210578288246680561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7278091228208768657814829 2729284210578288246680561)
                      ·
                        rfl

theorem cell23_5315262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_5315262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315262 prefixEnd_5315262 := by exact prefixLift 5315262
  have htrace : WordTrace (prefixWord ++ tailWord_5315262) baseStart_5315262 baseEnd_5315262 := by
    simpa [prefixWord, tailWord_5315262, baseEnd_5315262] using wordTrace_append hprefix tailTrace_5315262
  have hstable : (prefixWord ++ tailWord_5315262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315262).length < 2 ^ (prefixWord ++ tailWord_5315262).sum := by decide
  have hdescent : baseEnd_5315262 < baseStart_5315262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315309 : List Nat := [1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 3]
def baseStart_5315309 : Nat := 118140960795 + 5315309 * 2 ^ 59
def prefixEnd_5315309 : Nat := 4983230072969 + 3 ^ 40 * 5315309 * 2
def baseEnd_5315309 : Nat := 2729308344169049562792845

theorem tailTrace_5315309 : CollatzResearch.WordTrace tailWord_5315309 prefixEnd_5315309 2729308344169049562792845 := by
  unfold tailWord_5315309
  simp only [CollatzResearch.WordTrace]
  refine ⟨193865245900550750350052981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129243497267033833566701987 193865245900550750350052981)
  ·
    refine ⟨18174866803176632845317467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 193865245900550750350052981 18174866803176632845317467)
    ·
      refine ⟨27262300204764949267976201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18174866803176632845317467 27262300204764949267976201)
      ·
        refine ⟨20446725153573711950982151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27262300204764949267976201 20446725153573711950982151)
        ·
          refine ⟨30670087730360567926473227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20446725153573711950982151 30670087730360567926473227)
          ·
            refine ⟨46005131595540851889709841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30670087730360567926473227 46005131595540851889709841)
            ·
              refine ⟨34503848696655638917282381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46005131595540851889709841 34503848696655638917282381)
              ·
                refine ⟨12938943261245864593980893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34503848696655638917282381 12938943261245864593980893)
                ·
                  refine ⟨4852103722967199222742835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12938943261245864593980893 4852103722967199222742835)
                  ·
                    refine ⟨7278155584450798834114253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4852103722967199222742835 7278155584450798834114253)
                    ·
                      refine ⟨2729308344169049562792845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7278155584450798834114253 2729308344169049562792845)
                      ·
                        rfl

theorem cell23_5315309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_5315309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315309 prefixEnd_5315309 := by exact prefixLift 5315309
  have htrace : WordTrace (prefixWord ++ tailWord_5315309) baseStart_5315309 baseEnd_5315309 := by
    simpa [prefixWord, tailWord_5315309, baseEnd_5315309] using wordTrace_append hprefix tailTrace_5315309
  have hstable : (prefixWord ++ tailWord_5315309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315309).length < 2 ^ (prefixWord ++ tailWord_5315309).sum := by decide
  have hdescent : baseEnd_5315309 < baseStart_5315309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315326 : List Nat := [4, 2, 2, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_5315326 : Nat := 118140960795 + 5315326 * 2 ^ 59
def prefixEnd_5315326 : Nat := 4983230072969 + 3 ^ 40 * 5315326 * 2
def baseEnd_5315326 : Nat := 2729317073340175996280267

theorem tailTrace_5315326 : CollatzResearch.WordTrace tailWord_5315326 prefixEnd_5315326 2729317073340175996280267 := by
  unfold tailWord_5315326
  simp only [CollatzResearch.WordTrace]
  refine ⟨24233233242686145281677729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129243910627659441502281221 24233233242686145281677729)
  ·
    refine ⟨18174924932014608961258297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24233233242686145281677729 18174924932014608961258297)
    ·
      refine ⟨13631193699010956720943723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18174924932014608961258297 13631193699010956720943723)
      ·
        refine ⟨20446790548516435081415585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13631193699010956720943723 20446790548516435081415585)
        ·
          refine ⟨15335092911387326311061689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20446790548516435081415585 15335092911387326311061689)
          ·
            refine ⟨11501319683540494733296267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15335092911387326311061689 11501319683540494733296267)
            ·
              refine ⟨17251979525310742099944401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11501319683540494733296267 17251979525310742099944401)
              ·
                refine ⟨12938984643983056574958301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17251979525310742099944401 12938984643983056574958301)
                ·
                  refine ⟨4852119241493646215609363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12938984643983056574958301 4852119241493646215609363)
                  ·
                    refine ⟨7278178862240469323414045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4852119241493646215609363 7278178862240469323414045)
                    ·
                      refine ⟨2729317073340175996280267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7278178862240469323414045 2729317073340175996280267)
                      ·
                        rfl

theorem cell23_5315326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_5315326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315326 prefixEnd_5315326 := by exact prefixLift 5315326
  have htrace : WordTrace (prefixWord ++ tailWord_5315326) baseStart_5315326 baseEnd_5315326 := by
    simpa [prefixWord, tailWord_5315326, baseEnd_5315326] using wordTrace_append hprefix tailTrace_5315326
  have hstable : (prefixWord ++ tailWord_5315326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315326).length < 2 ^ (prefixWord ++ tailWord_5315326).sum := by decide
  have hdescent : baseEnd_5315326 < baseStart_5315326 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315332 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_5315332 : Nat := 118140960795 + 5315332 * 2 ^ 59
def prefixEnd_5315332 : Nat := 4983230072969 + 3 ^ 40 * 5315332 * 2
def baseEnd_5315332 : Nat := 2729320154224102972805239

theorem tailTrace_5315332 : CollatzResearch.WordTrace tailWord_5315332 prefixEnd_5315332 2729320154224102972805239 := by
  unfold tailWord_5315332
  simp only [CollatzResearch.WordTrace]
  refine ⟨96933042389733712639070125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129244056519644950185426833 96933042389733712639070125)
  ·
    refine ⟨36349890896150142239651297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 96933042389733712639070125 36349890896150142239651297)
    ·
      refine ⟨27262418172112606679738473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36349890896150142239651297 27262418172112606679738473)
      ·
        refine ⟨20446813629084455009803855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27262418172112606679738473 20446813629084455009803855)
        ·
          refine ⟨30670220443626682514705783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20446813629084455009803855 30670220443626682514705783)
          ·
            refine ⟨46005330665440023772058675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30670220443626682514705783 46005330665440023772058675)
            ·
              refine ⟨69007995998160035658088013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46005330665440023772058675 69007995998160035658088013)
              ·
                refine ⟨25877998499310013371783005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69007995998160035658088013 25877998499310013371783005)
                ·
                  refine ⟨9704249437241255014418627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25877998499310013371783005 9704249437241255014418627)
                  ·
                    refine ⟨14556374155861882521627941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9704249437241255014418627 14556374155861882521627941)
                    ·
                      refine ⟨2729320154224102972805239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14556374155861882521627941 2729320154224102972805239)
                      ·
                        rfl

theorem cell23_5315332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_5315332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315332 prefixEnd_5315332 := by exact prefixLift 5315332
  have htrace : WordTrace (prefixWord ++ tailWord_5315332) baseStart_5315332 baseEnd_5315332 := by
    simpa [prefixWord, tailWord_5315332, baseEnd_5315332] using wordTrace_append hprefix tailTrace_5315332
  have hstable : (prefixWord ++ tailWord_5315332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315332).length < 2 ^ (prefixWord ++ tailWord_5315332).sum := by decide
  have hdescent : baseEnd_5315332 < baseStart_5315332 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315336 : List Nat := [2, 1, 3, 2, 2, 4, 1, 1, 2, 3, 2]
def baseStart_5315336 : Nat := 118140960795 + 5315336 * 2 ^ 59
def prefixEnd_5315336 : Nat := 4983230072969 + 3 ^ 40 * 5315336 * 2
def baseEnd_5315336 : Nat := 2729322208146720957155221

theorem tailTrace_5315336 : CollatzResearch.WordTrace tailWord_5315336 prefixEnd_5315336 2729322208146720957155221 := by
  unfold tailWord_5315336
  simp only [CollatzResearch.WordTrace]
  refine ⟨96933115335726466980642931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129244153780968622640857241 96933115335726466980642931)
  ·
    refine ⟨145399673003589700470964397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96933115335726466980642931 145399673003589700470964397)
    ·
      refine ⟨54524877376346137676611649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 145399673003589700470964397 54524877376346137676611649)
      ·
        refine ⟨40893658032259603257458737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54524877376346137676611649 40893658032259603257458737)
        ·
          refine ⟨30670243524194702443094053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40893658032259603257458737 30670243524194702443094053)
          ·
            refine ⟨5750670660786506708080135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30670243524194702443094053 5750670660786506708080135)
            ·
              refine ⟨8626005991179760062120203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750670660786506708080135 8626005991179760062120203)
              ·
                refine ⟨12939008986769640093180305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8626005991179760062120203 12939008986769640093180305)
                ·
                  refine ⟨9704256740077230069885229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12939008986769640093180305 9704256740077230069885229)
                  ·
                    refine ⟨3639096277528961276206961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9704256740077230069885229 3639096277528961276206961)
                    ·
                      refine ⟨2729322208146720957155221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639096277528961276206961 2729322208146720957155221)
                      ·
                        rfl

theorem cell23_5315336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_5315336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315336 prefixEnd_5315336 := by exact prefixLift 5315336
  have htrace : WordTrace (prefixWord ++ tailWord_5315336) baseStart_5315336 baseEnd_5315336 := by
    simpa [prefixWord, tailWord_5315336, baseEnd_5315336] using wordTrace_append hprefix tailTrace_5315336
  have hstable : (prefixWord ++ tailWord_5315336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315336).length < 2 ^ (prefixWord ++ tailWord_5315336).sum := by decide
  have hdescent : baseEnd_5315336 < baseStart_5315336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315342 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 4, 4]
def baseStart_5315342 : Nat := 118140960795 + 5315342 * 2 ^ 59
def prefixEnd_5315342 : Nat := 4983230072969 + 3 ^ 40 * 5315342 * 2
def baseEnd_5315342 : Nat := 909775096343549311226731

theorem tailTrace_5315342 : CollatzResearch.WordTrace tailWord_5315342 prefixEnd_5315342 909775096343549311226731 := by
  unfold tailWord_5315342
  simp only [CollatzResearch.WordTrace]
  refine ⟨24233306188678899623250535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129244299672954131324002853 24233306188678899623250535)
  ·
    refine ⟨36349959283018349434875803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24233306188678899623250535 36349959283018349434875803)
    ·
      refine ⟨54524938924527524152313705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36349959283018349434875803 54524938924527524152313705)
      ·
        refine ⟨40893704193395643114235279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54524938924527524152313705 40893704193395643114235279)
        ·
          refine ⟨61340556290093464671352919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40893704193395643114235279 61340556290093464671352919)
          ·
            refine ⟨92010834435140197007029379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61340556290093464671352919 92010834435140197007029379)
            ·
              refine ⟨138016251652710295510544069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92010834435140197007029379 138016251652710295510544069)
              ·
                refine ⟨25878047184883180408227013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138016251652710295510544069 25878047184883180408227013)
                ·
                  refine ⟨4852133847165596326542565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25878047184883180408227013 4852133847165596326542565)
                  ·
                    refine ⟨909775096343549311226731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4852133847165596326542565 909775096343549311226731)
                    ·
                      rfl

theorem cell23_5315342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_5315342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315342 prefixEnd_5315342 := by exact prefixLift 5315342
  have htrace : WordTrace (prefixWord ++ tailWord_5315342) baseStart_5315342 baseEnd_5315342 := by
    simpa [prefixWord, tailWord_5315342, baseEnd_5315342] using wordTrace_append hprefix tailTrace_5315342
  have hstable : (prefixWord ++ tailWord_5315342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315342).length < 2 ^ (prefixWord ++ tailWord_5315342).sum := by decide
  have hdescent : baseEnd_5315342 < baseStart_5315342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315346 : List Nat := [3, 2, 4, 1, 2, 1, 1, 3, 1, 5]
def baseStart_5315346 : Nat := 118140960795 + 5315346 * 2 ^ 59
def prefixEnd_5315346 : Nat := 4983230072969 + 3 ^ 40 * 5315346 * 2
def baseEnd_5315346 : Nat := 909775780984421972676725

theorem tailTrace_5315346 : CollatzResearch.WordTrace tailWord_5315346 prefixEnd_5315346 909775780984421972676725 := by
  unfold tailWord_5315346
  simp only [CollatzResearch.WordTrace]
  refine ⟨48466648850354176417287473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129244396934277803779433261 48466648850354176417287473)
  ·
    refine ⟨36349986637765632312965605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48466648850354176417287473 36349986637765632312965605)
    ·
      refine ⟨6815622494581056058681051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36349986637765632312965605 6815622494581056058681051)
      ·
        refine ⟨10223433741871584088021577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6815622494581056058681051 10223433741871584088021577)
        ·
          refine ⟨7667575306403688066016183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10223433741871584088021577 7667575306403688066016183)
          ·
            refine ⟨11501362959605532099024275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7667575306403688066016183 11501362959605532099024275)
            ·
              refine ⟨17252044439408298148536413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11501362959605532099024275 17252044439408298148536413)
              ·
                refine ⟨6469516664778111805701155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17252044439408298148536413 6469516664778111805701155)
                ·
                  refine ⟨9704274997167167708551733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469516664778111805701155 9704274997167167708551733)
                  ·
                    refine ⟨909775780984421972676725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9704274997167167708551733 909775780984421972676725)
                    ·
                      rfl

theorem cell23_5315346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_5315346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315346 prefixEnd_5315346 := by exact prefixLift 5315346
  have htrace : WordTrace (prefixWord ++ tailWord_5315346) baseStart_5315346 baseEnd_5315346 := by
    simpa [prefixWord, tailWord_5315346, baseEnd_5315346] using wordTrace_append hprefix tailTrace_5315346
  have hstable : (prefixWord ++ tailWord_5315346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315346).length < 2 ^ (prefixWord ++ tailWord_5315346).sum := by decide
  have hdescent : baseEnd_5315346 < baseStart_5315346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315349 : List Nat := [1, 3, 2, 1, 2, 2, 1, 2, 5, 2, 2]
def baseStart_5315349 : Nat := 118140960795 + 5315349 * 2 ^ 59
def prefixEnd_5315349 : Nat := 4983230072969 + 3 ^ 40 * 5315349 * 2
def baseEnd_5315349 : Nat := 2729328883395229406292661

theorem tailTrace_5315349 : CollatzResearch.WordTrace tailWord_5315349 prefixEnd_5315349 2729328883395229406292661 := by
  unfold tailWord_5315349
  simp only [CollatzResearch.WordTrace]
  refine ⟨193866704820405837181509101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129244469880270558121006067 193866704820405837181509101)
  ·
    refine ⟨72700014307652188943065913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 193866704820405837181509101 72700014307652188943065913)
    ·
      refine ⟨54525010730739141707299435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72700014307652188943065913 54525010730739141707299435)
      ·
        refine ⟨81787516096108712560949153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54525010730739141707299435 81787516096108712560949153)
        ·
          refine ⟨61340637072081534420711865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81787516096108712560949153 61340637072081534420711865)
          ·
            refine ⟨46005477804061150815533899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61340637072081534420711865 46005477804061150815533899)
            ·
              refine ⟨69008216706091726223300849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46005477804061150815533899 69008216706091726223300849)
              ·
                refine ⟨51756162529568794667475637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69008216706091726223300849 51756162529568794667475637)
                ·
                  refine ⟨4852140237147074500075841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 51756162529568794667475637 4852140237147074500075841)
                  ·
                    refine ⟨3639105177860305875056881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4852140237147074500075841 3639105177860305875056881)
                    ·
                      refine ⟨2729328883395229406292661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639105177860305875056881 2729328883395229406292661)
                      ·
                        rfl

theorem cell23_5315349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_5315349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315349 prefixEnd_5315349 := by exact prefixLift 5315349
  have htrace : WordTrace (prefixWord ++ tailWord_5315349) baseStart_5315349 baseEnd_5315349 := by
    simpa [prefixWord, tailWord_5315349, baseEnd_5315349] using wordTrace_append hprefix tailTrace_5315349
  have hstable : (prefixWord ++ tailWord_5315349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315349).length < 2 ^ (prefixWord ++ tailWord_5315349).sum := by decide
  have hdescent : baseEnd_5315349 < baseStart_5315349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315359 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 2, 4]
def baseStart_5315359 : Nat := 118140960795 + 5315359 * 2 ^ 59
def prefixEnd_5315359 : Nat := 4983230072969 + 3 ^ 40 * 5315359 * 2
def baseEnd_5315359 : Nat := 909778006067258122389205

theorem tailTrace_5315359 : CollatzResearch.WordTrace tailWord_5315359 prefixEnd_5315359 909778006067258122389205 := by
  unfold tailWord_5315359
  simp only [CollatzResearch.WordTrace]
  refine ⟨193867069550369608889373131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129244713033579739259582087 193867069550369608889373131)
  ·
    refine ⟨290800604325554413334059697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193867069550369608889373131 290800604325554413334059697)
    ·
      refine ⟨218100453244165810000544773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 290800604325554413334059697 218100453244165810000544773)
      ·
        refine ⟨40893834983281089375102145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 218100453244165810000544773 40893834983281089375102145)
        ·
          refine ⟨30670376237460817031326609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40893834983281089375102145 30670376237460817031326609)
          ·
            refine ⟨23002782178095612773494957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30670376237460817031326609 23002782178095612773494957)
            ·
              refine ⟨8626043316785854790060609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23002782178095612773494957 8626043316785854790060609)
              ·
                refine ⟨6469532487589391092545457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8626043316785854790060609 6469532487589391092545457)
                ·
                  refine ⟨4852149365692043319409093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6469532487589391092545457 4852149365692043319409093)
                  ·
                    refine ⟨909778006067258122389205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4852149365692043319409093 909778006067258122389205)
                    ·
                      rfl

theorem cell23_5315359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 2, 4].length) (baseStart_5315359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315359 prefixEnd_5315359 := by exact prefixLift 5315359
  have htrace : WordTrace (prefixWord ++ tailWord_5315359) baseStart_5315359 baseEnd_5315359 := by
    simpa [prefixWord, tailWord_5315359, baseEnd_5315359] using wordTrace_append hprefix tailTrace_5315359
  have hstable : (prefixWord ++ tailWord_5315359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315359).length < 2 ^ (prefixWord ++ tailWord_5315359).sum := by decide
  have hdescent : baseEnd_5315359 < baseStart_5315359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315379 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 4]
def baseStart_5315379 : Nat := 118140960795 + 5315379 * 2 ^ 59
def prefixEnd_5315379 : Nat := 4983230072969 + 3 ^ 40 * 5315379 * 2
def baseEnd_5315379 : Nat := 2729344287814864288917523

theorem tailTrace_5315379 : CollatzResearch.WordTrace tailWord_5315379 prefixEnd_5315379 2729344287814864288917523 := by
  unfold tailWord_5315379
  simp only [CollatzResearch.WordTrace]
  refine ⟨193867799010297152305101191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129245199340198101536734127 193867799010297152305101191)
  ·
    refine ⟨290801698515445728457651787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193867799010297152305101191 290801698515445728457651787)
    ·
      refine ⟨436202547773168592686477681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290801698515445728457651787 436202547773168592686477681)
      ·
        refine ⟨327151910829876444514858261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 436202547773168592686477681 327151910829876444514858261)
        ·
          refine ⟨15335245820150458336633981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 327151910829876444514858261 15335245820150458336633981)
          ·
            refine ⟨5750717182556421876237743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15335245820150458336633981 5750717182556421876237743)
            ·
              refine ⟨8626075773834632814356615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5750717182556421876237743 8626075773834632814356615)
              ·
                refine ⟨12939113660751949221534923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8626075773834632814356615 12939113660751949221534923)
                ·
                  refine ⟨19408670491127923832302385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12939113660751949221534923 19408670491127923832302385)
                  ·
                    refine ⟨14556502868345942874226789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19408670491127923832302385 14556502868345942874226789)
                    ·
                      refine ⟨2729344287814864288917523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14556502868345942874226789 2729344287814864288917523)
                      ·
                        rfl

theorem cell23_5315379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 1, 2, 4].length) (baseStart_5315379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315379 prefixEnd_5315379 := by exact prefixLift 5315379
  have htrace : WordTrace (prefixWord ++ tailWord_5315379) baseStart_5315379 baseEnd_5315379 := by
    simpa [prefixWord, tailWord_5315379, baseEnd_5315379] using wordTrace_append hprefix tailTrace_5315379
  have hstable : (prefixWord ++ tailWord_5315379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315379).length < 2 ^ (prefixWord ++ tailWord_5315379).sum := by decide
  have hdescent : baseEnd_5315379 < baseStart_5315379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315386 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3]
def baseStart_5315386 : Nat := 118140960795 + 5315386 * 2 ^ 59
def prefixEnd_5315386 : Nat := 4983230072969 + 3 ^ 40 * 5315386 * 2
def baseEnd_5315386 : Nat := 2729347882179445761529991

theorem tailTrace_5315386 : CollatzResearch.WordTrace tailWord_5315386 prefixEnd_5315386 2729347882179445761529991 := by
  unfold tailWord_5315386
  simp only [CollatzResearch.WordTrace]
  refine ⟨48467013580317948125151503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129245369547514528333737341 48467013580317948125151503)
  ·
    refine ⟨72700520370476922187727255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48467013580317948125151503 72700520370476922187727255)
    ·
      refine ⟨109050780555715383281590883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72700520370476922187727255 109050780555715383281590883)
      ·
        refine ⟨163576170833573074922386325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109050780555715383281590883 163576170833573074922386325)
        ·
          refine ⟨7667633007823737886986859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 163576170833573074922386325 7667633007823737886986859)
          ·
            refine ⟨11501449511735606830480289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7667633007823737886986859 11501449511735606830480289)
            ·
              refine ⟨8626087133801705122860217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11501449511735606830480289 8626087133801705122860217)
              ·
                refine ⟨6469565350351278842145163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8626087133801705122860217 6469565350351278842145163)
                ·
                  refine ⟨9704348025526918263217745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6469565350351278842145163 9704348025526918263217745)
                  ·
                    refine ⟨7278261019145188697413309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9704348025526918263217745 7278261019145188697413309)
                    ·
                      refine ⟨2729347882179445761529991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7278261019145188697413309 2729347882179445761529991)
                      ·
                        rfl

theorem cell23_5315386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_5315386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315386 prefixEnd_5315386 := by exact prefixLift 5315386
  have htrace : WordTrace (prefixWord ++ tailWord_5315386) baseStart_5315386 baseEnd_5315386 := by
    simpa [prefixWord, tailWord_5315386, baseEnd_5315386] using wordTrace_append hprefix tailTrace_5315386
  have hstable : (prefixWord ++ tailWord_5315386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315386).length < 2 ^ (prefixWord ++ tailWord_5315386).sum := by decide
  have hdescent : baseEnd_5315386 < baseStart_5315386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315392 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 2, 7, 2]
def baseStart_5315392 : Nat := 118140960795 + 5315392 * 2 ^ 59
def prefixEnd_5315392 : Nat := 4983230072969 + 3 ^ 40 * 5315392 * 2
def baseEnd_5315392 : Nat := 2729350963063372738054963

theorem tailTrace_5315392 : CollatzResearch.WordTrace tailWord_5315392 prefixEnd_5315392 2729350963063372738054963 := by
  unfold tailWord_5315392
  simp only [CollatzResearch.WordTrace]
  refine ⟨96934136579625027762662215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129245515439500037016882953 96934136579625027762662215)
  ·
    refine ⟨145401204869437541643993323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96934136579625027762662215 145401204869437541643993323)
    ·
      refine ⟨218101807304156312465989985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 145401204869437541643993323 218101807304156312465989985)
      ·
        refine ⟨163576355478117234349492489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 218101807304156312465989985 163576355478117234349492489)
        ·
          refine ⟨122682266608587925762119367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 163576355478117234349492489 122682266608587925762119367)
          ·
            refine ⟨184023399912881888643179051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 122682266608587925762119367 184023399912881888643179051)
            ·
              refine ⟨276035099869322832964768577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 184023399912881888643179051 276035099869322832964768577)
              ·
                refine ⟨207026324901992124723576433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276035099869322832964768577 207026324901992124723576433)
                ·
                  refine ⟨155269743676494093542682325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 207026324901992124723576433 155269743676494093542682325)
                  ·
                    refine ⟨3639134617417830317406617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 155269743676494093542682325 3639134617417830317406617)
                    ·
                      refine ⟨2729350963063372738054963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3639134617417830317406617 2729350963063372738054963)
                      ·
                        rfl

theorem cell23_5315392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_5315392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315392 prefixEnd_5315392 := by exact prefixLift 5315392
  have htrace : WordTrace (prefixWord ++ tailWord_5315392) baseStart_5315392 baseEnd_5315392 := by
    simpa [prefixWord, tailWord_5315392, baseEnd_5315392] using wordTrace_append hprefix tailTrace_5315392
  have hstable : (prefixWord ++ tailWord_5315392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315392).length < 2 ^ (prefixWord ++ tailWord_5315392).sum := by decide
  have hdescent : baseEnd_5315392 < baseStart_5315392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315395 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 5]
def baseStart_5315395 : Nat := 118140960795 + 5315395 * 2 ^ 59
def prefixEnd_5315395 : Nat := 4983230072969 + 3 ^ 40 * 5315395 * 2
def baseEnd_5315395 : Nat := 2729352503505336226317449

theorem tailTrace_5315395 : CollatzResearch.WordTrace tailWord_5315395 prefixEnd_5315395 2729352503505336226317449 := by
  unfold tailWord_5315395
  simp only [CollatzResearch.WordTrace]
  refine ⟨193868382578239187037683639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129245588385492791358455759 193868382578239187037683639)
  ·
    refine ⟨290802573867358780556525459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193868382578239187037683639 290802573867358780556525459)
    ·
      refine ⟨436203860801038170834788189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290802573867358780556525459 436203860801038170834788189)
      ·
        refine ⟨163576447800389314063045571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 436203860801038170834788189 163576447800389314063045571)
        ·
          refine ⟨245364671700583971094568357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 163576447800389314063045571 245364671700583971094568357)
          ·
            refine ⟨46005875943859494580231567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 245364671700583971094568357 46005875943859494580231567)
            ·
              refine ⟨69008813915789241870347351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46005875943859494580231567 69008813915789241870347351)
              ·
                refine ⟨103513220873683862805521027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69008813915789241870347351 103513220873683862805521027)
                ·
                  refine ⟨155269831310525794208281541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 103513220873683862805521027 155269831310525794208281541)
                  ·
                    refine ⟨29113093370723586414052789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 155269831310525794208281541 29113093370723586414052789)
                    ·
                      refine ⟨2729352503505336226317449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29113093370723586414052789 2729352503505336226317449)
                      ·
                        rfl

theorem cell23_5315395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 5].length) (baseStart_5315395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315395 prefixEnd_5315395 := by exact prefixLift 5315395
  have htrace : WordTrace (prefixWord ++ tailWord_5315395) baseStart_5315395 baseEnd_5315395 := by
    simpa [prefixWord, tailWord_5315395, baseEnd_5315395] using wordTrace_append hprefix tailTrace_5315395
  have hstable : (prefixWord ++ tailWord_5315395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315395).length < 2 ^ (prefixWord ++ tailWord_5315395).sum := by decide
  have hdescent : baseEnd_5315395 < baseStart_5315395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315442 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 2, 1, 5]
def baseStart_5315442 : Nat := 118140960795 + 5315442 * 2 ^ 59
def prefixEnd_5315442 : Nat := 4983230072969 + 3 ^ 40 * 5315442 * 2
def baseEnd_5315442 : Nat := 2729376637096097542429733

theorem tailTrace_5315442 : CollatzResearch.WordTrace tailWord_5315442 prefixEnd_5315442 2729376637096097542429733 := by
  unfold tailWord_5315442
  simp only [CollatzResearch.WordTrace]
  refine ⟨48467524202267228516161145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129246731206045942709763053 48467524202267228516161145)
  ·
    refine ⟨36350643151700421387120859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48467524202267228516161145 36350643151700421387120859)
    ·
      refine ⟨54525964727550632080681289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36350643151700421387120859 54525964727550632080681289)
      ·
        refine ⟨40894473545662974060510967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54525964727550632080681289 40894473545662974060510967)
        ·
          refine ⟨61341710318494461090766451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40894473545662974060510967 61341710318494461090766451)
          ·
            refine ⟨92012565477741691636149677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61341710318494461090766451 92012565477741691636149677)
            ·
              refine ⟨34504712054153134363556129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92012565477741691636149677 34504712054153134363556129)
              ·
                refine ⟨25878534040614850772667097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34504712054153134363556129 25878534040614850772667097)
                ·
                  refine ⟨19408900530461138079500323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25878534040614850772667097 19408900530461138079500323)
                  ·
                    refine ⟨29113350795691707119250485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19408900530461138079500323 29113350795691707119250485)
                    ·
                      refine ⟨2729376637096097542429733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29113350795691707119250485 2729376637096097542429733)
                      ·
                        rfl

theorem cell23_5315442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_5315442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315442 prefixEnd_5315442 := by exact prefixLift 5315442
  have htrace : WordTrace (prefixWord ++ tailWord_5315442) baseStart_5315442 baseEnd_5315442 := by
    simpa [prefixWord, tailWord_5315442, baseEnd_5315442] using wordTrace_append hprefix tailTrace_5315442
  have hstable : (prefixWord ++ tailWord_5315442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315442).length < 2 ^ (prefixWord ++ tailWord_5315442).sum := by decide
  have hdescent : baseEnd_5315442 < baseStart_5315442 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5315479 : List Nat := [1, 1, 3, 3, 1, 2, 3, 4, 5]
def baseStart_5315479 : Nat := 118140960795 + 5315479 * 2 ^ 59
def prefixEnd_5315479 : Nat := 4983230072969 + 3 ^ 40 * 5315479 * 2
def baseEnd_5315479 : Nat := 303266181764479321963007

theorem tailTrace_5315479 : CollatzResearch.WordTrace tailWord_5315479 prefixEnd_5315479 303266181764479321963007 := by
  unfold tailWord_5315479
  simp only [CollatzResearch.WordTrace]
  refine ⟨193871446309934869383741491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129247630873289912922494327 193871446309934869383741491)
  ·
    refine ⟨290807169464902304075612237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 193871446309934869383741491 290807169464902304075612237)
    ·
      refine ⟨109052688549338364028354589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 290807169464902304075612237 109052688549338364028354589)
      ·
        refine ⟨40894758206001886510632971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109052688549338364028354589 40894758206001886510632971)
        ·
          refine ⟨61342137309002829765949457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40894758206001886510632971 61342137309002829765949457)
          ·
            refine ⟨46006602981752122324462093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61342137309002829765949457 46006602981752122324462093)
            ·
              refine ⟨17252476118157045871673285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46006602981752122324462093 17252476118157045871673285)
              ·
                refine ⟨3234839272154446100938741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17252476118157045871673285 3234839272154446100938741)
                ·
                  refine ⟨303266181764479321963007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3234839272154446100938741 303266181764479321963007)
                  ·
                    rfl

theorem cell23_5315479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 4, 5].length) (baseStart_5315479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5315479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5315479 prefixEnd_5315479 := by exact prefixLift 5315479
  have htrace : WordTrace (prefixWord ++ tailWord_5315479) baseStart_5315479 baseEnd_5315479 := by
    simpa [prefixWord, tailWord_5315479, baseEnd_5315479] using wordTrace_append hprefix tailTrace_5315479
  have hstable : (prefixWord ++ tailWord_5315479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5315479).length < 2 ^ (prefixWord ++ tailWord_5315479).sum := by decide
  have hdescent : baseEnd_5315479 < baseStart_5315479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5315479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
