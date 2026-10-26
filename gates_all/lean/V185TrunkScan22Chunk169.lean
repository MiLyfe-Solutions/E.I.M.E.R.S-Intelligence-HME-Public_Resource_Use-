import V185TrunkScan22Chunk168

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1507613 : List Nat := [1, 4, 2, 3, 2, 2, 2, 2, 4]
def baseStart_1507613 : Nat := 118140960795 + 1507613 * 2 ^ 59
def prefixEnd_1507613 : Nat := 4983230072969 + 3 ^ 40 * 1507613 * 2
def baseEnd_1507613 : Nat := 172028913325981153534249

theorem tailTrace_1507613 : CollatzResearch.WordTrace tailWord_1507613 prefixEnd_1507613 172028913325981153534249 := by
  unfold tailWord_1507613
  simp only [CollatzResearch.WordTrace]
  refine ⟨54987163487183055646495493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36658108991455370430996995 54987163487183055646495493)
  ·
    refine ⟨10310093153846822933717905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54987163487183055646495493 10310093153846822933717905)
    ·
      refine ⟨7732569865385117200288429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10310093153846822933717905 7732569865385117200288429)
      ·
        refine ⟨2899713699519418950108161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7732569865385117200288429 2899713699519418950108161)
        ·
          refine ⟨2174785274639564212581121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2899713699519418950108161 2174785274639564212581121)
          ·
            refine ⟨1631088955979673159435841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2174785274639564212581121 1631088955979673159435841)
            ·
              refine ⟨1223316716984754869576881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631088955979673159435841 1223316716984754869576881)
              ·
                refine ⟨917487537738566152182661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1223316716984754869576881 917487537738566152182661)
                ·
                  refine ⟨172028913325981153534249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917487537738566152182661 172028913325981153534249)
                  ·
                    rfl

theorem cell22_1507613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_1507613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507613 prefixEnd_1507613 := by exact prefixLift 1507613
  have htrace : WordTrace (prefixWord ++ tailWord_1507613) baseStart_1507613 baseEnd_1507613 := by
    simpa [prefixWord, tailWord_1507613, baseEnd_1507613] using wordTrace_append hprefix tailTrace_1507613
  have hstable : (prefixWord ++ tailWord_1507613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507613).length < 2 ^ (prefixWord ++ tailWord_1507613).sum := by decide
  have hdescent : baseEnd_1507613 < baseStart_1507613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507624 : List Nat := [2, 1, 5, 1, 3, 2, 1, 7]
def baseStart_1507624 : Nat := 118140960795 + 1507624 * 2 ^ 59
def prefixEnd_1507624 : Nat := 4983230072969 + 3 ^ 40 * 1507624 * 2
def baseEnd_1507624 : Nat := 57343389500304788730857

theorem tailTrace_1507624 : CollatzResearch.WordTrace tailWord_1507624 prefixEnd_1507624 57343389500304788730857 := by
  unfold tailWord_1507624
  simp only [CollatzResearch.WordTrace]
  refine ⟨27493782345071602262572963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36658376460095469683430617 27493782345071602262572963)
  ·
    refine ⟨41240673517607403393859445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27493782345071602262572963 41240673517607403393859445)
    ·
      refine ⟨3866313142275694068174323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41240673517607403393859445 3866313142275694068174323)
      ·
        refine ⟨5799469713413541102261485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3866313142275694068174323 5799469713413541102261485)
        ·
          refine ⟨2174801142530077913348057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5799469713413541102261485 2174801142530077913348057)
          ·
            refine ⟨1631100856897558435011043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2174801142530077913348057 1631100856897558435011043)
            ·
              refine ⟨2446651285346337652516565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631100856897558435011043 2446651285346337652516565)
              ·
                refine ⟨57343389500304788730857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2446651285346337652516565 57343389500304788730857)
                ·
                  rfl

theorem cell22_1507624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 7].length) (baseStart_1507624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507624 prefixEnd_1507624 := by exact prefixLift 1507624
  have htrace : WordTrace (prefixWord ++ tailWord_1507624) baseStart_1507624 baseEnd_1507624 := by
    simpa [prefixWord, tailWord_1507624, baseEnd_1507624] using wordTrace_append hprefix tailTrace_1507624
  have hstable : (prefixWord ++ tailWord_1507624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507624).length < 2 ^ (prefixWord ++ tailWord_1507624).sum := by decide
  have hdescent : baseEnd_1507624 < baseStart_1507624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507746 : List Nat := [3, 3, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_1507746 : Nat := 118140960795 + 1507746 * 2 ^ 59
def prefixEnd_1507746 : Nat := 4983230072969 + 3 ^ 40 * 1507746 * 2
def baseEnd_1507746 : Nat := 516132268595975447027339

theorem tailTrace_1507746 : CollatzResearch.WordTrace tailWord_1507746 prefixEnd_1507746 516132268595975447027339 := by
  unfold tailWord_1507746
  simp only [CollatzResearch.WordTrace]
  refine ⟨13748003598925304840271773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36661342930467479574058061 13748003598925304840271773)
  ·
    refine ⟨5155501349596989315101915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13748003598925304840271773 5155501349596989315101915)
    ·
      refine ⟨7733252024395483972652873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5155501349596989315101915 7733252024395483972652873)
      ·
        refine ⟨5799939018296612979489655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7733252024395483972652873 5799939018296612979489655)
        ·
          refine ⟨8699908527444919469234483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5799939018296612979489655 8699908527444919469234483)
          ·
            refine ⟨13049862791167379203851725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8699908527444919469234483 13049862791167379203851725)
            ·
              refine ⟨4893698546687767201444397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13049862791167379203851725 4893698546687767201444397)
              ·
                refine ⟨1835136955007912700541649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4893698546687767201444397 1835136955007912700541649)
                ·
                  refine ⟨1376352716255934525406237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1835136955007912700541649 1376352716255934525406237)
                  ·
                    refine ⟨516132268595975447027339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1376352716255934525406237 516132268595975447027339)
                    ·
                      rfl

theorem cell22_1507746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_1507746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507746 prefixEnd_1507746 := by exact prefixLift 1507746
  have htrace : WordTrace (prefixWord ++ tailWord_1507746) baseStart_1507746 baseEnd_1507746 := by
    simpa [prefixWord, tailWord_1507746, baseEnd_1507746] using wordTrace_append hprefix tailTrace_1507746
  have hstable : (prefixWord ++ tailWord_1507746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507746).length < 2 ^ (prefixWord ++ tailWord_1507746).sum := by decide
  have hdescent : baseEnd_1507746 < baseStart_1507746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507832 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 8]
def baseStart_1507832 : Nat := 118140960795 + 1507832 * 2 ^ 59
def prefixEnd_1507832 : Nat := 4983230072969 + 3 ^ 40 * 1507832 * 2
def baseEnd_1507832 : Nat := 172053902717833296459025

theorem tailTrace_1507832 : CollatzResearch.WordTrace tailWord_1507832 prefixEnd_1507832 172053902717833296459025 := by
  unfold tailWord_1507832
  simp only [CollatzResearch.WordTrace]
  refine ⟨27497575536694828024358875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36663434048926437365811833 27497575536694828024358875)
  ·
    refine ⟨41246363305042242036538313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27497575536694828024358875 41246363305042242036538313)
    ·
      refine ⟨30934772478781681527403735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41246363305042242036538313 30934772478781681527403735)
      ·
        refine ⟨46402158718172522291105603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30934772478781681527403735 46402158718172522291105603)
        ·
          refine ⟨69603238077258783436658405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46402158718172522291105603 69603238077258783436658405)
          ·
            refine ⟨13050607139486021894373451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69603238077258783436658405 13050607139486021894373451)
            ·
              refine ⟨19575910709229032841560177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13050607139486021894373451 19575910709229032841560177)
              ·
                refine ⟨14681933031921774631170133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19575910709229032841560177 14681933031921774631170133)
                ·
                  refine ⟨172053902717833296459025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14681933031921774631170133 172053902717833296459025)
                  ·
                    rfl

theorem cell22_1507832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 8].length) (baseStart_1507832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507832 prefixEnd_1507832 := by exact prefixLift 1507832
  have htrace : WordTrace (prefixWord ++ tailWord_1507832) baseStart_1507832 baseEnd_1507832 := by
    simpa [prefixWord, tailWord_1507832, baseEnd_1507832] using wordTrace_append hprefix tailTrace_1507832
  have hstable : (prefixWord ++ tailWord_1507832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507832).length < 2 ^ (prefixWord ++ tailWord_1507832).sum := by decide
  have hdescent : baseEnd_1507832 < baseStart_1507832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507853 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_1507853 : Nat := 118140960795 + 1507853 * 2 ^ 59
def prefixEnd_1507853 : Nat := 4983230072969 + 3 ^ 40 * 1507853 * 2
def baseEnd_1507853 : Nat := 516168896882662834602011

theorem tailTrace_1507853 : CollatzResearch.WordTrace tailWord_1507853 prefixEnd_1507853 516168896882662834602011 := by
  unfold tailWord_1507853
  simp only [CollatzResearch.WordTrace]
  refine ⟨54995917006313576635232213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36663944670875717756821475 54995917006313576635232213)
  ·
    refine ⟨1288966804835474452388255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 54995917006313576635232213 1288966804835474452388255)
    ·
      refine ⟨1933450207253211678582383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1288966804835474452388255 1933450207253211678582383)
      ·
        refine ⟨2900175310879817517873575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933450207253211678582383 2900175310879817517873575)
        ·
          refine ⟨4350262966319726276810363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2900175310879817517873575 4350262966319726276810363)
          ·
            refine ⟨6525394449479589415215545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4350262966319726276810363 6525394449479589415215545)
            ·
              refine ⟨4894045837109692061411659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6525394449479589415215545 4894045837109692061411659)
              ·
                refine ⟨7341068755664538092117489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4894045837109692061411659 7341068755664538092117489)
                ·
                  refine ⟨5505801566748403569088117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7341068755664538092117489 5505801566748403569088117)
                  ·
                    refine ⟨516168896882662834602011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5505801566748403569088117 516168896882662834602011)
                    ·
                      rfl

theorem cell22_1507853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_1507853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507853 prefixEnd_1507853 := by exact prefixLift 1507853
  have htrace : WordTrace (prefixWord ++ tailWord_1507853) baseStart_1507853 baseEnd_1507853 := by
    simpa [prefixWord, tailWord_1507853, baseEnd_1507853] using wordTrace_append hprefix tailTrace_1507853
  have hstable : (prefixWord ++ tailWord_1507853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507853).length < 2 ^ (prefixWord ++ tailWord_1507853).sum := by decide
  have hdescent : baseEnd_1507853 < baseStart_1507853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1507943 : List Nat := [1, 1, 5, 1, 1, 1, 1, 7, 1, 3]
def baseStart_1507943 : Nat := 118140960795 + 1507943 * 2 ^ 59
def prefixEnd_1507943 : Nat := 4983230072969 + 3 ^ 40 * 1507943 * 2
def baseEnd_1507943 : Nat := 516199705721932599851735

theorem tailTrace_1507943 : CollatzResearch.WordTrace tailWord_1507943 prefixEnd_1507943 516199705721932599851735 := by
  unfold tailWord_1507943
  simp only [CollatzResearch.WordTrace]
  refine ⟨54999199575987522006008483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36666133050658348004005655 54999199575987522006008483)
  ·
    refine ⟨82498799363981283009012725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54999199575987522006008483 82498799363981283009012725)
    ·
      refine ⟨7734262440373245282094943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82498799363981283009012725 7734262440373245282094943)
      ·
        refine ⟨11601393660559867923142415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7734262440373245282094943 11601393660559867923142415)
        ·
          refine ⟨17402090490839801884713623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11601393660559867923142415 17402090490839801884713623)
          ·
            refine ⟨26103135736259702827070435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17402090490839801884713623 26103135736259702827070435)
            ·
              refine ⟨39154703604389554240605653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26103135736259702827070435 39154703604389554240605653)
              ·
                refine ⟨917688365727880177514195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 39154703604389554240605653 917688365727880177514195)
                ·
                  refine ⟨1376532548591820266271293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 917688365727880177514195 1376532548591820266271293)
                  ·
                    refine ⟨516199705721932599851735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1376532548591820266271293 516199705721932599851735)
                    ·
                      rfl

theorem cell22_1507943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 7, 1, 3].length) (baseStart_1507943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1507943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1507943 prefixEnd_1507943 := by exact prefixLift 1507943
  have htrace : WordTrace (prefixWord ++ tailWord_1507943) baseStart_1507943 baseEnd_1507943 := by
    simpa [prefixWord, tailWord_1507943, baseEnd_1507943] using wordTrace_append hprefix tailTrace_1507943
  have hstable : (prefixWord ++ tailWord_1507943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1507943).length < 2 ^ (prefixWord ++ tailWord_1507943).sum := by decide
  have hdescent : baseEnd_1507943 < baseStart_1507943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1507943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508007 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 5]
def baseStart_1508007 : Nat := 118140960795 + 1508007 * 2 ^ 59
def prefixEnd_1508007 : Nat := 4983230072969 + 3 ^ 40 * 1508007 * 2
def baseEnd_1508007 : Nat := 172073871409952588750513

theorem tailTrace_1508007 : CollatzResearch.WordTrace tailWord_1508007 prefixEnd_1508007 172073871409952588750513 := by
  unfold tailWord_1508007
  simp only [CollatzResearch.WordTrace]
  refine ⟨55001533847755660936338275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36667689231837107290892183 55001533847755660936338275)
  ·
    refine ⟨82502300771633491404507413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55001533847755660936338275 82502300771633491404507413)
    ·
      refine ⟨3867295348670319909586285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82502300771633491404507413 3867295348670319909586285)
      ·
        refine ⟨1450235755751369966094857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3867295348670319909586285 1450235755751369966094857)
        ·
          refine ⟨1087676816813527474571143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1450235755751369966094857 1087676816813527474571143)
          ·
            refine ⟨1631515225220291211856715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1087676816813527474571143 1631515225220291211856715)
            ·
              refine ⟨2447272837830436817785073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631515225220291211856715 2447272837830436817785073)
              ·
                refine ⟨1835454628372827613338805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2447272837830436817785073 1835454628372827613338805)
                ·
                  refine ⟨172073871409952588750513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1835454628372827613338805 172073871409952588750513)
                  ·
                    rfl

theorem cell22_1508007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 5].length) (baseStart_1508007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508007 prefixEnd_1508007 := by exact prefixLift 1508007
  have htrace : WordTrace (prefixWord ++ tailWord_1508007) baseStart_1508007 baseEnd_1508007 := by
    simpa [prefixWord, tailWord_1508007, baseEnd_1508007] using wordTrace_append hprefix tailTrace_1508007
  have hstable : (prefixWord ++ tailWord_1508007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508007).length < 2 ^ (prefixWord ++ tailWord_1508007).sum := by decide
  have hdescent : baseEnd_1508007 < baseStart_1508007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508046 : List Nat := [4, 1, 1, 1, 3, 3, 1, 8]
def baseStart_1508046 : Nat := 118140960795 + 1508046 * 2 ^ 59
def prefixEnd_1508046 : Nat := 4983230072969 + 3 ^ 40 * 1508046 * 2
def baseEnd_1508046 : Nat := 57359440525208296058491

theorem tailTrace_1508046 : CollatzResearch.WordTrace tailWord_1508046 prefixEnd_1508046 57359440525208296058491 := by
  unfold tailWord_1508046
  simp only [CollatzResearch.WordTrace]
  refine ⟨6875369536826796324625999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36668637529742913731338661 6875369536826796324625999)
  ·
    refine ⟨10313054305240194486938999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6875369536826796324625999 10313054305240194486938999)
    ·
      refine ⟨15469581457860291730408499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10313054305240194486938999 15469581457860291730408499)
      ·
        refine ⟨23204372186790437595612749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15469581457860291730408499 23204372186790437595612749)
        ·
          refine ⟨8701639570046414098354781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23204372186790437595612749 8701639570046414098354781)
          ·
            refine ⟨3263114838767405286883043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8701639570046414098354781 3263114838767405286883043)
            ·
              refine ⟨4894672258151107930324565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263114838767405286883043 4894672258151107930324565)
              ·
                refine ⟨57359440525208296058491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4894672258151107930324565 57359440525208296058491)
                ·
                  rfl

theorem cell22_1508046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_1508046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508046 prefixEnd_1508046 := by exact prefixLift 1508046
  have htrace : WordTrace (prefixWord ++ tailWord_1508046) baseStart_1508046 baseEnd_1508046 := by
    simpa [prefixWord, tailWord_1508046, baseEnd_1508046] using wordTrace_append hprefix tailTrace_1508046
  have hstable : (prefixWord ++ tailWord_1508046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508046).length < 2 ^ (prefixWord ++ tailWord_1508046).sum := by decide
  have hdescent : baseEnd_1508046 < baseStart_1508046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508052 : List Nat := [2, 4, 1, 3, 2, 2, 1, 3, 4]
def baseStart_1508052 : Nat := 118140960795 + 1508052 * 2 ^ 59
def prefixEnd_1508052 : Nat := 4983230072969 + 3 ^ 40 * 1508052 * 2
def baseEnd_1508052 : Nat := 172079006216497549625467

theorem tailTrace_1508052 : CollatzResearch.WordTrace tailWord_1508052 prefixEnd_1508052 172079006216497549625467 := by
  unfold tailWord_1508052
  simp only [CollatzResearch.WordTrace]
  refine ⟨27501587566296316810863205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36668783421728422414484273 27501587566296316810863205)
  ·
    refine ⟨5156547668680559402036851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27501587566296316810863205 5156547668680559402036851)
    ·
      refine ⟨7734821503020839103055277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5156547668680559402036851 7734821503020839103055277)
      ·
        refine ⟨2900558063632814663645729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7734821503020839103055277 2900558063632814663645729)
        ·
          refine ⟨2175418547724610997734297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2900558063632814663645729 2175418547724610997734297)
          ·
            refine ⟨1631563910793458248300723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2175418547724610997734297 1631563910793458248300723)
            ·
              refine ⟨2447345866190187372451085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1631563910793458248300723 2447345866190187372451085)
              ·
                refine ⟨917754699821320264669157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2447345866190187372451085 917754699821320264669157)
                ·
                  refine ⟨172079006216497549625467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917754699821320264669157 172079006216497549625467)
                  ·
                    rfl

theorem cell22_1508052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_1508052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508052 prefixEnd_1508052 := by exact prefixLift 1508052
  have htrace : WordTrace (prefixWord ++ tailWord_1508052) baseStart_1508052 baseEnd_1508052 := by
    simpa [prefixWord, tailWord_1508052, baseEnd_1508052] using wordTrace_append hprefix tailTrace_1508052
  have hstable : (prefixWord ++ tailWord_1508052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508052).length < 2 ^ (prefixWord ++ tailWord_1508052).sum := by decide
  have hdescent : baseEnd_1508052 < baseStart_1508052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508059 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 6, 6]
def baseStart_1508059 : Nat := 118140960795 + 1508059 * 2 ^ 59
def prefixEnd_1508059 : Nat := 4983230072969 + 3 ^ 40 * 1508059 * 2
def baseEnd_1508059 : Nat := 516239414892546963951379

theorem tailTrace_1508059 : CollatzResearch.WordTrace tailWord_1508059 prefixEnd_1508059 516239414892546963951379 := by
  unfold tailWord_1508059
  simp only [CollatzResearch.WordTrace]
  refine ⟨55003430443567273817231231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36668953629044849211487487 55003430443567273817231231)
  ·
    refine ⟨82505145665350910725846847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55003430443567273817231231 82505145665350910725846847)
    ·
      refine ⟨123757718498026366088770271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82505145665350910725846847 123757718498026366088770271)
      ·
        refine ⟨185636577747039549133155407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123757718498026366088770271 185636577747039549133155407)
        ·
          refine ⟨278454866620559323699733111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185636577747039549133155407 278454866620559323699733111)
          ·
            refine ⟨417682299930838985549599667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278454866620559323699733111 417682299930838985549599667)
            ·
              refine ⟨626523449896258478324399501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 417682299930838985549599667 626523449896258478324399501)
              ·
                refine ⟨234946293711096929371649813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 626523449896258478324399501 234946293711096929371649813)
                ·
                  refine ⟨11013107517707668564296085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 234946293711096929371649813 11013107517707668564296085)
                  ·
                    refine ⟨516239414892546963951379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11013107517707668564296085 516239414892546963951379)
                    ·
                      rfl

theorem cell22_1508059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 6, 6].length) (baseStart_1508059 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508059 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508059 prefixEnd_1508059 := by exact prefixLift 1508059
  have htrace : WordTrace (prefixWord ++ tailWord_1508059) baseStart_1508059 baseEnd_1508059 := by
    simpa [prefixWord, tailWord_1508059, baseEnd_1508059] using wordTrace_append hprefix tailTrace_1508059
  have hstable : (prefixWord ++ tailWord_1508059).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508059).length < 2 ^ (prefixWord ++ tailWord_1508059).sum := by decide
  have hdescent : baseEnd_1508059 < baseStart_1508059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508084 : List Nat := [2, 6, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_1508084 : Nat := 118140960795 + 1508084 * 2 ^ 59
def prefixEnd_1508084 : Nat := 4983230072969 + 3 ^ 40 * 1508084 * 2
def baseEnd_1508084 : Nat := 516247972903455232076303

theorem tailTrace_1508084 : CollatzResearch.WordTrace tailWord_1508084 prefixEnd_1508084 516247972903455232076303 := by
  unfold tailWord_1508084
  simp only [CollatzResearch.WordTrace]
  refine ⟨27502171134238351543445653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36669561512317802057927537 27502171134238351543445653)
  ·
    refine ⟨1289164271917422728599015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27502171134238351543445653 1289164271917422728599015)
    ·
      refine ⟨1933746407876134092898523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1289164271917422728599015 1933746407876134092898523)
      ·
        refine ⟨2900619611814201139347785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1933746407876134092898523 2900619611814201139347785)
        ·
          refine ⟨2175464708860650854510839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2900619611814201139347785 2175464708860650854510839)
          ·
            refine ⟨3263197063290976281766259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2175464708860650854510839 3263197063290976281766259)
            ·
              refine ⟨4894795594936464422649389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263197063290976281766259 4894795594936464422649389)
              ·
                refine ⟨1835548348101174158493521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4894795594936464422649389 1835548348101174158493521)
                ·
                  refine ⟨1376661261075880618870141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1835548348101174158493521 1376661261075880618870141)
                  ·
                    refine ⟨516247972903455232076303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1376661261075880618870141 516247972903455232076303)
                    ·
                      rfl

theorem cell22_1508084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_1508084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508084 prefixEnd_1508084 := by exact prefixLift 1508084
  have htrace : WordTrace (prefixWord ++ tailWord_1508084) baseStart_1508084 baseEnd_1508084 := by
    simpa [prefixWord, tailWord_1508084, baseEnd_1508084] using wordTrace_append hprefix tailTrace_1508084
  have hstable : (prefixWord ++ tailWord_1508084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508084).length < 2 ^ (prefixWord ++ tailWord_1508084).sum := by decide
  have hdescent : baseEnd_1508084 < baseStart_1508084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508168 : List Nat := [2, 1, 3, 1, 1, 3, 2, 2, 4, 3]
def baseStart_1508168 : Nat := 118140960795 + 1508168 * 2 ^ 59
def prefixEnd_1508168 : Nat := 4983230072969 + 3 ^ 40 * 1508168 * 2
def baseEnd_1508168 : Nat := 516276727820107012976045

theorem tailTrace_1508168 : CollatzResearch.WordTrace tailWord_1508168 prefixEnd_1508168 516276727820107012976045 := by
  unfold tailWord_1508168
  simp only [CollatzResearch.WordTrace]
  refine ⟨27503703000086192716474579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36671604000114923621966105 27503703000086192716474579)
  ·
    refine ⟨41255554500129289074711869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27503703000086192716474579 41255554500129289074711869)
    ·
      refine ⟨15470832937548483403016951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41255554500129289074711869 15470832937548483403016951)
      ·
        refine ⟨23206249406322725104525427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15470832937548483403016951 23206249406322725104525427)
        ·
          refine ⟨34809374109484087656788141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23206249406322725104525427 34809374109484087656788141)
          ·
            refine ⟨13053515291056532871295553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34809374109484087656788141 13053515291056532871295553)
            ·
              refine ⟨9790136468292399653471665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13053515291056532871295553 9790136468292399653471665)
              ·
                refine ⟨7342602351219299740103749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9790136468292399653471665 7342602351219299740103749)
                ·
                  refine ⟨1376737940853618701269453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7342602351219299740103749 1376737940853618701269453)
                  ·
                    refine ⟨516276727820107012976045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1376737940853618701269453 516276727820107012976045)
                    ·
                      rfl

theorem cell22_1508168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 2, 4, 3].length) (baseStart_1508168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508168 prefixEnd_1508168 := by exact prefixLift 1508168
  have htrace : WordTrace (prefixWord ++ tailWord_1508168) baseStart_1508168 baseEnd_1508168 := by
    simpa [prefixWord, tailWord_1508168, baseEnd_1508168] using wordTrace_append hprefix tailTrace_1508168
  have hstable : (prefixWord ++ tailWord_1508168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508168).length < 2 ^ (prefixWord ++ tailWord_1508168).sum := by decide
  have hdescent : baseEnd_1508168 < baseStart_1508168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508172 : List Nat := [2, 2, 1, 3, 3, 3, 2, 1, 1, 4]
def baseStart_1508172 : Nat := 118140960795 + 1508172 * 2 ^ 59
def prefixEnd_1508172 : Nat := 4983230072969 + 3 ^ 40 * 1508172 * 2
def baseEnd_1508172 : Nat := 516278097101852335876033

theorem tailTrace_1508172 : CollatzResearch.WordTrace tailWord_1508172 prefixEnd_1508172 516278097101852335876033 := by
  unfold tailWord_1508172
  simp only [CollatzResearch.WordTrace]
  refine ⟨27503775946078947058047385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36671701261438596077396513 27503775946078947058047385)
  ·
    refine ⟨20627831959559210293535539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27503775946078947058047385 20627831959559210293535539)
    ·
      refine ⟨30941747939338815440303309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20627831959559210293535539 30941747939338815440303309)
      ·
        refine ⟨11603155477252055790113741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30941747939338815440303309 11603155477252055790113741)
        ·
          refine ⟨4351183303969520921292653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11603155477252055790113741 4351183303969520921292653)
          ·
            refine ⟨1631693738988570345484745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4351183303969520921292653 1631693738988570345484745)
            ·
              refine ⟨1223770304241427759113559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631693738988570345484745 1223770304241427759113559)
              ·
                refine ⟨1835655456362141638670339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223770304241427759113559 1835655456362141638670339)
                ·
                  refine ⟨2753483184543212458005509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1835655456362141638670339 2753483184543212458005509)
                  ·
                    refine ⟨516278097101852335876033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2753483184543212458005509 516278097101852335876033)
                    ·
                      rfl

theorem cell22_1508172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_1508172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508172 prefixEnd_1508172 := by exact prefixLift 1508172
  have htrace : WordTrace (prefixWord ++ tailWord_1508172) baseStart_1508172 baseEnd_1508172 := by
    simpa [prefixWord, tailWord_1508172, baseEnd_1508172] using wordTrace_append hprefix tailTrace_1508172
  have hstable : (prefixWord ++ tailWord_1508172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508172).length < 2 ^ (prefixWord ++ tailWord_1508172).sum := by decide
  have hdescent : baseEnd_1508172 < baseStart_1508172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508181 : List Nat := [1, 3, 2, 2, 2, 1, 11]
def baseStart_1508181 : Nat := 118140960795 + 1508181 * 2 ^ 59
def prefixEnd_1508181 : Nat := 4983230072969 + 3 ^ 40 * 1508181 * 2
def baseEnd_1508181 : Nat := 19121525110584418977815

theorem tailTrace_1508181 : CollatzResearch.WordTrace tailWord_1508181 prefixEnd_1508181 19121525110584418977815 := by
  unfold tailWord_1508181
  simp only [CollatzResearch.WordTrace]
  refine ⟨55007880149125288653172397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36671920099416859102114931 55007880149125288653172397)
  ·
    refine ⟨20627955055921983244939649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55007880149125288653172397 20627955055921983244939649)
    ·
      refine ⟨15470966291941487433704737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20627955055921983244939649 15470966291941487433704737)
      ·
        refine ⟨11603224718956115575278553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15470966291941487433704737 11603224718956115575278553)
        ·
          refine ⟨8702418539217086681458915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11603224718956115575278553 8702418539217086681458915)
          ·
            refine ⟨13053627808825630022188373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8702418539217086681458915 13053627808825630022188373)
            ·
              refine ⟨19121525110584418977815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 13053627808825630022188373 19121525110584418977815)
              ·
                rfl

theorem cell22_1508181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 11].length) (baseStart_1508181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508181 prefixEnd_1508181 := by exact prefixLift 1508181
  have htrace : WordTrace (prefixWord ++ tailWord_1508181) baseStart_1508181 baseEnd_1508181 := by
    simpa [prefixWord, tailWord_1508181, baseEnd_1508181] using wordTrace_append hprefix tailTrace_1508181
  have hstable : (prefixWord ++ tailWord_1508181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508181).length < 2 ^ (prefixWord ++ tailWord_1508181).sum := by decide
  have hdescent : baseEnd_1508181 < baseStart_1508181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508185 : List Nat := [1, 2, 1, 2, 2, 4, 3, 2, 2, 3]
def baseStart_1508185 : Nat := 118140960795 + 1508185 * 2 ^ 59
def prefixEnd_1508185 : Nat := 4983230072969 + 3 ^ 40 * 1508185 * 2
def baseEnd_1508185 : Nat := 516282547267524635300993

theorem tailTrace_1508185 : CollatzResearch.WordTrace tailWord_1508185 prefixEnd_1508185 516282547267524635300993 := by
  unfold tailWord_1508185
  simp only [CollatzResearch.WordTrace]
  refine ⟨55008026041110797336318009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36672017360740531557545339 55008026041110797336318009)
  ·
    refine ⟨41256019530833098002238507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55008026041110797336318009 41256019530833098002238507)
    ·
      refine ⟨61884029296249647003357761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41256019530833098002238507 61884029296249647003357761)
      ·
        refine ⟨46413021972187235252518321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61884029296249647003357761 46413021972187235252518321)
        ·
          refine ⟨34809766479140426439388741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46413021972187235252518321 34809766479140426439388741)
          ·
            refine ⟨6526831214838829957385389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34809766479140426439388741 6526831214838829957385389)
            ·
              refine ⟨2447561705564561234019521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6526831214838829957385389 2447561705564561234019521)
              ·
                refine ⟨1835671279173420925514641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2447561705564561234019521 1835671279173420925514641)
                ·
                  refine ⟨1376753459380065694135981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1835671279173420925514641 1376753459380065694135981)
                  ·
                    refine ⟨516282547267524635300993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1376753459380065694135981 516282547267524635300993)
                    ·
                      rfl

theorem cell22_1508185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_1508185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508185 prefixEnd_1508185 := by exact prefixLift 1508185
  have htrace : WordTrace (prefixWord ++ tailWord_1508185) baseStart_1508185 baseEnd_1508185 := by
    simpa [prefixWord, tailWord_1508185, baseEnd_1508185] using wordTrace_append hprefix tailTrace_1508185
  have hstable : (prefixWord ++ tailWord_1508185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508185).length < 2 ^ (prefixWord ++ tailWord_1508185).sum := by decide
  have hdescent : baseEnd_1508185 < baseStart_1508185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508211 : List Nat := [1, 1, 1, 2, 2, 1, 4, 2, 2, 6]
def baseStart_1508211 : Nat := 118140960795 + 1508211 * 2 ^ 59
def prefixEnd_1508211 : Nat := 4983230072969 + 3 ^ 40 * 1508211 * 2
def baseEnd_1508211 : Nat := 516291447598869234150913

theorem tailTrace_1508211 : CollatzResearch.WordTrace tailWord_1508211 prefixEnd_1508211 516291447598869234150913 := by
  unfold tailWord_1508211
  simp only [CollatzResearch.WordTrace]
  refine ⟨55008974339016603776764487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36672649559344402517842991 55008974339016603776764487)
  ·
    refine ⟨82513461508524905665146731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55008974339016603776764487 82513461508524905665146731)
    ·
      refine ⟨123770192262787358497720097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82513461508524905665146731 123770192262787358497720097)
      ·
        refine ⟨92827644197090518873290073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123770192262787358497720097 92827644197090518873290073)
        ·
          refine ⟨69620733147817889154967555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92827644197090518873290073 69620733147817889154967555)
          ·
            refine ⟨104431099721726833732451333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69620733147817889154967555 104431099721726833732451333)
            ·
              refine ⟨19580831197823781324834625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104431099721726833732451333 19580831197823781324834625)
              ·
                refine ⟨14685623398367835993625969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19580831197823781324834625 14685623398367835993625969)
                ·
                  refine ⟨11014217548775876995219477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14685623398367835993625969 11014217548775876995219477)
                  ·
                    refine ⟨516291447598869234150913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11014217548775876995219477 516291447598869234150913)
                    ·
                      rfl

theorem cell22_1508211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 6].length) (baseStart_1508211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508211 prefixEnd_1508211 := by exact prefixLift 1508211
  have htrace : WordTrace (prefixWord ++ tailWord_1508211) baseStart_1508211 baseEnd_1508211 := by
    simpa [prefixWord, tailWord_1508211, baseEnd_1508211] using wordTrace_append hprefix tailTrace_1508211
  have hstable : (prefixWord ++ tailWord_1508211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508211).length < 2 ^ (prefixWord ++ tailWord_1508211).sum := by decide
  have hdescent : baseEnd_1508211 < baseStart_1508211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508305 : List Nat := [1, 2, 2, 1, 2, 1, 5, 4, 4]
def baseStart_1508305 : Nat := 118140960795 + 1508305 * 2 ^ 59
def prefixEnd_1508305 : Nat := 4983230072969 + 3 ^ 40 * 1508305 * 2
def baseEnd_1508305 : Nat := 172107875239961440766875

theorem tailTrace_1508305 : CollatzResearch.WordTrace tailWord_1508305 prefixEnd_1508305 172107875239961440766875 := by
  unfold tailWord_1508305
  simp only [CollatzResearch.WordTrace]
  refine ⟨55012402800676057830686369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36674935200450705220457579 55012402800676057830686369)
  ·
    refine ⟨41259302100507043373014777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55012402800676057830686369 41259302100507043373014777)
    ·
      refine ⟨30944476575380282529761083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41259302100507043373014777 30944476575380282529761083)
      ·
        refine ⟨46416714863070423794641625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30944476575380282529761083 46416714863070423794641625)
        ·
          refine ⟨34812536147302817845981219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46416714863070423794641625 34812536147302817845981219)
          ·
            refine ⟨52218804220954226768971829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34812536147302817845981219 52218804220954226768971829)
            ·
              refine ⟨4895512895714458759591109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52218804220954226768971829 4895512895714458759591109)
              ·
                refine ⟨917908667946461017423333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4895512895714458759591109 917908667946461017423333)
                ·
                  refine ⟨172107875239961440766875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 917908667946461017423333 172107875239961440766875)
                  ·
                    rfl

theorem cell22_1508305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 4, 4].length) (baseStart_1508305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508305 prefixEnd_1508305 := by exact prefixLift 1508305
  have htrace : WordTrace (prefixWord ++ tailWord_1508305) baseStart_1508305 baseEnd_1508305 := by
    simpa [prefixWord, tailWord_1508305, baseEnd_1508305] using wordTrace_append hprefix tailTrace_1508305
  have hstable : (prefixWord ++ tailWord_1508305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508305).length < 2 ^ (prefixWord ++ tailWord_1508305).sum := by decide
  have hdescent : baseEnd_1508305 < baseStart_1508305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508322 : List Nat := [3, 3, 3, 1, 1, 2, 1, 2, 6]
def baseStart_1508322 : Nat := 118140960795 + 1508322 * 2 ^ 59
def prefixEnd_1508322 : Nat := 4983230072969 + 3 ^ 40 * 1508322 * 2
def baseEnd_1508322 : Nat := 172109815055767314875191

theorem tailTrace_1508322 : CollatzResearch.WordTrace tailWord_1508322 prefixEnd_1508322 172109815055767314875191 := by
  unfold tailWord_1508322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13753255710403617433513805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36675348561076313156036813 13753255710403617433513805)
  ·
    refine ⟨5157470891401356537567677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13753255710403617433513805 5157470891401356537567677)
    ·
      refine ⟨1934051584275508701587879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5157470891401356537567677 1934051584275508701587879)
      ·
        refine ⟨2901077376413263052381819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1934051584275508701587879 2901077376413263052381819)
        ·
          refine ⟨4351616064619894578572729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901077376413263052381819 4351616064619894578572729)
          ·
            refine ⟨3263712048464920933929547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4351616064619894578572729 3263712048464920933929547)
            ·
              refine ⟨4895568072697381400894321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3263712048464920933929547 4895568072697381400894321)
              ·
                refine ⟨3671676054523036050670741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4895568072697381400894321 3671676054523036050670741)
                ·
                  refine ⟨172109815055767314875191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3671676054523036050670741 172109815055767314875191)
                  ·
                    rfl

theorem cell22_1508322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_1508322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508322 prefixEnd_1508322 := by exact prefixLift 1508322
  have htrace : WordTrace (prefixWord ++ tailWord_1508322) baseStart_1508322 baseEnd_1508322 := by
    simpa [prefixWord, tailWord_1508322, baseEnd_1508322] using wordTrace_append hprefix tailTrace_1508322
  have hstable : (prefixWord ++ tailWord_1508322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508322).length < 2 ^ (prefixWord ++ tailWord_1508322).sum := by decide
  have hdescent : baseEnd_1508322 < baseStart_1508322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508335 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 2, 4]
def baseStart_1508335 : Nat := 118140960795 + 1508335 * 2 ^ 59
def prefixEnd_1508335 : Nat := 4983230072969 + 3 ^ 40 * 1508335 * 2
def baseEnd_1508335 : Nat := 516333895332974244050533

theorem tailTrace_1508335 : CollatzResearch.WordTrace tailWord_1508335 prefixEnd_1508335 516333895332974244050533 := by
  unfold tailWord_1508335
  simp only [CollatzResearch.WordTrace]
  refine ⟨55013496990567372954278459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36675664660378248636185639 55013496990567372954278459)
  ·
    refine ⟨82520245485851059431417689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55013496990567372954278459 82520245485851059431417689)
    ·
      refine ⟨61890184114388294573563267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82520245485851059431417689 61890184114388294573563267)
      ·
        refine ⟨92835276171582441860344901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61890184114388294573563267 92835276171582441860344901)
        ·
          refine ⟨17406614282171707848814669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92835276171582441860344901 17406614282171707848814669)
          ·
            refine ⟨6527480355814390443305501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17406614282171707848814669 6527480355814390443305501)
            ·
              refine ⟨2447805133430396416239563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6527480355814390443305501 2447805133430396416239563)
              ·
                refine ⟨3671707700145594624359345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2447805133430396416239563 3671707700145594624359345)
                ·
                  refine ⟨2753780775109195968269509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3671707700145594624359345 2753780775109195968269509)
                  ·
                    refine ⟨516333895332974244050533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2753780775109195968269509 516333895332974244050533)
                    ·
                      rfl

theorem cell22_1508335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 2, 4].length) (baseStart_1508335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508335 prefixEnd_1508335 := by exact prefixLift 1508335
  have htrace : WordTrace (prefixWord ++ tailWord_1508335) baseStart_1508335 baseEnd_1508335 := by
    simpa [prefixWord, tailWord_1508335, baseEnd_1508335] using wordTrace_append hprefix tailTrace_1508335
  have hstable : (prefixWord ++ tailWord_1508335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508335).length < 2 ^ (prefixWord ++ tailWord_1508335).sum := by decide
  have hdescent : baseEnd_1508335 < baseStart_1508335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508384 : List Nat := [2, 1, 1, 7, 1, 2, 2, 6]
def baseStart_1508384 : Nat := 118140960795 + 1508384 * 2 ^ 59
def prefixEnd_1508384 : Nat := 4983230072969 + 3 ^ 40 * 1508384 * 2
def baseEnd_1508384 : Nat := 57372296559372716619487

theorem tailTrace_1508384 : CollatzResearch.WordTrace tailWord_1508384 prefixEnd_1508384 57372296559372716619487 := by
  unfold tailWord_1508384
  simp only [CollatzResearch.WordTrace]
  refine ⟨27507642083694927161406103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36676856111593236215208137 27507642083694927161406103)
  ·
    refine ⟨41261463125542390742109155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27507642083694927161406103 41261463125542390742109155)
    ·
      refine ⟨61892194688313586113163733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41261463125542390742109155 61892194688313586113163733)
      ·
        refine ⟨1450598313007349674527275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 61892194688313586113163733 1450598313007349674527275)
        ·
          refine ⟨2175897469511024511790913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1450598313007349674527275 2175897469511024511790913)
          ·
            refine ⟨1631923102133268383843185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2175897469511024511790913 1631923102133268383843185)
            ·
              refine ⟨1223942326599951287882389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1631923102133268383843185 1223942326599951287882389)
              ·
                refine ⟨57372296559372716619487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1223942326599951287882389 57372296559372716619487)
                ·
                  rfl

theorem cell22_1508384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 6].length) (baseStart_1508384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508384 prefixEnd_1508384 := by exact prefixLift 1508384
  have htrace : WordTrace (prefixWord ++ tailWord_1508384) baseStart_1508384 baseEnd_1508384 := by
    simpa [prefixWord, tailWord_1508384, baseEnd_1508384] using wordTrace_append hprefix tailTrace_1508384
  have hstable : (prefixWord ++ tailWord_1508384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508384).length < 2 ^ (prefixWord ++ tailWord_1508384).sum := by decide
  have hdescent : baseEnd_1508384 < baseStart_1508384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508429 : List Nat := [1, 6, 1, 1, 1, 2, 4, 1, 5]
def baseStart_1508429 : Nat := 118140960795 + 1508429 * 2 ^ 59
def prefixEnd_1508429 : Nat := 4983230072969 + 3 ^ 40 * 1508429 * 2
def baseEnd_1508429 : Nat := 172122024484663110733415

theorem tailTrace_1508429 : CollatzResearch.WordTrace tailWord_1508429 prefixEnd_1508429 172122024484663110733415 := by
  unfold tailWord_1508429
  simp only [CollatzResearch.WordTrace]
  refine ⟨55016925452226827008200341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36677950301484551338800227 55016925452226827008200341)
  ·
    refine ⟨2578918380573132516009391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 55016925452226827008200341 2578918380573132516009391)
    ·
      refine ⟨3868377570859698774014087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2578918380573132516009391 3868377570859698774014087)
      ·
        refine ⟨5802566356289548161021131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3868377570859698774014087 5802566356289548161021131)
        ·
          refine ⟨8703849534434322241531697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5802566356289548161021131 8703849534434322241531697)
          ·
            refine ⟨6527887150825741681148773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8703849534434322241531697 6527887150825741681148773)
            ·
              refine ⟨1223978840779826565215395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6527887150825741681148773 1223978840779826565215395)
              ·
                refine ⟨1835968261169739847823093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1223978840779826565215395 1835968261169739847823093)
                ·
                  refine ⟨172122024484663110733415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1835968261169739847823093 172122024484663110733415)
                  ·
                    rfl

theorem cell22_1508429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_1508429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508429 prefixEnd_1508429 := by exact prefixLift 1508429
  have htrace : WordTrace (prefixWord ++ tailWord_1508429) baseStart_1508429 baseEnd_1508429 := by
    simpa [prefixWord, tailWord_1508429, baseEnd_1508429] using wordTrace_append hprefix tailTrace_1508429
  have hstable : (prefixWord ++ tailWord_1508429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508429).length < 2 ^ (prefixWord ++ tailWord_1508429).sum := by decide
  have hdescent : baseEnd_1508429 < baseStart_1508429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508455 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1508455 : Nat := 118140960795 + 1508455 * 2 ^ 59
def prefixEnd_1508455 : Nat := 4983230072969 + 3 ^ 40 * 1508455 * 2
def baseEnd_1508455 : Nat := 516374973785333931050165

theorem tailTrace_1508455 : CollatzResearch.WordTrace tailWord_1508455 prefixEnd_1508455 516374973785333931050165 := by
  unfold tailWord_1508455
  simp only [CollatzResearch.WordTrace]
  refine ⟨55017873750132633448646819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36678582500088422299097879 55017873750132633448646819)
  ·
    refine ⟨82526810625198950172970229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55017873750132633448646819 82526810625198950172970229)
    ·
      refine ⟨7736888496112401578715959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82526810625198950172970229 7736888496112401578715959)
      ·
        refine ⟨11605332744168602368073939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7736888496112401578715959 11605332744168602368073939)
        ·
          refine ⟨17407999116252903552110909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11605332744168602368073939 17407999116252903552110909)
          ·
            refine ⟨6527999668594838832041591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17407999116252903552110909 6527999668594838832041591)
            ·
              refine ⟨9791999502892258248062387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6527999668594838832041591 9791999502892258248062387)
              ·
                refine ⟨14687999254338387372093581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9791999502892258248062387 14687999254338387372093581)
                ·
                  refine ⟨5507999720376895264535093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14687999254338387372093581 5507999720376895264535093)
                  ·
                    refine ⟨516374973785333931050165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5507999720376895264535093 516374973785333931050165)
                    ·
                      rfl

theorem cell22_1508455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1508455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508455 prefixEnd_1508455 := by exact prefixLift 1508455
  have htrace : WordTrace (prefixWord ++ tailWord_1508455) baseStart_1508455 baseEnd_1508455 := by
    simpa [prefixWord, tailWord_1508455, baseEnd_1508455] using wordTrace_append hprefix tailTrace_1508455
  have hstable : (prefixWord ++ tailWord_1508455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508455).length < 2 ^ (prefixWord ++ tailWord_1508455).sum := by decide
  have hdescent : baseEnd_1508455 < baseStart_1508455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508472 : List Nat := [2, 1, 2, 1, 1, 1, 5, 4, 2, 3]
def baseStart_1508472 : Nat := 118140960795 + 1508472 * 2 ^ 59
def prefixEnd_1508472 : Nat := 4983230072969 + 3 ^ 40 * 1508472 * 2
def baseEnd_1508472 : Nat := 516380793232751553375113

theorem tailTrace_1508472 : CollatzResearch.WordTrace tailWord_1508472 prefixEnd_1508472 516380793232751553375113 := by
  unfold tailWord_1508472
  simp only [CollatzResearch.WordTrace]
  refine ⟨27509246895535522676007835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36678995860714030234677113 27509246895535522676007835)
  ·
    refine ⟨41263870343303284014011753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27509246895535522676007835 41263870343303284014011753)
    ·
      refine ⟨30947902757477463010508815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41263870343303284014011753 30947902757477463010508815)
      ·
        refine ⟨46421854136216194515763223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30947902757477463010508815 46421854136216194515763223)
        ·
          refine ⟨69632781204324291773644835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46421854136216194515763223 69632781204324291773644835)
          ·
            refine ⟨104449171806486437660467253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69632781204324291773644835 104449171806486437660467253)
            ·
              refine ⟨9792109856858103530668805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104449171806486437660467253 9792109856858103530668805)
              ·
                refine ⟨1836020598160894412000401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9792109856858103530668805 1836020598160894412000401)
                ·
                  refine ⟨1377015448620670809000301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1836020598160894412000401 1377015448620670809000301)
                  ·
                    refine ⟨516380793232751553375113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1377015448620670809000301 516380793232751553375113)
                    ·
                      rfl

theorem cell22_1508472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 2, 3].length) (baseStart_1508472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508472 prefixEnd_1508472 := by exact prefixLift 1508472
  have htrace : WordTrace (prefixWord ++ tailWord_1508472) baseStart_1508472 baseEnd_1508472 := by
    simpa [prefixWord, tailWord_1508472, baseEnd_1508472] using wordTrace_append hprefix tailTrace_1508472
  have hstable : (prefixWord ++ tailWord_1508472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508472).length < 2 ^ (prefixWord ++ tailWord_1508472).sum := by decide
  have hdescent : baseEnd_1508472 < baseStart_1508472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508504 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 2, 4]
def baseStart_1508504 : Nat := 118140960795 + 1508504 * 2 ^ 59
def prefixEnd_1508504 : Nat := 4983230072969 + 3 ^ 40 * 1508504 * 2
def baseEnd_1508504 : Nat := 516391747486714136575015

theorem tailTrace_1508504 : CollatzResearch.WordTrace tailWord_1508504 prefixEnd_1508504 516391747486714136575015 := by
  unfold tailWord_1508504
  simp only [CollatzResearch.WordTrace]
  refine ⟨27509830463477557408590283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36679773951303409878120377 27509830463477557408590283)
  ·
    refine ⟨41264745695216336112885425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27509830463477557408590283 41264745695216336112885425)
    ·
      refine ⟨30948559271412252084664069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41264745695216336112885425 30948559271412252084664069)
      ·
        refine ⟨5802854863389797265874513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30948559271412252084664069 5802854863389797265874513)
        ·
          refine ⟨4352141147542347949405885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5802854863389797265874513 4352141147542347949405885)
          ·
            refine ⟨1632052930328380481027207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4352141147542347949405885 1632052930328380481027207)
            ·
              refine ⟨2448079395492570721540811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632052930328380481027207 2448079395492570721540811)
              ·
                refine ⟨3672119093238856082311217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2448079395492570721540811 3672119093238856082311217)
                ·
                  refine ⟨2754089319929142061733413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3672119093238856082311217 2754089319929142061733413)
                  ·
                    refine ⟨516391747486714136575015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2754089319929142061733413 516391747486714136575015)
                    ·
                      rfl

theorem cell22_1508504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 2, 4].length) (baseStart_1508504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508504 prefixEnd_1508504 := by exact prefixLift 1508504
  have htrace : WordTrace (prefixWord ++ tailWord_1508504) baseStart_1508504 baseEnd_1508504 := by
    simpa [prefixWord, tailWord_1508504, baseEnd_1508504] using wordTrace_append hprefix tailTrace_1508504
  have hstable : (prefixWord ++ tailWord_1508504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508504).length < 2 ^ (prefixWord ++ tailWord_1508504).sum := by decide
  have hdescent : baseEnd_1508504 < baseStart_1508504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508568 : List Nat := [2, 1, 2, 2, 5, 2, 1, 3, 1, 3]
def baseStart_1508568 : Nat := 118140960795 + 1508568 * 2 ^ 59
def prefixEnd_1508568 : Nat := 4983230072969 + 3 ^ 40 * 1508568 * 2
def baseEnd_1508568 : Nat := 516413655994639302974819

theorem tailTrace_1508568 : CollatzResearch.WordTrace tailWord_1508568 prefixEnd_1508568 516413655994639302974819 := by
  unfold tailWord_1508568
  simp only [CollatzResearch.WordTrace]
  refine ⟨27510997599361626873755179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36681330132482169165006905 27510997599361626873755179)
  ·
    refine ⟨41266496399042440310632769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27510997599361626873755179 41266496399042440310632769)
    ·
      refine ⟨30949872299281830232974577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41266496399042440310632769 30949872299281830232974577)
      ·
        refine ⟨23212404224461372674730933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30949872299281830232974577 23212404224461372674730933)
        ·
          refine ⟨2176162896043253688256025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23212404224461372674730933 2176162896043253688256025)
          ·
            refine ⟨1632122172032440266192019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2176162896043253688256025 1632122172032440266192019)
            ·
              refine ⟨2448183258048660399288029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632122172032440266192019 2448183258048660399288029)
              ·
                refine ⟨918068721768247649733011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2448183258048660399288029 918068721768247649733011)
                ·
                  refine ⟨1377103082652371474599517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918068721768247649733011 1377103082652371474599517)
                  ·
                    refine ⟨516413655994639302974819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1377103082652371474599517 516413655994639302974819)
                    ·
                      rfl

theorem cell22_1508568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 3, 1, 3].length) (baseStart_1508568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508568 prefixEnd_1508568 := by exact prefixLift 1508568
  have htrace : WordTrace (prefixWord ++ tailWord_1508568) baseStart_1508568 baseEnd_1508568 := by
    simpa [prefixWord, tailWord_1508568, baseEnd_1508568] using wordTrace_append hprefix tailTrace_1508568
  have hstable : (prefixWord ++ tailWord_1508568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508568).length < 2 ^ (prefixWord ++ tailWord_1508568).sum := by decide
  have hdescent : baseEnd_1508568 < baseStart_1508568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508575 : List Nat := [1, 1, 2, 3, 2, 1, 2, 2, 8]
def baseStart_1508575 : Nat := 118140960795 + 1508575 * 2 ^ 59
def prefixEnd_1508575 : Nat := 4983230072969 + 3 ^ 40 * 1508575 * 2
def baseEnd_1508575 : Nat := 172138684079231206016599

theorem tailTrace_1508575 : CollatzResearch.WordTrace tailWord_1508575 prefixEnd_1508575 172138684079231206016599 := by
  unfold tailWord_1508575
  simp only [CollatzResearch.WordTrace]
  refine ⟨55022250509697893943015179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36681500339798595962010119 55022250509697893943015179)
  ·
    refine ⟨82533375764546840914522769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55022250509697893943015179 82533375764546840914522769)
    ·
      refine ⟨61900031823410130685892077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82533375764546840914522769 61900031823410130685892077)
      ·
        refine ⟨23212511933778799007209529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61900031823410130685892077 23212511933778799007209529)
        ·
          refine ⟨17409383950334099255407147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23212511933778799007209529 17409383950334099255407147)
          ·
            refine ⟨26114075925501148883110721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17409383950334099255407147 26114075925501148883110721)
            ·
              refine ⟨19585556944125861662333041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26114075925501148883110721 19585556944125861662333041)
              ·
                refine ⟨14689167708094396246749781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19585556944125861662333041 14689167708094396246749781)
                ·
                  refine ⟨172138684079231206016599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14689167708094396246749781 172138684079231206016599)
                  ·
                    rfl

theorem cell22_1508575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 2, 8].length) (baseStart_1508575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508575 prefixEnd_1508575 := by exact prefixLift 1508575
  have htrace : WordTrace (prefixWord ++ tailWord_1508575) baseStart_1508575 baseEnd_1508575 := by
    simpa [prefixWord, tailWord_1508575, baseEnd_1508575] using wordTrace_append hprefix tailTrace_1508575
  have hstable : (prefixWord ++ tailWord_1508575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508575).length < 2 ^ (prefixWord ++ tailWord_1508575).sum := by decide
  have hdescent : baseEnd_1508575 < baseStart_1508575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508637 : List Nat := [1, 4, 2, 3, 1, 11]
def baseStart_1508637 : Nat := 118140960795 + 1508637 * 2 ^ 59
def prefixEnd_1508637 : Nat := 4983230072969 + 3 ^ 40 * 1508637 * 2
def baseEnd_1508637 : Nat := 6375768840799334851847

theorem tailTrace_1508637 : CollatzResearch.WordTrace tailWord_1508637 prefixEnd_1508637 6375768840799334851847 := by
  unfold tailWord_1508637
  simp only [CollatzResearch.WordTrace]
  refine ⟨55024511835473278531772165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36683007890315519021181443 55024511835473278531772165)
  ·
    refine ⟨10317095969151239724707281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55024511835473278531772165 10317095969151239724707281)
    ·
      refine ⟨7737821976863429793530461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10317095969151239724707281 7737821976863429793530461)
      ·
        refine ⟨2901683241323786172573923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7737821976863429793530461 2901683241323786172573923)
        ·
          refine ⟨4352524861985679258860885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2901683241323786172573923 4352524861985679258860885)
          ·
            refine ⟨6375768840799334851847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4352524861985679258860885 6375768840799334851847)
            ·
              rfl

theorem cell22_1508637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 11].length) (baseStart_1508637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508637 prefixEnd_1508637 := by exact prefixLift 1508637
  have htrace : WordTrace (prefixWord ++ tailWord_1508637) baseStart_1508637 baseEnd_1508637 := by
    simpa [prefixWord, tailWord_1508637, baseEnd_1508637] using wordTrace_append hprefix tailTrace_1508637
  have hstable : (prefixWord ++ tailWord_1508637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508637).length < 2 ^ (prefixWord ++ tailWord_1508637).sum := by decide
  have hdescent : baseEnd_1508637 < baseStart_1508637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508697 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_1508697 : Nat := 118140960795 + 1508697 * 2 ^ 59
def prefixEnd_1508697 : Nat := 4983230072969 + 3 ^ 40 * 1508697 * 2
def baseEnd_1508697 : Nat := 516457815330925966499423

theorem tailTrace_1508697 : CollatzResearch.WordTrace tailWord_1508697 prefixEnd_1508697 516457815330925966499423 := by
  unfold tailWord_1508697
  simp only [CollatzResearch.WordTrace]
  refine ⟨55026700215255908778956345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36684466810170605852637563 55026700215255908778956345)
  ·
    refine ⟨41270025161441931584217259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55026700215255908778956345 41270025161441931584217259)
    ·
      refine ⟨61905037742162897376325889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41270025161441931584217259 61905037742162897376325889)
      ·
        refine ⟨46428778306622173032244417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61905037742162897376325889 46428778306622173032244417)
        ·
          refine ⟨34821583729966629774183313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46428778306622173032244417 34821583729966629774183313)
          ·
            refine ⟨26116187797474972330637485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34821583729966629774183313 26116187797474972330637485)
            ·
              refine ⟨9793570424053114623989057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26116187797474972330637485 9793570424053114623989057)
              ·
                refine ⟨7345177818039835967991793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9793570424053114623989057 7345177818039835967991793)
                ·
                  refine ⟨5508883363529876975993845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7345177818039835967991793 5508883363529876975993845)
                  ·
                    refine ⟨516457815330925966499423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5508883363529876975993845 516457815330925966499423)
                    ·
                      rfl

theorem cell22_1508697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_1508697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508697 prefixEnd_1508697 := by exact prefixLift 1508697
  have htrace : WordTrace (prefixWord ++ tailWord_1508697) baseStart_1508697 baseEnd_1508697 := by
    simpa [prefixWord, tailWord_1508697, baseEnd_1508697] using wordTrace_append hprefix tailTrace_1508697
  have hstable : (prefixWord ++ tailWord_1508697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508697).length < 2 ^ (prefixWord ++ tailWord_1508697).sum := by decide
  have hdescent : baseEnd_1508697 < baseStart_1508697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508716 : List Nat := [2, 2, 1, 1, 5, 2, 3, 1, 5]
def baseStart_1508716 : Nat := 118140960795 + 1508716 * 2 ^ 59
def prefixEnd_1508716 : Nat := 4983230072969 + 3 ^ 40 * 1508716 * 2
def baseEnd_1508716 : Nat := 172154773139738750091455

theorem tailTrace_1508716 : CollatzResearch.WordTrace tailWord_1508716 prefixEnd_1508716 172154773139738750091455 := by
  unfold tailWord_1508716
  simp only [CollatzResearch.WordTrace]
  refine ⟨27513696601093537511949001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36684928801458050015932001 27513696601093537511949001)
  ·
    refine ⟨20635272450820153133961751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27513696601093537511949001 20635272450820153133961751)
    ·
      refine ⟨30952908676230229700942627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20635272450820153133961751 30952908676230229700942627)
      ·
        refine ⟨46429363014345344551413941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30952908676230229700942627 46429363014345344551413941)
        ·
          refine ⟨4352752782594876051695057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46429363014345344551413941 4352752782594876051695057)
          ·
            refine ⟨3264564586946157038771293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4352752782594876051695057 3264564586946157038771293)
            ·
              refine ⟨1224211720104808889539235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3264564586946157038771293 1224211720104808889539235)
              ·
                refine ⟨1836317580157213334308853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224211720104808889539235 1836317580157213334308853)
                ·
                  refine ⟨172154773139738750091455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1836317580157213334308853 172154773139738750091455)
                  ·
                    rfl

theorem cell22_1508716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 5].length) (baseStart_1508716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508716 prefixEnd_1508716 := by exact prefixLift 1508716
  have htrace : WordTrace (prefixWord ++ tailWord_1508716) baseStart_1508716 baseEnd_1508716 := by
    simpa [prefixWord, tailWord_1508716, baseEnd_1508716] using wordTrace_append hprefix tailTrace_1508716
  have hstable : (prefixWord ++ tailWord_1508716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508716).length < 2 ^ (prefixWord ++ tailWord_1508716).sum := by decide
  have hdescent : baseEnd_1508716 < baseStart_1508716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508727 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 6]
def baseStart_1508727 : Nat := 118140960795 + 1508727 * 2 ^ 59
def prefixEnd_1508727 : Nat := 4983230072969 + 3 ^ 40 * 1508727 * 2
def baseEnd_1508727 : Nat := 172156028314671962749777

theorem tailTrace_1508727 : CollatzResearch.WordTrace tailWord_1508727 prefixEnd_1508727 172156028314671962749777 := by
  unfold tailWord_1508727
  simp only [CollatzResearch.WordTrace]
  refine ⟨55027794405147223902548435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36685196270098149268365623 55027794405147223902548435)
  ·
    refine ⟨82541691607720835853822653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55027794405147223902548435 82541691607720835853822653)
    ·
      refine ⟨30953134352895313445183495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82541691607720835853822653 30953134352895313445183495)
      ·
        refine ⟨46429701529342970167775243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30953134352895313445183495 46429701529342970167775243)
        ·
          refine ⟨69644552294014455251662865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46429701529342970167775243 69644552294014455251662865)
          ·
            refine ⟨52233414220510841438747149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69644552294014455251662865 52233414220510841438747149)
            ·
              refine ⟨19587530332691565539530181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52233414220510841438747149 19587530332691565539530181)
              ·
                refine ⟨3672661937379668538661909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19587530332691565539530181 3672661937379668538661909)
                ·
                  refine ⟨172156028314671962749777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3672661937379668538661909 172156028314671962749777)
                  ·
                    rfl

theorem cell22_1508727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 6].length) (baseStart_1508727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508727 prefixEnd_1508727 := by exact prefixLift 1508727
  have htrace : WordTrace (prefixWord ++ tailWord_1508727) baseStart_1508727 baseEnd_1508727 := by
    simpa [prefixWord, tailWord_1508727, baseEnd_1508727] using wordTrace_append hprefix tailTrace_1508727
  have hstable : (prefixWord ++ tailWord_1508727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508727).length < 2 ^ (prefixWord ++ tailWord_1508727).sum := by decide
  have hdescent : baseEnd_1508727 < baseStart_1508727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508729 : List Nat := [1, 2, 1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_1508729 : Nat := 118140960795 + 1508729 * 2 ^ 59
def prefixEnd_1508729 : Nat := 4983230072969 + 3 ^ 40 * 1508729 * 2
def baseEnd_1508729 : Nat := 516468769584888549699325

theorem tailTrace_1508729 : CollatzResearch.WordTrace tailWord_1508729 prefixEnd_1508729 516468769584888549699325 := by
  unfold tailWord_1508729
  simp only [CollatzResearch.WordTrace]
  refine ⟨55027867351139978244121241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36685244900759985496080827 55027867351139978244121241)
  ·
    refine ⟨41270900513354983683090931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55027867351139978244121241 41270900513354983683090931)
    ·
      refine ⟨61906350770032475524636397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41270900513354983683090931 61906350770032475524636397)
      ·
        refine ⟨23214881538762178321738649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61906350770032475524636397 23214881538762178321738649)
        ·
          refine ⟨17411161154071633741303987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23214881538762178321738649 17411161154071633741303987)
          ·
            refine ⟨26116741731107450611955981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17411161154071633741303987 26116741731107450611955981)
            ·
              refine ⟨9793778149165293979483493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26116741731107450611955981 9793778149165293979483493)
              ·
                refine ⟨1836333402968492621153155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9793778149165293979483493 1836333402968492621153155)
                ·
                  refine ⟨2754500104452738931729733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836333402968492621153155 2754500104452738931729733)
                  ·
                    refine ⟨516468769584888549699325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2754500104452738931729733 516468769584888549699325)
                    ·
                      rfl

theorem cell22_1508729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_1508729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508729 prefixEnd_1508729 := by exact prefixLift 1508729
  have htrace : WordTrace (prefixWord ++ tailWord_1508729) baseStart_1508729 baseEnd_1508729 := by
    simpa [prefixWord, tailWord_1508729, baseEnd_1508729] using wordTrace_append hprefix tailTrace_1508729
  have hstable : (prefixWord ++ tailWord_1508729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508729).length < 2 ^ (prefixWord ++ tailWord_1508729).sum := by decide
  have hdescent : baseEnd_1508729 < baseStart_1508729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508737 : List Nat := [1, 2, 4, 3, 3, 1, 1, 3, 1, 3]
def baseStart_1508737 : Nat := 118140960795 + 1508737 * 2 ^ 59
def prefixEnd_1508737 : Nat := 4983230072969 + 3 ^ 40 * 1508737 * 2
def baseEnd_1508737 : Nat := 516471508148379195499301

theorem tailTrace_1508737 : CollatzResearch.WordTrace tailWord_1508737 prefixEnd_1508737 516471508148379195499301 := by
  unfold tailWord_1508737
  simp only [CollatzResearch.WordTrace]
  refine ⟨55028159135110995610412465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36685439423407330406941643 55028159135110995610412465)
  ·
    refine ⟨41271119351333246707809349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55028159135110995610412465 41271119351333246707809349)
    ·
      refine ⟨7738334878374983757714253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41271119351333246707809349 7738334878374983757714253)
      ·
        refine ⟨2901875579390618909142845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7738334878374983757714253 2901875579390618909142845)
        ·
          refine ⟨1088203342271482090928567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2901875579390618909142845 1088203342271482090928567)
          ·
            refine ⟨1632305013407223136392851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1088203342271482090928567 1632305013407223136392851)
            ·
              refine ⟨2448457520110834704589277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1632305013407223136392851 2448457520110834704589277)
              ·
                refine ⟨918171570041563014220979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2448457520110834704589277 918171570041563014220979)
                ·
                  refine ⟨1377257355062344521331469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918171570041563014220979 1377257355062344521331469)
                  ·
                    refine ⟨516471508148379195499301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1377257355062344521331469 516471508148379195499301)
                    ·
                      rfl

theorem cell22_1508737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_1508737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508737 prefixEnd_1508737 := by exact prefixLift 1508737
  have htrace : WordTrace (prefixWord ++ tailWord_1508737) baseStart_1508737 baseEnd_1508737 := by
    simpa [prefixWord, tailWord_1508737, baseEnd_1508737] using wordTrace_append hprefix tailTrace_1508737
  have hstable : (prefixWord ++ tailWord_1508737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508737).length < 2 ^ (prefixWord ++ tailWord_1508737).sum := by decide
  have hdescent : baseEnd_1508737 < baseStart_1508737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508787 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 2, 7]
def baseStart_1508787 : Nat := 118140960795 + 1508787 * 2 ^ 59
def prefixEnd_1508787 : Nat := 4983230072969 + 3 ^ 40 * 1508787 * 2
def baseEnd_1508787 : Nat := 516488624170195731749147

theorem tailTrace_1508787 : CollatzResearch.WordTrace tailWord_1508787 prefixEnd_1508787 516488624170195731749147 := by
  unfold tailWord_1508787
  simp only [CollatzResearch.WordTrace]
  refine ⟨55029982784929854149732615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36686655189953236099821743 55029982784929854149732615)
  ·
    refine ⟨82544974177394781224598923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55029982784929854149732615 82544974177394781224598923)
    ·
      refine ⟨123817461266092171836898385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82544974177394781224598923 123817461266092171836898385)
      ·
        refine ⟨92863095949569128877673789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123817461266092171836898385 92863095949569128877673789)
        ·
          refine ⟨34823660981088423329127671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92863095949569128877673789 34823660981088423329127671)
          ·
            refine ⟨52235491471632634993691507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34823660981088423329127671 52235491471632634993691507)
            ·
              refine ⟨78353237207448952490537261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52235491471632634993691507 78353237207448952490537261)
              ·
                refine ⟨29382463952793357183951473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78353237207448952490537261 29382463952793357183951473)
                ·
                  refine ⟨22036847964595017887963605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29382463952793357183951473 22036847964595017887963605)
                  ·
                    refine ⟨516488624170195731749147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22036847964595017887963605 516488624170195731749147)
                    ·
                      rfl

theorem cell22_1508787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_1508787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508787 prefixEnd_1508787 := by exact prefixLift 1508787
  have htrace : WordTrace (prefixWord ++ tailWord_1508787) baseStart_1508787 baseEnd_1508787 := by
    simpa [prefixWord, tailWord_1508787, baseEnd_1508787] using wordTrace_append hprefix tailTrace_1508787
  have hstable : (prefixWord ++ tailWord_1508787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508787).length < 2 ^ (prefixWord ++ tailWord_1508787).sum := by decide
  have hdescent : baseEnd_1508787 < baseStart_1508787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508789 : List Nat := [1, 3, 3, 2, 2, 1, 2, 8]
def baseStart_1508789 : Nat := 118140960795 + 1508789 * 2 ^ 59
def prefixEnd_1508789 : Nat := 4983230072969 + 3 ^ 40 * 1508789 * 2
def baseEnd_1508789 : Nat := 57387700979007599244349

theorem tailTrace_1508789 : CollatzResearch.WordTrace tailWord_1508789 prefixEnd_1508789 57387700979007599244349 := by
  unfold tailWord_1508789
  simp only [CollatzResearch.WordTrace]
  refine ⟨55030055730922608491305421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36686703820615072327536947 55030055730922608491305421)
  ·
    refine ⟨20636270899095978184239533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55030055730922608491305421 20636270899095978184239533)
    ·
      refine ⟨7738601587160991819089825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20636270899095978184239533 7738601587160991819089825)
      ·
        refine ⟨5803951190370743864317369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7738601587160991819089825 5803951190370743864317369)
        ·
          refine ⟨4352963392778057898238027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5803951190370743864317369 4352963392778057898238027)
          ·
            refine ⟨6529445089167086847357041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4352963392778057898238027 6529445089167086847357041)
            ·
              refine ⟨4897083816875315135517781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6529445089167086847357041 4897083816875315135517781)
              ·
                refine ⟨57387700979007599244349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4897083816875315135517781 57387700979007599244349)
                ·
                  rfl

theorem cell22_1508789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 8].length) (baseStart_1508789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508789 prefixEnd_1508789 := by exact prefixLift 1508789
  have htrace : WordTrace (prefixWord ++ tailWord_1508789) baseStart_1508789 baseEnd_1508789 := by
    simpa [prefixWord, tailWord_1508789, baseEnd_1508789] using wordTrace_append hprefix tailTrace_1508789
  have hstable : (prefixWord ++ tailWord_1508789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508789).length < 2 ^ (prefixWord ++ tailWord_1508789).sum := by decide
  have hdescent : baseEnd_1508789 < baseStart_1508789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508821 : List Nat := [1, 3, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_1508821 : Nat := 118140960795 + 1508821 * 2 ^ 59
def prefixEnd_1508821 : Nat := 4983230072969 + 3 ^ 40 * 1508821 * 2
def baseEnd_1508821 : Nat := 516500263065030976399043

theorem tailTrace_1508821 : CollatzResearch.WordTrace tailWord_1508821 prefixEnd_1508821 516500263065030976399043 := by
  unfold tailWord_1508821
  simp only [CollatzResearch.WordTrace]
  refine ⟨55031222866806677956470317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36687481911204451970980211 55031222866806677956470317)
  ·
    refine ⟨20636708575052504233676369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55031222866806677956470317 20636708575052504233676369)
    ·
      refine ⟨15477531431289378175257277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20636708575052504233676369 15477531431289378175257277)
      ·
        refine ⟨5804074286733516815721479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15477531431289378175257277 5804074286733516815721479)
        ·
          refine ⟨8706111430100275223582219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5804074286733516815721479 8706111430100275223582219)
          ·
            refine ⟨13059167145150412835373329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8706111430100275223582219 13059167145150412835373329)
            ·
              refine ⟨9794375358862809626529997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13059167145150412835373329 9794375358862809626529997)
              ·
                refine ⟨3672890759573553609948749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9794375358862809626529997 3672890759573553609948749)
                ·
                  refine ⟨1377334034840082603730781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3672890759573553609948749 1377334034840082603730781)
                  ·
                    refine ⟨516500263065030976399043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1377334034840082603730781 516500263065030976399043)
                    ·
                      rfl

theorem cell22_1508821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_1508821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508821 prefixEnd_1508821 := by exact prefixLift 1508821
  have htrace : WordTrace (prefixWord ++ tailWord_1508821) baseStart_1508821 baseEnd_1508821 := by
    simpa [prefixWord, tailWord_1508821, baseEnd_1508821] using wordTrace_append hprefix tailTrace_1508821
  have hstable : (prefixWord ++ tailWord_1508821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508821).length < 2 ^ (prefixWord ++ tailWord_1508821).sum := by decide
  have hdescent : baseEnd_1508821 < baseStart_1508821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508896 : List Nat := [2, 1, 1, 6, 1, 1, 2, 2, 6]
def baseStart_1508896 : Nat := 118140960795 + 1508896 * 2 ^ 59
def prefixEnd_1508896 : Nat := 4983230072969 + 3 ^ 40 * 1508896 * 2
def baseEnd_1508896 : Nat := 172175312365918593591271

theorem tailTrace_1508896 : CollatzResearch.WordTrace tailWord_1508896 prefixEnd_1508896 172175312365918593591271 := by
  unfold tailWord_1508896
  simp only [CollatzResearch.WordTrace]
  refine ⟨27516979170767482882725271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36689305561023310510300361 27516979170767482882725271)
  ·
    refine ⟨41275468756151224324087907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27516979170767482882725271 41275468756151224324087907)
    ·
      refine ⟨61913203134226836486131861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41275468756151224324087907 61913203134226836486131861)
      ·
        refine ⟨2902181396916882960287431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61913203134226836486131861 2902181396916882960287431)
        ·
          refine ⟨4353272095375324440431147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2902181396916882960287431 4353272095375324440431147)
          ·
            refine ⟨6529908143062986660646721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4353272095375324440431147 6529908143062986660646721)
            ·
              refine ⟨4897431107297239995485041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6529908143062986660646721 4897431107297239995485041)
              ·
                refine ⟨3673073330472929996613781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4897431107297239995485041 3673073330472929996613781)
                ·
                  refine ⟨172175312365918593591271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3673073330472929996613781 172175312365918593591271)
                  ·
                    rfl

theorem cell22_1508896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 2, 6].length) (baseStart_1508896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508896 prefixEnd_1508896 := by exact prefixLift 1508896
  have htrace : WordTrace (prefixWord ++ tailWord_1508896) baseStart_1508896 baseEnd_1508896 := by
    simpa [prefixWord, tailWord_1508896, baseEnd_1508896] using wordTrace_append hprefix tailTrace_1508896
  have hstable : (prefixWord ++ tailWord_1508896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508896).length < 2 ^ (prefixWord ++ tailWord_1508896).sum := by decide
  have hdescent : baseEnd_1508896 < baseStart_1508896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1508969 : List Nat := [1, 2, 1, 1, 1, 4, 2, 1, 9]
def baseStart_1508969 : Nat := 118140960795 + 1508969 * 2 ^ 59
def prefixEnd_1508969 : Nat := 4983230072969 + 3 ^ 40 * 1508969 * 2
def baseEnd_1508969 : Nat := 172183642163202641232863

theorem tailTrace_1508969 : CollatzResearch.WordTrace tailWord_1508969 prefixEnd_1508969 172183642163202641232863 := by
  unfold tailWord_1508969
  simp only [CollatzResearch.WordTrace]
  refine ⟨55036620870270499232857961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36691080580180332821905307 55036620870270499232857961)
  ·
    refine ⟨41277465652702874424643471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55036620870270499232857961 41277465652702874424643471)
    ·
      refine ⟨61916198479054311636965207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41277465652702874424643471 61916198479054311636965207)
      ·
        refine ⟨92874297718581467455447811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61916198479054311636965207 92874297718581467455447811)
        ·
          refine ⟨139311446577872201183171717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92874297718581467455447811 139311446577872201183171717)
          ·
            refine ⟨26120896233351037721844697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139311446577872201183171717 26120896233351037721844697)
            ·
              refine ⟨19590672175013278291383523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26120896233351037721844697 19590672175013278291383523)
              ·
                refine ⟨29386008262519917437075285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19590672175013278291383523 29386008262519917437075285)
                ·
                  refine ⟨172183642163202641232863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 29386008262519917437075285 172183642163202641232863)
                  ·
                    rfl

theorem cell22_1508969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_1508969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1508969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1508969 prefixEnd_1508969 := by exact prefixLift 1508969
  have htrace : WordTrace (prefixWord ++ tailWord_1508969) baseStart_1508969 baseEnd_1508969 := by
    simpa [prefixWord, tailWord_1508969, baseEnd_1508969] using wordTrace_append hprefix tailTrace_1508969
  have hstable : (prefixWord ++ tailWord_1508969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1508969).length < 2 ^ (prefixWord ++ tailWord_1508969).sum := by decide
  have hdescent : baseEnd_1508969 < baseStart_1508969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1508969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509061 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_1509061 : Nat := 118140960795 + 1509061 * 2 ^ 59
def prefixEnd_1509061 : Nat := 4983230072969 + 3 ^ 40 * 1509061 * 2
def baseEnd_1509061 : Nat := 516582419969750350398307

theorem tailTrace_1509061 : CollatzResearch.WordTrace tailWord_1509061 prefixEnd_1509061 516582419969750350398307 := by
  unfold tailWord_1509061
  simp only [CollatzResearch.WordTrace]
  refine ⟨55039976385937198945207037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36693317590624799296804691 55039976385937198945207037)
  ·
    refine ⟨20639991144726449604452639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55039976385937198945207037 20639991144726449604452639)
    ·
      refine ⟨30959986717089674406678959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20639991144726449604452639 30959986717089674406678959)
      ·
        refine ⟨46439980075634511610018439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30959986717089674406678959 46439980075634511610018439)
        ·
          refine ⟨69659970113451767415027659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46439980075634511610018439 69659970113451767415027659)
          ·
            refine ⟨104489955170177651122541489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69659970113451767415027659 104489955170177651122541489)
            ·
              refine ⟨78367466377633238341906117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104489955170177651122541489 78367466377633238341906117)
              ·
                refine ⟨14693899945806232189107397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78367466377633238341906117 14693899945806232189107397)
                ·
                  refine ⟨2755106239838668535457637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14693899945806232189107397 2755106239838668535457637)
                  ·
                    refine ⟨516582419969750350398307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755106239838668535457637 516582419969750350398307)
                    ·
                      rfl

theorem cell22_1509061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_1509061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509061 prefixEnd_1509061 := by exact prefixLift 1509061
  have htrace : WordTrace (prefixWord ++ tailWord_1509061) baseStart_1509061 baseEnd_1509061 := by
    simpa [prefixWord, tailWord_1509061, baseEnd_1509061] using wordTrace_append hprefix tailTrace_1509061
  have hstable : (prefixWord ++ tailWord_1509061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509061).length < 2 ^ (prefixWord ++ tailWord_1509061).sum := by decide
  have hdescent : baseEnd_1509061 < baseStart_1509061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509202 : List Nat := [3, 2, 2, 1, 1, 3, 4, 1, 1, 4]
def baseStart_1509202 : Nat := 118140960795 + 1509202 * 2 ^ 59
def prefixEnd_1509202 : Nat := 4983230072969 + 3 ^ 40 * 1509202 * 2
def baseEnd_1509202 : Nat := 516630687151272982622875

theorem tailTrace_1509202 : CollatzResearch.WordTrace tailWord_1509202 prefixEnd_1509202 516630687151272982622875 := by
  unfold tailWord_1509202
  simp only [CollatzResearch.WordTrace]
  refine ⟨13761279769606595006522465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36696746052284253350726573 13761279769606595006522465)
  ·
    refine ⟨10320959827204946254891849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13761279769606595006522465 10320959827204946254891849)
    ·
      refine ⟨7740719870403709691168887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10320959827204946254891849 7740719870403709691168887)
      ·
        refine ⟨11611079805605564536753331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7740719870403709691168887 11611079805605564536753331)
        ·
          refine ⟨17416619708408346805129997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11611079805605564536753331 17416619708408346805129997)
          ·
            refine ⟨6531232390653130051923749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17416619708408346805129997 6531232390653130051923749)
            ·
              refine ⟨1224606073247461884735703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6531232390653130051923749 1224606073247461884735703)
              ·
                refine ⟨1836909109871192827103555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224606073247461884735703 1836909109871192827103555)
                ·
                  refine ⟨2755363664806789240655333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1836909109871192827103555 2755363664806789240655333)
                  ·
                    refine ⟨516630687151272982622875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755363664806789240655333 516630687151272982622875)
                    ·
                      rfl

theorem cell22_1509202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 1, 1, 4].length) (baseStart_1509202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509202 prefixEnd_1509202 := by exact prefixLift 1509202
  have htrace : WordTrace (prefixWord ++ tailWord_1509202) baseStart_1509202 baseEnd_1509202 := by
    simpa [prefixWord, tailWord_1509202, baseEnd_1509202] using wordTrace_append hprefix tailTrace_1509202
  have hstable : (prefixWord ++ tailWord_1509202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509202).length < 2 ^ (prefixWord ++ tailWord_1509202).sum := by decide
  have hdescent : baseEnd_1509202 < baseStart_1509202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509215 : List Nat := [1, 1, 2, 3, 1, 5, 1, 1, 4, 3]
def baseStart_1509215 : Nat := 118140960795 + 1509215 * 2 ^ 59
def prefixEnd_1509215 : Nat := 4983230072969 + 3 ^ 40 * 1509215 * 2
def baseEnd_1509215 : Nat := 516635137316945282047835

theorem tailTrace_1509215 : CollatzResearch.WordTrace tailWord_1509215 prefixEnd_1509215 516635137316945282047835 := by
  unfold tailWord_1509215
  simp only [CollatzResearch.WordTrace]
  refine ⟨55045593227379283246313099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36697062151586188830875399 55045593227379283246313099)
  ·
    refine ⟨82568389841068924869469649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55045593227379283246313099 82568389841068924869469649)
    ·
      refine ⟨61926292380801693652102237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82568389841068924869469649 61926292380801693652102237)
      ·
        refine ⟨23222359642800635119538339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61926292380801693652102237 23222359642800635119538339)
        ·
          refine ⟨34833539464200952679307509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23222359642800635119538339 34833539464200952679307509)
          ·
            refine ⟨3265644324768839313685079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34833539464200952679307509 3265644324768839313685079)
            ·
              refine ⟨4898466487153258970527619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3265644324768839313685079 4898466487153258970527619)
              ·
                refine ⟨7347699730729888455791429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898466487153258970527619 7347699730729888455791429)
                ·
                  refine ⟨1377693699511854085460893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7347699730729888455791429 1377693699511854085460893)
                  ·
                    refine ⟨516635137316945282047835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1377693699511854085460893 516635137316945282047835)
                    ·
                      rfl

theorem cell22_1509215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 1, 4, 3].length) (baseStart_1509215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509215 prefixEnd_1509215 := by exact prefixLift 1509215
  have htrace : WordTrace (prefixWord ++ tailWord_1509215) baseStart_1509215 baseEnd_1509215 := by
    simpa [prefixWord, tailWord_1509215, baseEnd_1509215] using wordTrace_append hprefix tailTrace_1509215
  have hstable : (prefixWord ++ tailWord_1509215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509215).length < 2 ^ (prefixWord ++ tailWord_1509215).sum := by decide
  have hdescent : baseEnd_1509215 < baseStart_1509215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509230 : List Nat := [4, 1, 2, 3, 1, 1, 1, 2, 1, 6]
def baseStart_1509230 : Nat := 118140960795 + 1509230 * 2 ^ 59
def prefixEnd_1509230 : Nat := 4983230072969 + 3 ^ 40 * 1509230 * 2
def baseEnd_1509230 : Nat := 516640272123490242922789

theorem tailTrace_1509230 : CollatzResearch.WordTrace tailWord_1509230 prefixEnd_1509230 516640272123490242922789 := by
  unfold tailWord_1509230
  simp only [CollatzResearch.WordTrace]
  refine ⟨6880767540290617601013643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36697426881549960538739429 6880767540290617601013643)
  ·
    refine ⟨10321151310435926401520465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6880767540290617601013643 10321151310435926401520465)
    ·
      refine ⟨7740863482826944801140349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10321151310435926401520465 7740863482826944801140349)
      ·
        refine ⟨2902823806060104300427631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7740863482826944801140349 2902823806060104300427631)
        ·
          refine ⟨4354235709090156450641447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2902823806060104300427631 4354235709090156450641447)
          ·
            refine ⟨6531353563635234675962171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4354235709090156450641447 6531353563635234675962171)
            ·
              refine ⟨9797030345452852013943257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6531353563635234675962171 9797030345452852013943257)
              ·
                refine ⟨7347772759089639010457443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9797030345452852013943257 7347772759089639010457443)
                ·
                  refine ⟨11021659138634458515686165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7347772759089639010457443 11021659138634458515686165)
                  ·
                    refine ⟨516640272123490242922789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11021659138634458515686165 516640272123490242922789)
                    ·
                      rfl

theorem cell22_1509230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 1, 2, 1, 6].length) (baseStart_1509230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509230 prefixEnd_1509230 := by exact prefixLift 1509230
  have htrace : WordTrace (prefixWord ++ tailWord_1509230) baseStart_1509230 baseEnd_1509230 := by
    simpa [prefixWord, tailWord_1509230, baseEnd_1509230] using wordTrace_append hprefix tailTrace_1509230
  have hstable : (prefixWord ++ tailWord_1509230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509230).length < 2 ^ (prefixWord ++ tailWord_1509230).sum := by decide
  have hdescent : baseEnd_1509230 < baseStart_1509230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509262 : List Nat := [4, 1, 1, 5, 1, 2, 8]
def baseStart_1509262 : Nat := 118140960795 + 1509262 * 2 ^ 59
def prefixEnd_1509262 : Nat := 4983230072969 + 3 ^ 40 * 1509262 * 2
def baseEnd_1509262 : Nat := 19135230606572326893433

theorem tailTrace_1509262 : CollatzResearch.WordTrace tailWord_1509262 prefixEnd_1509262 19135230606572326893433 := by
  unfold tailWord_1509262
  simp only [CollatzResearch.WordTrace]
  refine ⟨6880913432276126284159255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36698204972139340182182693 6880913432276126284159255)
  ·
    refine ⟨10321370148414189426238883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6880913432276126284159255 10321370148414189426238883)
    ·
      refine ⟨15482055222621284139358325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10321370148414189426238883 15482055222621284139358325)
      ·
        refine ⟨1451442677120745388064843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 15482055222621284139358325 1451442677120745388064843)
        ·
          refine ⟨2177164015681118082097265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1451442677120745388064843 2177164015681118082097265)
          ·
            refine ⟨1632873011760838561572949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2177164015681118082097265 1632873011760838561572949)
            ·
              refine ⟨19135230606572326893433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1632873011760838561572949 19135230606572326893433)
              ·
                rfl

theorem cell22_1509262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 2, 8].length) (baseStart_1509262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509262 prefixEnd_1509262 := by exact prefixLift 1509262
  have htrace : WordTrace (prefixWord ++ tailWord_1509262) baseStart_1509262 baseEnd_1509262 := by
    simpa [prefixWord, tailWord_1509262, baseEnd_1509262] using wordTrace_append hprefix tailTrace_1509262
  have hstable : (prefixWord ++ tailWord_1509262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509262).length < 2 ^ (prefixWord ++ tailWord_1509262).sum := by decide
  have hdescent : baseEnd_1509262 < baseStart_1509262 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509273 : List Nat := [1, 2, 1, 2, 1, 3, 4, 1, 7]
def baseStart_1509273 : Nat := 118140960795 + 1509273 * 2 ^ 59
def prefixEnd_1509273 : Nat := 4983230072969 + 3 ^ 40 * 1509273 * 2
def baseEnd_1509273 : Nat := 172218330634084154699219

theorem tailTrace_1509273 : CollatzResearch.WordTrace tailWord_1509273 prefixEnd_1509273 172218330634084154699219 := by
  unfold tailWord_1509273
  simp only [CollatzResearch.WordTrace]
  refine ⟨55047708661169159151924473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36698472440779439434616315 55047708661169159151924473)
  ·
    refine ⟨41285781495876869363943355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55047708661169159151924473 41285781495876869363943355)
    ·
      refine ⟨61928672243815304045915033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41285781495876869363943355 61928672243815304045915033)
      ·
        refine ⟨46446504182861478034436275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61928672243815304045915033 46446504182861478034436275)
        ·
          refine ⟨69669756274292217051654413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46446504182861478034436275 69669756274292217051654413)
          ·
            refine ⟨26126158602859581394370405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69669756274292217051654413 26126158602859581394370405)
            ·
              refine ⟨4898654738036171511444451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26126158602859581394370405 4898654738036171511444451)
              ·
                refine ⟨7347982107054257267166677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4898654738036171511444451 7347982107054257267166677)
                ·
                  refine ⟨172218330634084154699219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7347982107054257267166677 172218330634084154699219)
                  ·
                    rfl

theorem cell22_1509273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_1509273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509273 prefixEnd_1509273 := by exact prefixLift 1509273
  have htrace : WordTrace (prefixWord ++ tailWord_1509273) baseStart_1509273 baseEnd_1509273 := by
    simpa [prefixWord, tailWord_1509273, baseEnd_1509273] using wordTrace_append hprefix tailTrace_1509273
  have hstable : (prefixWord ++ tailWord_1509273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509273).length < 2 ^ (prefixWord ++ tailWord_1509273).sum := by decide
  have hdescent : baseEnd_1509273 < baseStart_1509273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509277 : List Nat := [1, 4, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_1509277 : Nat := 118140960795 + 1509277 * 2 ^ 59
def prefixEnd_1509277 : Nat := 4983230072969 + 3 ^ 40 * 1509277 * 2
def baseEnd_1509277 : Nat := 516656361183997786997645

theorem tailTrace_1509277 : CollatzResearch.WordTrace tailWord_1509277 prefixEnd_1509277 516656361183997786997645 := by
  unfold tailWord_1509277
  simp only [CollatzResearch.WordTrace]
  refine ⟨55047854553154667835070085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36698569702103111890046723 55047854553154667835070085)
  ·
    refine ⟨10321472728716500219075641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55047854553154667835070085 10321472728716500219075641)
    ·
      refine ⟨7741104546537375164306731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10321472728716500219075641 7741104546537375164306731)
      ·
        refine ⟨11611656819806062746460097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7741104546537375164306731 11611656819806062746460097)
        ·
          refine ⟨8708742614854547059845073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11611656819806062746460097 8708742614854547059845073)
          ·
            refine ⟨6531556961140910294883805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8708742614854547059845073 6531556961140910294883805)
            ·
              refine ⟨2449333860427841360581427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6531556961140910294883805 2449333860427841360581427)
              ·
                refine ⟨3674000790641762040872141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2449333860427841360581427 3674000790641762040872141)
                ·
                  refine ⟨1377750296490660765327053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3674000790641762040872141 1377750296490660765327053)
                  ·
                    refine ⟨516656361183997786997645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1377750296490660765327053 516656361183997786997645)
                    ·
                      rfl

theorem cell22_1509277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_1509277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509277 prefixEnd_1509277 := by exact prefixLift 1509277
  have htrace : WordTrace (prefixWord ++ tailWord_1509277) baseStart_1509277 baseEnd_1509277 := by
    simpa [prefixWord, tailWord_1509277, baseEnd_1509277] using wordTrace_append hprefix tailTrace_1509277
  have hstable : (prefixWord ++ tailWord_1509277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509277).length < 2 ^ (prefixWord ++ tailWord_1509277).sum := by decide
  have hdescent : baseEnd_1509277 < baseStart_1509277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509363 : List Nat := [1, 1, 1, 2, 2, 2, 1, 12]
def baseStart_1509363 : Nat := 118140960795 + 1509363 * 2 ^ 59
def prefixEnd_1509363 : Nat := 4983230072969 + 3 ^ 40 * 1509363 * 2
def baseEnd_1509363 : Nat := 57409533415724692149709

theorem tailTrace_1509363 : CollatzResearch.WordTrace tailWord_1509363 prefixEnd_1509363 57409533415724692149709 := by
  unfold tailWord_1509363
  simp only [CollatzResearch.WordTrace]
  refine ⟨55050991230843104522700743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36700660820562069681800495 55050991230843104522700743)
  ·
    refine ⟨82576486846264656784051115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55050991230843104522700743 82576486846264656784051115)
    ·
      refine ⟨123864730269396985176076673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82576486846264656784051115 123864730269396985176076673)
      ·
        refine ⟨92898547702047738882057505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123864730269396985176076673 92898547702047738882057505)
        ·
          refine ⟨69673910776535804161543129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92898547702047738882057505 69673910776535804161543129)
          ·
            refine ⟨52255433082401853121157347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69673910776535804161543129 52255433082401853121157347)
            ·
              refine ⟨78383149623602779681736021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52255433082401853121157347 78383149623602779681736021)
              ·
                refine ⟨57409533415724692149709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 78383149623602779681736021 57409533415724692149709)
                ·
                  rfl

theorem cell22_1509363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 12].length) (baseStart_1509363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509363 prefixEnd_1509363 := by exact prefixLift 1509363
  have htrace : WordTrace (prefixWord ++ tailWord_1509363) baseStart_1509363 baseEnd_1509363 := by
    simpa [prefixWord, tailWord_1509363, baseEnd_1509363] using wordTrace_append hprefix tailTrace_1509363
  have hstable : (prefixWord ++ tailWord_1509363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509363).length < 2 ^ (prefixWord ++ tailWord_1509363).sum := by decide
  have hdescent : baseEnd_1509363 < baseStart_1509363 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509425 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 7]
def baseStart_1509425 : Nat := 118140960795 + 1509425 * 2 ^ 59
def prefixEnd_1509425 : Nat := 4983230072969 + 3 ^ 40 * 1509425 * 2
def baseEnd_1509425 : Nat := 172235674869524911432397

theorem tailTrace_1509425 : CollatzResearch.WordTrace tailWord_1509425 prefixEnd_1509425 172235674869524911432397 := by
  unfold tailWord_1509425
  simp only [CollatzResearch.WordTrace]
  refine ⟨55053252556618489111457729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36702168371078992740971819 55053252556618489111457729)
  ·
    refine ⟨41289939417463866833593297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55053252556618489111457729 41289939417463866833593297)
    ·
      refine ⟨30967454563097900125194973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41289939417463866833593297 30967454563097900125194973)
      ·
        refine ⟨11612795461161712546948115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30967454563097900125194973 11612795461161712546948115)
        ·
          refine ⟨17419193191742568820422173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11612795461161712546948115 17419193191742568820422173)
          ·
            refine ⟨6532197446903463307658315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17419193191742568820422173 6532197446903463307658315)
            ·
              refine ⟨9798296170355194961487473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6532197446903463307658315 9798296170355194961487473)
              ·
                refine ⟨7348722127766396221115605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9798296170355194961487473 7348722127766396221115605)
                ·
                  refine ⟨172235674869524911432397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7348722127766396221115605 172235674869524911432397)
                  ·
                    rfl

theorem cell22_1509425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_1509425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509425 prefixEnd_1509425 := by exact prefixLift 1509425
  have htrace : WordTrace (prefixWord ++ tailWord_1509425) baseStart_1509425 baseEnd_1509425 := by
    simpa [prefixWord, tailWord_1509425, baseEnd_1509425] using wordTrace_append hprefix tailTrace_1509425
  have hstable : (prefixWord ++ tailWord_1509425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509425).length < 2 ^ (prefixWord ++ tailWord_1509425).sum := by decide
  have hdescent : baseEnd_1509425 < baseStart_1509425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509455 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 5, 4]
def baseStart_1509455 : Nat := 118140960795 + 1509455 * 2 ^ 59
def prefixEnd_1509455 : Nat := 4983230072969 + 3 ^ 40 * 1509455 * 2
def baseEnd_1509455 : Nat := 516717294221664656047099

theorem tailTrace_1509455 : CollatzResearch.WordTrace tailWord_1509455 prefixEnd_1509455 516717294221664656047099 := by
  unfold tailWord_1509455
  simp only [CollatzResearch.WordTrace]
  refine ⟨55054346746509804235049819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36702897831006536156699879 55054346746509804235049819)
  ·
    refine ⟨82581520119764706352574729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55054346746509804235049819 82581520119764706352574729)
    ·
      refine ⟨61936140089823529764431047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82581520119764706352574729 61936140089823529764431047)
      ·
        refine ⟨92904210134735294646646571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61936140089823529764431047 92904210134735294646646571)
        ·
          refine ⟨139356315202102941969969857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92904210134735294646646571 139356315202102941969969857)
          ·
            refine ⟨104517236401577206477477393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139356315202102941969969857 104517236401577206477477393)
            ·
              refine ⟨78387927301182904858108045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104517236401577206477477393 78387927301182904858108045)
              ·
                refine ⟨29395472737943589321790517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78387927301182904858108045 29395472737943589321790517)
                ·
                  refine ⟨2755825569182211498917861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29395472737943589321790517 2755825569182211498917861)
                  ·
                    refine ⟨516717294221664656047099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755825569182211498917861 516717294221664656047099)
                    ·
                      rfl

theorem cell22_1509455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_1509455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509455 prefixEnd_1509455 := by exact prefixLift 1509455
  have htrace : WordTrace (prefixWord ++ tailWord_1509455) baseStart_1509455 baseEnd_1509455 := by
    simpa [prefixWord, tailWord_1509455, baseEnd_1509455] using wordTrace_append hprefix tailTrace_1509455
  have hstable : (prefixWord ++ tailWord_1509455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509455).length < 2 ^ (prefixWord ++ tailWord_1509455).sum := by decide
  have hdescent : baseEnd_1509455 < baseStart_1509455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509472 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 3, 4]
def baseStart_1509472 : Nat := 118140960795 + 1509472 * 2 ^ 59
def prefixEnd_1509472 : Nat := 4983230072969 + 3 ^ 40 * 1509472 * 2
def baseEnd_1509472 : Nat := 516723113669082278372047

theorem tailTrace_1509472 : CollatzResearch.WordTrace tailWord_1509472 prefixEnd_1509472 516723113669082278372047 := by
  unfold tailWord_1509472
  simp only [CollatzResearch.WordTrace]
  refine ⟨27527483393724108069209335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36703311191632144092279113 27527483393724108069209335)
  ·
    refine ⟨41291225090586162103814003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27527483393724108069209335 41291225090586162103814003)
    ·
      refine ⟨61936837635879243155721005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41291225090586162103814003 61936837635879243155721005)
      ·
        refine ⟨23226314113454716183395377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61936837635879243155721005 23226314113454716183395377)
        ·
          refine ⟨17419735585091037137546533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23226314113454716183395377 17419735585091037137546533)
          ·
            refine ⟨3266200422204569463289975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17419735585091037137546533 3266200422204569463289975)
            ·
              refine ⟨4899300633306854194934963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3266200422204569463289975 4899300633306854194934963)
              ·
                refine ⟨7348950949960281292402445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4899300633306854194934963 7348950949960281292402445)
                ·
                  refine ⟨2755856606235105484650917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7348950949960281292402445 2755856606235105484650917)
                  ·
                    refine ⟨516723113669082278372047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755856606235105484650917 516723113669082278372047)
                    ·
                      rfl

theorem cell22_1509472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 3, 4].length) (baseStart_1509472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509472 prefixEnd_1509472 := by exact prefixLift 1509472
  have htrace : WordTrace (prefixWord ++ tailWord_1509472) baseStart_1509472 baseEnd_1509472 := by
    simpa [prefixWord, tailWord_1509472, baseEnd_1509472] using wordTrace_append hprefix tailTrace_1509472
  have hstable : (prefixWord ++ tailWord_1509472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509472).length < 2 ^ (prefixWord ++ tailWord_1509472).sum := by decide
  have hdescent : baseEnd_1509472 < baseStart_1509472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509489 : List Nat := [1, 2, 2, 2, 1, 1, 7, 1, 1, 4]
def baseStart_1509489 : Nat := 118140960795 + 1509489 * 2 ^ 59
def prefixEnd_1509489 : Nat := 4983230072969 + 3 ^ 40 * 1509489 * 2
def baseEnd_1509489 : Nat := 516728933116499900696995

theorem tailTrace_1509489 : CollatzResearch.WordTrace tailWord_1509489 prefixEnd_1509489 516728933116499900696995 := by
  unfold tailWord_1509489
  simp only [CollatzResearch.WordTrace]
  refine ⟨55055586828386628041787521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36703724552257752027858347 55055586828386628041787521)
  ·
    refine ⟨41291690121289971031340641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55055586828386628041787521 41291690121289971031340641)
    ·
      refine ⟨30968767590967478273505481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41291690121289971031340641 30968767590967478273505481)
      ·
        refine ⟨23226575693225608705129111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30968767590967478273505481 23226575693225608705129111)
        ·
          refine ⟨34839863539838413057693667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23226575693225608705129111 34839863539838413057693667)
          ·
            refine ⟨52259795309757619586540501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34839863539838413057693667 52259795309757619586540501)
            ·
              refine ⟨1224838952572444209059543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 52259795309757619586540501 1224838952572444209059543)
              ·
                refine ⟨1837258428858666313589315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224838952572444209059543 1837258428858666313589315)
                ·
                  refine ⟨2755887643287999470383973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837258428858666313589315 2755887643287999470383973)
                  ·
                    refine ⟨516728933116499900696995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2755887643287999470383973 516728933116499900696995)
                    ·
                      rfl

theorem cell22_1509489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_1509489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509489 prefixEnd_1509489 := by exact prefixLift 1509489
  have htrace : WordTrace (prefixWord ++ tailWord_1509489) baseStart_1509489 baseEnd_1509489 := by
    simpa [prefixWord, tailWord_1509489, baseEnd_1509489] using wordTrace_append hprefix tailTrace_1509489
  have hstable : (prefixWord ++ tailWord_1509489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509489).length < 2 ^ (prefixWord ++ tailWord_1509489).sum := by decide
  have hdescent : baseEnd_1509489 < baseStart_1509489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509553 : List Nat := [1, 2, 2, 5, 2, 2, 1, 2, 2, 3]
def baseStart_1509553 : Nat := 118140960795 + 1509553 * 2 ^ 59
def prefixEnd_1509553 : Nat := 4983230072969 + 3 ^ 40 * 1509553 * 2
def baseEnd_1509553 : Nat := 516750841624425067096799

theorem tailTrace_1509553 : CollatzResearch.WordTrace tailWord_1509553 prefixEnd_1509553 516750841624425067096799 := by
  unfold tailWord_1509553
  simp only [CollatzResearch.WordTrace]
  refine ⟨55057921100154766972117313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36705280733436511314744875 55057921100154766972117313)
  ·
    refine ⟨41293440825116075229087985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55057921100154766972117313 41293440825116075229087985)
    ·
      refine ⟨30970080618837056421815989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41293440825116075229087985 30970080618837056421815989)
      ·
        refine ⟨2903445058015974039545249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30970080618837056421815989 2903445058015974039545249)
        ·
          refine ⟨2177583793511980529658937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2903445058015974039545249 2177583793511980529658937)
          ·
            refine ⟨1633187845133985397244203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2177583793511980529658937 1633187845133985397244203)
            ·
              refine ⟨2449781767700978095866305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633187845133985397244203 2449781767700978095866305)
              ·
                refine ⟨1837336325775733571899729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2449781767700978095866305 1837336325775733571899729)
                ·
                  refine ⟨1378002244331800178924797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1837336325775733571899729 1378002244331800178924797)
                  ·
                    refine ⟨516750841624425067096799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378002244331800178924797 516750841624425067096799)
                    ·
                      rfl

theorem cell22_1509553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_1509553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509553 prefixEnd_1509553 := by exact prefixLift 1509553
  have htrace : WordTrace (prefixWord ++ tailWord_1509553) baseStart_1509553 baseEnd_1509553 := by
    simpa [prefixWord, tailWord_1509553, baseEnd_1509553] using wordTrace_append hprefix tailTrace_1509553
  have hstable : (prefixWord ++ tailWord_1509553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509553).length < 2 ^ (prefixWord ++ tailWord_1509553).sum := by decide
  have hdescent : baseEnd_1509553 < baseStart_1509553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509641 : List Nat := [1, 2, 1, 1, 3, 6, 1, 2, 1, 4]
def baseStart_1509641 : Nat := 118140960795 + 1509641 * 2 ^ 59
def prefixEnd_1509641 : Nat := 4983230072969 + 3 ^ 40 * 1509641 * 2
def baseEnd_1509641 : Nat := 516780965822822170896529

theorem tailTrace_1509641 : CollatzResearch.WordTrace tailWord_1509641 prefixEnd_1509641 516780965822822170896529 := by
  unfold tailWord_1509641
  simp only [CollatzResearch.WordTrace]
  refine ⟨55061130723835958001320777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36707420482557305334213851 55061130723835958001320777)
  ·
    refine ⟨41295848042876968500990583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55061130723835958001320777 41295848042876968500990583)
    ·
      refine ⟨61943772064315452751485875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41295848042876968500990583 61943772064315452751485875)
      ·
        refine ⟨92915658096473179127228813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61943772064315452751485875 92915658096473179127228813)
        ·
          refine ⟨34843371786177442172710805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92915658096473179127228813 34843371786177442172710805)
          ·
            refine ⟨1633283052477067601845819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34843371786177442172710805 1633283052477067601845819)
            ·
              refine ⟨2449924578715601402768729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1633283052477067601845819 2449924578715601402768729)
              ·
                refine ⟨1837443434036701052076547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2449924578715601402768729 1837443434036701052076547)
                ·
                  refine ⟨2756165151055051578114821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837443434036701052076547 2756165151055051578114821)
                  ·
                    refine ⟨516780965822822170896529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2756165151055051578114821 516780965822822170896529)
                    ·
                      rfl

theorem cell22_1509641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_1509641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509641 prefixEnd_1509641 := by exact prefixLift 1509641
  have htrace : WordTrace (prefixWord ++ tailWord_1509641) baseStart_1509641 baseEnd_1509641 := by
    simpa [prefixWord, tailWord_1509641, baseEnd_1509641] using wordTrace_append hprefix tailTrace_1509641
  have hstable : (prefixWord ++ tailWord_1509641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509641).length < 2 ^ (prefixWord ++ tailWord_1509641).sum := by decide
  have hdescent : baseEnd_1509641 < baseStart_1509641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509658 : List Nat := [3, 1, 1, 3, 4, 1, 3, 1, 1, 4]
def baseStart_1509658 : Nat := 118140960795 + 1509658 * 2 ^ 59
def prefixEnd_1509658 : Nat := 4983230072969 + 3 ^ 40 * 1509658 * 2
def baseEnd_1509658 : Nat := 516786785270239793221477

theorem tailTrace_1509658 : CollatzResearch.WordTrace tailWord_1509658 prefixEnd_1509658 516786785270239793221477 := by
  unfold tailWord_1509658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13765437691193592476172407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36707833843182913269793085 13765437691193592476172407)
  ·
    refine ⟨20648156536790388714258611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13765437691193592476172407 20648156536790388714258611)
    ·
      refine ⟨30972234805185583071387917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20648156536790388714258611 30972234805185583071387917)
      ·
        refine ⟨11614588051944593651770469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30972234805185583071387917 11614588051944593651770469)
        ·
          refine ⟨2177735259739611309706963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11614588051944593651770469 2177735259739611309706963)
          ·
            refine ⟨3266602889609416964560445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2177735259739611309706963 3266602889609416964560445)
            ·
              refine ⟨1224976083603531361710167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3266602889609416964560445 1224976083603531361710167)
              ·
                refine ⟨1837464125405297042565251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1224976083603531361710167 1837464125405297042565251)
                ·
                  refine ⟨2756196188107945563847877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1837464125405297042565251 2756196188107945563847877)
                  ·
                    refine ⟨516786785270239793221477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2756196188107945563847877 516786785270239793221477)
                    ·
                      rfl

theorem cell22_1509658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 1, 1, 4].length) (baseStart_1509658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509658 prefixEnd_1509658 := by exact prefixLift 1509658
  have htrace : WordTrace (prefixWord ++ tailWord_1509658) baseStart_1509658 baseEnd_1509658 := by
    simpa [prefixWord, tailWord_1509658, baseEnd_1509658] using wordTrace_append hprefix tailTrace_1509658
  have hstable : (prefixWord ++ tailWord_1509658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509658).length < 2 ^ (prefixWord ++ tailWord_1509658).sum := by decide
  have hdescent : baseEnd_1509658 < baseStart_1509658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509699 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 5, 3]
def baseStart_1509699 : Nat := 118140960795 + 1509699 * 2 ^ 59
def prefixEnd_1509699 : Nat := 4983230072969 + 3 ^ 40 * 1509699 * 2
def baseEnd_1509699 : Nat := 516800820408129352946351

theorem tailTrace_1509699 : CollatzResearch.WordTrace tailWord_1509699 prefixEnd_1509699 516800820408129352946351 := by
  unfold tailWord_1509699
  simp only [CollatzResearch.WordTrace]
  refine ⟨55063246157625833906932151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36708830771750555937954767 55063246157625833906932151)
  ·
    refine ⟨82594869236438750860398227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55063246157625833906932151 82594869236438750860398227)
    ·
      refine ⟨123892303854658126290597341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82594869236438750860398227 123892303854658126290597341)
      ·
        refine ⟨46459613945496797358974003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123892303854658126290597341 46459613945496797358974003)
        ·
          refine ⟨69689420918245196038461005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46459613945496797358974003 69689420918245196038461005)
          ·
            refine ⟨26133532844341948514422877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69689420918245196038461005 26133532844341948514422877)
            ·
              refine ⟨9800074816628230692908579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26133532844341948514422877 9800074816628230692908579)
              ·
                refine ⟨14700112224942346039362869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9800074816628230692908579 14700112224942346039362869)
                ·
                  refine ⟨1378135521088344941190269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14700112224942346039362869 1378135521088344941190269)
                  ·
                    refine ⟨516800820408129352946351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378135521088344941190269 516800820408129352946351)
                    ·
                      rfl

theorem cell22_1509699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5, 3].length) (baseStart_1509699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509699 prefixEnd_1509699 := by exact prefixLift 1509699
  have htrace : WordTrace (prefixWord ++ tailWord_1509699) baseStart_1509699 baseEnd_1509699 := by
    simpa [prefixWord, tailWord_1509699, baseEnd_1509699] using wordTrace_append hprefix tailTrace_1509699
  have hstable : (prefixWord ++ tailWord_1509699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509699).length < 2 ^ (prefixWord ++ tailWord_1509699).sum := by decide
  have hdescent : baseEnd_1509699 < baseStart_1509699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509733 : List Nat := [1, 3, 1, 3, 1, 3, 2, 4, 1, 3]
def baseStart_1509733 : Nat := 118140960795 + 1509733 * 2 ^ 59
def prefixEnd_1509733 : Nat := 4983230072969 + 3 ^ 40 * 1509733 * 2
def baseEnd_1509733 : Nat := 516812459302964597596247

theorem tailTrace_1509733 : CollatzResearch.WordTrace tailWord_1509733 prefixEnd_1509733 516812459302964597596247 := by
  unfold tailWord_1509733
  simp only [CollatzResearch.WordTrace]
  refine ⟨55064486239502657713669853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36709657493001771809113235 55064486239502657713669853)
  ·
    refine ⟨20649182339813496642626195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55064486239502657713669853 20649182339813496642626195)
    ·
      refine ⟨30973773509720244963939293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20649182339813496642626195 30973773509720244963939293)
      ·
        refine ⟨11615165066145091861477235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30973773509720244963939293 11615165066145091861477235)
        ·
          refine ⟨17422747599217637792215853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11615165066145091861477235 17422747599217637792215853)
          ·
            refine ⟨6533530349706614172080945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17422747599217637792215853 6533530349706614172080945)
            ·
              refine ⟨4900147762279960629060709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6533530349706614172080945 4900147762279960629060709)
              ·
                refine ⟨918777705427492617948883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4900147762279960629060709 918777705427492617948883)
                ·
                  refine ⟨1378166558141238926923325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918777705427492617948883 1378166558141238926923325)
                  ·
                    refine ⟨516812459302964597596247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378166558141238926923325 516812459302964597596247)
                    ·
                      rfl

theorem cell22_1509733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_1509733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509733 prefixEnd_1509733 := by exact prefixLift 1509733
  have htrace : WordTrace (prefixWord ++ tailWord_1509733) baseStart_1509733 baseEnd_1509733 := by
    simpa [prefixWord, tailWord_1509733, baseEnd_1509733] using wordTrace_append hprefix tailTrace_1509733
  have hstable : (prefixWord ++ tailWord_1509733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509733).length < 2 ^ (prefixWord ++ tailWord_1509733).sum := by decide
  have hdescent : baseEnd_1509733 < baseStart_1509733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509744 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 2, 5]
def baseStart_1509744 : Nat := 118140960795 + 1509744 * 2 ^ 59
def prefixEnd_1509744 : Nat := 4983230072969 + 3 ^ 40 * 1509744 * 2
def baseEnd_1509744 : Nat := 516816224827764235571213

theorem tailTrace_1509744 : CollatzResearch.WordTrace tailWord_1509744 prefixEnd_1509744 516816224827764235571213 := by
  unfold tailWord_1509744
  simp only [CollatzResearch.WordTrace]
  refine ⟨27532443721231403296160143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36709924961641871061546857 27532443721231403296160143)
  ·
    refine ⟨41298665581847104944240215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27532443721231403296160143 41298665581847104944240215)
    ·
      refine ⟨61947998372770657416360323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41298665581847104944240215 61947998372770657416360323)
      ·
        refine ⟨92921997559155986124540485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61947998372770657416360323 92921997559155986124540485)
        ·
          refine ⟨17422874542341747398351341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92921997559155986124540485 17422874542341747398351341)
          ·
            refine ⟨6533577953378155274381753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17422874542341747398351341 6533577953378155274381753)
            ·
              refine ⟨4900183465033616455786315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6533577953378155274381753 4900183465033616455786315)
              ·
                refine ⟨7350275197550424683679473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4900183465033616455786315 7350275197550424683679473)
                ·
                  refine ⟨5512706398162818512759605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7350275197550424683679473 5512706398162818512759605)
                  ·
                    refine ⟨516816224827764235571213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5512706398162818512759605 516816224827764235571213)
                    ·
                      rfl

theorem cell22_1509744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 2, 5].length) (baseStart_1509744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509744 prefixEnd_1509744 := by exact prefixLift 1509744
  have htrace : WordTrace (prefixWord ++ tailWord_1509744) baseStart_1509744 baseEnd_1509744 := by
    simpa [prefixWord, tailWord_1509744, baseEnd_1509744] using wordTrace_append hprefix tailTrace_1509744
  have hstable : (prefixWord ++ tailWord_1509744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509744).length < 2 ^ (prefixWord ++ tailWord_1509744).sum := by decide
  have hdescent : baseEnd_1509744 < baseStart_1509744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509804 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 6, 4]
def baseStart_1509804 : Nat := 118140960795 + 1509804 * 2 ^ 59
def prefixEnd_1509804 : Nat := 4983230072969 + 3 ^ 40 * 1509804 * 2
def baseEnd_1509804 : Nat := 516836764053944079071029

theorem tailTrace_1509804 : CollatzResearch.WordTrace tailWord_1509804 prefixEnd_1509804 516836764053944079071029 := by
  unfold tailWord_1509804
  simp only [CollatzResearch.WordTrace]
  refine ⟨27533537911122718419752233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36711383881496957893002977 27533537911122718419752233)
  ·
    refine ⟨20650153433342038814814175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27533537911122718419752233 20650153433342038814814175)
    ·
      refine ⟨30975230150013058222221263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20650153433342038814814175 30975230150013058222221263)
      ·
        refine ⟨46462845225019587333331895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30975230150013058222221263 46462845225019587333331895)
        ·
          refine ⟨69694267837529380999997843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46462845225019587333331895 69694267837529380999997843)
          ·
            refine ⟨104541401756294071499996765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69694267837529380999997843 104541401756294071499996765)
            ·
              refine ⟨39203025658610276812498787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104541401756294071499996765 39203025658610276812498787)
              ·
                refine ⟨58804538487915415218748181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39203025658610276812498787 58804538487915415218748181)
                ·
                  refine ⟨2756462741621035088378821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58804538487915415218748181 2756462741621035088378821)
                  ·
                    refine ⟨516836764053944079071029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2756462741621035088378821 516836764053944079071029)
                    ·
                      rfl

theorem cell22_1509804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 4].length) (baseStart_1509804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509804 prefixEnd_1509804 := by exact prefixLift 1509804
  have htrace : WordTrace (prefixWord ++ tailWord_1509804) baseStart_1509804 baseEnd_1509804 := by
    simpa [prefixWord, tailWord_1509804, baseEnd_1509804] using wordTrace_append hprefix tailTrace_1509804
  have hstable : (prefixWord ++ tailWord_1509804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509804).length < 2 ^ (prefixWord ++ tailWord_1509804).sum := by decide
  have hdescent : baseEnd_1509804 < baseStart_1509804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509821 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 2, 4]
def baseStart_1509821 : Nat := 118140960795 + 1509821 * 2 ^ 59
def prefixEnd_1509821 : Nat := 4983230072969 + 3 ^ 40 * 1509821 * 2
def baseEnd_1509821 : Nat := 516842583501361701395977

theorem tailTrace_1509821 : CollatzResearch.WordTrace tailWord_1509821 prefixEnd_1509821 516842583501361701395977 := by
  unfold tailWord_1509821
  simp only [CollatzResearch.WordTrace]
  refine ⟨55067695863183848742873317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36711797242122565828582211 55067695863183848742873317)
  ·
    refine ⟨10325192974346971639288747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55067695863183848742873317 10325192974346971639288747)
    ·
      refine ⟨15487789461520457458933121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10325192974346971639288747 15487789461520457458933121)
      ·
        refine ⟨11615842096140343094199841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15487789461520457458933121 11615842096140343094199841)
        ·
          refine ⟨8711881572105257320649881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11615842096140343094199841 8711881572105257320649881)
          ·
            refine ⟨6533911179078942990487411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8711881572105257320649881 6533911179078942990487411)
            ·
              refine ⟨9800866768618414485731117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6533911179078942990487411 9800866768618414485731117)
              ·
                refine ⟨3675325038231905432149169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9800866768618414485731117 3675325038231905432149169)
                ·
                  refine ⟨2756493778673929074111877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3675325038231905432149169 2756493778673929074111877)
                  ·
                    refine ⟨516842583501361701395977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2756493778673929074111877 516842583501361701395977)
                    ·
                      rfl

theorem cell22_1509821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_1509821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509821 prefixEnd_1509821 := by exact prefixLift 1509821
  have htrace : WordTrace (prefixWord ++ tailWord_1509821) baseStart_1509821 baseEnd_1509821 := by
    simpa [prefixWord, tailWord_1509821, baseEnd_1509821] using wordTrace_append hprefix tailTrace_1509821
  have hstable : (prefixWord ++ tailWord_1509821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509821).length < 2 ^ (prefixWord ++ tailWord_1509821).sum := by decide
  have hdescent : baseEnd_1509821 < baseStart_1509821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509836 : List Nat := [2, 2, 1, 4, 4, 9]
def baseStart_1509836 : Nat := 118140960795 + 1509836 * 2 ^ 59
def prefixEnd_1509836 : Nat := 4983230072969 + 3 ^ 40 * 1509836 * 2
def baseEnd_1509836 : Nat := 6380836028492674842851

theorem tailTrace_1509836 : CollatzResearch.WordTrace tailWord_1509836 prefixEnd_1509836 6380836028492674842851 := by
  unfold tailWord_1509836
  simp only [CollatzResearch.WordTrace]
  refine ⟨27534121479064753152334681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36712161972086337536446241 27534121479064753152334681)
  ·
    refine ⟨20650591109298564864251011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27534121479064753152334681 20650591109298564864251011)
    ·
      refine ⟨30975886663947847296376517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20650591109298564864251011 30975886663947847296376517)
      ·
        refine ⟨5807978749490221368070597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30975886663947847296376517 5807978749490221368070597)
        ·
          refine ⟨1088996015529416506513237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5807978749490221368070597 1088996015529416506513237)
          ·
            refine ⟨6380836028492674842851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1088996015529416506513237 6380836028492674842851)
            ·
              rfl

theorem cell22_1509836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 9].length) (baseStart_1509836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509836 prefixEnd_1509836 := by exact prefixLift 1509836
  have htrace : WordTrace (prefixWord ++ tailWord_1509836) baseStart_1509836 baseEnd_1509836 := by
    simpa [prefixWord, tailWord_1509836, baseEnd_1509836] using wordTrace_append hprefix tailTrace_1509836
  have hstable : (prefixWord ++ tailWord_1509836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509836).length < 2 ^ (prefixWord ++ tailWord_1509836).sum := by decide
  have hdescent : baseEnd_1509836 < baseStart_1509836 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509849 : List Nat := [1, 2, 1, 2, 4, 1, 1, 1, 1, 8]
def baseStart_1509849 : Nat := 118140960795 + 1509849 * 2 ^ 59
def prefixEnd_1509849 : Nat := 4983230072969 + 3 ^ 40 * 1509849 * 2
def baseEnd_1509849 : Nat := 516852168473578961695891

theorem tailTrace_1509849 : CollatzResearch.WordTrace tailWord_1509849 prefixEnd_1509849 516852168473578961695891 := by
  unfold tailWord_1509849
  simp only [CollatzResearch.WordTrace]
  refine ⟨55068717107082409524892601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36712478071388273016595067 55068717107082409524892601)
  ·
    refine ⟨41301537830311807143669451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55068717107082409524892601 41301537830311807143669451)
    ·
      refine ⟨61952306745467710715504177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41301537830311807143669451 61952306745467710715504177)
      ·
        refine ⟨46464230059100783036628133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61952306745467710715504177 46464230059100783036628133)
        ·
          refine ⟨8712043136081396819367775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46464230059100783036628133 8712043136081396819367775)
          ·
            refine ⟨13068064704122095229051663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8712043136081396819367775 13068064704122095229051663)
            ·
              refine ⟨19602097056183142843577495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13068064704122095229051663 19602097056183142843577495)
              ·
                refine ⟨29403145584274714265366243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19602097056183142843577495 29403145584274714265366243)
                ·
                  refine ⟨44104718376412071398049365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29403145584274714265366243 44104718376412071398049365)
                  ·
                    refine ⟨516852168473578961695891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44104718376412071398049365 516852168473578961695891)
                    ·
                      rfl

theorem cell22_1509849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 8].length) (baseStart_1509849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509849 prefixEnd_1509849 := by exact prefixLift 1509849
  have htrace : WordTrace (prefixWord ++ tailWord_1509849) baseStart_1509849 baseEnd_1509849 := by
    simpa [prefixWord, tailWord_1509849, baseEnd_1509849] using wordTrace_append hprefix tailTrace_1509849
  have hstable : (prefixWord ++ tailWord_1509849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509849).length < 2 ^ (prefixWord ++ tailWord_1509849).sum := by decide
  have hdescent : baseEnd_1509849 < baseStart_1509849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509885 : List Nat := [1, 4, 1, 1, 1, 3, 4, 3, 1, 3]
def baseStart_1509885 : Nat := 118140960795 + 1509885 * 2 ^ 59
def prefixEnd_1509885 : Nat := 4983230072969 + 3 ^ 40 * 1509885 * 2
def baseEnd_1509885 : Nat := 516864492009286867795781

theorem tailTrace_1509885 : CollatzResearch.WordTrace tailWord_1509885 prefixEnd_1509885 516864492009286867795781 := by
  unfold tailWord_1509885
  simp only [CollatzResearch.WordTrace]
  refine ⟨55070030134951987673203109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36713353423301325115468739 55070030134951987673203109)
  ·
    refine ⟨10325630650303497688725583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55070030134951987673203109 10325630650303497688725583)
    ·
      refine ⟨15488445975455246533088375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10325630650303497688725583 15488445975455246533088375)
      ·
        refine ⟨23232668963182869799632563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15488445975455246533088375 23232668963182869799632563)
        ·
          refine ⟨34849003444774304699448845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23232668963182869799632563 34849003444774304699448845)
          ·
            refine ⟨13068376291790364262293317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34849003444774304699448845 13068376291790364262293317)
            ·
              refine ⟨2450320554710693299179997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13068376291790364262293317 2450320554710693299179997)
              ·
                refine ⟨918870208016509987192499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2450320554710693299179997 918870208016509987192499)
                ·
                  refine ⟨1378305312024764980788749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 918870208016509987192499 1378305312024764980788749)
                  ·
                    refine ⟨516864492009286867795781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378305312024764980788749 516864492009286867795781)
                    ·
                      rfl

theorem cell22_1509885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 4, 3, 1, 3].length) (baseStart_1509885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509885 prefixEnd_1509885 := by exact prefixLift 1509885
  have htrace : WordTrace (prefixWord ++ tailWord_1509885) baseStart_1509885 baseEnd_1509885 := by
    simpa [prefixWord, tailWord_1509885, baseEnd_1509885] using wordTrace_append hprefix tailTrace_1509885
  have hstable : (prefixWord ++ tailWord_1509885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509885).length < 2 ^ (prefixWord ++ tailWord_1509885).sum := by decide
  have hdescent : baseEnd_1509885 < baseStart_1509885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1509941 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1509941 : Nat := 118140960795 + 1509941 * 2 ^ 59
def prefixEnd_1509941 : Nat := 4983230072969 + 3 ^ 40 * 1509941 * 2
def baseEnd_1509941 : Nat := 516883661953721388395609

theorem tailTrace_1509941 : CollatzResearch.WordTrace tailWord_1509941 prefixEnd_1509941 516883661953721388395609 := by
  unfold tailWord_1509941
  simp only [CollatzResearch.WordTrace]
  refine ⟨55072072622749109237241677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36714715081832739491494451 55072072622749109237241677)
  ·
    refine ⟨20652027233530915963965629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55072072622749109237241677 20652027233530915963965629)
    ·
      refine ⟨7744510212574093486487111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20652027233530915963965629 7744510212574093486487111)
      ·
        refine ⟨11616765318861140229730667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7744510212574093486487111 11616765318861140229730667)
        ·
          refine ⟨17425147978291710344596001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11616765318861140229730667 17425147978291710344596001)
          ·
            refine ⟨13068860983718782758447001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17425147978291710344596001 13068860983718782758447001)
            ·
              refine ⟨9801645737789087068835251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13068860983718782758447001 9801645737789087068835251)
              ·
                refine ⟨14702468606683630603252877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9801645737789087068835251 14702468606683630603252877)
                ·
                  refine ⟨5513425727506361476219829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14702468606683630603252877 5513425727506361476219829)
                  ·
                    refine ⟨516883661953721388395609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5513425727506361476219829 516883661953721388395609)
                    ·
                      rfl

theorem cell22_1509941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1509941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1509941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1509941 prefixEnd_1509941 := by exact prefixLift 1509941
  have htrace : WordTrace (prefixWord ++ tailWord_1509941) baseStart_1509941 baseEnd_1509941 := by
    simpa [prefixWord, tailWord_1509941, baseEnd_1509941] using wordTrace_append hprefix tailTrace_1509941
  have hstable : (prefixWord ++ tailWord_1509941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1509941).length < 2 ^ (prefixWord ++ tailWord_1509941).sum := by decide
  have hdescent : baseEnd_1509941 < baseStart_1509941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1509941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510031 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 2, 5]
def baseStart_1510031 : Nat := 118140960795 + 1510031 * 2 ^ 59
def prefixEnd_1510031 : Nat := 4983230072969 + 3 ^ 40 * 1510031 * 2
def baseEnd_1510031 : Nat := 516914470792991153645333

theorem tailTrace_1510031 : CollatzResearch.WordTrace tailWord_1510031 prefixEnd_1510031 516914470792991153645333 := by
  unfold tailWord_1510031
  simp only [CollatzResearch.WordTrace]
  refine ⟨55075355192423054608017947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36716903461615369738678631 55075355192423054608017947)
  ·
    refine ⟨82613032788634581912026921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55075355192423054608017947 82613032788634581912026921)
    ·
      refine ⟨61959774591475936434020191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82613032788634581912026921 61959774591475936434020191)
      ·
        refine ⟨92939661887213904651030287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61959774591475936434020191 92939661887213904651030287)
        ·
          refine ⟨139409492830820856976545431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92939661887213904651030287 139409492830820856976545431)
          ·
            refine ⟨209114239246231285464818147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139409492830820856976545431 209114239246231285464818147)
            ·
              refine ⟨313671358869346928197227221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209114239246231285464818147 313671358869346928197227221)
              ·
                refine ⟨7351672473500318629622513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 313671358869346928197227221 7351672473500318629622513)
                ·
                  refine ⟨5513754355125238972216885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7351672473500318629622513 5513754355125238972216885)
                  ·
                    refine ⟨516914470792991153645333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5513754355125238972216885 516914470792991153645333)
                    ·
                      rfl

theorem cell22_1510031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_1510031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510031 prefixEnd_1510031 := by exact prefixLift 1510031
  have htrace : WordTrace (prefixWord ++ tailWord_1510031) baseStart_1510031 baseEnd_1510031 := by
    simpa [prefixWord, tailWord_1510031, baseEnd_1510031] using wordTrace_append hprefix tailTrace_1510031
  have hstable : (prefixWord ++ tailWord_1510031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510031).length < 2 ^ (prefixWord ++ tailWord_1510031).sum := by decide
  have hdescent : baseEnd_1510031 < baseStart_1510031 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510125 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 2, 4]
def baseStart_1510125 : Nat := 118140960795 + 1510125 * 2 ^ 59
def prefixEnd_1510125 : Nat := 4983230072969 + 3 ^ 40 * 1510125 * 2
def baseEnd_1510125 : Nat := 516946648914006241795045

theorem tailTrace_1510125 : CollatzResearch.WordTrace tailWord_1510125 prefixEnd_1510125 516946648914006241795045 := by
  unfold tailWord_1510125
  simp only [CollatzResearch.WordTrace]
  refine ⟨55078783654082508661939829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36719189102721672441293219 55078783654082508661939829)
  ·
    refine ⟨5163635967570235187056859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55078783654082508661939829 5163635967570235187056859)
    ·
      refine ⟨7745453951355352780585289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5163635967570235187056859 7745453951355352780585289)
      ·
        refine ⟨5809090463516514585438967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7745453951355352780585289 5809090463516514585438967)
        ·
          refine ⟨8713635695274771878158451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5809090463516514585438967 8713635695274771878158451)
          ·
            refine ⟨13070453542912157817237677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8713635695274771878158451 13070453542912157817237677)
            ·
              refine ⟨4901420078592059181464129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13070453542912157817237677 4901420078592059181464129)
              ·
                refine ⟨3676065058944044386098097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901420078592059181464129 3676065058944044386098097)
                ·
                  refine ⟨2757048794208033289573573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3676065058944044386098097 2757048794208033289573573)
                  ·
                    refine ⟨516946648914006241795045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757048794208033289573573 516946648914006241795045)
                    ·
                      rfl

theorem cell22_1510125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_1510125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510125 prefixEnd_1510125 := by exact prefixLift 1510125
  have htrace : WordTrace (prefixWord ++ tailWord_1510125) baseStart_1510125 baseEnd_1510125 := by
    simpa [prefixWord, tailWord_1510125, baseEnd_1510125] using wordTrace_append hprefix tailTrace_1510125
  have hstable : (prefixWord ++ tailWord_1510125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510125).length < 2 ^ (prefixWord ++ tailWord_1510125).sum := by decide
  have hdescent : baseEnd_1510125 < baseStart_1510125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510215 : List Nat := [1, 1, 4, 1, 2, 1, 1, 6, 1, 4]
def baseStart_1510215 : Nat := 118140960795 + 1510215 * 2 ^ 59
def prefixEnd_1510215 : Nat := 4983230072969 + 3 ^ 40 * 1510215 * 2
def baseEnd_1510215 : Nat := 516977457753276007044769

theorem tailTrace_1510215 : CollatzResearch.WordTrace tailWord_1510215 prefixEnd_1510215 516977457753276007044769 := by
  unfold tailWord_1510215
  simp only [CollatzResearch.WordTrace]
  refine ⟨55082066223756454032716099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36721377482504302688477399 55082066223756454032716099)
  ·
    refine ⟨82623099335634681049074149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55082066223756454032716099 82623099335634681049074149)
    ·
      refine ⟨15491831125431502696701403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82623099335634681049074149 15491831125431502696701403)
      ·
        refine ⟨23237746688147254045052105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15491831125431502696701403 23237746688147254045052105)
        ·
          refine ⟨17428310016110440533789079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23237746688147254045052105 17428310016110440533789079)
          ·
            refine ⟨26142465024165660800683619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17428310016110440533789079 26142465024165660800683619)
            ·
              refine ⟨39213697536248491201025429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26142465024165660800683619 39213697536248491201025429)
              ·
                refine ⟨1838142072011648025048067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39213697536248491201025429 1838142072011648025048067)
                ·
                  refine ⟨2757213108017472037572101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838142072011648025048067 2757213108017472037572101)
                  ·
                    refine ⟨516977457753276007044769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757213108017472037572101 516977457753276007044769)
                    ·
                      rfl

theorem cell22_1510215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_1510215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510215 prefixEnd_1510215 := by exact prefixLift 1510215
  have htrace : WordTrace (prefixWord ++ tailWord_1510215) baseStart_1510215 baseEnd_1510215 := by
    simpa [prefixWord, tailWord_1510215, baseEnd_1510215] using wordTrace_append hprefix tailTrace_1510215
  have hstable : (prefixWord ++ tailWord_1510215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510215).length < 2 ^ (prefixWord ++ tailWord_1510215).sum := by decide
  have hdescent : baseEnd_1510215 < baseStart_1510215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510247 : List Nat := [1, 1, 5, 1, 2, 2, 2, 4, 4]
def baseStart_1510247 : Nat := 118140960795 + 1510247 * 2 ^ 59
def prefixEnd_1510247 : Nat := 4983230072969 + 3 ^ 40 * 1510247 * 2
def baseEnd_1510247 : Nat := 172329470669079530081557

theorem tailTrace_1510247 : CollatzResearch.WordTrace tailWord_1510247 prefixEnd_1510247 172329470669079530081557 := by
  unfold tailWord_1510247
  simp only [CollatzResearch.WordTrace]
  refine ⟨55083233359640523497880995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36722155573093682331920663 55083233359640523497880995)
  ·
    refine ⟨82624850039460785246821493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55083233359640523497880995 82624850039460785246821493)
    ·
      refine ⟨7746079691199448616889515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82624850039460785246821493 7746079691199448616889515)
      ·
        refine ⟨11619119536799172925334273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7746079691199448616889515 11619119536799172925334273)
        ·
          refine ⟨8714339652599379694000705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11619119536799172925334273 8714339652599379694000705)
          ·
            refine ⟨6535754739449534770500529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8714339652599379694000705 6535754739449534770500529)
            ·
              refine ⟨4901816054587151077875397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6535754739449534770500529 4901816054587151077875397)
              ·
                refine ⟨919090510235090827101637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4901816054587151077875397 919090510235090827101637)
                ·
                  refine ⟨172329470669079530081557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 919090510235090827101637 172329470669079530081557)
                  ·
                    rfl

theorem cell22_1510247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 4].length) (baseStart_1510247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510247 prefixEnd_1510247 := by exact prefixLift 1510247
  have htrace : WordTrace (prefixWord ++ tailWord_1510247) baseStart_1510247 baseEnd_1510247 := by
    simpa [prefixWord, tailWord_1510247, baseEnd_1510247] using wordTrace_append hprefix tailTrace_1510247
  have hstable : (prefixWord ++ tailWord_1510247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510247).length < 2 ^ (prefixWord ++ tailWord_1510247).sum := by decide
  have hdescent : baseEnd_1510247 < baseStart_1510247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510307 : List Nat := [1, 1, 1, 4, 1, 2, 5, 1, 3, 3]
def baseStart_1510307 : Nat := 118140960795 + 1510307 * 2 ^ 59
def prefixEnd_1510307 : Nat := 4983230072969 + 3 ^ 40 * 1510307 * 2
def baseEnd_1510307 : Nat := 517008951233418433744487

theorem tailTrace_1510307 : CollatzResearch.WordTrace tailWord_1510307 prefixEnd_1510307 517008951233418433744487 := by
  unfold tailWord_1510307
  simp only [CollatzResearch.WordTrace]
  refine ⟨55085421739423153745065175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36723614492948769163376783 55085421739423153745065175)
  ·
    refine ⟨82628132609134730617597763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55085421739423153745065175 82628132609134730617597763)
    ·
      refine ⟨123942198913702095926396645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82628132609134730617597763 123942198913702095926396645)
      ·
        refine ⟨23239162296319142986199371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123942198913702095926396645 23239162296319142986199371)
        ·
          refine ⟨34858743444478714479299057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23239162296319142986199371 34858743444478714479299057)
          ·
            refine ⟨26144057583359035859474293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34858743444478714479299057 26144057583359035859474293)
            ·
              refine ⟨2451005398439909611825715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26144057583359035859474293 2451005398439909611825715)
              ·
                refine ⟨3676508097659864417738573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451005398439909611825715 3676508097659864417738573)
                ·
                  refine ⟨1378690536622449156651965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3676508097659864417738573 1378690536622449156651965)
                  ·
                    refine ⟨517008951233418433744487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378690536622449156651965 517008951233418433744487)
                    ·
                      rfl

theorem cell22_1510307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 1, 3, 3].length) (baseStart_1510307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510307 prefixEnd_1510307 := by exact prefixLift 1510307
  have htrace : WordTrace (prefixWord ++ tailWord_1510307) baseStart_1510307 baseEnd_1510307 := by
    simpa [prefixWord, tailWord_1510307, baseEnd_1510307] using wordTrace_append hprefix tailTrace_1510307
  have hstable : (prefixWord ++ tailWord_1510307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510307).length < 2 ^ (prefixWord ++ tailWord_1510307).sum := by decide
  have hdescent : baseEnd_1510307 < baseStart_1510307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510354 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 5]
def baseStart_1510354 : Nat := 118140960795 + 1510354 * 2 ^ 59
def prefixEnd_1510354 : Nat := 4983230072969 + 3 ^ 40 * 1510354 * 2
def baseEnd_1510354 : Nat := 172341680097975325939781

theorem tailTrace_1510354 : CollatzResearch.WordTrace tailWord_1510354 prefixEnd_1510354 172341680097975325939781 := by
  unfold tailWord_1510354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13771783992563220193006529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36724757313501920514684077 13771783992563220193006529)
  ·
    refine ⟨10328837994422415144754897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13771783992563220193006529 10328837994422415144754897)
    ·
      refine ⟨7746628495816811358566173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10328837994422415144754897 7746628495816811358566173)
      ·
        refine ⟨2904985685931304259462315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7746628495816811358566173 2904985685931304259462315)
        ·
          refine ⟨4357478528896956389193473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2904985685931304259462315 4357478528896956389193473)
          ·
            refine ⟨3268108896672717291895105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4357478528896956389193473 3268108896672717291895105)
            ·
              refine ⟨2451081672504537968921329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3268108896672717291895105 2451081672504537968921329)
              ·
                refine ⟨1838311254378403476690997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2451081672504537968921329 1838311254378403476690997)
                ·
                  refine ⟨172341680097975325939781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1838311254378403476690997 172341680097975325939781)
                  ·
                    rfl

theorem cell22_1510354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_1510354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510354 prefixEnd_1510354 := by exact prefixLift 1510354
  have htrace : WordTrace (prefixWord ++ tailWord_1510354) baseStart_1510354 baseEnd_1510354 := by
    simpa [prefixWord, tailWord_1510354, baseEnd_1510354] using wordTrace_append hprefix tailTrace_1510354
  have hstable : (prefixWord ++ tailWord_1510354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510354).length < 2 ^ (prefixWord ++ tailWord_1510354).sum := by decide
  have hdescent : baseEnd_1510354 < baseStart_1510354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510358 : List Nat := [5, 2, 1, 1, 2, 2, 1, 4, 1, 3]
def baseStart_1510358 : Nat := 118140960795 + 1510358 * 2 ^ 59
def prefixEnd_1510358 : Nat := 4983230072969 + 3 ^ 40 * 1510358 * 2
def baseEnd_1510358 : Nat := 517026409575671300719331

theorem tailTrace_1510358 : CollatzResearch.WordTrace tailWord_1510358 prefixEnd_1510358 517026409575671300719331 := by
  unfold tailWord_1510358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3442955116389899340948233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36724854574825592970114485 3442955116389899340948233)
  ·
    refine ⟨2582216337292424505711175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3442955116389899340948233 2582216337292424505711175)
    ·
      refine ⟨3873324505938636758566763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2582216337292424505711175 3873324505938636758566763)
      ·
        refine ⟨5809986758907955137850145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3873324505938636758566763 5809986758907955137850145)
        ·
          refine ⟨4357490069180966353387609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5809986758907955137850145 4357490069180966353387609)
          ·
            refine ⟨3268117551885724765040707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4357490069180966353387609 3268117551885724765040707)
            ·
              refine ⟨4902176327828587147561061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268117551885724765040707 4902176327828587147561061)
              ·
                refine ⟨919158061467860090167699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4902176327828587147561061 919158061467860090167699)
                ·
                  refine ⟨1378737092201790135251549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919158061467860090167699 1378737092201790135251549)
                  ·
                    refine ⟨517026409575671300719331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378737092201790135251549 517026409575671300719331)
                    ·
                      rfl

theorem cell22_1510358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 4, 1, 3].length) (baseStart_1510358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510358 prefixEnd_1510358 := by exact prefixLift 1510358
  have htrace : WordTrace (prefixWord ++ tailWord_1510358) baseStart_1510358 baseEnd_1510358 := by
    simpa [prefixWord, tailWord_1510358, baseEnd_1510358] using wordTrace_append hprefix tailTrace_1510358
  have hstable : (prefixWord ++ tailWord_1510358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510358).length < 2 ^ (prefixWord ++ tailWord_1510358).sum := by decide
  have hdescent : baseEnd_1510358 < baseStart_1510358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510397 : List Nat := [1, 4, 1, 1, 1, 2, 1, 4, 4, 3]
def baseStart_1510397 : Nat := 118140960795 + 1510397 * 2 ^ 59
def prefixEnd_1510397 : Nat := 4983230072969 + 3 ^ 40 * 1510397 * 2
def baseEnd_1510397 : Nat := 517039760072688198994211

theorem tailTrace_1510397 : CollatzResearch.WordTrace tailWord_1510397 prefixEnd_1510397 517039760072688198994211 := by
  unfold tailWord_1510397
  simp only [CollatzResearch.WordTrace]
  refine ⟨55088704309097099115841445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36725802872731399410560963 55088704309097099115841445)
  ·
    refine ⟨10329132057955706084220271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55088704309097099115841445 10329132057955706084220271)
    ·
      refine ⟨15493698086933559126330407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10329132057955706084220271 15493698086933559126330407)
      ·
        refine ⟨23240547130400338689495611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15493698086933559126330407 23240547130400338689495611)
        ·
          refine ⟨34860820695600508034243417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23240547130400338689495611 34860820695600508034243417)
          ·
            refine ⟨26145615521700381025682563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34860820695600508034243417 26145615521700381025682563)
            ·
              refine ⟨39218423282550571538523845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26145615521700381025682563 39218423282550571538523845)
              ·
                refine ⟨7353454365478232163473221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39218423282550571538523845 7353454365478232163473221)
                ·
                  refine ⟨1378772693527168530651229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7353454365478232163473221 1378772693527168530651229)
                  ·
                    refine ⟨517039760072688198994211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378772693527168530651229 517039760072688198994211)
                    ·
                      rfl

theorem cell22_1510397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_1510397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510397 prefixEnd_1510397 := by exact prefixLift 1510397
  have htrace : WordTrace (prefixWord ++ tailWord_1510397) baseStart_1510397 baseEnd_1510397 := by
    simpa [prefixWord, tailWord_1510397, baseEnd_1510397] using wordTrace_append hprefix tailTrace_1510397
  have hstable : (prefixWord ++ tailWord_1510397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510397).length < 2 ^ (prefixWord ++ tailWord_1510397).sum := by decide
  have hdescent : baseEnd_1510397 < baseStart_1510397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510401 : List Nat := [1, 2, 4, 1, 2, 4, 2, 1, 1, 4]
def baseStart_1510401 : Nat := 118140960795 + 1510401 * 2 ^ 59
def prefixEnd_1510401 : Nat := 4983230072969 + 3 ^ 40 * 1510401 * 2
def baseEnd_1510401 : Nat := 517041129354433521894199

theorem tailTrace_1510401 : CollatzResearch.WordTrace tailWord_1510401 prefixEnd_1510401 517041129354433521894199 := by
  unfold tailWord_1510401
  simp only [CollatzResearch.WordTrace]
  refine ⟨55088850201082607798987057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36725900134055071865991371 55088850201082607798987057)
  ·
    refine ⟨41316637650811955849240293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55088850201082607798987057 41316637650811955849240293)
    ·
      refine ⟨7746869559527241721732555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41316637650811955849240293 7746869559527241721732555)
      ·
        refine ⟨11620304339290862582598833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7746869559527241721732555 11620304339290862582598833)
        ·
          refine ⟨8715228254468146936949125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11620304339290862582598833 8715228254468146936949125)
          ·
            refine ⟨1634105297712777550677961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8715228254468146936949125 1634105297712777550677961)
            ·
              refine ⟨1225578973284583163008471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1634105297712777550677961 1225578973284583163008471)
              ·
                refine ⟨1838368459926874744512707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225578973284583163008471 1838368459926874744512707)
                ·
                  refine ⟨2757552689890312116769061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838368459926874744512707 2757552689890312116769061)
                  ·
                    refine ⟨517041129354433521894199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757552689890312116769061 517041129354433521894199)
                    ·
                      rfl

theorem cell22_1510401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_1510401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510401 prefixEnd_1510401 := by exact prefixLift 1510401
  have htrace : WordTrace (prefixWord ++ tailWord_1510401) baseStart_1510401 baseEnd_1510401 := by
    simpa [prefixWord, tailWord_1510401, baseEnd_1510401] using wordTrace_append hprefix tailTrace_1510401
  have hstable : (prefixWord ++ tailWord_1510401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510401).length < 2 ^ (prefixWord ++ tailWord_1510401).sum := by decide
  have hdescent : baseEnd_1510401 < baseStart_1510401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510414 : List Nat := [4, 1, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_1510414 : Nat := 118140960795 + 1510414 * 2 ^ 59
def prefixEnd_1510414 : Nat := 4983230072969 + 3 ^ 40 * 1510414 * 2
def baseEnd_1510414 : Nat := 517045579520105821319159

theorem tailTrace_1510414 : CollatzResearch.WordTrace tailWord_1510414 prefixEnd_1510414 517045579520105821319159 := by
  unfold tailWord_1510414
  simp only [CollatzResearch.WordTrace]
  refine ⟨6886165543754438877401287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36726216233357007346140197 6886165543754438877401287)
  ·
    refine ⟨10329248315631658316101931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6886165543754438877401287 10329248315631658316101931)
    ·
      refine ⟨15493872473447487474152897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10329248315631658316101931 15493872473447487474152897)
      ·
        refine ⟨11620404355085615605614673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15493872473447487474152897 11620404355085615605614673)
        ·
          refine ⟨8715303266314211704211005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11620404355085615605614673 8715303266314211704211005)
          ·
            refine ⟨3268238724867829389079127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8715303266314211704211005 3268238724867829389079127)
            ·
              refine ⟨4902358087301744083618691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268238724867829389079127 4902358087301744083618691)
              ·
                refine ⟨7353537130952616125428037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4902358087301744083618691 7353537130952616125428037)
                ·
                  refine ⟨1378788212053615523517757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7353537130952616125428037 1378788212053615523517757)
                  ·
                    refine ⟨517045579520105821319159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378788212053615523517757 517045579520105821319159)
                    ·
                      rfl

theorem cell22_1510414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_1510414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510414 prefixEnd_1510414 := by exact prefixLift 1510414
  have htrace : WordTrace (prefixWord ++ tailWord_1510414) baseStart_1510414 baseEnd_1510414 := by
    simpa [prefixWord, tailWord_1510414, baseEnd_1510414] using wordTrace_append hprefix tailTrace_1510414
  have hstable : (prefixWord ++ tailWord_1510414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510414).length < 2 ^ (prefixWord ++ tailWord_1510414).sum := by decide
  have hdescent : baseEnd_1510414 < baseStart_1510414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510431 : List Nat := [1, 1, 2, 4, 1, 4, 3, 1, 2, 3]
def baseStart_1510431 : Nat := 118140960795 + 1510431 * 2 ^ 59
def prefixEnd_1510431 : Nat := 4983230072969 + 3 ^ 40 * 1510431 * 2
def baseEnd_1510431 : Nat := 517051398967523443644107

theorem tailTrace_1510431 : CollatzResearch.WordTrace tailWord_1510431 prefixEnd_1510431 517051398967523443644107 := by
  unfold tailWord_1510431
  simp only [CollatzResearch.WordTrace]
  refine ⟨55089944390973922922579147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36726629593982615281719431 55089944390973922922579147)
  ·
    refine ⟨82634916586460884383868721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55089944390973922922579147 82634916586460884383868721)
    ·
      refine ⟨61976187439845663287901541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82634916586460884383868721 61976187439845663287901541)
      ·
        refine ⟨11620535144971061866481539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61976187439845663287901541 11620535144971061866481539)
        ·
          refine ⟨17430802717456592799722309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11620535144971061866481539 17430802717456592799722309)
          ·
            refine ⟨3268275509523111149947933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17430802717456592799722309 3268275509523111149947933)
            ·
              refine ⟨1225603316071166681230475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3268275509523111149947933 1225603316071166681230475)
              ·
                refine ⟨1838404974106750021845713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225603316071166681230475 1838404974106750021845713)
                ·
                  refine ⟨1378803730580062516384285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1838404974106750021845713 1378803730580062516384285)
                  ·
                    refine ⟨517051398967523443644107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378803730580062516384285 517051398967523443644107)
                    ·
                      rfl

theorem cell22_1510431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 1, 2, 3].length) (baseStart_1510431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510431 prefixEnd_1510431 := by exact prefixLift 1510431
  have htrace : WordTrace (prefixWord ++ tailWord_1510431) baseStart_1510431 baseEnd_1510431 := by
    simpa [prefixWord, tailWord_1510431, baseEnd_1510431] using wordTrace_append hprefix tailTrace_1510431
  have hstable : (prefixWord ++ tailWord_1510431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510431).length < 2 ^ (prefixWord ++ tailWord_1510431).sum := by decide
  have hdescent : baseEnd_1510431 < baseStart_1510431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510472 : List Nat := [2, 1, 3, 1, 1, 1, 4, 4, 5]
def baseStart_1510472 : Nat := 118140960795 + 1510472 * 2 ^ 59
def prefixEnd_1510472 : Nat := 4983230072969 + 3 ^ 40 * 1510472 * 2
def baseEnd_1510472 : Nat := 172355144701804334456327

theorem tailTrace_1510472 : CollatzResearch.WordTrace tailWord_1510472 prefixEnd_1510472 172355144701804334456327 := by
  unfold tailWord_1510472
  simp only [CollatzResearch.WordTrace]
  refine ⟨27545719891912693462410835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36727626522550257949881113 27545719891912693462410835)
  ·
    refine ⟨41318579837869040193616253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27545719891912693462410835 41318579837869040193616253)
    ·
      refine ⟨15494467439200890072606095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41318579837869040193616253 15494467439200890072606095)
      ·
        refine ⟨23241701158801335108909143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15494467439200890072606095 23241701158801335108909143)
        ·
          refine ⟨34862551738202002663363715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23241701158801335108909143 34862551738202002663363715)
          ·
            refine ⟨52293827607303003995045573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34862551738202002663363715 52293827607303003995045573)
            ·
              refine ⟨9805092676369313249071045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52293827607303003995045573 9805092676369313249071045)
              ·
                refine ⟨1838454876819246234200821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9805092676369313249071045 1838454876819246234200821)
                ·
                  refine ⟨172355144701804334456327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1838454876819246234200821 172355144701804334456327)
                  ·
                    rfl

theorem cell22_1510472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 4, 5].length) (baseStart_1510472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510472 prefixEnd_1510472 := by exact prefixLift 1510472
  have htrace : WordTrace (prefixWord ++ tailWord_1510472) baseStart_1510472 baseEnd_1510472 := by
    simpa [prefixWord, tailWord_1510472, baseEnd_1510472] using wordTrace_append hprefix tailTrace_1510472
  have hstable : (prefixWord ++ tailWord_1510472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510472).length < 2 ^ (prefixWord ++ tailWord_1510472).sum := by decide
  have hdescent : baseEnd_1510472 < baseStart_1510472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510547 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 4, 4]
def baseStart_1510547 : Nat := 118140960795 + 1510547 * 2 ^ 59
def prefixEnd_1510547 : Nat := 4983230072969 + 3 ^ 40 * 1510547 * 2
def baseEnd_1510547 : Nat := 517091108138137807743751

theorem tailTrace_1510547 : CollatzResearch.WordTrace tailWord_1510547 prefixEnd_1510547 517091108138137807743751 := by
  unfold tailWord_1510547
  simp only [CollatzResearch.WordTrace]
  refine ⟨55094175258553674733801895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36729450172369116489201263 55094175258553674733801895)
  ·
    refine ⟨82641262887830512100702843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55094175258553674733801895 82641262887830512100702843)
    ·
      refine ⟨123961894331745768151054265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82641262887830512100702843 123961894331745768151054265)
      ·
        refine ⟨92971420748809326113290699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123961894331745768151054265 92971420748809326113290699)
        ·
          refine ⟨139457131123213989169936049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92971420748809326113290699 139457131123213989169936049)
          ·
            refine ⟨104592848342410491877452037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139457131123213989169936049 104592848342410491877452037)
            ·
              refine ⟨19611159064201967227022257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104592848342410491877452037 19611159064201967227022257)
              ·
                refine ⟨14708369298151475420266693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19611159064201967227022257 14708369298151475420266693)
                ·
                  refine ⟨2757819243403401641300005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14708369298151475420266693 2757819243403401641300005)
                  ·
                    refine ⟨517091108138137807743751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757819243403401641300005 517091108138137807743751)
                    ·
                      rfl

theorem cell22_1510547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 4, 4].length) (baseStart_1510547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510547 prefixEnd_1510547 := by exact prefixLift 1510547
  have htrace : WordTrace (prefixWord ++ tailWord_1510547) baseStart_1510547 baseEnd_1510547 := by
    simpa [prefixWord, tailWord_1510547, baseEnd_1510547] using wordTrace_append hprefix tailTrace_1510547
  have hstable : (prefixWord ++ tailWord_1510547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510547).length < 2 ^ (prefixWord ++ tailWord_1510547).sum := by decide
  have hdescent : baseEnd_1510547 < baseStart_1510547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510564 : List Nat := [2, 3, 1, 2, 3, 2, 1, 1, 1, 6]
def baseStart_1510564 : Nat := 118140960795 + 1510564 * 2 ^ 59
def prefixEnd_1510564 : Nat := 4983230072969 + 3 ^ 40 * 1510564 * 2
def baseEnd_1510564 : Nat := 517096927585555430068699

theorem tailTrace_1510564 : CollatzResearch.WordTrace tailWord_1510564 prefixEnd_1510564 517096927585555430068699 := by
  unfold tailWord_1510564
  simp only [CollatzResearch.WordTrace]
  refine ⟨27547397649746043318585373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36729863532994724424780497 27547397649746043318585373)
  ·
    refine ⟨10330274118654766244469515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27547397649746043318585373 10330274118654766244469515)
    ·
      refine ⟨15495411177982149366704273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10330274118654766244469515 15495411177982149366704273)
      ·
        refine ⟨11621558383486612025028205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15495411177982149366704273 11621558383486612025028205)
        ·
          refine ⟨4358084393807479509385577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11621558383486612025028205 4358084393807479509385577)
          ·
            refine ⟨3268563295355609632039183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4358084393807479509385577 3268563295355609632039183)
            ·
              refine ⟨4902844943033414448058775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268563295355609632039183 4902844943033414448058775)
              ·
                refine ⟨7354267414550121672088163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4902844943033414448058775 7354267414550121672088163)
                ·
                  refine ⟨11031401121825182508132245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7354267414550121672088163 11031401121825182508132245)
                  ·
                    refine ⟨517096927585555430068699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11031401121825182508132245 517096927585555430068699)
                    ·
                      rfl

theorem cell22_1510564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 1, 1, 1, 6].length) (baseStart_1510564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510564 prefixEnd_1510564 := by exact prefixLift 1510564
  have htrace : WordTrace (prefixWord ++ tailWord_1510564) baseStart_1510564 baseEnd_1510564 := by
    simpa [prefixWord, tailWord_1510564, baseEnd_1510564] using wordTrace_append hprefix tailTrace_1510564
  have hstable : (prefixWord ++ tailWord_1510564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510564).length < 2 ^ (prefixWord ++ tailWord_1510564).sum := by decide
  have hdescent : baseEnd_1510564 < baseStart_1510564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510570 : List Nat := [3, 1, 5, 1, 1, 3, 2, 1, 1, 4]
def baseStart_1510570 : Nat := 118140960795 + 1510570 * 2 ^ 59
def prefixEnd_1510570 : Nat := 4983230072969 + 3 ^ 40 * 1510570 * 2
def baseEnd_1510570 : Nat := 517098981508173414418681

theorem tailTrace_1510570 : CollatzResearch.WordTrace tailWord_1510570 prefixEnd_1510570 517098981508173414418681 := by
  unfold tailWord_1510570
  simp only [CollatzResearch.WordTrace]
  refine ⟨13773753534367587415472291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36730009424980233107926109 13773753534367587415472291)
  ·
    refine ⟨20660630301551381123208437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13773753534367587415472291 20660630301551381123208437)
    ·
      refine ⟨1936934090770441980300791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20660630301551381123208437 1936934090770441980300791)
      ·
        refine ⟨2905401136155662970451187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1936934090770441980300791 2905401136155662970451187)
        ·
          refine ⟨4358101704233494455676781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2905401136155662970451187 4358101704233494455676781)
          ·
            refine ⟨1634288139087560420878793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4358101704233494455676781 1634288139087560420878793)
            ·
              refine ⟨1225716104315670315659095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1634288139087560420878793 1225716104315670315659095)
              ·
                refine ⟨1838574156473505473488643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1225716104315670315659095 1838574156473505473488643)
                ·
                  refine ⟨2757861234710258210232965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1838574156473505473488643 2757861234710258210232965)
                  ·
                    refine ⟨517098981508173414418681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2757861234710258210232965 517098981508173414418681)
                    ·
                      rfl

theorem cell22_1510570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_1510570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510570 prefixEnd_1510570 := by exact prefixLift 1510570
  have htrace : WordTrace (prefixWord ++ tailWord_1510570) baseStart_1510570 baseEnd_1510570 := by
    simpa [prefixWord, tailWord_1510570, baseEnd_1510570] using wordTrace_append hprefix tailTrace_1510570
  have hstable : (prefixWord ++ tailWord_1510570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510570).length < 2 ^ (prefixWord ++ tailWord_1510570).sum := by decide
  have hdescent : baseEnd_1510570 < baseStart_1510570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510628 : List Nat := [2, 3, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_1510628 : Nat := 118140960795 + 1510628 * 2 ^ 59
def prefixEnd_1510628 : Nat := 4983230072969 + 3 ^ 40 * 1510628 * 2
def baseEnd_1510628 : Nat := 517118836093480596468503

theorem tailTrace_1510628 : CollatzResearch.WordTrace tailWord_1510628 prefixEnd_1510628 517118836093480596468503 := by
  unfold tailWord_1510628
  simp only [CollatzResearch.WordTrace]
  refine ⟨27548564785630112783750269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36731419714173483711667025 27548564785630112783750269)
  ·
    refine ⟨10330711794611292293906351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27548564785630112783750269 10330711794611292293906351)
    ·
      refine ⟨15496067691916938440859527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10330711794611292293906351 15496067691916938440859527)
      ·
        refine ⟨23244101537875407661289291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15496067691916938440859527 23244101537875407661289291)
        ·
          refine ⟨34866152306813111491933937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23244101537875407661289291 34866152306813111491933937)
          ·
            refine ⟨26149614230109833618950453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34866152306813111491933937 26149614230109833618950453)
            ·
              refine ⟨2451526334072796901776605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26149614230109833618950453 2451526334072796901776605)
              ·
                refine ⟨919322375277298838166227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2451526334072796901776605 919322375277298838166227)
                ·
                  refine ⟨1378983562915948257249341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919322375277298838166227 1378983562915948257249341)
                  ·
                    refine ⟨517118836093480596468503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1378983562915948257249341 517118836093480596468503)
                    ·
                      rfl

theorem cell22_1510628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_1510628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510628 prefixEnd_1510628 := by exact prefixLift 1510628
  have htrace : WordTrace (prefixWord ++ tailWord_1510628) baseStart_1510628 baseEnd_1510628 := by
    simpa [prefixWord, tailWord_1510628, baseEnd_1510628] using wordTrace_append hprefix tailTrace_1510628
  have hstable : (prefixWord ++ tailWord_1510628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510628).length < 2 ^ (prefixWord ++ tailWord_1510628).sum := by decide
  have hdescent : baseEnd_1510628 < baseStart_1510628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510658 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 5]
def baseStart_1510658 : Nat := 118140960795 + 1510658 * 2 ^ 59
def prefixEnd_1510658 : Nat := 4983230072969 + 3 ^ 40 * 1510658 * 2
def baseEnd_1510658 : Nat := 172376368568856839406137

theorem tailTrace_1510658 : CollatzResearch.WordTrace tailWord_1510658 prefixEnd_1510658 172376368568856839406137 := by
  unfold tailWord_1510658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13774555940287885172773157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36732149174101027127395085 13774555940287885172773157)
  ·
    refine ⟨2582729238803978469894967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13774555940287885172773157 2582729238803978469894967)
    ·
      refine ⟨3874093858205967704842451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2582729238803978469894967 3874093858205967704842451)
      ·
        refine ⟨5811140787308951557263677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874093858205967704842451 5811140787308951557263677)
        ·
          refine ⟨2179177795240856833973879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5811140787308951557263677 2179177795240856833973879)
          ·
            refine ⟨3268766692861285250960819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2179177795240856833973879 3268766692861285250960819)
            ·
              refine ⟨4903150039291927876441229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3268766692861285250960819 4903150039291927876441229)
              ·
                refine ⟨1838681264734472953665461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4903150039291927876441229 1838681264734472953665461)
                ·
                  refine ⟨172376368568856839406137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1838681264734472953665461 172376368568856839406137)
                  ·
                    rfl

theorem cell22_1510658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 5].length) (baseStart_1510658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510658 prefixEnd_1510658 := by exact prefixLift 1510658
  have htrace : WordTrace (prefixWord ++ tailWord_1510658) baseStart_1510658 baseEnd_1510658 := by
    simpa [prefixWord, tailWord_1510658, baseEnd_1510658] using wordTrace_append hprefix tailTrace_1510658
  have hstable : (prefixWord ++ tailWord_1510658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510658).length < 2 ^ (prefixWord ++ tailWord_1510658).sum := by decide
  have hdescent : baseEnd_1510658 < baseStart_1510658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510684 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 3, 5]
def baseStart_1510684 : Nat := 118140960795 + 1510684 * 2 ^ 59
def prefixEnd_1510684 : Nat := 4983230072969 + 3 ^ 40 * 1510684 * 2
def baseEnd_1510684 : Nat := 517138006037915117068331

theorem tailTrace_1510684 : CollatzResearch.WordTrace tailWord_1510684 prefixEnd_1510684 517138006037915117068331 := by
  unfold tailWord_1510684
  simp only [CollatzResearch.WordTrace]
  refine ⟨27549586029528673565769553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36732781372704898087692737 27549586029528673565769553)
  ·
    refine ⟨20662189522146505174327165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27549586029528673565769553 20662189522146505174327165)
    ·
      refine ⟨7748321070804939440372687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20662189522146505174327165 7748321070804939440372687)
      ·
        refine ⟨11622481606207409160559031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7748321070804939440372687 11622481606207409160559031)
        ·
          refine ⟨17433722409311113740838547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11622481606207409160559031 17433722409311113740838547)
          ·
            refine ⟨26150583613966670611257821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17433722409311113740838547 26150583613966670611257821)
            ·
              refine ⟨9806468855237501479221683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26150583613966670611257821 9806468855237501479221683)
              ·
                refine ⟨14709703282856252218832525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9806468855237501479221683 14709703282856252218832525)
                ·
                  refine ⟨5516138731071094582062197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14709703282856252218832525 5516138731071094582062197)
                  ·
                    refine ⟨517138006037915117068331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5516138731071094582062197 517138006037915117068331)
                    ·
                      rfl

theorem cell22_1510684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_1510684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510684 prefixEnd_1510684 := by exact prefixLift 1510684
  have htrace : WordTrace (prefixWord ++ tailWord_1510684) baseStart_1510684 baseEnd_1510684 := by
    simpa [prefixWord, tailWord_1510684, baseEnd_1510684] using wordTrace_append hprefix tailTrace_1510684
  have hstable : (prefixWord ++ tailWord_1510684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510684).length < 2 ^ (prefixWord ++ tailWord_1510684).sum := by decide
  have hdescent : baseEnd_1510684 < baseStart_1510684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510718 : List Nat := [4, 2, 1, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1510718 : Nat := 118140960795 + 1510718 * 2 ^ 59
def prefixEnd_1510718 : Nat := 4983230072969 + 3 ^ 40 * 1510718 * 2
def baseEnd_1510718 : Nat := 517149644932750361718227

theorem tailTrace_1510718 : CollatzResearch.WordTrace tailWord_1510718 prefixEnd_1510718 517149644932750361718227 := by
  unfold tailWord_1510718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887551517616771367284601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36733608093956113958851205 6887551517616771367284601)
  ·
    refine ⟨5165663638212578525463451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6887551517616771367284601 5165663638212578525463451)
    ·
      refine ⟨7748495457318867788195177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5165663638212578525463451 7748495457318867788195177)
      ·
        refine ⟨5811371592989150841146383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7748495457318867788195177 5811371592989150841146383)
        ·
          refine ⟨8717057389483726261719575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811371592989150841146383 8717057389483726261719575)
          ·
            refine ⟨13075586084225589392579363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8717057389483726261719575 13075586084225589392579363)
            ·
              refine ⟨19613379126338384088869045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13075586084225589392579363 19613379126338384088869045)
              ·
                refine ⟨1838754293094223508331473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19613379126338384088869045 1838754293094223508331473)
                ·
                  refine ⟨1379065719820667631248605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1838754293094223508331473 1379065719820667631248605)
                  ·
                    refine ⟨517149644932750361718227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1379065719820667631248605 517149644932750361718227)
                    ·
                      rfl

theorem cell22_1510718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1510718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510718 prefixEnd_1510718 := by exact prefixLift 1510718
  have htrace : WordTrace (prefixWord ++ tailWord_1510718) baseStart_1510718 baseEnd_1510718 := by
    simpa [prefixWord, tailWord_1510718, baseEnd_1510718] using wordTrace_append hprefix tailTrace_1510718
  have hstable : (prefixWord ++ tailWord_1510718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510718).length < 2 ^ (prefixWord ++ tailWord_1510718).sum := by decide
  have hdescent : baseEnd_1510718 < baseStart_1510718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510782 : List Nat := [4, 2, 3, 2, 1, 2, 2, 6]
def baseStart_1510782 : Nat := 118140960795 + 1510782 * 2 ^ 59
def prefixEnd_1510782 : Nat := 4983230072969 + 3 ^ 40 * 1510782 * 2
def baseEnd_1510782 : Nat := 57463505937852836457559

theorem tailTrace_1510782 : CollatzResearch.WordTrace tailWord_1510782 prefixEnd_1510782 57463505937852836457559 := by
  unfold tailWord_1510782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887843301587788733575825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36735164275134873245737733 6887843301587788733575825)
  ·
    refine ⟨5165882476190841550181869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6887843301587788733575825 5165882476190841550181869)
    ·
      refine ⟨1937205928571565581318201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5165882476190841550181869 1937205928571565581318201)
      ·
        refine ⟨1452904446428674185988651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1937205928571565581318201 1452904446428674185988651)
        ·
          refine ⟨2179356669643011278982977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1452904446428674185988651 2179356669643011278982977)
          ·
            refine ⟨1634517502232258459237233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2179356669643011278982977 1634517502232258459237233)
            ·
              refine ⟨1225888126674193844427925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1634517502232258459237233 1225888126674193844427925)
              ·
                refine ⟨57463505937852836457559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1225888126674193844427925 57463505937852836457559)
                ·
                  rfl

theorem cell22_1510782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_1510782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510782 prefixEnd_1510782 := by exact prefixLift 1510782
  have htrace : WordTrace (prefixWord ++ tailWord_1510782) baseStart_1510782 baseEnd_1510782 := by
    simpa [prefixWord, tailWord_1510782, baseEnd_1510782] using wordTrace_append hprefix tailTrace_1510782
  have hstable : (prefixWord ++ tailWord_1510782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510782).length < 2 ^ (prefixWord ++ tailWord_1510782).sum := by decide
  have hdescent : baseEnd_1510782 < baseStart_1510782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510814 : List Nat := [4, 3, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_1510814 : Nat := 118140960795 + 1510814 * 2 ^ 59
def prefixEnd_1510814 : Nat := 4983230072969 + 3 ^ 40 * 1510814 * 2
def baseEnd_1510814 : Nat := 517182507694638111317933

theorem tailTrace_1510814 : CollatzResearch.WordTrace tailWord_1510814 prefixEnd_1510814 517182507694638111317933 := by
  unfold tailWord_1510814
  simp only [CollatzResearch.WordTrace]
  refine ⟨6887989193573297416721437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36735942365724252889180997 6887989193573297416721437)
  ·
    refine ⟨2582995947589986531270539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6887989193573297416721437 2582995947589986531270539)
    ·
      refine ⟨3874493921384979796905809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2582995947589986531270539 3874493921384979796905809)
      ·
        refine ⟨2905870441038734847679357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3874493921384979796905809 2905870441038734847679357)
        ·
          refine ⟨1089701415389525567879759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2905870441038734847679357 1089701415389525567879759)
          ·
            refine ⟨1634552123084288351819639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1089701415389525567879759 1634552123084288351819639)
            ·
              refine ⟨2451828184626432527729459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634552123084288351819639 2451828184626432527729459)
              ·
                refine ⟨3677742276939648791594189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2451828184626432527729459 3677742276939648791594189)
                ·
                  refine ⟨1379153353852368296847821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3677742276939648791594189 1379153353852368296847821)
                  ·
                    refine ⟨517182507694638111317933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1379153353852368296847821 517182507694638111317933)
                    ·
                      rfl

theorem cell22_1510814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_1510814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510814 prefixEnd_1510814 := by exact prefixLift 1510814
  have htrace : WordTrace (prefixWord ++ tailWord_1510814) baseStart_1510814 baseEnd_1510814 := by
    simpa [prefixWord, tailWord_1510814, baseEnd_1510814] using wordTrace_append hprefix tailTrace_1510814
  have hstable : (prefixWord ++ tailWord_1510814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510814).length < 2 ^ (prefixWord ++ tailWord_1510814).sum := by decide
  have hdescent : baseEnd_1510814 < baseStart_1510814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510851 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 2, 4]
def baseStart_1510851 : Nat := 118140960795 + 1510851 * 2 ^ 59
def prefixEnd_1510851 : Nat := 4983230072969 + 3 ^ 40 * 1510851 * 2
def baseEnd_1510851 : Nat := 517195173550782348142819

theorem tailTrace_1510851 : CollatzResearch.WordTrace tailWord_1510851 prefixEnd_1510851 517195173550782348142819 := by
  unfold tailWord_1510851
  simp only [CollatzResearch.WordTrace]
  refine ⟨55105263049452334652868407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36736842032968223101912271 55105263049452334652868407)
  ·
    refine ⟨82657894574178501979302611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55105263049452334652868407 82657894574178501979302611)
    ·
      refine ⟨123986841861267752968953917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82657894574178501979302611 123986841861267752968953917)
      ·
        refine ⟨46495065697975407363357719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123986841861267752968953917 46495065697975407363357719)
        ·
          refine ⟨69742598546963111045036579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46495065697975407363357719 69742598546963111045036579)
          ·
            refine ⟨104613897820444666567554869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69742598546963111045036579 104613897820444666567554869)
            ·
              refine ⟨9807552920666687490708269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104613897820444666567554869 9807552920666687490708269)
              ·
                refine ⟨3677832345250007809015601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9807552920666687490708269 3677832345250007809015601)
                ·
                  refine ⟨2758374258937505856761701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3677832345250007809015601 2758374258937505856761701)
                  ·
                    refine ⟨517195173550782348142819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2758374258937505856761701 517195173550782348142819)
                    ·
                      rfl

theorem cell22_1510851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 2, 4].length) (baseStart_1510851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510851 prefixEnd_1510851 := by exact prefixLift 1510851
  have htrace : WordTrace (prefixWord ++ tailWord_1510851) baseStart_1510851 baseEnd_1510851 := by
    simpa [prefixWord, tailWord_1510851, baseEnd_1510851] using wordTrace_append hprefix tailTrace_1510851
  have hstable : (prefixWord ++ tailWord_1510851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510851).length < 2 ^ (prefixWord ++ tailWord_1510851).sum := by decide
  have hdescent : baseEnd_1510851 < baseStart_1510851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510883 : List Nat := [1, 1, 1, 6, 2, 3, 1, 7]
def baseStart_1510883 : Nat := 118140960795 + 1510883 * 2 ^ 59
def prefixEnd_1510883 : Nat := 4983230072969 + 3 ^ 40 * 1510883 * 2
def baseEnd_1510883 : Nat := 57467347533860547926969

theorem tailTrace_1510883 : CollatzResearch.WordTrace tailWord_1510883 prefixEnd_1510883 57467347533860547926969 := by
  unfold tailWord_1510883
  simp only [CollatzResearch.WordTrace]
  refine ⟨55106430185336404118033303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36737620123557602745355535 55106430185336404118033303)
  ·
    refine ⟨82659645278004606177049955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55106430185336404118033303 82659645278004606177049955)
    ·
      refine ⟨123989467917006909265574933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82659645278004606177049955 123989467917006909265574933)
      ·
        refine ⟨5812006308609698871823825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 123989467917006909265574933 5812006308609698871823825)
        ·
          refine ⟨4359004731457274153867869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5812006308609698871823825 4359004731457274153867869)
          ·
            refine ⟨1634626774296477807700451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4359004731457274153867869 1634626774296477807700451)
            ·
              refine ⟨2451940161444716711550677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634626774296477807700451 2451940161444716711550677)
              ·
                refine ⟨57467347533860547926969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2451940161444716711550677 57467347533860547926969)
                ·
                  rfl

theorem cell22_1510883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 7].length) (baseStart_1510883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510883 prefixEnd_1510883 := by exact prefixLift 1510883
  have htrace : WordTrace (prefixWord ++ tailWord_1510883) baseStart_1510883 baseEnd_1510883 := by
    simpa [prefixWord, tailWord_1510883, baseEnd_1510883] using wordTrace_append hprefix tailTrace_1510883
  have hstable : (prefixWord ++ tailWord_1510883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510883).length < 2 ^ (prefixWord ++ tailWord_1510883).sum := by decide
  have hdescent : baseEnd_1510883 < baseStart_1510883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510945 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 5]
def baseStart_1510945 : Nat := 118140960795 + 1510945 * 2 ^ 59
def prefixEnd_1510945 : Nat := 4983230072969 + 3 ^ 40 * 1510945 * 2
def baseEnd_1510945 : Nat := 172409117223932478764177

theorem tailTrace_1510945 : CollatzResearch.WordTrace tailWord_1510945 prefixEnd_1510945 172409117223932478764177 := by
  unfold tailWord_1510945
  simp only [CollatzResearch.WordTrace]
  refine ⟨55108691511111788706790289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36739127674074525804526859 55108691511111788706790289)
  ·
    refine ⟨41331518633333841530092717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55108691511111788706790289 41331518633333841530092717)
    ·
      refine ⟨15499319487500190573784769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41331518633333841530092717 15499319487500190573784769)
      ·
        refine ⟨11624489615625142930338577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15499319487500190573784769 11624489615625142930338577)
        ·
          refine ⟨8718367211718857197753933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11624489615625142930338577 8718367211718857197753933)
          ·
            refine ⟨3269387704394571449157725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8718367211718857197753933 3269387704394571449157725)
            ·
              refine ⟨1226020389147964293434147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3269387704394571449157725 1226020389147964293434147)
              ·
                refine ⟨1839030583721946440151221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226020389147964293434147 1839030583721946440151221)
                ·
                  refine ⟨172409117223932478764177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1839030583721946440151221 172409117223932478764177)
                  ·
                    rfl

theorem cell22_1510945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 5].length) (baseStart_1510945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510945 prefixEnd_1510945 := by exact prefixLift 1510945
  have htrace : WordTrace (prefixWord ++ tailWord_1510945) baseStart_1510945 baseEnd_1510945 := by
    simpa [prefixWord, tailWord_1510945, baseEnd_1510945] using wordTrace_append hprefix tailTrace_1510945
  have hstable : (prefixWord ++ tailWord_1510945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510945).length < 2 ^ (prefixWord ++ tailWord_1510945).sum := by decide
  have hdescent : baseEnd_1510945 < baseStart_1510945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1510966 : List Nat := [5, 1, 2, 1, 3, 2, 1, 3, 1, 3]
def baseStart_1510966 : Nat := 118140960795 + 1510966 * 2 ^ 59
def prefixEnd_1510966 : Nat := 4983230072969 + 3 ^ 40 * 1510966 * 2
def baseEnd_1510966 : Nat := 517234540400960381517467

theorem tailTrace_1510966 : CollatzResearch.WordTrace tailWord_1510966 prefixEnd_1510966 517234540400960381517467 := by
  unfold tailWord_1510966
  simp only [CollatzResearch.WordTrace]
  refine ⟨3444341090252231830831547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36739638296023806195536501 3444341090252231830831547)
  ·
    refine ⟨5166511635378347746247321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3444341090252231830831547 5166511635378347746247321)
    ·
      refine ⟨3874883726533760809685491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5166511635378347746247321 3874883726533760809685491)
      ·
        refine ⟨5812325589800641214528237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874883726533760809685491 5812325589800641214528237)
        ·
          refine ⟨2179622096175240455448089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5812325589800641214528237 2179622096175240455448089)
          ·
            refine ⟨1634716572131430341586067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2179622096175240455448089 1634716572131430341586067)
            ·
              refine ⟨2452074858197145512379101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1634716572131430341586067 2452074858197145512379101)
              ·
                refine ⟨919528071823929567142163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2452074858197145512379101 919528071823929567142163)
                ·
                  refine ⟨1379292107735894350713245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919528071823929567142163 1379292107735894350713245)
                  ·
                    refine ⟨517234540400960381517467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1379292107735894350713245 517234540400960381517467)
                    ·
                      rfl

theorem cell22_1510966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 1, 3].length) (baseStart_1510966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1510966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1510966 prefixEnd_1510966 := by exact prefixLift 1510966
  have htrace : WordTrace (prefixWord ++ tailWord_1510966) baseStart_1510966 baseEnd_1510966 := by
    simpa [prefixWord, tailWord_1510966, baseEnd_1510966] using wordTrace_append hprefix tailTrace_1510966
  have hstable : (prefixWord ++ tailWord_1510966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1510966).length < 2 ^ (prefixWord ++ tailWord_1510966).sum := by decide
  have hdescent : baseEnd_1510966 < baseStart_1510966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1510966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511018 : List Nat := [3, 1, 3, 2, 1, 2, 2, 8]
def baseStart_1511018 : Nat := 118140960795 + 1511018 * 2 ^ 59
def prefixEnd_1511018 : Nat := 4983230072969 + 3 ^ 40 * 1511018 * 2
def baseEnd_1511018 : Nat := 57472482340405508801923

theorem tailTrace_1511018 : CollatzResearch.WordTrace tailWord_1511018 prefixEnd_1511018 57472482340405508801923 := by
  unfold tailWord_1511018
  simp only [CollatzResearch.WordTrace]
  refine ⟨13777838509961830543549427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36740902693231548116131805 13777838509961830543549427)
  ·
    refine ⟨20666757764942745815324141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13777838509961830543549427 20666757764942745815324141)
    ·
      refine ⟨7750034161853529680746553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20666757764942745815324141 7750034161853529680746553)
      ·
        refine ⟨5812525621390147260559915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7750034161853529680746553 5812525621390147260559915)
        ·
          refine ⟨8718788432085220890839873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5812525621390147260559915 8718788432085220890839873)
          ·
            refine ⟨6539091324063915668129905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8718788432085220890839873 6539091324063915668129905)
            ·
              refine ⟨4904318493047936751097429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6539091324063915668129905 4904318493047936751097429)
              ·
                refine ⟨57472482340405508801923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4904318493047936751097429 57472482340405508801923)
                ·
                  rfl

theorem cell22_1511018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 8].length) (baseStart_1511018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511018 prefixEnd_1511018 := by exact prefixLift 1511018
  have htrace : WordTrace (prefixWord ++ tailWord_1511018) baseStart_1511018 baseEnd_1511018 := by
    simpa [prefixWord, tailWord_1511018, baseEnd_1511018] using wordTrace_append hprefix tailTrace_1511018
  have hstable : (prefixWord ++ tailWord_1511018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511018).length < 2 ^ (prefixWord ++ tailWord_1511018).sum := by decide
  have hdescent : baseEnd_1511018 < baseStart_1511018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511140 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 6, 3]
def baseStart_1511140 : Nat := 118140960795 + 1511140 * 2 ^ 59
def prefixEnd_1511140 : Nat := 4983230072969 + 3 ^ 40 * 1511140 * 2
def baseEnd_1511140 : Nat := 517294104156881927666933

theorem tailTrace_1511140 : CollatzResearch.WordTrace tailWord_1511140 prefixEnd_1511140 517294104156881927666933 := by
  unfold tailWord_1511140
  simp only [CollatzResearch.WordTrace]
  refine ⟨27557901872702668505069437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36743869163603558006759249 27557901872702668505069437)
  ·
    refine ⟨10334213202263500689401039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27557901872702668505069437 10334213202263500689401039)
    ·
      refine ⟨15501319803395251034101559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10334213202263500689401039 15501319803395251034101559)
      ·
        refine ⟨23251979705092876551152339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15501319803395251034101559 23251979705092876551152339)
        ·
          refine ⟨34877969557639314826728509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23251979705092876551152339 34877969557639314826728509)
          ·
            refine ⟨13079238584114743060023191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34877969557639314826728509 13079238584114743060023191)
            ·
              refine ⟨19618857876172114590034787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13079238584114743060023191 19618857876172114590034787)
              ·
                refine ⟨29428286814258171885052181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19618857876172114590034787 29428286814258171885052181)
                ·
                  refine ⟨1379450944418351807111821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 29428286814258171885052181 1379450944418351807111821)
                  ·
                    refine ⟨517294104156881927666933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1379450944418351807111821 517294104156881927666933)
                    ·
                      rfl

theorem cell22_1511140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 6, 3].length) (baseStart_1511140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511140 prefixEnd_1511140 := by exact prefixLift 1511140
  have htrace : WordTrace (prefixWord ++ tailWord_1511140) baseStart_1511140 baseEnd_1511140 := by
    simpa [prefixWord, tailWord_1511140, baseEnd_1511140] using wordTrace_append hprefix tailTrace_1511140
  have hstable : (prefixWord ++ tailWord_1511140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511140).length < 2 ^ (prefixWord ++ tailWord_1511140).sum := by decide
  have hdescent : baseEnd_1511140 < baseStart_1511140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511153 : List Nat := [1, 2, 2, 2, 2, 3, 10]
def baseStart_1511153 : Nat := 118140960795 + 1511153 * 2 ^ 59
def prefixEnd_1511153 : Nat := 4983230072969 + 3 ^ 40 * 1511153 * 2
def baseEnd_1511153 : Nat := 19159205715650156558959

theorem tailTrace_1511153 : CollatzResearch.WordTrace tailWord_1511153 prefixEnd_1511153 19159205715650156558959 := by
  unfold tailWord_1511153
  simp only [CollatzResearch.WordTrace]
  refine ⟨55116277894358240230362113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36744185262905493486908075 55116277894358240230362113)
  ·
    refine ⟨41337208420768680172771585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55116277894358240230362113 41337208420768680172771585)
    ·
      refine ⟨31002906315576510129578689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41337208420768680172771585 31002906315576510129578689)
      ·
        refine ⟨23252179736682382597184017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31002906315576510129578689 23252179736682382597184017)
        ·
          refine ⟨17439134802511786947888013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23252179736682382597184017 17439134802511786947888013)
          ·
            refine ⟨6539675550941920105458005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17439134802511786947888013 6539675550941920105458005)
            ·
              refine ⟨19159205715650156558959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6539675550941920105458005 19159205715650156558959)
              ·
                rfl

theorem cell22_1511153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 10].length) (baseStart_1511153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511153 prefixEnd_1511153 := by exact prefixLift 1511153
  have htrace : WordTrace (prefixWord ++ tailWord_1511153) baseStart_1511153 baseEnd_1511153 := by
    simpa [prefixWord, tailWord_1511153, baseEnd_1511153] using wordTrace_append hprefix tailTrace_1511153
  have hstable : (prefixWord ++ tailWord_1511153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511153).length < 2 ^ (prefixWord ++ tailWord_1511153).sum := by decide
  have hdescent : baseEnd_1511153 < baseStart_1511153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511183 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 4, 6]
def baseStart_1511183 : Nat := 118140960795 + 1511183 * 2 ^ 59
def prefixEnd_1511183 : Nat := 4983230072969 + 3 ^ 40 * 1511183 * 2
def baseEnd_1511183 : Nat := 517308823935644148841801

theorem tailTrace_1511183 : CollatzResearch.WordTrace tailWord_1511183 prefixEnd_1511183 517308823935644148841801 := by
  unfold tailWord_1511183
  simp only [CollatzResearch.WordTrace]
  refine ⟨55117372084249555353954203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36744914722833036902636135 55117372084249555353954203)
  ·
    refine ⟨82676058126374333030931305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55117372084249555353954203 82676058126374333030931305)
    ·
      refine ⟨62007043594780749773198479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82676058126374333030931305 62007043594780749773198479)
      ·
        refine ⟨93010565392171124659797719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62007043594780749773198479 93010565392171124659797719)
        ·
          refine ⟨139515848088256686989696579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93010565392171124659797719 139515848088256686989696579)
          ·
            refine ⟨209273772132385030484544869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139515848088256686989696579 209273772132385030484544869)
            ·
              refine ⟨39238832274822193215852163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209273772132385030484544869 39238832274822193215852163)
              ·
                refine ⟨58858248412233289823778245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39238832274822193215852163 58858248412233289823778245)
                ·
                  refine ⟨11035921577293741841958421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58858248412233289823778245 11035921577293741841958421)
                  ·
                    refine ⟨517308823935644148841801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11035921577293741841958421 517308823935644148841801)
                    ·
                      rfl

theorem cell22_1511183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 6].length) (baseStart_1511183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511183 prefixEnd_1511183 := by exact prefixLift 1511183
  have htrace : WordTrace (prefixWord ++ tailWord_1511183) baseStart_1511183 baseEnd_1511183 := by
    simpa [prefixWord, tailWord_1511183, baseEnd_1511183] using wordTrace_append hprefix tailTrace_1511183
  have hstable : (prefixWord ++ tailWord_1511183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511183).length < 2 ^ (prefixWord ++ tailWord_1511183).sum := by decide
  have hdescent : baseEnd_1511183 < baseStart_1511183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511185 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 5, 3]
def baseStart_1511185 : Nat := 118140960795 + 1511185 * 2 ^ 59
def prefixEnd_1511185 : Nat := 4983230072969 + 3 ^ 40 * 1511185 * 2
def baseEnd_1511185 : Nat := 517309508576516810291795

theorem tailTrace_1511185 : CollatzResearch.WordTrace tailWord_1511185 prefixEnd_1511185 517309508576516810291795 := by
  unfold tailWord_1511185
  simp only [CollatzResearch.WordTrace]
  refine ⟨55117445030242309695527009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36744963353494873130351339 55117445030242309695527009)
  ·
    refine ⟨41338083772681732271645257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55117445030242309695527009 41338083772681732271645257)
    ·
      refine ⟨31003562829511299203733943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41338083772681732271645257 31003562829511299203733943)
      ·
        refine ⟨46505344244266948805600915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31003562829511299203733943 46505344244266948805600915)
        ·
          refine ⟨69758016366400423208401373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46505344244266948805600915 69758016366400423208401373)
          ·
            refine ⟨26159256137400158703150515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69758016366400423208401373 26159256137400158703150515)
            ·
              refine ⟨39238884206100238054725773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26159256137400158703150515 39238884206100238054725773)
              ·
                refine ⟨14714581577287589270522165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39238884206100238054725773 14714581577287589270522165)
                ·
                  refine ⟨1379492022870711494111453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14714581577287589270522165 1379492022870711494111453)
                  ·
                    refine ⟨517309508576516810291795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1379492022870711494111453 517309508576516810291795)
                    ·
                      rfl

theorem cell22_1511185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 5, 3].length) (baseStart_1511185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511185 prefixEnd_1511185 := by exact prefixLift 1511185
  have htrace : WordTrace (prefixWord ++ tailWord_1511185) baseStart_1511185 baseEnd_1511185 := by
    simpa [prefixWord, tailWord_1511185, baseEnd_1511185] using wordTrace_append hprefix tailTrace_1511185
  have hstable : (prefixWord ++ tailWord_1511185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511185).length < 2 ^ (prefixWord ++ tailWord_1511185).sum := by decide
  have hdescent : baseEnd_1511185 < baseStart_1511185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511290 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_1511290 : Nat := 118140960795 + 1511290 * 2 ^ 59
def prefixEnd_1511290 : Nat := 4983230072969 + 3 ^ 40 * 1511290 * 2
def baseEnd_1511290 : Nat := 517345452222331536416473

theorem tailTrace_1511290 : CollatzResearch.WordTrace tailWord_1511290 prefixEnd_1511290 517345452222331536416473 := by
  unfold tailWord_1511290
  simp only [CollatzResearch.WordTrace]
  refine ⟨13780318673715478157024831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36747516463241275085399549 13780318673715478157024831)
  ·
    refine ⟨20670478010573217235537247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13780318673715478157024831 20670478010573217235537247)
    ·
      refine ⟨31005717015859825853305871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20670478010573217235537247 31005717015859825853305871)
      ·
        refine ⟨46508575523789738779958807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31005717015859825853305871 46508575523789738779958807)
        ·
          refine ⟨69762863285684608169938211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46508575523789738779958807 69762863285684608169938211)
          ·
            refine ⟨104644294928526912254907317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69762863285684608169938211 104644294928526912254907317)
            ·
              refine ⟨9810402649549398023897561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104644294928526912254907317 9810402649549398023897561)
              ·
                refine ⟨7357801987162048517923171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9810402649549398023897561 7357801987162048517923171)
                ·
                  refine ⟨11036702980743072776884757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7357801987162048517923171 11036702980743072776884757)
                  ·
                    refine ⟨517345452222331536416473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11036702980743072776884757 517345452222331536416473)
                    ·
                      rfl

theorem cell22_1511290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_1511290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511290 prefixEnd_1511290 := by exact prefixLift 1511290
  have htrace : WordTrace (prefixWord ++ tailWord_1511290) baseStart_1511290 baseEnd_1511290 := by
    simpa [prefixWord, tailWord_1511290, baseEnd_1511290] using wordTrace_append hprefix tailTrace_1511290
  have hstable : (prefixWord ++ tailWord_1511290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511290).length < 2 ^ (prefixWord ++ tailWord_1511290).sum := by decide
  have hdescent : baseEnd_1511290 < baseStart_1511290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511294 : List Nat := [4, 2, 3, 1, 1, 1, 2, 2, 6]
def baseStart_1511294 : Nat := 118140960795 + 1511294 * 2 ^ 59
def prefixEnd_1511294 : Nat := 4983230072969 + 3 ^ 40 * 1511294 * 2
def baseEnd_1511294 : Nat := 172448940501358953105487

theorem tailTrace_1511294 : CollatzResearch.WordTrace tailWord_1511294 prefixEnd_1511294 172448940501358953105487 := by
  unfold tailWord_1511294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6890177573355927663905617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36747613724564947540829957 6890177573355927663905617)
  ·
    refine ⟨5167633180016945747929213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6890177573355927663905617 5167633180016945747929213)
    ·
      refine ⟨1937862442506354655473455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5167633180016945747929213 1937862442506354655473455)
      ·
        refine ⟨2906793663759531983210183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1937862442506354655473455 2906793663759531983210183)
        ·
          refine ⟨4360190495639297974815275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2906793663759531983210183 4360190495639297974815275)
          ·
            refine ⟨6540285743458946962222913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4360190495639297974815275 6540285743458946962222913)
            ·
              refine ⟨4905214307594210221667185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6540285743458946962222913 4905214307594210221667185)
              ·
                refine ⟨3678910730695657666250389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4905214307594210221667185 3678910730695657666250389)
                ·
                  refine ⟨172448940501358953105487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3678910730695657666250389 172448940501358953105487)
                  ·
                    rfl

theorem cell22_1511294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 2, 6].length) (baseStart_1511294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511294 prefixEnd_1511294 := by exact prefixLift 1511294
  have htrace : WordTrace (prefixWord ++ tailWord_1511294) baseStart_1511294 baseEnd_1511294 := by
    simpa [prefixWord, tailWord_1511294, baseEnd_1511294] using wordTrace_append hprefix tailTrace_1511294
  have hstable : (prefixWord ++ tailWord_1511294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511294).length < 2 ^ (prefixWord ++ tailWord_1511294).sum := by decide
  have hdescent : baseEnd_1511294 < baseStart_1511294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511305 : List Nat := [1, 2, 1, 1, 5, 1, 3, 8]
def baseStart_1511305 : Nat := 118140960795 + 1511305 * 2 ^ 59
def prefixEnd_1511305 : Nat := 4983230072969 + 3 ^ 40 * 1511305 * 2
def baseEnd_1511305 : Nat := 57483398558764055254603

theorem tailTrace_1511305 : CollatzResearch.WordTrace tailWord_1511305 prefixEnd_1511305 57483398558764055254603 := by
  unfold tailWord_1511305
  simp only [CollatzResearch.WordTrace]
  refine ⟨55121821789807570189895369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36747881193205046793263579 55121821789807570189895369)
  ·
    refine ⟨41341366342355677642421527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55121821789807570189895369 41341366342355677642421527)
    ·
      refine ⟨62012049513533516463632291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41341366342355677642421527 62012049513533516463632291)
      ·
        refine ⟨93018074270300274695448437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62012049513533516463632291 93018074270300274695448437)
        ·
          refine ⟨8720444462840650752698291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93018074270300274695448437 8720444462840650752698291)
          ·
            refine ⟨13080666694260976129047437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8720444462840650752698291 13080666694260976129047437)
            ·
              refine ⟨4905250010347866048392789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13080666694260976129047437 4905250010347866048392789)
              ·
                refine ⟨57483398558764055254603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4905250010347866048392789 57483398558764055254603)
                ·
                  rfl

theorem cell22_1511305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 8].length) (baseStart_1511305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511305 prefixEnd_1511305 := by exact prefixLift 1511305
  have htrace : WordTrace (prefixWord ++ tailWord_1511305) baseStart_1511305 baseEnd_1511305 := by
    simpa [prefixWord, tailWord_1511305, baseEnd_1511305] using wordTrace_append hprefix tailTrace_1511305
  have hstable : (prefixWord ++ tailWord_1511305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511305).length < 2 ^ (prefixWord ++ tailWord_1511305).sum := by decide
  have hdescent : baseEnd_1511305 < baseStart_1511305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511322 : List Nat := [3, 1, 1, 4, 2, 3, 8]
def baseStart_1511322 : Nat := 118140960795 + 1511322 * 2 ^ 59
def prefixEnd_1511322 : Nat := 4983230072969 + 3 ^ 40 * 1511322 * 2
def baseEnd_1511322 : Nat := 19161348388010893319125

theorem tailTrace_1511322 : CollatzResearch.WordTrace tailWord_1511322 prefixEnd_1511322 19161348388010893319125 := by
  unfold tailWord_1511322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13780610457686495523316055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36748294553830654728842813 13780610457686495523316055)
  ·
    refine ⟨20670915686529743284974083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13780610457686495523316055 20670915686529743284974083)
    ·
      refine ⟨31006373529794614927461125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20670915686529743284974083 31006373529794614927461125)
      ·
        refine ⟨5813695036836490298898961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31006373529794614927461125 5813695036836490298898961)
        ·
          refine ⟨4360271277627367724174221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5813695036836490298898961 4360271277627367724174221)
          ·
            refine ⟨1635101729110262896565333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4360271277627367724174221 1635101729110262896565333)
            ·
              refine ⟨19161348388010893319125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1635101729110262896565333 19161348388010893319125)
              ·
                rfl

theorem cell22_1511322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 8].length) (baseStart_1511322 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511322 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511322 prefixEnd_1511322 := by exact prefixLift 1511322
  have htrace : WordTrace (prefixWord ++ tailWord_1511322) baseStart_1511322 baseEnd_1511322 := by
    simpa [prefixWord, tailWord_1511322, baseEnd_1511322] using wordTrace_append hprefix tailTrace_1511322
  have hstable : (prefixWord ++ tailWord_1511322).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511322).length < 2 ^ (prefixWord ++ tailWord_1511322).sum := by decide
  have hdescent : baseEnd_1511322 < baseStart_1511322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511324 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 2, 4]
def baseStart_1511324 : Nat := 118140960795 + 1511324 * 2 ^ 59
def prefixEnd_1511324 : Nat := 4983230072969 + 3 ^ 40 * 1511324 * 2
def baseEnd_1511324 : Nat := 517357091117166781066369

theorem tailTrace_1511324 : CollatzResearch.WordTrace tailWord_1511324 prefixEnd_1511324 517357091117166781066369 := by
  unfold tailWord_1511324
  simp only [CollatzResearch.WordTrace]
  refine ⟨27561257388369368217418513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36748343184492490956558017 27561257388369368217418513)
  ·
    refine ⟨20670943041277026163063885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27561257388369368217418513 20670943041277026163063885)
    ·
      refine ⟨7751603640478884811148957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20670943041277026163063885 7751603640478884811148957)
      ·
        refine ⟨2906851365179581804180859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7751603640478884811148957 2906851365179581804180859)
        ·
          refine ⟨4360277047769372706271289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2906851365179581804180859 4360277047769372706271289)
          ·
            refine ⟨3270207785827029529703467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4360277047769372706271289 3270207785827029529703467)
            ·
              refine ⟨4905311678740544294555201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270207785827029529703467 4905311678740544294555201)
              ·
                refine ⟨3678983759055408220916401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4905311678740544294555201 3678983759055408220916401)
                ·
                  refine ⟨2759237819291556165687301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3678983759055408220916401 2759237819291556165687301)
                  ·
                    refine ⟨517357091117166781066369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2759237819291556165687301 517357091117166781066369)
                    ·
                      rfl

theorem cell22_1511324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_1511324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511324 prefixEnd_1511324 := by exact prefixLift 1511324
  have htrace : WordTrace (prefixWord ++ tailWord_1511324) baseStart_1511324 baseEnd_1511324 := by
    simpa [prefixWord, tailWord_1511324, baseEnd_1511324] using wordTrace_append hprefix tailTrace_1511324
  have hstable : (prefixWord ++ tailWord_1511324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511324).length < 2 ^ (prefixWord ++ tailWord_1511324).sum := by decide
  have hdescent : baseEnd_1511324 < baseStart_1511324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511337 : List Nat := [1, 2, 1, 1, 1, 1, 4, 5, 3, 3]
def baseStart_1511337 : Nat := 118140960795 + 1511337 * 2 ^ 59
def prefixEnd_1511337 : Nat := 4983230072969 + 3 ^ 40 * 1511337 * 2
def baseEnd_1511337 : Nat := 517361541282839080491329

theorem tailTrace_1511337 : CollatzResearch.WordTrace tailWord_1511337 prefixEnd_1511337 517361541282839080491329 := by
  unfold tailWord_1511337
  simp only [CollatzResearch.WordTrace]
  refine ⟨55122988925691639655060265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36748659283794426436706843 55122988925691639655060265)
  ·
    refine ⟨41342241694268729741295199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55122988925691639655060265 41342241694268729741295199)
    ·
      refine ⟨62013362541403094611942799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41342241694268729741295199 62013362541403094611942799)
      ·
        refine ⟨93020043812104641917914199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62013362541403094611942799 93020043812104641917914199)
        ·
          refine ⟨139530065718156962876871299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93020043812104641917914199 139530065718156962876871299)
          ·
            refine ⟨209295098577235444315306949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139530065718156962876871299 209295098577235444315306949)
            ·
              refine ⟨39242830983231645809120053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209295098577235444315306949 39242830983231645809120053)
              ·
                refine ⟨3679015404677966794605005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39242830983231645809120053 3679015404677966794605005)
                ·
                  refine ⟨1379630776754237547976877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3679015404677966794605005 1379630776754237547976877)
                  ·
                    refine ⟨517361541282839080491329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1379630776754237547976877 517361541282839080491329)
                    ·
                      rfl

theorem cell22_1511337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 3].length) (baseStart_1511337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511337 prefixEnd_1511337 := by exact prefixLift 1511337
  have htrace : WordTrace (prefixWord ++ tailWord_1511337) baseStart_1511337 baseEnd_1511337 := by
    simpa [prefixWord, tailWord_1511337, baseEnd_1511337] using wordTrace_append hprefix tailTrace_1511337
  have hstable : (prefixWord ++ tailWord_1511337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511337).length < 2 ^ (prefixWord ++ tailWord_1511337).sum := by decide
  have hdescent : baseEnd_1511337 < baseStart_1511337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511365 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_1511365 : Nat := 118140960795 + 1511365 * 2 ^ 59
def prefixEnd_1511365 : Nat := 4983230072969 + 3 ^ 40 * 1511365 * 2
def baseEnd_1511365 : Nat := 517371126255056340791243

theorem tailTrace_1511365 : CollatzResearch.WordTrace tailWord_1511365 prefixEnd_1511365 517371126255056340791243 := by
  unfold tailWord_1511365
  simp only [CollatzResearch.WordTrace]
  refine ⟨55124010169590200437079549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36749340113060133624719699 55124010169590200437079549)
  ·
    refine ⟨20671503813596325163904831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55124010169590200437079549 20671503813596325163904831)
    ·
      refine ⟨31007255720394487745857247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20671503813596325163904831 31007255720394487745857247)
      ·
        refine ⟨46510883580591731618785871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31007255720394487745857247 46510883580591731618785871)
        ·
          refine ⟨69766325370887597428178807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46510883580591731618785871 69766325370887597428178807)
          ·
            refine ⟨104649488056331396142268211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69766325370887597428178807 104649488056331396142268211)
            ·
              refine ⟨156974232084497094213402317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104649488056331396142268211 156974232084497094213402317)
              ·
                refine ⟨58865337031686410330025869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156974232084497094213402317 58865337031686410330025869)
                ·
                  refine ⟨22074501386882403873759701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58865337031686410330025869 22074501386882403873759701)
                  ·
                    refine ⟨517371126255056340791243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 22074501386882403873759701 517371126255056340791243)
                    ·
                      rfl

theorem cell22_1511365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_1511365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511365 prefixEnd_1511365 := by exact prefixLift 1511365
  have htrace : WordTrace (prefixWord ++ tailWord_1511365) baseStart_1511365 baseEnd_1511365 := by
    simpa [prefixWord, tailWord_1511365, baseEnd_1511365] using wordTrace_append hprefix tailTrace_1511365
  have hstable : (prefixWord ++ tailWord_1511365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511365).length < 2 ^ (prefixWord ++ tailWord_1511365).sum := by decide
  have hdescent : baseEnd_1511365 < baseStart_1511365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511399 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 2, 5]
def baseStart_1511399 : Nat := 118140960795 + 1511399 * 2 ^ 59
def prefixEnd_1511399 : Nat := 4983230072969 + 3 ^ 40 * 1511399 * 2
def baseEnd_1511399 : Nat := 517382765149891585441139

theorem tailTrace_1511399 : CollatzResearch.WordTrace tailWord_1511399 prefixEnd_1511399 517382765149891585441139 := by
  unfold tailWord_1511399
  simp only [CollatzResearch.WordTrace]
  refine ⟨55125250251467024243817251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36750166834311349495878167 55125250251467024243817251)
  ·
    refine ⟨82687875377200536365725877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55125250251467024243817251 82687875377200536365725877)
    ·
      refine ⟨7751988316612550284286801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82687875377200536365725877 7751988316612550284286801)
      ·
        refine ⟨5813991237459412713215101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7751988316612550284286801 5813991237459412713215101)
        ·
          refine ⟨2180246714047279767455663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5813991237459412713215101 2180246714047279767455663)
          ·
            refine ⟨3270370071070919651183495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180246714047279767455663 3270370071070919651183495)
            ·
              refine ⟨4905555106606379476775243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270370071070919651183495 4905555106606379476775243)
              ·
                refine ⟨7358332659909569215162865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4905555106606379476775243 7358332659909569215162865)
                ·
                  refine ⟨5518749494932176911372149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7358332659909569215162865 5518749494932176911372149)
                  ·
                    refine ⟨517382765149891585441139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5518749494932176911372149 517382765149891585441139)
                    ·
                      rfl

theorem cell22_1511399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 2, 5].length) (baseStart_1511399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511399 prefixEnd_1511399 := by exact prefixLift 1511399
  have htrace : WordTrace (prefixWord ++ tailWord_1511399) baseStart_1511399 baseEnd_1511399 := by
    simpa [prefixWord, tailWord_1511399, baseEnd_1511399] using wordTrace_append hprefix tailTrace_1511399
  have hstable : (prefixWord ++ tailWord_1511399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511399).length < 2 ^ (prefixWord ++ tailWord_1511399).sum := by decide
  have hdescent : baseEnd_1511399 < baseStart_1511399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511429 : List Nat := [1, 3, 1, 1, 2, 4, 1, 5, 4]
def baseStart_1511429 : Nat := 118140960795 + 1511429 * 2 ^ 59
def prefixEnd_1511429 : Nat := 4983230072969 + 3 ^ 40 * 1511429 * 2
def baseEnd_1511429 : Nat := 172464344920993835730349

theorem tailTrace_1511429 : CollatzResearch.WordTrace tailWord_1511429 prefixEnd_1511429 172464344920993835730349 := by
  unfold tailWord_1511429
  simp only [CollatzResearch.WordTrace]
  refine ⟨55126344441358339367409341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36750896294238892911606227 55126344441358339367409341)
  ·
    refine ⟨20672379165509377262778503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55126344441358339367409341 20672379165509377262778503)
    ·
      refine ⟨31008568748264065894167755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20672379165509377262778503 31008568748264065894167755)
      ·
        refine ⟨46512853122396098841251633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31008568748264065894167755 46512853122396098841251633)
        ·
          refine ⟨34884639841797074130938725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46512853122396098841251633 34884639841797074130938725)
          ·
            refine ⟨6540869970336951399551011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34884639841797074130938725 6540869970336951399551011)
            ·
              refine ⟨9811304955505427099326517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6540869970336951399551011 9811304955505427099326517)
              ·
                refine ⟨919809839578633790561861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9811304955505427099326517 919809839578633790561861)
                ·
                  refine ⟨172464344920993835730349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 919809839578633790561861 172464344920993835730349)
                  ·
                    rfl

theorem cell22_1511429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_1511429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511429 prefixEnd_1511429 := by exact prefixLift 1511429
  have htrace : WordTrace (prefixWord ++ tailWord_1511429) baseStart_1511429 baseEnd_1511429 := by
    simpa [prefixWord, tailWord_1511429, baseEnd_1511429] using wordTrace_append hprefix tailTrace_1511429
  have hstable : (prefixWord ++ tailWord_1511429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511429).length < 2 ^ (prefixWord ++ tailWord_1511429).sum := by decide
  have hdescent : baseEnd_1511429 < baseStart_1511429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511431 : List Nat := [1, 1, 4, 3, 1, 2, 4, 1, 1, 4]
def baseStart_1511431 : Nat := 118140960795 + 1511431 * 2 ^ 59
def prefixEnd_1511431 : Nat := 4983230072969 + 3 ^ 40 * 1511431 * 2
def baseEnd_1511431 : Nat := 517393719403854168641041

theorem tailTrace_1511431 : CollatzResearch.WordTrace tailWord_1511431 prefixEnd_1511431 517393719403854168641041 := by
  unfold tailWord_1511431
  simp only [CollatzResearch.WordTrace]
  refine ⟨55126417387351093708982147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36750944924900729139321431 55126417387351093708982147)
  ·
    refine ⟨82689626081026640563473221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55126417387351093708982147 82689626081026640563473221)
    ·
      refine ⟨15504304890192495105651229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82689626081026640563473221 15504304890192495105651229)
      ·
        refine ⟨5814114333822185664619211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15504304890192495105651229 5814114333822185664619211)
        ·
          refine ⟨8721171500733278496928817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5814114333822185664619211 8721171500733278496928817)
          ·
            refine ⟨6540878625549958872696613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8721171500733278496928817 6540878625549958872696613)
            ·
              refine ⟨1226414742290617288630615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6540878625549958872696613 1226414742290617288630615)
              ·
                refine ⟨1839622113435925932945923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226414742290617288630615 1839622113435925932945923)
                ·
                  refine ⟨2759433170153888899418885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1839622113435925932945923 2759433170153888899418885)
                  ·
                    refine ⟨517393719403854168641041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2759433170153888899418885 517393719403854168641041)
                    ·
                      rfl

theorem cell22_1511431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 1, 1, 4].length) (baseStart_1511431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511431 prefixEnd_1511431 := by exact prefixLift 1511431
  have htrace : WordTrace (prefixWord ++ tailWord_1511431) baseStart_1511431 baseEnd_1511431 := by
    simpa [prefixWord, tailWord_1511431, baseEnd_1511431] using wordTrace_append hprefix tailTrace_1511431
  have hstable : (prefixWord ++ tailWord_1511431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511431).length < 2 ^ (prefixWord ++ tailWord_1511431).sum := by decide
  have hdescent : baseEnd_1511431 < baseStart_1511431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511474 : List Nat := [3, 2, 1, 1, 2, 3, 4, 6]
def baseStart_1511474 : Nat := 118140960795 + 1511474 * 2 ^ 59
def prefixEnd_1511474 : Nat := 4983230072969 + 3 ^ 40 * 1511474 * 2
def baseEnd_1511474 : Nat := 57489826575846265535101

theorem tailTrace_1511474 : CollatzResearch.WordTrace tailWord_1511474 prefixEnd_1511474 57489826575846265535101 := by
  unfold tailWord_1511474
  simp only [CollatzResearch.WordTrace]
  refine ⟨13781996431548828013199369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36751990484130208035198317 13781996431548828013199369)
  ·
    refine ⟨10336497323661621009899527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13781996431548828013199369 10336497323661621009899527)
    ·
      refine ⟨15504745985492431514849291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10336497323661621009899527 15504745985492431514849291)
      ·
        refine ⟨23257118978238647272273937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15504745985492431514849291 23257118978238647272273937)
        ·
          refine ⟨17442839233678985454205453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23257118978238647272273937 17442839233678985454205453)
          ·
            refine ⟨6541064712629619545327045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17442839233678985454205453 6541064712629619545327045)
            ·
              refine ⟨1226449633618053664748821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6541064712629619545327045 1226449633618053664748821)
              ·
                refine ⟨57489826575846265535101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1226449633618053664748821 57489826575846265535101)
                ·
                  rfl

theorem cell22_1511474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 6].length) (baseStart_1511474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511474 prefixEnd_1511474 := by exact prefixLift 1511474
  have htrace : WordTrace (prefixWord ++ tailWord_1511474) baseStart_1511474 baseEnd_1511474 := by
    simpa [prefixWord, tailWord_1511474, baseEnd_1511474] using wordTrace_append hprefix tailTrace_1511474
  have hstable : (prefixWord ++ tailWord_1511474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511474).length < 2 ^ (prefixWord ++ tailWord_1511474).sum := by decide
  have hdescent : baseEnd_1511474 < baseStart_1511474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511574 : List Nat := [5, 3, 2, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1511574 : Nat := 118140960795 + 1511574 * 2 ^ 59
def prefixEnd_1511574 : Nat := 4983230072969 + 3 ^ 40 * 1511574 * 2
def baseEnd_1511574 : Nat := 517442671226249462315603

theorem tailTrace_1511574 : CollatzResearch.WordTrace tailWord_1511574 prefixEnd_1511574 517442671226249462315603 := by
  unfold tailWord_1511574
  simp only [CollatzResearch.WordTrace]
  refine ⟨3445727064114564320714861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36754422017222019420958517 3445727064114564320714861)
  ·
    refine ⟨1292147649042961620268073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3445727064114564320714861 1292147649042961620268073)
    ·
      refine ⟨969110736782221215201055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1292147649042961620268073 969110736782221215201055)
      ·
        refine ⟨1453666105173331822801583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969110736782221215201055 1453666105173331822801583)
        ·
          refine ⟨2180499157759997734202375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453666105173331822801583 2180499157759997734202375)
          ·
            refine ⟨3270748736639996601303563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2180499157759997734202375 3270748736639996601303563)
            ·
              refine ⟨4906123104959994901955345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3270748736639996601303563 4906123104959994901955345)
              ·
                refine ⟨3679592328719996176466509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4906123104959994901955345 3679592328719996176466509)
                ·
                  refine ⟨1379847123269998566174941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3679592328719996176466509 1379847123269998566174941)
                  ·
                    refine ⟨517442671226249462315603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1379847123269998566174941 517442671226249462315603)
                    ·
                      rfl

theorem cell22_1511574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1511574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511574 prefixEnd_1511574 := by exact prefixLift 1511574
  have htrace : WordTrace (prefixWord ++ tailWord_1511574) baseStart_1511574 baseEnd_1511574 := by
    simpa [prefixWord, tailWord_1511574, baseEnd_1511574] using wordTrace_append hprefix tailTrace_1511574
  have hstable : (prefixWord ++ tailWord_1511574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511574).length < 2 ^ (prefixWord ++ tailWord_1511574).sum := by decide
  have hdescent : baseEnd_1511574 < baseStart_1511574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511604 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1511604 : Nat := 118140960795 + 1511604 * 2 ^ 59
def prefixEnd_1511604 : Nat := 4983230072969 + 3 ^ 40 * 1511604 * 2
def baseEnd_1511604 : Nat := 172484313613113128021837

theorem tailTrace_1511604 : CollatzResearch.WordTrace tailWord_1511604 prefixEnd_1511604 172484313613113128021837 := by
  unfold tailWord_1511604
  simp only [CollatzResearch.WordTrace]
  refine ⟨27566363607862172127514933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36755151477149562836686577 27566363607862172127514933)
  ·
    refine ⟨2584346588237078636954525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27566363607862172127514933 2584346588237078636954525)
    ·
      refine ⟨969129970588904488857947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2584346588237078636954525 969129970588904488857947)
      ·
        refine ⟨1453694955883356733286921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969129970588904488857947 1453694955883356733286921)
        ·
          refine ⟨1090271216912517549965191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1453694955883356733286921 1090271216912517549965191)
          ·
            refine ⟨1635406825368776324947787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1090271216912517549965191 1635406825368776324947787)
            ·
              refine ⟨2453110238053164487421681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635406825368776324947787 2453110238053164487421681)
              ·
                refine ⟨1839832678539873365566261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453110238053164487421681 1839832678539873365566261)
                ·
                  refine ⟨172484313613113128021837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1839832678539873365566261 172484313613113128021837)
                  ·
                    rfl

theorem cell22_1511604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1511604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511604 prefixEnd_1511604 := by exact prefixLift 1511604
  have htrace : WordTrace (prefixWord ++ tailWord_1511604) baseStart_1511604 baseEnd_1511604 := by
    simpa [prefixWord, tailWord_1511604, baseEnd_1511604] using wordTrace_append hprefix tailTrace_1511604
  have hstable : (prefixWord ++ tailWord_1511604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511604).length < 2 ^ (prefixWord ++ tailWord_1511604).sum := by decide
  have hdescent : baseEnd_1511604 < baseStart_1511604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511630 : List Nat := [4, 1, 1, 1, 4, 2, 3, 1, 2, 3]
def baseStart_1511630 : Nat := 118140960795 + 1511630 * 2 ^ 59
def prefixEnd_1511630 : Nat := 4983230072969 + 3 ^ 40 * 1511630 * 2
def baseEnd_1511630 : Nat := 517461841170683982915431

theorem tailTrace_1511630 : CollatzResearch.WordTrace tailWord_1511630 prefixEnd_1511630 517461841170683982915431 := by
  unfold tailWord_1511630
  simp only [CollatzResearch.WordTrace]
  refine ⟨6891709439203768836934543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36755783675753433796984229 6891709439203768836934543)
  ·
    refine ⟨10337564158805653255401815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6891709439203768836934543 10337564158805653255401815)
    ·
      refine ⟨15506346238208479883102723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10337564158805653255401815 15506346238208479883102723)
      ·
        refine ⟨23259519357312719824654085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15506346238208479883102723 23259519357312719824654085)
        ·
          refine ⟨4361159879496134967122641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23259519357312719824654085 4361159879496134967122641)
          ·
            refine ⟨3270869909622101225341981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4361159879496134967122641 3270869909622101225341981)
            ·
              refine ⟨1226576216108287959503243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3270869909622101225341981 1226576216108287959503243)
              ·
                refine ⟨1839864324162431939254865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226576216108287959503243 1839864324162431939254865)
                ·
                  refine ⟨1379898243121823954441149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1839864324162431939254865 1379898243121823954441149)
                  ·
                    refine ⟨517461841170683982915431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1379898243121823954441149 517461841170683982915431)
                    ·
                      rfl

theorem cell22_1511630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 1, 2, 3].length) (baseStart_1511630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511630 prefixEnd_1511630 := by exact prefixLift 1511630
  have htrace : WordTrace (prefixWord ++ tailWord_1511630) baseStart_1511630 baseEnd_1511630 := by
    simpa [prefixWord, tailWord_1511630, baseEnd_1511630] using wordTrace_append hprefix tailTrace_1511630
  have hstable : (prefixWord ++ tailWord_1511630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511630).length < 2 ^ (prefixWord ++ tailWord_1511630).sum := by decide
  have hdescent : baseEnd_1511630 < baseStart_1511630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511641 : List Nat := [1, 2, 1, 2, 3, 1, 4, 2, 3, 3]
def baseStart_1511641 : Nat := 118140960795 + 1511641 * 2 ^ 59
def prefixEnd_1511641 : Nat := 4983230072969 + 3 ^ 40 * 1511641 * 2
def baseEnd_1511641 : Nat := 517465606695483620890397

theorem tailTrace_1511641 : CollatzResearch.WordTrace tailWord_1511641 prefixEnd_1511641 517465606695483620890397 := by
  unfold tailWord_1511641
  simp only [CollatzResearch.WordTrace]
  refine ⟨55134076716590299574126777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36756051144393533049417851 55134076716590299574126777)
  ·
    refine ⟨41350557537442724680595083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55134076716590299574126777 41350557537442724680595083)
    ·
      refine ⟨62025836306164087020892625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41350557537442724680595083 62025836306164087020892625)
      ·
        refine ⟨46519377229623065265669469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62025836306164087020892625 46519377229623065265669469)
        ·
          refine ⟨17444766461108649474626051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46519377229623065265669469 17444766461108649474626051)
          ·
            refine ⟨26167149691662974211939077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17444766461108649474626051 26167149691662974211939077)
            ·
              refine ⟨4906340567186807664738577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26167149691662974211939077 4906340567186807664738577)
              ·
                refine ⟨3679755425390105748553933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4906340567186807664738577 3679755425390105748553933)
                ·
                  refine ⟨1379908284521289655707725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3679755425390105748553933 1379908284521289655707725)
                  ·
                    refine ⟨517465606695483620890397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1379908284521289655707725 517465606695483620890397)
                    ·
                      rfl

theorem cell22_1511641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_1511641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511641 prefixEnd_1511641 := by exact prefixLift 1511641
  have htrace : WordTrace (prefixWord ++ tailWord_1511641) baseStart_1511641 baseEnd_1511641 := by
    simpa [prefixWord, tailWord_1511641, baseEnd_1511641] using wordTrace_append hprefix tailTrace_1511641
  have hstable : (prefixWord ++ tailWord_1511641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511641).length < 2 ^ (prefixWord ++ tailWord_1511641).sum := by decide
  have hdescent : baseEnd_1511641 < baseStart_1511641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511688 : List Nat := [2, 1, 3, 2, 3, 1, 4, 1, 5]
def baseStart_1511688 : Nat := 118140960795 + 1511688 * 2 ^ 59
def prefixEnd_1511688 : Nat := 4983230072969 + 3 ^ 40 * 1511688 * 2
def baseEnd_1511688 : Nat := 172493898585330388321751

theorem tailTrace_1511688 : CollatzResearch.WordTrace tailWord_1511688 prefixEnd_1511688 172493898585330388321751 := by
  unfold tailWord_1511688
  simp only [CollatzResearch.WordTrace]
  refine ⟨27567895473710013300543859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36757193964946684400725145 27567895473710013300543859)
  ·
    refine ⟨41351843210565019950815789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27567895473710013300543859 41351843210565019950815789)
    ·
      refine ⟨15506941203961882481555921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41351843210565019950815789 15506941203961882481555921)
      ·
        refine ⟨11630205902971411861166941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15506941203961882481555921 11630205902971411861166941)
        ·
          refine ⟨4361327213614279447937603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11630205902971411861166941 4361327213614279447937603)
          ·
            refine ⟨6541990820421419171906405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4361327213614279447937603 6541990820421419171906405)
            ·
              refine ⟨1226623278829016094732451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6541990820421419171906405 1226623278829016094732451)
              ·
                refine ⟨1839934918243524142098677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1226623278829016094732451 1839934918243524142098677)
                ·
                  refine ⟨172493898585330388321751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1839934918243524142098677 172493898585330388321751)
                  ·
                    rfl

theorem cell22_1511688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 1, 5].length) (baseStart_1511688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511688 prefixEnd_1511688 := by exact prefixLift 1511688
  have htrace : WordTrace (prefixWord ++ tailWord_1511688) baseStart_1511688 baseEnd_1511688 := by
    simpa [prefixWord, tailWord_1511688, baseEnd_1511688] using wordTrace_append hprefix tailTrace_1511688
  have hstable : (prefixWord ++ tailWord_1511688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511688).length < 2 ^ (prefixWord ++ tailWord_1511688).sum := by decide
  have hdescent : baseEnd_1511688 < baseStart_1511688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511699 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 6]
def baseStart_1511699 : Nat := 118140960795 + 1511699 * 2 ^ 59
def prefixEnd_1511699 : Nat := 4983230072969 + 3 ^ 40 * 1511699 * 2
def baseEnd_1511699 : Nat := 172495153760263600980073

theorem tailTrace_1511699 : CollatzResearch.WordTrace tailWord_1511699 prefixEnd_1511699 172495153760263600980073 := by
  unfold tailWord_1511699
  simp only [CollatzResearch.WordTrace]
  refine ⟨55136192150380175479738151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36757461433586783653158767 55136192150380175479738151)
  ·
    refine ⟨82704288225570263219607227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55136192150380175479738151 82704288225570263219607227)
    ·
      refine ⟨124056432338355394829410841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82704288225570263219607227 124056432338355394829410841)
      ·
        refine ⟨93042324253766546122058131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124056432338355394829410841 93042324253766546122058131)
        ·
          refine ⟨139563486380649819183087197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93042324253766546122058131 139563486380649819183087197)
          ·
            refine ⟨52336307392743682193657699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139563486380649819183087197 52336307392743682193657699)
            ·
              refine ⟨78504461089115523290486549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52336307392743682193657699 78504461089115523290486549)
              ·
                refine ⟨3679896613552290154241557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78504461089115523290486549 3679896613552290154241557)
                ·
                  refine ⟨172495153760263600980073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3679896613552290154241557 172495153760263600980073)
                  ·
                    rfl

theorem cell22_1511699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 6].length) (baseStart_1511699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511699 prefixEnd_1511699 := by exact prefixLift 1511699
  have htrace : WordTrace (prefixWord ++ tailWord_1511699) baseStart_1511699 baseEnd_1511699 := by
    simpa [prefixWord, tailWord_1511699, baseEnd_1511699] using wordTrace_append hprefix tailTrace_1511699
  have hstable : (prefixWord ++ tailWord_1511699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511699).length < 2 ^ (prefixWord ++ tailWord_1511699).sum := by decide
  have hdescent : baseEnd_1511699 < baseStart_1511699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511726 : List Nat := [4, 1, 3, 3, 1, 2, 2, 2, 1, 3]
def baseStart_1511726 : Nat := 118140960795 + 1511726 * 2 ^ 59
def prefixEnd_1511726 : Nat := 4983230072969 + 3 ^ 40 * 1511726 * 2
def baseEnd_1511726 : Nat := 517494703932571732515137

theorem tailTrace_1511726 : CollatzResearch.WordTrace tailWord_1511726 prefixEnd_1511726 517494703932571732515137 := by
  unfold tailWord_1511726
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892147115160294886371379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36758117947521572727314021 6892147115160294886371379)
  ·
    refine ⟨10338220672740442329557069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6892147115160294886371379 10338220672740442329557069)
    ·
      refine ⟨3876832752277665873583901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10338220672740442329557069 3876832752277665873583901)
      ·
        refine ⟨1453812282104124702593963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3876832752277665873583901 1453812282104124702593963)
        ·
          refine ⟨2180718423156187053890945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1453812282104124702593963 2180718423156187053890945)
          ·
            refine ⟨1635538817367140290418209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2180718423156187053890945 1635538817367140290418209)
            ·
              refine ⟨1226654113025355217813657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635538817367140290418209 1226654113025355217813657)
              ·
                refine ⟨919990584769016413360243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1226654113025355217813657 919990584769016413360243)
                ·
                  refine ⟨1379985877153524620040365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 919990584769016413360243 1379985877153524620040365)
                  ·
                    refine ⟨517494703932571732515137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1379985877153524620040365 517494703932571732515137)
                    ·
                      rfl

theorem cell22_1511726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_1511726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511726 prefixEnd_1511726 := by exact prefixLift 1511726
  have htrace : WordTrace (prefixWord ++ tailWord_1511726) baseStart_1511726 baseEnd_1511726 := by
    simpa [prefixWord, tailWord_1511726, baseEnd_1511726] using wordTrace_append hprefix tailTrace_1511726
  have hstable : (prefixWord ++ tailWord_1511726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511726).length < 2 ^ (prefixWord ++ tailWord_1511726).sum := by decide
  have hdescent : baseEnd_1511726 < baseStart_1511726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511733 : List Nat := [1, 3, 3, 1, 2, 1, 3, 4, 4]
def baseStart_1511733 : Nat := 118140960795 + 1511733 * 2 ^ 59
def prefixEnd_1511733 : Nat := 4983230072969 + 3 ^ 40 * 1511733 * 2
def baseEnd_1511733 : Nat := 172499033391875349196705

theorem tailTrace_1511733 : CollatzResearch.WordTrace tailWord_1511733 prefixEnd_1511733 172499033391875349196705 := by
  unfold tailWord_1511733
  simp only [CollatzResearch.WordTrace]
  refine ⟨55137432232256999286475853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36758288154837999524317235 55137432232256999286475853)
  ·
    refine ⟨20676537087096374732428445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55137432232256999286475853 20676537087096374732428445)
    ·
      refine ⟨7753701407661140524660667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20676537087096374732428445 7753701407661140524660667)
      ·
        refine ⟨11630552111491710786991001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7753701407661140524660667 11630552111491710786991001)
        ·
          refine ⟨8722914083618783090243251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11630552111491710786991001 8722914083618783090243251)
          ·
            refine ⟨13084371125428174635364877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8722914083618783090243251 13084371125428174635364877)
            ·
              refine ⟨4906639172035565488261829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13084371125428174635364877 4906639172035565488261829)
              ·
                refine ⟨919994844756668529049093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4906639172035565488261829 919994844756668529049093)
                ·
                  refine ⟨172499033391875349196705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 919994844756668529049093 172499033391875349196705)
                  ·
                    rfl

theorem cell22_1511733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_1511733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511733 prefixEnd_1511733 := by exact prefixLift 1511733
  have htrace : WordTrace (prefixWord ++ tailWord_1511733) baseStart_1511733 baseEnd_1511733 := by
    simpa [prefixWord, tailWord_1511733, baseEnd_1511733] using wordTrace_append hprefix tailTrace_1511733
  have hstable : (prefixWord ++ tailWord_1511733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511733).length < 2 ^ (prefixWord ++ tailWord_1511733).sum := by decide
  have hdescent : baseEnd_1511733 < baseStart_1511733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511744 : List Nat := [2, 1, 1, 2, 2, 1, 2, 11]
def baseStart_1511744 : Nat := 118140960795 + 1511744 * 2 ^ 59
def prefixEnd_1511744 : Nat := 4983230072969 + 3 ^ 40 * 1511744 * 2
def baseEnd_1511744 : Nat := 57500096188936187285009

theorem tailTrace_1511744 : CollatzResearch.WordTrace tailWord_1511744 prefixEnd_1511744 57500096188936187285009 := by
  unfold tailWord_1511744
  simp only [CollatzResearch.WordTrace]
  refine ⟨27568916717608574082563143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36758555623478098776750857 27568916717608574082563143)
  ·
    refine ⟨41353375076412861123844715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27568916717608574082563143 41353375076412861123844715)
    ·
      refine ⟨62030062614619291685767073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41353375076412861123844715 62030062614619291685767073)
      ·
        refine ⟨46522546960964468764325305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62030062614619291685767073 46522546960964468764325305)
        ·
          refine ⟨34891910220723351573243979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46522546960964468764325305 34891910220723351573243979)
          ·
            refine ⟨52337865331085027359865969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34891910220723351573243979 52337865331085027359865969)
            ·
              refine ⟨39253398998313770519899477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52337865331085027359865969 39253398998313770519899477)
              ·
                refine ⟨57500096188936187285009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 39253398998313770519899477 57500096188936187285009)
                ·
                  rfl

theorem cell22_1511744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 11].length) (baseStart_1511744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511744 prefixEnd_1511744 := by exact prefixLift 1511744
  have htrace : WordTrace (prefixWord ++ tailWord_1511744) baseStart_1511744 baseEnd_1511744 := by
    simpa [prefixWord, tailWord_1511744, baseEnd_1511744] using wordTrace_append hprefix tailTrace_1511744
  have hstable : (prefixWord ++ tailWord_1511744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511744).length < 2 ^ (prefixWord ++ tailWord_1511744).sum := by decide
  have hdescent : baseEnd_1511744 < baseStart_1511744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511759 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 1, 9]
def baseStart_1511759 : Nat := 118140960795 + 1511759 * 2 ^ 59
def prefixEnd_1511759 : Nat := 4983230072969 + 3 ^ 40 * 1511759 * 2
def baseEnd_1511759 : Nat := 517506000506970646440035

theorem tailTrace_1511759 : CollatzResearch.WordTrace tailWord_1511759 prefixEnd_1511759 517506000506970646440035 := by
  unfold tailWord_1511759
  simp only [CollatzResearch.WordTrace]
  refine ⟨55138380530162805726922331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36758920353441870484614887 55138380530162805726922331)
  ·
    refine ⟨82707570795244208590383497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55138380530162805726922331 82707570795244208590383497)
    ·
      refine ⟨62030678096433156442787623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82707570795244208590383497 62030678096433156442787623)
      ·
        refine ⟨93046017144649734664181435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62030678096433156442787623 93046017144649734664181435)
        ·
          refine ⟨139569025716974601996272153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93046017144649734664181435 139569025716974601996272153)
          ·
            refine ⟨104676769287730951497204115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139569025716974601996272153 104676769287730951497204115)
            ·
              refine ⟨157015153931596427245806173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104676769287730951497204115 157015153931596427245806173)
              ·
                refine ⟨58880682724348660217177315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157015153931596427245806173 58880682724348660217177315)
                ·
                  refine ⟨88321024086522990325765973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58880682724348660217177315 88321024086522990325765973)
                  ·
                    refine ⟨517506000506970646440035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 88321024086522990325765973 517506000506970646440035)
                    ·
                      rfl

theorem cell22_1511759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 9].length) (baseStart_1511759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511759 prefixEnd_1511759 := by exact prefixLift 1511759
  have htrace : WordTrace (prefixWord ++ tailWord_1511759) baseStart_1511759 baseEnd_1511759 := by
    simpa [prefixWord, tailWord_1511759, baseEnd_1511759] using wordTrace_append hprefix tailTrace_1511759
  have hstable : (prefixWord ++ tailWord_1511759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511759).length < 2 ^ (prefixWord ++ tailWord_1511759).sum := by decide
  have hdescent : baseEnd_1511759 < baseStart_1511759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511866 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1511866 : Nat := 118140960795 + 1511866 * 2 ^ 59
def prefixEnd_1511866 : Nat := 4983230072969 + 3 ^ 40 * 1511866 * 2
def baseEnd_1511866 : Nat := 517542628793658034014707

theorem tailTrace_1511866 : CollatzResearch.WordTrace tailWord_1511866 prefixEnd_1511866 517542628793658034014707 := by
  unfold tailWord_1511866
  simp only [CollatzResearch.WordTrace]
  refine ⟨13785570785193790750266863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36761522093850108667378301 13785570785193790750266863)
  ·
    refine ⟨20678356177790686125400295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13785570785193790750266863 20678356177790686125400295)
    ·
      refine ⟨31017534266686029188100443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20678356177790686125400295 31017534266686029188100443)
      ·
        refine ⟨46526301400029043782150665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31017534266686029188100443 46526301400029043782150665)
        ·
          refine ⟨34894726050021782836612999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46526301400029043782150665 34894726050021782836612999)
          ·
            refine ⟨52342089075032674254919499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34894726050021782836612999 52342089075032674254919499)
            ·
              refine ⟨78513133612549011382379249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52342089075032674254919499 78513133612549011382379249)
              ·
                refine ⟨58884850209411758536784437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78513133612549011382379249 58884850209411758536784437)
                ·
                  refine ⟨5520454707132352362823541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58884850209411758536784437 5520454707132352362823541)
                  ·
                    refine ⟨517542628793658034014707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5520454707132352362823541 517542628793658034014707)
                    ·
                      rfl

theorem cell22_1511866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1511866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511866 prefixEnd_1511866 := by exact prefixLift 1511866
  have htrace : WordTrace (prefixWord ++ tailWord_1511866) baseStart_1511866 baseEnd_1511866 := by
    simpa [prefixWord, tailWord_1511866, baseEnd_1511866] using wordTrace_append hprefix tailTrace_1511866
  have hstable : (prefixWord ++ tailWord_1511866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511866).length < 2 ^ (prefixWord ++ tailWord_1511866).sum := by decide
  have hdescent : baseEnd_1511866 < baseStart_1511866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511870 : List Nat := [4, 2, 1, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1511870 : Nat := 118140960795 + 1511870 * 2 ^ 59
def prefixEnd_1511870 : Nat := 4983230072969 + 3 ^ 40 * 1511870 * 2
def baseEnd_1511870 : Nat := 517543998075403356914695

theorem tailTrace_1511870 : CollatzResearch.WordTrace tailWord_1511870 prefixEnd_1511870 517543998075403356914695 := by
  unfold tailWord_1511870
  simp only [CollatzResearch.WordTrace]
  refine ⟨6892803629095083960526633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36761619355173781122808709 6892803629095083960526633)
  ·
    refine ⟨5169602721821312970394975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6892803629095083960526633 5169602721821312970394975)
    ·
      refine ⟨7754404082731969455592463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5169602721821312970394975 7754404082731969455592463)
      ·
        refine ⟨11631606124097954183388695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7754404082731969455592463 11631606124097954183388695)
        ·
          refine ⟨17447409186146931275083043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11631606124097954183388695 17447409186146931275083043)
          ·
            refine ⟨26171113779220396912624565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17447409186146931275083043 26171113779220396912624565)
            ·
              refine ⟨2453541916801912210558553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26171113779220396912624565 2453541916801912210558553)
              ·
                refine ⟨1840156437601434157918915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453541916801912210558553 1840156437601434157918915)
                ·
                  refine ⟨2760234656402151236878373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840156437601434157918915 2760234656402151236878373)
                  ·
                    refine ⟨517543998075403356914695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760234656402151236878373 517543998075403356914695)
                    ·
                      rfl

theorem cell22_1511870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1511870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511870 prefixEnd_1511870 := by exact prefixLift 1511870
  have htrace : WordTrace (prefixWord ++ tailWord_1511870) baseStart_1511870 baseEnd_1511870 := by
    simpa [prefixWord, tailWord_1511870, baseEnd_1511870] using wordTrace_append hprefix tailTrace_1511870
  have hstable : (prefixWord ++ tailWord_1511870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511870).length < 2 ^ (prefixWord ++ tailWord_1511870).sum := by decide
  have hdescent : baseEnd_1511870 < baseStart_1511870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511881 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_1511881 : Nat := 118140960795 + 1511881 * 2 ^ 59
def prefixEnd_1511881 : Nat := 4983230072969 + 3 ^ 40 * 1511881 * 2
def baseEnd_1511881 : Nat := 517547763600202994889661

theorem tailTrace_1511881 : CollatzResearch.WordTrace tailWord_1511881 prefixEnd_1511881 517547763600202994889661 := by
  unfold tailWord_1511881
  simp only [CollatzResearch.WordTrace]
  refine ⟨55142830235720820562863497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36761886823813880375242331 55142830235720820562863497)
  ·
    refine ⟨41357122676790615422147623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55142830235720820562863497 41357122676790615422147623)
    ·
      refine ⟨62035684015185923133221435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41357122676790615422147623 62035684015185923133221435)
      ·
        refine ⟨93053526022778884699832153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62035684015185923133221435 93053526022778884699832153)
        ·
          refine ⟨69790144517084163524874115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93053526022778884699832153 69790144517084163524874115)
          ·
            refine ⟨104685216775626245287311173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69790144517084163524874115 104685216775626245287311173)
            ·
              refine ⟨19628478145429920991370845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104685216775626245287311173 19628478145429920991370845)
              ·
                refine ⟨7360679304536220371764067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19628478145429920991370845 7360679304536220371764067)
                ·
                  refine ⟨11041018956804330557646101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7360679304536220371764067 11041018956804330557646101)
                  ·
                    refine ⟨517547763600202994889661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11041018956804330557646101 517547763600202994889661)
                    ·
                      rfl

theorem cell22_1511881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_1511881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511881 prefixEnd_1511881 := by exact prefixLift 1511881
  have htrace : WordTrace (prefixWord ++ tailWord_1511881) baseStart_1511881 baseEnd_1511881 := by
    simpa [prefixWord, tailWord_1511881, baseEnd_1511881] using wordTrace_append hprefix tailTrace_1511881
  have hstable : (prefixWord ++ tailWord_1511881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511881).length < 2 ^ (prefixWord ++ tailWord_1511881).sum := by decide
  have hdescent : baseEnd_1511881 < baseStart_1511881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511898 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_1511898 : Nat := 118140960795 + 1511898 * 2 ^ 59
def prefixEnd_1511898 : Nat := 4983230072969 + 3 ^ 40 * 1511898 * 2
def baseEnd_1511898 : Nat := 517553583047620617214609

theorem tailTrace_1511898 : CollatzResearch.WordTrace tailWord_1511898 prefixEnd_1511898 517553583047620617214609 := by
  unfold tailWord_1511898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13785862569164808116558087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36762300184439488310821565 13785862569164808116558087)
  ·
    refine ⟨20678793853747212174837131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13785862569164808116558087 20678793853747212174837131)
    ·
      refine ⟨31018190780620818262255697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20678793853747212174837131 31018190780620818262255697)
      ·
        refine ⟨23263643085465613696691773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31018190780620818262255697 23263643085465613696691773)
        ·
          refine ⟨8723866157049605136259415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23263643085465613696691773 8723866157049605136259415)
          ·
            refine ⟨13085799235574407704389123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8723866157049605136259415 13085799235574407704389123)
            ·
              refine ⟨19628698853361611556583685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13085799235574407704389123 19628698853361611556583685)
              ·
                refine ⟨3680381035005302166859441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19628698853361611556583685 3680381035005302166859441)
                ·
                  refine ⟨2760285776253976625144581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3680381035005302166859441 2760285776253976625144581)
                  ·
                    refine ⟨517553583047620617214609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760285776253976625144581 517553583047620617214609)
                    ·
                      rfl

theorem cell22_1511898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_1511898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511898 prefixEnd_1511898 := by exact prefixLift 1511898
  have htrace : WordTrace (prefixWord ++ tailWord_1511898) baseStart_1511898 baseEnd_1511898 := by
    simpa [prefixWord, tailWord_1511898, baseEnd_1511898] using wordTrace_append hprefix tailTrace_1511898
  have hstable : (prefixWord ++ tailWord_1511898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511898).length < 2 ^ (prefixWord ++ tailWord_1511898).sum := by decide
  have hdescent : baseEnd_1511898 < baseStart_1511898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511917 : List Nat := [1, 5, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_1511917 : Nat := 118140960795 + 1511917 * 2 ^ 59
def prefixEnd_1511917 : Nat := 4983230072969 + 3 ^ 40 * 1511917 * 2
def baseEnd_1511917 : Nat := 517560087135910900989551

theorem tailTrace_1511917 : CollatzResearch.WordTrace tailWord_1511917 prefixEnd_1511917 517560087135910900989551 := by
  unfold tailWord_1511917
  simp only [CollatzResearch.WordTrace]
  refine ⟨55144143263590398711174005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36762762175726932474116003 55144143263590398711174005)
  ·
    refine ⟨5169763430961599879172563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55144143263590398711174005 5169763430961599879172563)
    ·
      refine ⟨7754645146442399818758845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5169763430961599879172563 7754645146442399818758845)
      ·
        refine ⟨2907991929915899932034567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7754645146442399818758845 2907991929915899932034567)
        ·
          refine ⟨4361987894873849898051851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2907991929915899932034567 4361987894873849898051851)
          ·
            refine ⟨6542981842310774847077777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4361987894873849898051851 6542981842310774847077777)
            ·
              refine ⟨4907236381733081135308333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6542981842310774847077777 4907236381733081135308333)
              ·
                refine ⟨1840213643149905425740625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4907236381733081135308333 1840213643149905425740625)
                ·
                  refine ⟨1380160232362429069305469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1840213643149905425740625 1380160232362429069305469)
                  ·
                    refine ⟨517560087135910900989551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1380160232362429069305469 517560087135910900989551)
                    ·
                      rfl

theorem cell22_1511917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_1511917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511917 prefixEnd_1511917 := by exact prefixLift 1511917
  have htrace : WordTrace (prefixWord ++ tailWord_1511917) baseStart_1511917 baseEnd_1511917 := by
    simpa [prefixWord, tailWord_1511917, baseEnd_1511917] using wordTrace_append hprefix tailTrace_1511917
  have hstable : (prefixWord ++ tailWord_1511917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511917).length < 2 ^ (prefixWord ++ tailWord_1511917).sum := by decide
  have hdescent : baseEnd_1511917 < baseStart_1511917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511962 : List Nat := [3, 1, 1, 3, 1, 1, 4, 4, 1, 3]
def baseStart_1511962 : Nat := 118140960795 + 1511962 * 2 ^ 59
def prefixEnd_1511962 : Nat := 4983230072969 + 3 ^ 40 * 1511962 * 2
def baseEnd_1511962 : Nat := 517575491555545783614413

theorem tailTrace_1511962 : CollatzResearch.WordTrace tailWord_1511962 prefixEnd_1511962 517575491555545783614413 := by
  unfold tailWord_1511962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13786446137106842849140535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36763856365618247597708093 13786446137106842849140535)
  ·
    refine ⟨20679669205660264273710803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13786446137106842849140535 20679669205660264273710803)
    ·
      refine ⟨31019503808490396410566205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20679669205660264273710803 31019503808490396410566205)
      ·
        refine ⟨11632313928183898653962327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31019503808490396410566205 11632313928183898653962327)
        ·
          refine ⟨17448470892275847980943491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11632313928183898653962327 17448470892275847980943491)
          ·
            refine ⟨26172706338413771971415237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17448470892275847980943491 26172706338413771971415237)
            ·
              refine ⟨4907382438452582244640357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26172706338413771971415237 4907382438452582244640357)
              ·
                refine ⟨920134207209859170870067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4907382438452582244640357 920134207209859170870067)
                ·
                  refine ⟨1380201310814788756305101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920134207209859170870067 1380201310814788756305101)
                  ·
                    refine ⟨517575491555545783614413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1380201310814788756305101 517575491555545783614413)
                    ·
                      rfl

theorem cell22_1511962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 1, 3].length) (baseStart_1511962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511962 prefixEnd_1511962 := by exact prefixLift 1511962
  have htrace : WordTrace (prefixWord ++ tailWord_1511962) baseStart_1511962 baseEnd_1511962 := by
    simpa [prefixWord, tailWord_1511962, baseEnd_1511962] using wordTrace_append hprefix tailTrace_1511962
  have hstable : (prefixWord ++ tailWord_1511962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511962).length < 2 ^ (prefixWord ++ tailWord_1511962).sum := by decide
  have hdescent : baseEnd_1511962 < baseStart_1511962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511973 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 2, 5]
def baseStart_1511973 : Nat := 118140960795 + 1511973 * 2 ^ 59
def prefixEnd_1511973 : Nat := 4983230072969 + 3 ^ 40 * 1511973 * 2
def baseEnd_1511973 : Nat := 517579257080345421589379

theorem tailTrace_1511973 : CollatzResearch.WordTrace tailWord_1511973 prefixEnd_1511973 517579257080345421589379 := by
  unfold tailWord_1511973
  simp only [CollatzResearch.WordTrace]
  refine ⟨55146185751387520275212573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36764123834258346850141715 55146185751387520275212573)
  ·
    refine ⟨20679819656770320103204715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55146185751387520275212573 20679819656770320103204715)
    ·
      refine ⟨31019729485155480154807073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20679819656770320103204715 31019729485155480154807073)
      ·
        refine ⟨23264797113866610116105305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31019729485155480154807073 23264797113866610116105305)
        ·
          refine ⟨17448597835399957587078979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23264797113866610116105305 17448597835399957587078979)
          ·
            refine ⟨26172896753099936380618469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17448597835399957587078979 26172896753099936380618469)
            ·
              refine ⟨4907418141206238071365963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26172896753099936380618469 4907418141206238071365963)
              ·
                refine ⟨7361127211809357107048945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4907418141206238071365963 7361127211809357107048945)
                ·
                  refine ⟨5520845408857017830286709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7361127211809357107048945 5520845408857017830286709)
                  ·
                    refine ⟨517579257080345421589379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5520845408857017830286709 517579257080345421589379)
                    ·
                      rfl

theorem cell22_1511973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 2, 5].length) (baseStart_1511973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511973 prefixEnd_1511973 := by exact prefixLift 1511973
  have htrace : WordTrace (prefixWord ++ tailWord_1511973) baseStart_1511973 baseEnd_1511973 := by
    simpa [prefixWord, tailWord_1511973, baseEnd_1511973] using wordTrace_append hprefix tailTrace_1511973
  have hstable : (prefixWord ++ tailWord_1511973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511973).length < 2 ^ (prefixWord ++ tailWord_1511973).sum := by decide
  have hdescent : baseEnd_1511973 < baseStart_1511973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1511981 : List Nat := [1, 5, 4, 1, 1, 2, 2, 6]
def baseStart_1511981 : Nat := 118140960795 + 1511981 * 2 ^ 59
def prefixEnd_1511981 : Nat := 4983230072969 + 3 ^ 40 * 1511981 * 2
def baseEnd_1511981 : Nat := 57509110627092896376595

theorem tailTrace_1511981 : CollatzResearch.WordTrace tailWord_1511981 prefixEnd_1511981 57509110627092896376595 := by
  unfold tailWord_1511981
  simp only [CollatzResearch.WordTrace]
  refine ⟨55146477535358537641503797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36764318356905691761002531 55146477535358537641503797)
  ·
    refine ⟨5169982268939862903890981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55146477535358537641503797 5169982268939862903890981)
    ·
      refine ⟨969371675426224294479559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5169982268939862903890981 969371675426224294479559)
      ·
        refine ⟨1454057513139336441719339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 969371675426224294479559 1454057513139336441719339)
        ·
          refine ⟨2181086269709004662579009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454057513139336441719339 2181086269709004662579009)
          ·
            refine ⟨1635814702281753496934257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2181086269709004662579009 1635814702281753496934257)
            ·
              refine ⟨1226861026711315122700693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1635814702281753496934257 1226861026711315122700693)
              ·
                refine ⟨57509110627092896376595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1226861026711315122700693 57509110627092896376595)
                ·
                  rfl

theorem cell22_1511981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 6].length) (baseStart_1511981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1511981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1511981 prefixEnd_1511981 := by exact prefixLift 1511981
  have htrace : WordTrace (prefixWord ++ tailWord_1511981) baseStart_1511981 baseEnd_1511981 := by
    simpa [prefixWord, tailWord_1511981, baseEnd_1511981] using wordTrace_append hprefix tailTrace_1511981
  have hstable : (prefixWord ++ tailWord_1511981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1511981).length < 2 ^ (prefixWord ++ tailWord_1511981).sum := by decide
  have hdescent : baseEnd_1511981 < baseStart_1511981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1511981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512005 : List Nat := [1, 3, 1, 1, 1, 5, 2, 3, 1, 4]
def baseStart_1512005 : Nat := 118140960795 + 1512005 * 2 ^ 59
def prefixEnd_1512005 : Nat := 4983230072969 + 3 ^ 40 * 1512005 * 2
def baseEnd_1512005 : Nat := 517590211334308004789281

theorem tailTrace_1512005 : CollatzResearch.WordTrace tailWord_1512005 prefixEnd_1512005 517590211334308004789281 := by
  unfold tailWord_1512005
  simp only [CollatzResearch.WordTrace]
  refine ⟨55147352887271589740377469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36764901924847726493584979 55147352887271589740377469)
  ·
    refine ⟨20680257332726846152641551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55147352887271589740377469 20680257332726846152641551)
    ·
      refine ⟨31020385999090269228962327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20680257332726846152641551 31020385999090269228962327)
      ·
        refine ⟨46530578998635403843443491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31020385999090269228962327 46530578998635403843443491)
        ·
          refine ⟨69795868497953105765165237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46530578998635403843443491 69795868497953105765165237)
          ·
            refine ⟨6543362671683103665484241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69795868497953105765165237 6543362671683103665484241)
            ·
              refine ⟨4907522003762327749113181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6543362671683103665484241 4907522003762327749113181)
              ·
                refine ⟨1840320751410872905917443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4907522003762327749113181 1840320751410872905917443)
                ·
                  refine ⟨2760481127116309358876165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1840320751410872905917443 2760481127116309358876165)
                  ·
                    refine ⟨517590211334308004789281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2760481127116309358876165 517590211334308004789281)
                    ·
                      rfl

theorem cell22_1512005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 4].length) (baseStart_1512005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512005 prefixEnd_1512005 := by exact prefixLift 1512005
  have htrace : WordTrace (prefixWord ++ tailWord_1512005) baseStart_1512005 baseEnd_1512005 := by
    simpa [prefixWord, tailWord_1512005, baseEnd_1512005] using wordTrace_append hprefix tailTrace_1512005
  have hstable : (prefixWord ++ tailWord_1512005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512005).length < 2 ^ (prefixWord ++ tailWord_1512005).sum := by decide
  have hdescent : baseEnd_1512005 < baseStart_1512005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512020 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1512020 : Nat := 118140960795 + 1512020 * 2 ^ 59
def prefixEnd_1512020 : Nat := 4983230072969 + 3 ^ 40 * 1512020 * 2
def baseEnd_1512020 : Nat := 172531782046950988554745

theorem tailTrace_1512020 : CollatzResearch.WordTrace tailWord_1512020 prefixEnd_1512020 172531782046950988554745 := by
  unfold tailWord_1512020
  simp only [CollatzResearch.WordTrace]
  refine ⟨27573949991108623651086757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36765266654811498201449009 27573949991108623651086757)
  ·
    refine ⟨5170115623332866934578767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27573949991108623651086757 5170115623332866934578767)
    ·
      refine ⟨7755173434999300401868151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5170115623332866934578767 7755173434999300401868151)
      ·
        refine ⟨11632760152498950602802227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7755173434999300401868151 11632760152498950602802227)
        ·
          refine ⟨17449140228748425904203341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11632760152498950602802227 17449140228748425904203341)
          ·
            refine ⟨6543427585780659714076253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17449140228748425904203341 6543427585780659714076253)
            ·
              refine ⟨2453785344667747392778595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6543427585780659714076253 2453785344667747392778595)
              ·
                refine ⟨3680678017001621089167893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2453785344667747392778595 3680678017001621089167893)
                ·
                  refine ⟨172531782046950988554745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3680678017001621089167893 172531782046950988554745)
                  ·
                    rfl

theorem cell22_1512020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1512020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512020 prefixEnd_1512020 := by exact prefixLift 1512020
  have htrace : WordTrace (prefixWord ++ tailWord_1512020) baseStart_1512020 baseEnd_1512020 := by
    simpa [prefixWord, tailWord_1512020, baseEnd_1512020] using wordTrace_append hprefix tailTrace_1512020
  have hstable : (prefixWord ++ tailWord_1512020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512020).length < 2 ^ (prefixWord ++ tailWord_1512020).sum := by decide
  have hdescent : baseEnd_1512020 < baseStart_1512020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512082 : List Nat := [3, 2, 3, 1, 2, 3, 1, 7]
def baseStart_1512082 : Nat := 118140960795 + 1512082 * 2 ^ 59
def prefixEnd_1512082 : Nat := 4983230072969 + 3 ^ 40 * 1512082 * 2
def baseEnd_1512082 : Nat := 57512952223100607846005

theorem tailTrace_1512082 : CollatzResearch.WordTrace tailWord_1512082 prefixEnd_1512082 57512952223100607846005 := by
  unfold tailWord_1512082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13787540326998157972732625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36766774205328421260620333 13787540326998157972732625)
  ·
    refine ⟨10340655245248618479549469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13787540326998157972732625 10340655245248618479549469)
    ·
      refine ⟨3877745716968231929831051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10340655245248618479549469 3877745716968231929831051)
      ·
        refine ⟨5816618575452347894746577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3877745716968231929831051 5816618575452347894746577)
        ·
          refine ⟨4362463931589260921059933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5816618575452347894746577 4362463931589260921059933)
          ·
            refine ⟨1635923974345972845397475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4362463931589260921059933 1635923974345972845397475)
            ·
              refine ⟨2453885961518959268096213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635923974345972845397475 2453885961518959268096213)
              ·
                refine ⟨57512952223100607846005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2453885961518959268096213 57512952223100607846005)
                ·
                  rfl

theorem cell22_1512082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 7].length) (baseStart_1512082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512082 prefixEnd_1512082 := by exact prefixLift 1512082
  have htrace : WordTrace (prefixWord ++ tailWord_1512082) baseStart_1512082 baseEnd_1512082 := by
    simpa [prefixWord, tailWord_1512082, baseEnd_1512082] using wordTrace_append hprefix tailTrace_1512082
  have hstable : (prefixWord ++ tailWord_1512082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512082).length < 2 ^ (prefixWord ++ tailWord_1512082).sum := by decide
  have hdescent : baseEnd_1512082 < baseStart_1512082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512125 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1512125 : Nat := 118140960795 + 1512125 * 2 ^ 59
def prefixEnd_1512125 : Nat := 4983230072969 + 3 ^ 40 * 1512125 * 2
def baseEnd_1512125 : Nat := 517631289786667691788913

theorem tailTrace_1512125 : CollatzResearch.WordTrace tailWord_1512125 prefixEnd_1512125 517631289786667691788913 := by
  unfold tailWord_1512125
  simp only [CollatzResearch.WordTrace]
  refine ⟨55151729646836850234745829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36767819764557900156497219 55151729646836850234745829)
  ·
    refine ⟨10340949308781909419014843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55151729646836850234745829 10340949308781909419014843)
    ·
      refine ⟨15511423963172864128522265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10340949308781909419014843 15511423963172864128522265)
      ·
        refine ⟨11633567972379648096391699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15511423963172864128522265 11633567972379648096391699)
        ·
          refine ⟨17450351958569472144587549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11633567972379648096391699 17450351958569472144587549)
          ·
            refine ⟨6543881984463552054220331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17450351958569472144587549 6543881984463552054220331)
            ·
              refine ⟨9815822976695328081330497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6543881984463552054220331 9815822976695328081330497)
              ·
                refine ⟨7361867232521496060997873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9815822976695328081330497 7361867232521496060997873)
                ·
                  refine ⟨5521400424391122045748405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7361867232521496060997873 5521400424391122045748405)
                  ·
                    refine ⟨517631289786667691788913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5521400424391122045748405 517631289786667691788913)
                    ·
                      rfl

theorem cell22_1512125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1512125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512125 prefixEnd_1512125 := by exact prefixLift 1512125
  have htrace : WordTrace (prefixWord ++ tailWord_1512125) baseStart_1512125 baseEnd_1512125 := by
    simpa [prefixWord, tailWord_1512125, baseEnd_1512125] using wordTrace_append hprefix tailTrace_1512125
  have hstable : (prefixWord ++ tailWord_1512125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512125).length < 2 ^ (prefixWord ++ tailWord_1512125).sum := by decide
  have hdescent : baseEnd_1512125 < baseStart_1512125 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512127 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 5]
def baseStart_1512127 : Nat := 118140960795 + 1512127 * 2 ^ 59
def prefixEnd_1512127 : Nat := 4983230072969 + 3 ^ 40 * 1512127 * 2
def baseEnd_1512127 : Nat := 172543991475846784412969

theorem tailTrace_1512127 : CollatzResearch.WordTrace tailWord_1512127 prefixEnd_1512127 172543991475846784412969 := by
  unfold tailWord_1512127
  simp only [CollatzResearch.WordTrace]
  refine ⟨55151802592829604576318635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36767868395219736384212423 55151802592829604576318635)
  ·
    refine ⟨82727703889244406864477953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55151802592829604576318635 82727703889244406864477953)
    ·
      refine ⟨62045777916933305148358465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82727703889244406864477953 62045777916933305148358465)
      ·
        refine ⟨46534333437699978861268849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62045777916933305148358465 46534333437699978861268849)
        ·
          refine ⟨34900750078274984145951637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46534333437699978861268849 34900750078274984145951637)
          ·
            refine ⟨1635972659919139881841483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34900750078274984145951637 1635972659919139881841483)
            ·
              refine ⟨2453958989878709822762225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1635972659919139881841483 2453958989878709822762225)
              ·
                refine ⟨1840469242409032367071669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2453958989878709822762225 1840469242409032367071669)
                ·
                  refine ⟨172543991475846784412969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1840469242409032367071669 172543991475846784412969)
                  ·
                    rfl

theorem cell22_1512127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 5].length) (baseStart_1512127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512127 prefixEnd_1512127 := by exact prefixLift 1512127
  have htrace : WordTrace (prefixWord ++ tailWord_1512127) baseStart_1512127 baseEnd_1512127 := by
    simpa [prefixWord, tailWord_1512127, baseEnd_1512127] using wordTrace_append hprefix tailTrace_1512127
  have hstable : (prefixWord ++ tailWord_1512127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512127).length < 2 ^ (prefixWord ++ tailWord_1512127).sum := by decide
  have hdescent : baseEnd_1512127 < baseStart_1512127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512170 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1512170 : Nat := 118140960795 + 1512170 * 2 ^ 59
def prefixEnd_1512170 : Nat := 4983230072969 + 3 ^ 40 * 1512170 * 2
def baseEnd_1512170 : Nat := 517646694206302574413775

theorem tailTrace_1512170 : CollatzResearch.WordTrace tailWord_1512170 prefixEnd_1512170 517646694206302574413775 := by
  unfold tailWord_1512170
  simp only [CollatzResearch.WordTrace]
  refine ⟨13788342732918455730033491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36768913954449215280089309 13788342732918455730033491)
  ·
    refine ⟨20682514099377683595050237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13788342732918455730033491 20682514099377683595050237)
    ·
      refine ⟨7755942787266631348143839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20682514099377683595050237 7755942787266631348143839)
      ·
        refine ⟨11633914180899947022215759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7755942787266631348143839 11633914180899947022215759)
        ·
          refine ⟨17450871271349920533323639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11633914180899947022215759 17450871271349920533323639)
          ·
            refine ⟨26176306907024880799985459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17450871271349920533323639 26176306907024880799985459)
            ·
              refine ⟨39264460360537321199978189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26176306907024880799985459 39264460360537321199978189)
              ·
                refine ⟨14724172635201495449991821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39264460360537321199978189 14724172635201495449991821)
                ·
                  refine ⟨5521564738200560793746933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14724172635201495449991821 5521564738200560793746933)
                  ·
                    refine ⟨517646694206302574413775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5521564738200560793746933 517646694206302574413775)
                    ·
                      rfl

theorem cell22_1512170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1512170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512170 prefixEnd_1512170 := by exact prefixLift 1512170
  have htrace : WordTrace (prefixWord ++ tailWord_1512170) baseStart_1512170 baseEnd_1512170 := by
    simpa [prefixWord, tailWord_1512170, baseEnd_1512170] using wordTrace_append hprefix tailTrace_1512170
  have hstable : (prefixWord ++ tailWord_1512170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512170).length < 2 ^ (prefixWord ++ tailWord_1512170).sum := by decide
  have hdescent : baseEnd_1512170 < baseStart_1512170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512189 : List Nat := [1, 4, 1, 1, 1, 1, 7, 2, 4]
def baseStart_1512189 : Nat := 118140960795 + 1512189 * 2 ^ 59
def prefixEnd_1512189 : Nat := 4983230072969 + 3 ^ 40 * 1512189 * 2
def baseEnd_1512189 : Nat := 172551066098197619396239

theorem tailTrace_1512189 : CollatzResearch.WordTrace tailWord_1512189 prefixEnd_1512189 172551066098197619396239 := by
  unfold tailWord_1512189
  simp only [CollatzResearch.WordTrace]
  refine ⟨55154063918604989165075621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36769375945736659443383747 55154063918604989165075621)
  ·
    refine ⟨10341386984738435468451679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55154063918604989165075621 10341386984738435468451679)
    ·
      refine ⟨15512080477107653202677519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10341386984738435468451679 15512080477107653202677519)
      ·
        refine ⟨23268120715661479804016279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15512080477107653202677519 23268120715661479804016279)
        ·
          refine ⟨34902181073492219706024419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23268120715661479804016279 34902181073492219706024419)
          ·
            refine ⟨52353271610238329559036629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34902181073492219706024419 52353271610238329559036629)
            ·
              refine ⟨1227029803364960849039921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 52353271610238329559036629 1227029803364960849039921)
              ·
                refine ⟨920272352523720636779941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227029803364960849039921 920272352523720636779941)
                ·
                  refine ⟨172551066098197619396239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920272352523720636779941 172551066098197619396239)
                  ·
                    rfl

theorem cell22_1512189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_1512189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512189 prefixEnd_1512189 := by exact prefixLift 1512189
  have htrace : WordTrace (prefixWord ++ tailWord_1512189) baseStart_1512189 baseEnd_1512189 := by
    simpa [prefixWord, tailWord_1512189, baseEnd_1512189] using wordTrace_append hprefix tailTrace_1512189
  have hstable : (prefixWord ++ tailWord_1512189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512189).length < 2 ^ (prefixWord ++ tailWord_1512189).sum := by decide
  have hdescent : baseEnd_1512189 < baseStart_1512189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512200 : List Nat := [2, 1, 3, 2, 2, 2, 1, 9]
def baseStart_1512200 : Nat := 118140960795 + 1512200 * 2 ^ 59
def prefixEnd_1512200 : Nat := 4983230072969 + 3 ^ 40 * 1512200 * 2
def baseEnd_1512200 : Nat := 57517440424376944018187

theorem tailTrace_1512200 : CollatzResearch.WordTrace tailWord_1512200 prefixEnd_1512200 57517440424376944018187 := by
  unfold tailWord_1512200
  simp only [CollatzResearch.WordTrace]
  refine ⟨27577232560782569021863027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36769643414376758695817369 27577232560782569021863027)
  ·
    refine ⟨41365848841173853532794541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27577232560782569021863027 41365848841173853532794541)
    ·
      refine ⟨15512193315440195074797953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41365848841173853532794541 15512193315440195074797953)
      ·
        refine ⟨11634144986580146306098465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15512193315440195074797953 11634144986580146306098465)
        ·
          refine ⟨8725608739935109729573849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11634144986580146306098465 8725608739935109729573849)
          ·
            refine ⟨6544206554951332297180387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8725608739935109729573849 6544206554951332297180387)
            ·
              refine ⟨9816309832426998445770581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6544206554951332297180387 9816309832426998445770581)
              ·
                refine ⟨57517440424376944018187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9816309832426998445770581 57517440424376944018187)
                ·
                  rfl

theorem cell22_1512200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 9].length) (baseStart_1512200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512200 prefixEnd_1512200 := by exact prefixLift 1512200
  have htrace : WordTrace (prefixWord ++ tailWord_1512200) baseStart_1512200 baseEnd_1512200 := by
    simpa [prefixWord, tailWord_1512200, baseEnd_1512200] using wordTrace_append hprefix tailTrace_1512200
  have hstable : (prefixWord ++ tailWord_1512200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512200).length < 2 ^ (prefixWord ++ tailWord_1512200).sum := by decide
  have hdescent : baseEnd_1512200 < baseStart_1512200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512234 : List Nat := [3, 1, 4, 3, 2, 9]
def baseStart_1512234 : Nat := 118140960795 + 1512234 * 2 ^ 59
def prefixEnd_1512234 : Nat := 4983230072969 + 3 ^ 40 * 1512234 * 2
def baseEnd_1512234 : Nat := 6390970403879354824859

theorem tailTrace_1512234 : CollatzResearch.WordTrace tailWord_1512234 prefixEnd_1512234 6390970403879354824859 := by
  unfold tailWord_1512234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13788926300860490462615939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36770470135627974566975837 13788926300860490462615939)
  ·
    refine ⟨20683389451290735693923909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13788926300860490462615939 20683389451290735693923909)
    ·
      refine ⟨3878135522117012942610733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20683389451290735693923909 3878135522117012942610733)
      ·
        refine ⟨1454300820793879853479025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3878135522117012942610733 1454300820793879853479025)
        ·
          refine ⟨1090725615595409890109269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1454300820793879853479025 1090725615595409890109269)
          ·
            refine ⟨6390970403879354824859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1090725615595409890109269 6390970403879354824859)
            ·
              rfl

theorem cell22_1512234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 2, 9].length) (baseStart_1512234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512234 prefixEnd_1512234 := by exact prefixLift 1512234
  have htrace : WordTrace (prefixWord ++ tailWord_1512234) baseStart_1512234 baseEnd_1512234 := by
    simpa [prefixWord, tailWord_1512234, baseEnd_1512234] using wordTrace_append hprefix tailTrace_1512234
  have hstable : (prefixWord ++ tailWord_1512234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512234).length < 2 ^ (prefixWord ++ tailWord_1512234).sum := by decide
  have hdescent : baseEnd_1512234 < baseStart_1512234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512337 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_1512337 : Nat := 118140960795 + 1512337 * 2 ^ 59
def prefixEnd_1512337 : Nat := 4983230072969 + 3 ^ 40 * 1512337 * 2
def baseEnd_1512337 : Nat := 517703861719169805488263

theorem tailTrace_1512337 : CollatzResearch.WordTrace tailWord_1512337 prefixEnd_1512337 517703861719169805488263 := by
  unfold tailWord_1512337
  simp only [CollatzResearch.WordTrace]
  refine ⟨55159461922068810441463265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36772974614712540294308843 55159461922068810441463265)
  ·
    refine ⟨41369596441551607831097449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55159461922068810441463265 41369596441551607831097449)
    ·
      refine ⟨31027197331163705873323087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41369596441551607831097449 31027197331163705873323087)
      ·
        refine ⟨46540795996745558809984631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31027197331163705873323087 46540795996745558809984631)
        ·
          refine ⟨69811193995118338214976947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46540795996745558809984631 69811193995118338214976947)
          ·
            refine ⟨104716790992677507322465421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69811193995118338214976947 104716790992677507322465421)
            ·
              refine ⟨39268796622254065245924533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104716790992677507322465421 39268796622254065245924533)
              ·
                refine ⟨3681449683336318616805425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39268796622254065245924533 3681449683336318616805425)
                ·
                  refine ⟨2761087262502238962604069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3681449683336318616805425 2761087262502238962604069)
                  ·
                    refine ⟨517703861719169805488263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2761087262502238962604069 517703861719169805488263)
                    ·
                      rfl

theorem cell22_1512337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_1512337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512337 prefixEnd_1512337 := by exact prefixLift 1512337
  have htrace : WordTrace (prefixWord ++ tailWord_1512337) baseStart_1512337 baseEnd_1512337 := by
    simpa [prefixWord, tailWord_1512337, baseEnd_1512337] using wordTrace_append hprefix tailTrace_1512337
  have hstable : (prefixWord ++ tailWord_1512337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512337).length < 2 ^ (prefixWord ++ tailWord_1512337).sum := by decide
  have hdescent : baseEnd_1512337 < baseStart_1512337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512341 : List Nat := [1, 3, 2, 1, 1, 6, 1, 3, 4]
def baseStart_1512341 : Nat := 118140960795 + 1512341 * 2 ^ 59
def prefixEnd_1512341 : Nat := 4983230072969 + 3 ^ 40 * 1512341 * 2
def baseEnd_1512341 : Nat := 172568410333638376129417

theorem tailTrace_1512341 : CollatzResearch.WordTrace tailWord_1512341 prefixEnd_1512341 172568410333638376129417 := by
  unfold tailWord_1512341
  simp only [CollatzResearch.WordTrace]
  refine ⟨55159607814054319124608877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36773071876036212749739251 55159607814054319124608877)
  ·
    refine ⟨20684852930270369671728329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55159607814054319124608877 20684852930270369671728329)
    ·
      refine ⟨15513639697702777253796247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20684852930270369671728329 15513639697702777253796247)
      ·
        refine ⟨23270459546554165880694371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15513639697702777253796247 23270459546554165880694371)
        ·
          refine ⟨34905689319831248821041557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23270459546554165880694371 34905689319831248821041557)
          ·
            refine ⟨1636204186867089788486323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34905689319831248821041557 1636204186867089788486323)
            ·
              refine ⟨2454306280300634682729485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636204186867089788486323 2454306280300634682729485)
              ·
                refine ⟨920364855112738006023557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2454306280300634682729485 920364855112738006023557)
                ·
                  refine ⟨172568410333638376129417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920364855112738006023557 172568410333638376129417)
                  ·
                    rfl

theorem cell22_1512341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_1512341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512341 prefixEnd_1512341 := by exact prefixLift 1512341
  have htrace : WordTrace (prefixWord ++ tailWord_1512341) baseStart_1512341 baseEnd_1512341 := by
    simpa [prefixWord, tailWord_1512341, baseEnd_1512341] using wordTrace_append hprefix tailTrace_1512341
  have hstable : (prefixWord ++ tailWord_1512341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512341).length < 2 ^ (prefixWord ++ tailWord_1512341).sum := by decide
  have hdescent : baseEnd_1512341 < baseStart_1512341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512354 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_1512354 : Nat := 118140960795 + 1512354 * 2 ^ 59
def prefixEnd_1512354 : Nat := 4983230072969 + 3 ^ 40 * 1512354 * 2
def baseEnd_1512354 : Nat := 517709681166587427813211

theorem tailTrace_1512354 : CollatzResearch.WordTrace tailWord_1512354 prefixEnd_1512354 517709681166587427813211 := by
  unfold tailWord_1512354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13790020490751805586208029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36773387975338148229888077 13790020490751805586208029)
  ·
    refine ⟨5171257684031927094828011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13790020490751805586208029 5171257684031927094828011)
    ·
      refine ⟨7756886526047890642242017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171257684031927094828011 7756886526047890642242017)
      ·
        refine ⟨5817664894535917981681513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7756886526047890642242017 5817664894535917981681513)
        ·
          refine ⟨4363248670901938486261135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5817664894535917981681513 4363248670901938486261135)
          ·
            refine ⟨6544873006352907729391703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4363248670901938486261135 6544873006352907729391703)
            ·
              refine ⟨9817309509529361594087555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6544873006352907729391703 9817309509529361594087555)
              ·
                refine ⟨14725964264294042391131333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9817309509529361594087555 14725964264294042391131333)
                ·
                  refine ⟨2761118299555132948337125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14725964264294042391131333 2761118299555132948337125)
                  ·
                    refine ⟨517709681166587427813211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2761118299555132948337125 517709681166587427813211)
                    ·
                      rfl

theorem cell22_1512354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_1512354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512354 prefixEnd_1512354 := by exact prefixLift 1512354
  have htrace : WordTrace (prefixWord ++ tailWord_1512354) baseStart_1512354 baseEnd_1512354 := by
    simpa [prefixWord, tailWord_1512354, baseEnd_1512354] using wordTrace_append hprefix tailTrace_1512354
  have hstable : (prefixWord ++ tailWord_1512354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512354).length < 2 ^ (prefixWord ++ tailWord_1512354).sum := by decide
  have hdescent : baseEnd_1512354 < baseStart_1512354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512369 : List Nat := [1, 2, 2, 4, 3, 1, 2, 7]
def baseStart_1512369 : Nat := 118140960795 + 1512369 * 2 ^ 59
def prefixEnd_1512369 : Nat := 4983230072969 + 3 ^ 40 * 1512369 * 2
def baseEnd_1512369 : Nat := 57523868441459154298685

theorem tailTrace_1512369 : CollatzResearch.WordTrace tailWord_1512369 prefixEnd_1512369 57523868441459154298685 := by
  unfold tailWord_1512369
  simp only [CollatzResearch.WordTrace]
  refine ⟨55160629057952879906628161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36773752705301919937752107 55160629057952879906628161)
  ·
    refine ⟨41370471793464659929971121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55160629057952879906628161 41370471793464659929971121)
    ·
      refine ⟨31027853845098494947478341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41370471793464659929971121 31027853845098494947478341)
      ·
        refine ⟨5817722595955967802652189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31027853845098494947478341 5817722595955967802652189)
        ·
          refine ⟨2181645973483487925994571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5817722595955967802652189 2181645973483487925994571)
          ·
            refine ⟨3272468960225231888991857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181645973483487925994571 3272468960225231888991857)
            ·
              refine ⟨2454351720168923916743893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3272468960225231888991857 2454351720168923916743893)
              ·
                refine ⟨57523868441459154298685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2454351720168923916743893 57523868441459154298685)
                ·
                  rfl

theorem cell22_1512369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 7].length) (baseStart_1512369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512369 prefixEnd_1512369 := by exact prefixLift 1512369
  have htrace : WordTrace (prefixWord ++ tailWord_1512369) baseStart_1512369 baseEnd_1512369 := by
    simpa [prefixWord, tailWord_1512369, baseEnd_1512369] using wordTrace_append hprefix tailTrace_1512369
  have hstable : (prefixWord ++ tailWord_1512369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512369).length < 2 ^ (prefixWord ++ tailWord_1512369).sum := by decide
  have hdescent : baseEnd_1512369 < baseStart_1512369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512388 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 2, 4]
def baseStart_1512388 : Nat := 118140960795 + 1512388 * 2 ^ 59
def prefixEnd_1512388 : Nat := 4983230072969 + 3 ^ 40 * 1512388 * 2
def baseEnd_1512388 : Nat := 517721320061422672463107

theorem tailTrace_1512388 : CollatzResearch.WordTrace tailWord_1512388 prefixEnd_1512388 517721320061422672463107 := by
  unfold tailWord_1512388
  simp only [CollatzResearch.WordTrace]
  refine ⟨27580661022442023075784909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36774214696589364101046545 27580661022442023075784909)
  ·
    refine ⟨10342747883415758653419341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27580661022442023075784909 10342747883415758653419341)
    ·
      refine ⟨3878530456280909495032253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10342747883415758653419341 3878530456280909495032253)
      ·
        refine ⟨1454448921105341060637095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3878530456280909495032253 1454448921105341060637095)
        ·
          refine ⟨2181673381658011590955643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1454448921105341060637095 2181673381658011590955643)
          ·
            refine ⟨3272510072487017386433465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181673381658011590955643 3272510072487017386433465)
            ·
              refine ⟨2454382554365263039825099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3272510072487017386433465 2454382554365263039825099)
              ·
                refine ⟨3681573831547894559737649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454382554365263039825099 3681573831547894559737649)
                ·
                  refine ⟨2761180373660920919803237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3681573831547894559737649 2761180373660920919803237)
                  ·
                    refine ⟨517721320061422672463107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2761180373660920919803237 517721320061422672463107)
                    ·
                      rfl

theorem cell22_1512388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_1512388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512388 prefixEnd_1512388 := by exact prefixLift 1512388
  have htrace : WordTrace (prefixWord ++ tailWord_1512388) baseStart_1512388 baseEnd_1512388 := by
    simpa [prefixWord, tailWord_1512388, baseEnd_1512388] using wordTrace_append hprefix tailTrace_1512388
  have hstable : (prefixWord ++ tailWord_1512388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512388).length < 2 ^ (prefixWord ++ tailWord_1512388).sum := by decide
  have hdescent : baseEnd_1512388 < baseStart_1512388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512401 : List Nat := [1, 2, 2, 1, 2, 1, 4, 5, 1, 3]
def baseStart_1512401 : Nat := 118140960795 + 1512401 * 2 ^ 59
def prefixEnd_1512401 : Nat := 4983230072969 + 3 ^ 40 * 1512401 * 2
def baseEnd_1512401 : Nat := 517725770227094971888067

theorem tailTrace_1512401 : CollatzResearch.WordTrace tailWord_1512401 prefixEnd_1512401 517725770227094971888067 := by
  unfold tailWord_1512401
  simp only [CollatzResearch.WordTrace]
  refine ⟨55161796193836949371793057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36774530795891299581195371 55161796193836949371793057)
  ·
    refine ⟨41371347145377712028844793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55161796193836949371793057 41371347145377712028844793)
    ·
      refine ⟨31028510359033284021633595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41371347145377712028844793 31028510359033284021633595)
      ·
        refine ⟨46542765538549926032450393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31028510359033284021633595 46542765538549926032450393)
        ·
          refine ⟨34907074153912444524337795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46542765538549926032450393 34907074153912444524337795)
          ·
            refine ⟨52360611230868666786506693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34907074153912444524337795 52360611230868666786506693)
            ·
              refine ⟨9817614605787875022470005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52360611230868666786506693 9817614605787875022470005)
              ·
                refine ⟨920401369292613283356563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9817614605787875022470005 920401369292613283356563)
                ·
                  refine ⟨1380602053938919925034845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920401369292613283356563 1380602053938919925034845)
                  ·
                    refine ⟨517725770227094971888067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1380602053938919925034845 517725770227094971888067)
                    ·
                      rfl

theorem cell22_1512401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 5, 1, 3].length) (baseStart_1512401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512401 prefixEnd_1512401 := by exact prefixLift 1512401
  have htrace : WordTrace (prefixWord ++ tailWord_1512401) baseStart_1512401 baseEnd_1512401 := by
    simpa [prefixWord, tailWord_1512401, baseEnd_1512401] using wordTrace_append hprefix tailTrace_1512401
  have hstable : (prefixWord ++ tailWord_1512401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512401).length < 2 ^ (prefixWord ++ tailWord_1512401).sum := by decide
  have hdescent : baseEnd_1512401 < baseStart_1512401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512444 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1512444 : Nat := 118140960795 + 1512444 * 2 ^ 59
def prefixEnd_1512444 : Nat := 4983230072969 + 3 ^ 40 * 1512444 * 2
def baseEnd_1512444 : Nat := 517740490005857193062935

theorem tailTrace_1512444 : CollatzResearch.WordTrace tailWord_1512444 prefixEnd_1512444 517740490005857193062935 := by
  unfold tailWord_1512444
  simp only [CollatzResearch.WordTrace]
  refine ⟨27581682266340583857804193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36775576355120778477072257 27581682266340583857804193)
  ·
    refine ⟨20686261699755437893353145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27581682266340583857804193 20686261699755437893353145)
    ·
      refine ⟨15514696274816578420014859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20686261699755437893353145 15514696274816578420014859)
      ·
        refine ⟨23272044412224867630022289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15514696274816578420014859 23272044412224867630022289)
        ·
          refine ⟨17454033309168650722516717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23272044412224867630022289 17454033309168650722516717)
          ·
            refine ⟨6545262490938244020943769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17454033309168650722516717 6545262490938244020943769)
            ·
              refine ⟨4908946868203683015707827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6545262490938244020943769 4908946868203683015707827)
              ·
                refine ⟨7363420302305524523561741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4908946868203683015707827 7363420302305524523561741)
                ·
                  refine ⟨2761282613364571696335653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7363420302305524523561741 2761282613364571696335653)
                  ·
                    refine ⟨517740490005857193062935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2761282613364571696335653 517740490005857193062935)
                    ·
                      rfl

theorem cell22_1512444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1512444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512444 prefixEnd_1512444 := by exact prefixLift 1512444
  have htrace : WordTrace (prefixWord ++ tailWord_1512444) baseStart_1512444 baseEnd_1512444 := by
    simpa [prefixWord, tailWord_1512444, baseEnd_1512444] using wordTrace_append hprefix tailTrace_1512444
  have hstable : (prefixWord ++ tailWord_1512444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512444).length < 2 ^ (prefixWord ++ tailWord_1512444).sum := by decide
  have hdescent : baseEnd_1512444 < baseStart_1512444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512476 : List Nat := [2, 2, 3, 1, 4, 1, 2, 1, 6]
def baseStart_1512476 : Nat := 118140960795 + 1512476 * 2 ^ 59
def prefixEnd_1512476 : Nat := 4983230072969 + 3 ^ 40 * 1512476 * 2
def baseEnd_1512476 : Nat := 172583814753273258754279

theorem tailTrace_1512476 : CollatzResearch.WordTrace tailWord_1512476 prefixEnd_1512476 172583814753273258754279 := by
  unfold tailWord_1512476
  simp only [CollatzResearch.WordTrace]
  refine ⟨27582265834282618590386641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36776354445710158120515521 27582265834282618590386641)
  ·
    refine ⟨20686699375711963942789981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27582265834282618590386641 20686699375711963942789981)
    ·
      refine ⟨7757512265891986478546243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20686699375711963942789981 7757512265891986478546243)
      ·
        refine ⟨11636268398837979717819365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7757512265891986478546243 11636268398837979717819365)
        ·
          refine ⟨2181800324782121197091131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11636268398837979717819365 2181800324782121197091131)
          ·
            refine ⟨3272700487173181795636697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2181800324782121197091131 3272700487173181795636697)
            ·
              refine ⟨2454525365379886346727523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3272700487173181795636697 2454525365379886346727523)
              ·
                refine ⟨3681788048069829520091285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454525365379886346727523 3681788048069829520091285)
                ·
                  refine ⟨172583814753273258754279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3681788048069829520091285 172583814753273258754279)
                  ·
                    rfl

theorem cell22_1512476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_1512476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512476 prefixEnd_1512476 := by exact prefixLift 1512476
  have htrace : WordTrace (prefixWord ++ tailWord_1512476) baseStart_1512476 baseEnd_1512476 := by
    simpa [prefixWord, tailWord_1512476, baseEnd_1512476] using wordTrace_append hprefix tailTrace_1512476
  have hstable : (prefixWord ++ tailWord_1512476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512476).length < 2 ^ (prefixWord ++ tailWord_1512476).sum := by decide
  have hdescent : baseEnd_1512476 < baseStart_1512476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512504 : List Nat := [2, 1, 2, 1, 5, 2, 1, 8]
def baseStart_1512504 : Nat := 118140960795 + 1512504 * 2 ^ 59
def prefixEnd_1512504 : Nat := 4983230072969 + 3 ^ 40 * 1512504 * 2
def baseEnd_1512504 : Nat := 57529003248004115173639

theorem tailTrace_1512504 : CollatzResearch.WordTrace tailWord_1512504 prefixEnd_1512504 57529003248004115173639 := by
  unfold tailWord_1512504
  simp only [CollatzResearch.WordTrace]
  refine ⟨27582776456231898981396283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36777035274975865308528377 27582776456231898981396283)
  ·
    refine ⟨41374164684347848472094425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27582776456231898981396283 41374164684347848472094425)
    ·
      refine ⟨31030623513260886354070819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41374164684347848472094425 31030623513260886354070819)
      ·
        refine ⟨46545935269891329531106229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31030623513260886354070819 46545935269891329531106229)
        ·
          refine ⟨4363681431552312143541209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46545935269891329531106229 4363681431552312143541209)
          ·
            refine ⟨3272761073664234107655907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4363681431552312143541209 3272761073664234107655907)
            ·
              refine ⟨4909141610496351161483861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272761073664234107655907 4909141610496351161483861)
              ·
                refine ⟨57529003248004115173639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4909141610496351161483861 57529003248004115173639)
                ·
                  rfl

theorem cell22_1512504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 8].length) (baseStart_1512504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512504 prefixEnd_1512504 := by exact prefixLift 1512504
  have htrace : WordTrace (prefixWord ++ tailWord_1512504) baseStart_1512504 baseEnd_1512504 := by
    simpa [prefixWord, tailWord_1512504, baseEnd_1512504] using wordTrace_append hprefix tailTrace_1512504
  have hstable : (prefixWord ++ tailWord_1512504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512504).length < 2 ^ (prefixWord ++ tailWord_1512504).sum := by decide
  have hdescent : baseEnd_1512504 < baseStart_1512504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512510 : List Nat := [4, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_1512510 : Nat := 118140960795 + 1512510 * 2 ^ 59
def prefixEnd_1512510 : Nat := 4983230072969 + 3 ^ 40 * 1512510 * 2
def baseEnd_1512510 : Nat := 172587694384885006970911

theorem tailTrace_1512510 : CollatzResearch.WordTrace tailWord_1512510 prefixEnd_1512510 172587694384885006970911 := by
  unfold tailWord_1512510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895721468805257623438873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36777181166961373991673989 6895721468805257623438873)
  ·
    refine ⟨5171791101603943217579155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6895721468805257623438873 5171791101603943217579155)
    ·
      refine ⟨7757686652405914826368733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5171791101603943217579155 7757686652405914826368733)
      ·
        refine ⟨2909132494652218059888275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7757686652405914826368733 2909132494652218059888275)
        ·
          refine ⟨4363698741978327089832413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909132494652218059888275 4363698741978327089832413)
          ·
            refine ⟨1636387028241872658687155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4363698741978327089832413 1636387028241872658687155)
            ·
              refine ⟨2454580542362808988030733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636387028241872658687155 2454580542362808988030733)
              ·
                refine ⟨920467703386053370511525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2454580542362808988030733 920467703386053370511525)
                ·
                  refine ⟨172587694384885006970911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920467703386053370511525 172587694384885006970911)
                  ·
                    rfl

theorem cell22_1512510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_1512510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512510 prefixEnd_1512510 := by exact prefixLift 1512510
  have htrace : WordTrace (prefixWord ++ tailWord_1512510) baseStart_1512510 baseEnd_1512510 := by
    simpa [prefixWord, tailWord_1512510, baseEnd_1512510] using wordTrace_append hprefix tailTrace_1512510
  have hstable : (prefixWord ++ tailWord_1512510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512510).length < 2 ^ (prefixWord ++ tailWord_1512510).sum := by decide
  have hdescent : baseEnd_1512510 < baseStart_1512510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512542 : List Nat := [4, 4, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1512542 : Nat := 118140960795 + 1512542 * 2 ^ 59
def prefixEnd_1512542 : Nat := 4983230072969 + 3 ^ 40 * 1512542 * 2
def baseEnd_1512542 : Nat := 517774037408617604112635

theorem tailTrace_1512542 : CollatzResearch.WordTrace tailWord_1512542 prefixEnd_1512542 517774037408617604112635 := by
  unfold tailWord_1512542
  simp only [CollatzResearch.WordTrace]
  refine ⟨6895867360790766306584485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36777959257550753635117253 6895867360790766306584485)
  ·
    refine ⟨1292975130148268682484591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6895867360790766306584485 1292975130148268682484591)
    ·
      refine ⟨1939462695222403023726887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1292975130148268682484591 1939462695222403023726887)
      ·
        refine ⟨2909194042833604535590331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1939462695222403023726887 2909194042833604535590331)
        ·
          refine ⟨4363791064250406803385497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2909194042833604535590331 4363791064250406803385497)
          ·
            refine ⟨3272843298187805102539123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4363791064250406803385497 3272843298187805102539123)
            ·
              refine ⟨4909264947281707653808685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3272843298187805102539123 4909264947281707653808685)
              ·
                refine ⟨1840974355230640370178257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4909264947281707653808685 1840974355230640370178257)
                ·
                  refine ⟨1380730766422980277633693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1840974355230640370178257 1380730766422980277633693)
                  ·
                    refine ⟨517774037408617604112635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1380730766422980277633693 517774037408617604112635)
                    ·
                      rfl

theorem cell22_1512542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1512542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512542 prefixEnd_1512542 := by exact prefixLift 1512542
  have htrace : WordTrace (prefixWord ++ tailWord_1512542) baseStart_1512542 baseEnd_1512542 := by
    simpa [prefixWord, tailWord_1512542, baseEnd_1512542] using wordTrace_append hprefix tailTrace_1512542
  have hstable : (prefixWord ++ tailWord_1512542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512542).length < 2 ^ (prefixWord ++ tailWord_1512542).sum := by decide
  have hdescent : baseEnd_1512542 < baseStart_1512542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512624 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_1512624 : Nat := 118140960795 + 1512624 * 2 ^ 59
def prefixEnd_1512624 : Nat := 4983230072969 + 3 ^ 40 * 1512624 * 2
def baseEnd_1512624 : Nat := 517802107684396723562383

theorem tailTrace_1512624 : CollatzResearch.WordTrace tailWord_1512624 prefixEnd_1512624 517802107684396723562383 := by
  unfold tailWord_1512624
  simp only [CollatzResearch.WordTrace]
  refine ⟨27584964836014529228580463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36779953114686038971440617 27584964836014529228580463)
  ·
    refine ⟨41377447254021793842870695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27584964836014529228580463 41377447254021793842870695)
    ·
      refine ⟨62066170881032690764306043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41377447254021793842870695 62066170881032690764306043)
      ·
        refine ⟨93099256321549036146459065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62066170881032690764306043 93099256321549036146459065)
        ·
          refine ⟨69824442241161777109844299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93099256321549036146459065 69824442241161777109844299)
          ·
            refine ⟨104736663361742665664766449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69824442241161777109844299 104736663361742665664766449)
            ·
              refine ⟨78552497521306999248574837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104736663361742665664766449 78552497521306999248574837)
              ·
                refine ⟨7364296642622531179553891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78552497521306999248574837 7364296642622531179553891)
                ·
                  refine ⟨11046444963933796769330837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7364296642622531179553891 11046444963933796769330837)
                  ·
                    refine ⟨517802107684396723562383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11046444963933796769330837 517802107684396723562383)
                    ·
                      rfl

theorem cell22_1512624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_1512624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512624 prefixEnd_1512624 := by exact prefixLift 1512624
  have htrace : WordTrace (prefixWord ++ tailWord_1512624) baseStart_1512624 baseEnd_1512624 := by
    simpa [prefixWord, tailWord_1512624, baseEnd_1512624] using wordTrace_append hprefix tailTrace_1512624
  have hstable : (prefixWord ++ tailWord_1512624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512624).length < 2 ^ (prefixWord ++ tailWord_1512624).sum := by decide
  have hdescent : baseEnd_1512624 < baseStart_1512624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512626 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_1512626 : Nat := 118140960795 + 1512626 * 2 ^ 59
def prefixEnd_1512626 : Nat := 4983230072969 + 3 ^ 40 * 1512626 * 2
def baseEnd_1512626 : Nat := 517802792325269385012377

theorem tailTrace_1512626 : CollatzResearch.WordTrace tailWord_1512626 prefixEnd_1512626 517802792325269385012377 := by
  unfold tailWord_1512626
  simp only [CollatzResearch.WordTrace]
  refine ⟨13792500654505453199683433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36780001745347875199155821 13792500654505453199683433)
  ·
    refine ⟨10344375490879089899762575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13792500654505453199683433 10344375490879089899762575)
    ·
      refine ⟨15516563236318634849643863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10344375490879089899762575 15516563236318634849643863)
      ·
        refine ⟨23274844854477952274465795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15516563236318634849643863 23274844854477952274465795)
        ·
          refine ⟨34912267281716928411698693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23274844854477952274465795 34912267281716928411698693)
          ·
            refine ⟨6546050115321924077193505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34912267281716928411698693 6546050115321924077193505)
            ·
              refine ⟨4909537586491443057895129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6546050115321924077193505 4909537586491443057895129)
              ·
                refine ⟨3682153189868582293421347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4909537586491443057895129 3682153189868582293421347)
                ·
                  refine ⟨5523229784802873440132021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3682153189868582293421347 5523229784802873440132021)
                  ·
                    refine ⟨517802792325269385012377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5523229784802873440132021 517802792325269385012377)
                    ·
                      rfl

theorem cell22_1512626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_1512626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512626 prefixEnd_1512626 := by exact prefixLift 1512626
  have htrace : WordTrace (prefixWord ++ tailWord_1512626) baseStart_1512626 baseEnd_1512626 := by
    simpa [prefixWord, tailWord_1512626, baseEnd_1512626] using wordTrace_append hprefix tailTrace_1512626
  have hstable : (prefixWord ++ tailWord_1512626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512626).length < 2 ^ (prefixWord ++ tailWord_1512626).sum := by decide
  have hdescent : baseEnd_1512626 < baseStart_1512626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512673 : List Nat := [1, 2, 3, 1, 3, 4, 2, 6]
def baseStart_1512673 : Nat := 118140960795 + 1512673 * 2 ^ 59
def prefixEnd_1512673 : Nat := 4983230072969 + 3 ^ 40 * 1512673 * 2
def baseEnd_1512673 : Nat := 57535431265086325454137

theorem tailTrace_1512673 : CollatzResearch.WordTrace tailWord_1512673 prefixEnd_1512673 57535431265086325454137 := by
  unfold tailWord_1512673
  simp only [CollatzResearch.WordTrace]
  refine ⟨55171716848851539825694673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36781144565901026550463115 55171716848851539825694673)
  ·
    refine ⟨41378787636638654869271005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55171716848851539825694673 41378787636638654869271005)
    ·
      refine ⟨15517045363739495575976627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41378787636638654869271005 15517045363739495575976627)
      ·
        refine ⟨23275568045609243363964941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15517045363739495575976627 23275568045609243363964941)
        ·
          refine ⟨8728338017103466261486853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23275568045609243363964941 8728338017103466261486853)
          ·
            refine ⟨1636563378206899924028785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8728338017103466261486853 1636563378206899924028785)
            ·
              refine ⟨1227422533655174943021589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1636563378206899924028785 1227422533655174943021589)
              ·
                refine ⟨57535431265086325454137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1227422533655174943021589 57535431265086325454137)
                ·
                  rfl

theorem cell22_1512673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 6].length) (baseStart_1512673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512673 prefixEnd_1512673 := by exact prefixLift 1512673
  have htrace : WordTrace (prefixWord ++ tailWord_1512673) baseStart_1512673 baseEnd_1512673 := by
    simpa [prefixWord, tailWord_1512673, baseEnd_1512673] using wordTrace_append hprefix tailTrace_1512673
  have hstable : (prefixWord ++ tailWord_1512673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512673).length < 2 ^ (prefixWord ++ tailWord_1512673).sum := by decide
  have hdescent : baseEnd_1512673 < baseStart_1512673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512705 : List Nat := [1, 2, 4, 1, 1, 5, 1, 1, 3, 3]
def baseStart_1512705 : Nat := 118140960795 + 1512705 * 2 ^ 59
def prefixEnd_1512705 : Nat := 4983230072969 + 3 ^ 40 * 1512705 * 2
def baseEnd_1512705 : Nat := 517829835639739512287135

theorem tailTrace_1512705 : CollatzResearch.WordTrace tailWord_1512705 prefixEnd_1512705 517829835639739512287135 := by
  unfold tailWord_1512705
  simp only [CollatzResearch.WordTrace]
  refine ⟨55172883984735609290859569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36781922656490406193906379 55172883984735609290859569)
  ·
    refine ⟨41379662988551706968144677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55172883984735609290859569 41379662988551706968144677)
    ·
      refine ⟨7758686810353445056527127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41379662988551706968144677 7758686810353445056527127)
      ·
        refine ⟨11638030215530167584790691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7758686810353445056527127 11638030215530167584790691)
        ·
          refine ⟨17457045323295251377186037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11638030215530167584790691 17457045323295251377186037)
          ·
            refine ⟨1636597999058929816611191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17457045323295251377186037 1636597999058929816611191)
            ·
              refine ⟨2454896998588394724916787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636597999058929816611191 2454896998588394724916787)
              ·
                refine ⟨3682345497882592087375181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2454896998588394724916787 3682345497882592087375181)
                ·
                  refine ⟨1380879561705972032765693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3682345497882592087375181 1380879561705972032765693)
                  ·
                    refine ⟨517829835639739512287135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1380879561705972032765693 517829835639739512287135)
                    ·
                      rfl

theorem cell22_1512705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_1512705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512705 prefixEnd_1512705 := by exact prefixLift 1512705
  have htrace : WordTrace (prefixWord ++ tailWord_1512705) baseStart_1512705 baseEnd_1512705 := by
    simpa [prefixWord, tailWord_1512705, baseEnd_1512705] using wordTrace_append hprefix tailTrace_1512705
  have hstable : (prefixWord ++ tailWord_1512705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512705).length < 2 ^ (prefixWord ++ tailWord_1512705).sum := by decide
  have hdescent : baseEnd_1512705 < baseStart_1512705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512718 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 5]
def baseStart_1512718 : Nat := 118140960795 + 1512718 * 2 ^ 59
def prefixEnd_1512718 : Nat := 4983230072969 + 3 ^ 40 * 1512718 * 2
def baseEnd_1512718 : Nat := 172611428601803937237365

theorem tailTrace_1512718 : CollatzResearch.WordTrace tailWord_1512718 prefixEnd_1512718 172611428601803937237365 := by
  unfold tailWord_1512718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6896669766711064063885351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36782238755792341674055205 6896669766711064063885351)
  ·
    refine ⟨10345004650066596095828027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6896669766711064063885351 10345004650066596095828027)
    ·
      refine ⟨15517506975099894143742041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10345004650066596095828027 15517506975099894143742041)
      ·
        refine ⟨11638130231324920607806531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15517506975099894143742041 11638130231324920607806531)
        ·
          refine ⟨17457195346987380911709797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11638130231324920607806531 17457195346987380911709797)
          ·
            refine ⟨3273224127560133920945587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17457195346987380911709797 3273224127560133920945587)
            ·
              refine ⟨4909836191340200881418381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273224127560133920945587 4909836191340200881418381)
              ·
                refine ⟨1841188571752575330531893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4909836191340200881418381 1841188571752575330531893)
                ·
                  refine ⟨172611428601803937237365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1841188571752575330531893 172611428601803937237365)
                  ·
                    rfl

theorem cell22_1512718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_1512718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512718 prefixEnd_1512718 := by exact prefixLift 1512718
  have htrace : WordTrace (prefixWord ++ tailWord_1512718) baseStart_1512718 baseEnd_1512718 := by
    simpa [prefixWord, tailWord_1512718, baseEnd_1512718] using wordTrace_append hprefix tailTrace_1512718
  have hstable : (prefixWord ++ tailWord_1512718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512718).length < 2 ^ (prefixWord ++ tailWord_1512718).sum := by decide
  have hdescent : baseEnd_1512718 < baseStart_1512718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512776 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_1512776 : Nat := 118140960795 + 1512776 * 2 ^ 59
def prefixEnd_1512776 : Nat := 4983230072969 + 3 ^ 40 * 1512776 * 2
def baseEnd_1512776 : Nat := 517854140390718993761917

theorem tailTrace_1512776 : CollatzResearch.WordTrace tailWord_1512776 prefixEnd_1512776 517854140390718993761917 := by
  unfold tailWord_1512776
  simp only [CollatzResearch.WordTrace]
  refine ⟨27587736783739194208347091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36783649044985592277796121 27587736783739194208347091)
  ·
    refine ⟨41381605175608791312520637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27587736783739194208347091 41381605175608791312520637)
    ·
      refine ⟨15518101940853296742195239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41381605175608791312520637 15518101940853296742195239)
      ·
        refine ⟨23277152911279945113292859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15518101940853296742195239 23277152911279945113292859)
        ·
          refine ⟨34915729366919917669939289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23277152911279945113292859 34915729366919917669939289)
          ·
            refine ⟨26186797025189938252454467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34915729366919917669939289 26186797025189938252454467)
            ·
              refine ⟨39280195537784907378681701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26186797025189938252454467 39280195537784907378681701)
              ·
                refine ⟨7365036663334670133502819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39280195537784907378681701 7365036663334670133502819)
                ·
                  refine ⟨11047554995002005200254229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7365036663334670133502819 11047554995002005200254229)
                  ·
                    refine ⟨517854140390718993761917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11047554995002005200254229 517854140390718993761917)
                    ·
                      rfl

theorem cell22_1512776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_1512776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512776 prefixEnd_1512776 := by exact prefixLift 1512776
  have htrace : WordTrace (prefixWord ++ tailWord_1512776) baseStart_1512776 baseEnd_1512776 := by
    simpa [prefixWord, tailWord_1512776, baseEnd_1512776] using wordTrace_append hprefix tailTrace_1512776
  have hstable : (prefixWord ++ tailWord_1512776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512776).length < 2 ^ (prefixWord ++ tailWord_1512776).sum := by decide
  have hdescent : baseEnd_1512776 < baseStart_1512776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512793 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_1512793 : Nat := 118140960795 + 1512793 * 2 ^ 59
def prefixEnd_1512793 : Nat := 4983230072969 + 3 ^ 40 * 1512793 * 2
def baseEnd_1512793 : Nat := 517859959838136616086865

theorem tailTrace_1512793 : CollatzResearch.WordTrace tailWord_1512793 prefixEnd_1512793 517859959838136616086865 := by
  unfold tailWord_1512793
  simp only [CollatzResearch.WordTrace]
  refine ⟨55176093608416800320063033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36784062405611200213375355 55176093608416800320063033)
  ·
    refine ⟨41382070206312600240047275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55176093608416800320063033 41382070206312600240047275)
    ·
      refine ⟨62073105309468900360070913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41382070206312600240047275 62073105309468900360070913)
      ·
        refine ⟨46554828982101675270053185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62073105309468900360070913 46554828982101675270053185)
        ·
          refine ⟨34916121736576256452539889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46554828982101675270053185 34916121736576256452539889)
          ·
            refine ⟨26187091302432192339404917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34916121736576256452539889 26187091302432192339404917)
            ·
              refine ⟨2455039809603018031819211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26187091302432192339404917 2455039809603018031819211)
              ·
                refine ⟨3682559714404527047728817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455039809603018031819211 3682559714404527047728817)
                ·
                  refine ⟨2761919785803395285796613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3682559714404527047728817 2761919785803395285796613)
                  ·
                    refine ⟨517859959838136616086865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2761919785803395285796613 517859959838136616086865)
                    ·
                      rfl

theorem cell22_1512793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_1512793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512793 prefixEnd_1512793 := by exact prefixLift 1512793
  have htrace : WordTrace (prefixWord ++ tailWord_1512793) baseStart_1512793 baseEnd_1512793 := by
    simpa [prefixWord, tailWord_1512793, baseEnd_1512793] using wordTrace_append hprefix tailTrace_1512793
  have hstable : (prefixWord ++ tailWord_1512793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512793).length < 2 ^ (prefixWord ++ tailWord_1512793).sum := by decide
  have hdescent : baseEnd_1512793 < baseStart_1512793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512808 : List Nat := [2, 1, 4, 2, 3, 1, 9]
def baseStart_1512808 : Nat := 118140960795 + 1512808 * 2 ^ 59
def prefixEnd_1512808 : Nat := 4983230072969 + 3 ^ 40 * 1512808 * 2
def baseEnd_1512808 : Nat := 19180188690543762109697

theorem tailTrace_1512808 : CollatzResearch.WordTrace tailWord_1512808 prefixEnd_1512808 19180188690543762109697 := by
  unfold tailWord_1512808
  simp only [CollatzResearch.WordTrace]
  refine ⟨27588320351681228940929539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36784427135574971921239385 27588320351681228940929539)
  ·
    refine ⟨41382480527521843411394309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27588320351681228940929539 41382480527521843411394309)
    ·
      refine ⟨7759215098910345639636433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41382480527521843411394309 7759215098910345639636433)
      ·
        refine ⟨5819411324182759229727325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7759215098910345639636433 5819411324182759229727325)
        ·
          refine ⟨2182279246568534711147747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5819411324182759229727325 2182279246568534711147747)
          ·
            refine ⟨3273418869852802066721621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2182279246568534711147747 3273418869852802066721621)
            ·
              refine ⟨19180188690543762109697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3273418869852802066721621 19180188690543762109697)
              ·
                rfl

theorem cell22_1512808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 9].length) (baseStart_1512808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512808 prefixEnd_1512808 := by exact prefixLift 1512808
  have htrace : WordTrace (prefixWord ++ tailWord_1512808) baseStart_1512808 baseEnd_1512808 := by
    simpa [prefixWord, tailWord_1512808, baseEnd_1512808] using wordTrace_append hprefix tailTrace_1512808
  have hstable : (prefixWord ++ tailWord_1512808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512808).length < 2 ^ (prefixWord ++ tailWord_1512808).sum := by decide
  have hdescent : baseEnd_1512808 < baseStart_1512808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512812 : List Nat := [2, 2, 1, 1, 5, 3, 1, 2, 2, 3]
def baseStart_1512812 : Nat := 118140960795 + 1512812 * 2 ^ 59
def prefixEnd_1512812 : Nat := 4983230072969 + 3 ^ 40 * 1512812 * 2
def baseEnd_1512812 : Nat := 517866463926426899861807

theorem tailTrace_1512812 : CollatzResearch.WordTrace tailWord_1512812 prefixEnd_1512812 517866463926426899861807 := by
  unfold tailWord_1512812
  simp only [CollatzResearch.WordTrace]
  refine ⟨27588393297673983282502345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36784524396898644376669793 27588393297673983282502345)
  ·
    refine ⟨20691294973255487461876759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27588393297673983282502345 20691294973255487461876759)
    ·
      refine ⟨31036942459883231192815139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20691294973255487461876759 31036942459883231192815139)
      ·
        refine ⟨46555413689824846789222709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31036942459883231192815139 46555413689824846789222709)
        ·
          refine ⟨4364570033421079386489629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46555413689824846789222709 4364570033421079386489629)
          ·
            refine ⟨1636713762532904769933611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4364570033421079386489629 1636713762532904769933611)
            ·
              refine ⟨2455070643799357154900417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1636713762532904769933611 2455070643799357154900417)
              ·
                refine ⟨1841302982849517866175313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455070643799357154900417 1841302982849517866175313)
                ·
                  refine ⟨1380977237137138399631485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1841302982849517866175313 1380977237137138399631485)
                  ·
                    refine ⟨517866463926426899861807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1380977237137138399631485 517866463926426899861807)
                    ·
                      rfl

theorem cell22_1512812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 3].length) (baseStart_1512812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512812 prefixEnd_1512812 := by exact prefixLift 1512812
  have htrace : WordTrace (prefixWord ++ tailWord_1512812) baseStart_1512812 baseEnd_1512812 := by
    simpa [prefixWord, tailWord_1512812, baseEnd_1512812] using wordTrace_append hprefix tailTrace_1512812
  have hstable : (prefixWord ++ tailWord_1512812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512812).length < 2 ^ (prefixWord ++ tailWord_1512812).sum := by decide
  have hdescent : baseEnd_1512812 < baseStart_1512812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512840 : List Nat := [2, 1, 3, 3, 1, 2, 2, 2, 3, 3]
def baseStart_1512840 : Nat := 118140960795 + 1512840 * 2 ^ 59
def prefixEnd_1512840 : Nat := 4983230072969 + 3 ^ 40 * 1512840 * 2
def baseEnd_1512840 : Nat := 517876048898644160161721

theorem tailTrace_1512840 : CollatzResearch.WordTrace tailWord_1512840 prefixEnd_1512840 517876048898644160161721 := by
  unfold tailWord_1512840
  simp only [CollatzResearch.WordTrace]
  refine ⟨27588903919623263673511987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36785205226164351564682649 27588903919623263673511987)
  ·
    refine ⟨41383355879434895510267981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27588903919623263673511987 41383355879434895510267981)
    ·
      refine ⟨15518758454788085816350493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41383355879434895510267981 15518758454788085816350493)
      ·
        refine ⟨5819534420545532181131435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15518758454788085816350493 5819534420545532181131435)
        ·
          refine ⟨8729301630818298271697153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5819534420545532181131435 8729301630818298271697153)
          ·
            refine ⟨6546976223113723703772865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8729301630818298271697153 6546976223113723703772865)
            ·
              refine ⟨4910232167335292777829649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6546976223113723703772865 4910232167335292777829649)
              ·
                refine ⟨3682674125501469583372237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4910232167335292777829649 3682674125501469583372237)
                ·
                  refine ⟨1381002797063051093764589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3682674125501469583372237 1381002797063051093764589)
                  ·
                    refine ⟨517876048898644160161721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1381002797063051093764589 517876048898644160161721)
                    ·
                      rfl

theorem cell22_1512840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 2, 3, 3].length) (baseStart_1512840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512840 prefixEnd_1512840 := by exact prefixLift 1512840
  have htrace : WordTrace (prefixWord ++ tailWord_1512840) baseStart_1512840 baseEnd_1512840 := by
    simpa [prefixWord, tailWord_1512840, baseEnd_1512840] using wordTrace_append hprefix tailTrace_1512840
  have hstable : (prefixWord ++ tailWord_1512840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512840).length < 2 ^ (prefixWord ++ tailWord_1512840).sum := by decide
  have hdescent : baseEnd_1512840 < baseStart_1512840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512857 : List Nat := [1, 2, 1, 2, 1, 5, 3, 3, 1, 3]
def baseStart_1512857 : Nat := 118140960795 + 1512857 * 2 ^ 59
def prefixEnd_1512857 : Nat := 4983230072969 + 3 ^ 40 * 1512857 * 2
def baseEnd_1512857 : Nat := 517881868346061782486669

theorem tailTrace_1512857 : CollatzResearch.WordTrace tailWord_1512857 prefixEnd_1512857 517881868346061782486669 := by
  unfold tailWord_1512857
  simp only [CollatzResearch.WordTrace]
  refine ⟨55178427880184939250392825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36785618586789959500261883 55178427880184939250392825)
  ·
    refine ⟨41383820910138704437794619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55178427880184939250392825 41383820910138704437794619)
    ·
      refine ⟨62075731365208056656691929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41383820910138704437794619 62075731365208056656691929)
      ·
        refine ⟨46556798523906042492518947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62075731365208056656691929 46556798523906042492518947)
        ·
          refine ⟨69835197785859063738778421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46556798523906042492518947 69835197785859063738778421)
          ·
            refine ⟨6547049792424287225510477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69835197785859063738778421 6547049792424287225510477)
            ·
              refine ⟨2455143672159107709566429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6547049792424287225510477 2455143672159107709566429)
              ·
                refine ⟨920678877059665391087411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2455143672159107709566429 920678877059665391087411)
                ·
                  refine ⟨1381018315589498086631117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 920678877059665391087411 1381018315589498086631117)
                  ·
                    refine ⟨517881868346061782486669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1381018315589498086631117 517881868346061782486669)
                    ·
                      rfl

theorem cell22_1512857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 3, 1, 3].length) (baseStart_1512857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512857 prefixEnd_1512857 := by exact prefixLift 1512857
  have htrace : WordTrace (prefixWord ++ tailWord_1512857) baseStart_1512857 baseEnd_1512857 := by
    simpa [prefixWord, tailWord_1512857, baseEnd_1512857] using wordTrace_append hprefix tailTrace_1512857
  have hstable : (prefixWord ++ tailWord_1512857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512857).length < 2 ^ (prefixWord ++ tailWord_1512857).sum := by decide
  have hdescent : baseEnd_1512857 < baseStart_1512857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512917 : List Nat := [1, 3, 2, 3, 1, 1, 5, 1, 1, 4]
def baseStart_1512917 : Nat := 118140960795 + 1512917 * 2 ^ 59
def prefixEnd_1512917 : Nat := 4983230072969 + 3 ^ 40 * 1512917 * 2
def baseEnd_1512917 : Nat := 517902407572241625986485

theorem tailTrace_1512917 : CollatzResearch.WordTrace tailWord_1512917 prefixEnd_1512917 517902407572241625986485 := by
  unfold tailWord_1512917
  simp only [CollatzResearch.WordTrace]
  refine ⟨55180616259967569497577005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36787077506645046331718003 55180616259967569497577005)
  ·
    refine ⟨20692731097487838561591377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55180616259967569497577005 20692731097487838561591377)
    ·
      refine ⟨15519548323115878921193533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20692731097487838561591377 15519548323115878921193533)
      ·
        refine ⟨5819830621168454595447575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15519548323115878921193533 5819830621168454595447575)
        ·
          refine ⟨8729745931752681893171363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5819830621168454595447575 8729745931752681893171363)
          ·
            refine ⟨13094618897629022839757045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8729745931752681893171363 13094618897629022839757045)
            ·
              refine ⟨1227620521652720891227223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13094618897629022839757045 1227620521652720891227223)
              ·
                refine ⟨1841430782479081336840835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1227620521652720891227223 1841430782479081336840835)
                ·
                  refine ⟨2762146173718622005261253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1841430782479081336840835 2762146173718622005261253)
                  ·
                    refine ⟨517902407572241625986485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2762146173718622005261253 517902407572241625986485)
                    ·
                      rfl

theorem cell22_1512917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 1, 1, 4].length) (baseStart_1512917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512917 prefixEnd_1512917 := by exact prefixLift 1512917
  have htrace : WordTrace (prefixWord ++ tailWord_1512917) baseStart_1512917 baseEnd_1512917 := by
    simpa [prefixWord, tailWord_1512917, baseEnd_1512917] using wordTrace_append hprefix tailTrace_1512917
  have hstable : (prefixWord ++ tailWord_1512917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512917).length < 2 ^ (prefixWord ++ tailWord_1512917).sum := by decide
  have hdescent : baseEnd_1512917 < baseStart_1512917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512928 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_1512928 : Nat := 118140960795 + 1512928 * 2 ^ 59
def prefixEnd_1512928 : Nat := 4983230072969 + 3 ^ 40 * 1512928 * 2
def baseEnd_1512928 : Nat := 517906173097041263961451

theorem tailTrace_1512928 : CollatzResearch.WordTrace tailWord_1512928 prefixEnd_1512928 517906173097041263961451 := by
  unfold tailWord_1512928
  simp only [CollatzResearch.WordTrace]
  refine ⟨27590508731463859188113719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36787344975285145584151625 27590508731463859188113719)
  ·
    refine ⟨41385763097195788782170579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27590508731463859188113719 41385763097195788782170579)
    ·
      refine ⟨62078644645793683173255869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41385763097195788782170579 62078644645793683173255869)
      ·
        refine ⟨23279491742172631189970951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62078644645793683173255869 23279491742172631189970951)
        ·
          refine ⟨34919237613258946784956427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23279491742172631189970951 34919237613258946784956427)
          ·
            refine ⟨52378856419888420177434641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34919237613258946784956427 52378856419888420177434641)
            ·
              refine ⟨39284142314916315133075981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52378856419888420177434641 39284142314916315133075981)
              ·
                refine ⟨14731553368093618174903493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39284142314916315133075981 14731553368093618174903493)
                ·
                  refine ⟨2762166256517553407794405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14731553368093618174903493 2762166256517553407794405)
                  ·
                    refine ⟨517906173097041263961451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2762166256517553407794405 517906173097041263961451)
                    ·
                      rfl

theorem cell22_1512928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_1512928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512928 prefixEnd_1512928 := by exact prefixLift 1512928
  have htrace : WordTrace (prefixWord ++ tailWord_1512928) baseStart_1512928 baseEnd_1512928 := by
    simpa [prefixWord, tailWord_1512928, baseEnd_1512928] using wordTrace_append hprefix tailTrace_1512928
  have hstable : (prefixWord ++ tailWord_1512928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512928).length < 2 ^ (prefixWord ++ tailWord_1512928).sum := by decide
  have hdescent : baseEnd_1512928 < baseStart_1512928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512943 : List Nat := [1, 1, 2, 1, 4, 1, 5, 7]
def baseStart_1512943 : Nat := 118140960795 + 1512943 * 2 ^ 59
def prefixEnd_1512943 : Nat := 4983230072969 + 3 ^ 40 * 1512943 * 2
def baseEnd_1512943 : Nat := 57545700878176247204045

theorem tailTrace_1512943 : CollatzResearch.WordTrace tailWord_1512943 prefixEnd_1512943 57545700878176247204045 := by
  unfold tailWord_1512943
  simp only [CollatzResearch.WordTrace]
  refine ⟨55181564557873375938023483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36787709705248917292015655 55181564557873375938023483)
  ·
    refine ⟨82772346836810063907035225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55181564557873375938023483 82772346836810063907035225)
    ·
      refine ⟨62079260127607547930276419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82772346836810063907035225 62079260127607547930276419)
      ·
        refine ⟨93118890191411321895414629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62079260127607547930276419 93118890191411321895414629)
        ·
          refine ⟨17459791910889622855390243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 93118890191411321895414629 17459791910889622855390243)
          ·
            refine ⟨26189687866334434283085365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17459791910889622855390243 26189687866334434283085365)
            ·
              refine ⟨2455283237468853214039253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26189687866334434283085365 2455283237468853214039253)
              ·
                refine ⟨57545700878176247204045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2455283237468853214039253 57545700878176247204045)
                ·
                  rfl

theorem cell22_1512943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 7].length) (baseStart_1512943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512943 prefixEnd_1512943 := by exact prefixLift 1512943
  have htrace : WordTrace (prefixWord ++ tailWord_1512943) baseStart_1512943 baseEnd_1512943 := by
    simpa [prefixWord, tailWord_1512943, baseEnd_1512943] using wordTrace_append hprefix tailTrace_1512943
  have hstable : (prefixWord ++ tailWord_1512943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512943).length < 2 ^ (prefixWord ++ tailWord_1512943).sum := by decide
  have hdescent : baseEnd_1512943 < baseStart_1512943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512962 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_1512962 : Nat := 118140960795 + 1512962 * 2 ^ 59
def prefixEnd_1512962 : Nat := 4983230072969 + 3 ^ 40 * 1512962 * 2
def baseEnd_1512962 : Nat := 517917811991876508611347

theorem tailTrace_1512962 : CollatzResearch.WordTrace tailWord_1512962 prefixEnd_1512962 517917811991876508611347 := by
  unfold tailWord_1512962
  simp only [CollatzResearch.WordTrace]
  refine ⟨13795564386201135545741285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36788171696536361455310093 13795564386201135545741285)
  ·
    refine ⟨2586668322412712914826491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13795564386201135545741285 2586668322412712914826491)
    ·
      refine ⟨3880002483619069372239737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2586668322412712914826491 3880002483619069372239737)
      ·
        refine ⟨2910001862714302029179803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3880002483619069372239737 2910001862714302029179803)
        ·
          refine ⟨4365002794071453043769705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2910001862714302029179803 4365002794071453043769705)
          ·
            refine ⟨3273752095553589782827279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4365002794071453043769705 3273752095553589782827279)
            ·
              refine ⟨4910628143330384674240919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3273752095553589782827279 4910628143330384674240919)
              ·
                refine ⟨7365942214995577011361379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4910628143330384674240919 7365942214995577011361379)
                ·
                  refine ⟨11048913322493365517042069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7365942214995577011361379 11048913322493365517042069)
                  ·
                    refine ⟨517917811991876508611347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11048913322493365517042069 517917811991876508611347)
                    ·
                      rfl

theorem cell22_1512962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_1512962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512962 prefixEnd_1512962 := by exact prefixLift 1512962
  have htrace : WordTrace (prefixWord ++ tailWord_1512962) baseStart_1512962 baseEnd_1512962 := by
    simpa [prefixWord, tailWord_1512962, baseEnd_1512962] using wordTrace_append hprefix tailTrace_1512962
  have hstable : (prefixWord ++ tailWord_1512962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512962).length < 2 ^ (prefixWord ++ tailWord_1512962).sum := by decide
  have hdescent : baseEnd_1512962 < baseStart_1512962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1512992 : List Nat := [2, 1, 1, 6, 1, 1, 1, 3, 3, 3]
def baseStart_1512992 : Nat := 118140960795 + 1512992 * 2 ^ 59
def prefixEnd_1512992 : Nat := 4983230072969 + 3 ^ 40 * 1512992 * 2
def baseEnd_1512992 : Nat := 517928081604966430361255

theorem tailTrace_1512992 : CollatzResearch.WordTrace tailWord_1512992 prefixEnd_1512992 517928081604966430361255 := by
  unfold tailWord_1512992
  simp only [CollatzResearch.WordTrace]
  refine ⟨27591675867347928653278615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36788901156463904871038153 27591675867347928653278615)
  ·
    refine ⟨41387513801021892979917923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27591675867347928653278615 41387513801021892979917923)
    ·
      refine ⟨62081270701532839469876885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41387513801021892979917923 62081270701532839469876885)
      ·
        refine ⟨2910059564134351850150479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62081270701532839469876885 2910059564134351850150479)
        ·
          refine ⟨4365089346201527775225719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2910059564134351850150479 4365089346201527775225719)
          ·
            refine ⟨6547634019302291662838579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4365089346201527775225719 6547634019302291662838579)
            ·
              refine ⟨9821451028953437494257869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6547634019302291662838579 9821451028953437494257869)
              ·
                refine ⟨3683044135857539060346701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9821451028953437494257869 3683044135857539060346701)
                ·
                  refine ⟨1381141550946577147630013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3683044135857539060346701 1381141550946577147630013)
                  ·
                    refine ⟨517928081604966430361255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1381141550946577147630013 517928081604966430361255)
                    ·
                      rfl

theorem cell22_1512992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 3, 3, 3].length) (baseStart_1512992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1512992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1512992 prefixEnd_1512992 := by exact prefixLift 1512992
  have htrace : WordTrace (prefixWord ++ tailWord_1512992) baseStart_1512992 baseEnd_1512992 := by
    simpa [prefixWord, tailWord_1512992, baseEnd_1512992] using wordTrace_append hprefix tailTrace_1512992
  have hstable : (prefixWord ++ tailWord_1512992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1512992).length < 2 ^ (prefixWord ++ tailWord_1512992).sum := by decide
  have hdescent : baseEnd_1512992 < baseStart_1512992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1512992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513033 : List Nat := [1, 2, 1, 1, 2, 2, 1, 4, 8]
def baseStart_1513033 : Nat := 118140960795 + 1513033 * 2 ^ 59
def prefixEnd_1513033 : Nat := 4983230072969 + 3 ^ 40 * 1513033 * 2
def baseEnd_1513033 : Nat := 172647372247618663362043

theorem tailTrace_1513033 : CollatzResearch.WordTrace tailWord_1513033 prefixEnd_1513033 172647372247618663362043 := by
  unfold tailWord_1513033
  simp only [CollatzResearch.WordTrace]
  refine ⟨55184847127547321308799753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36789898085031547539199835 55184847127547321308799753)
  ·
    refine ⟨41388635345660490981599815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55184847127547321308799753 41388635345660490981599815)
    ·
      refine ⟨62082953018490736472399723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41388635345660490981599815 62082953018490736472399723)
      ·
        refine ⟨93124429527736104708599585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62082953018490736472399723 93124429527736104708599585)
        ·
          refine ⟨69843322145802078531449689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93124429527736104708599585 69843322145802078531449689)
          ·
            refine ⟨52382491609351558898587267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69843322145802078531449689 52382491609351558898587267)
            ·
              refine ⟨78573737414027338347880901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52382491609351558898587267 78573737414027338347880901)
              ·
                refine ⟨14732575765130125940227669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78573737414027338347880901 14732575765130125940227669)
                ·
                  refine ⟨172647372247618663362043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14732575765130125940227669 172647372247618663362043)
                  ·
                    rfl

theorem cell22_1513033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_1513033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513033 prefixEnd_1513033 := by exact prefixLift 1513033
  have htrace : WordTrace (prefixWord ++ tailWord_1513033) baseStart_1513033 baseEnd_1513033 := by
    simpa [prefixWord, tailWord_1513033, baseEnd_1513033] using wordTrace_append hprefix tailTrace_1513033
  have hstable : (prefixWord ++ tailWord_1513033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513033).length < 2 ^ (prefixWord ++ tailWord_1513033).sum := by decide
  have hdescent : baseEnd_1513033 < baseStart_1513033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513112 : List Nat := [2, 1, 2, 4, 1, 4, 1, 7]
def baseStart_1513112 : Nat := 118140960795 + 1513112 * 2 ^ 59
def prefixEnd_1513112 : Nat := 4983230072969 + 3 ^ 40 * 1513112 * 2
def baseEnd_1513112 : Nat := 57552128895258457484543

theorem tailTrace_1513112 : CollatzResearch.WordTrace tailWord_1513112 prefixEnd_1513112 57552128895258457484543 := by
  unfold tailWord_1513112
  simp only [CollatzResearch.WordTrace]
  refine ⟨27593864247130558900462795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36791818996174078533950393 27593864247130558900462795)
  ·
    refine ⟨41390796370695838350694193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27593864247130558900462795 41390796370695838350694193)
    ·
      refine ⟨31043097278021878763020645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41390796370695838350694193 31043097278021878763020645)
      ·
        refine ⟨5820580739629102268066371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 31043097278021878763020645 5820580739629102268066371)
        ·
          refine ⟨8730871109443653402099557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5820580739629102268066371 8730871109443653402099557)
          ·
            refine ⟨1637038333020685012893667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8730871109443653402099557 1637038333020685012893667)
            ·
              refine ⟨2455557499531027519340501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637038333020685012893667 2455557499531027519340501)
              ·
                refine ⟨57552128895258457484543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2455557499531027519340501 57552128895258457484543)
                ·
                  rfl

theorem cell22_1513112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 7].length) (baseStart_1513112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513112 prefixEnd_1513112 := by exact prefixLift 1513112
  have htrace : WordTrace (prefixWord ++ tailWord_1513112) baseStart_1513112 baseEnd_1513112 := by
    simpa [prefixWord, tailWord_1513112, baseEnd_1513112] using wordTrace_append hprefix tailTrace_1513112
  have hstable : (prefixWord ++ tailWord_1513112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513112).length < 2 ^ (prefixWord ++ tailWord_1513112).sum := by decide
  have hdescent : baseEnd_1513112 < baseStart_1513112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513249 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_1513249 : Nat := 118140960795 + 1513249 * 2 ^ 59
def prefixEnd_1513249 : Nat := 4983230072969 + 3 ^ 40 * 1513249 * 2
def baseEnd_1513249 : Nat := 518016057957103426685467

theorem tailTrace_1513249 : CollatzResearch.WordTrace tailWord_1513249 prefixEnd_1513249 518016057957103426685467 := by
  unfold tailWord_1513249
  simp only [CollatzResearch.WordTrace]
  refine ⟨55192725294764790198662801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36795150196509860132441867 55192725294764790198662801)
  ·
    refine ⟨41394543971073592648997101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55192725294764790198662801 41394543971073592648997101)
    ·
      refine ⟨15522953989152597243373913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41394543971073592648997101 15522953989152597243373913)
      ·
        refine ⟨11642215491864447932530435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15522953989152597243373913 11642215491864447932530435)
        ·
          refine ⟨17463323237796671898795653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11642215491864447932530435 17463323237796671898795653)
          ·
            refine ⟨3274373107086875981024185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17463323237796671898795653 3274373107086875981024185)
            ·
              refine ⟨2455779830315156985768139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274373107086875981024185 2455779830315156985768139)
              ·
                refine ⟨3683669745472735478652209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2455779830315156985768139 3683669745472735478652209)
                ·
                  refine ⟨2762752309104551608989157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3683669745472735478652209 2762752309104551608989157)
                  ·
                    refine ⟨518016057957103426685467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2762752309104551608989157 518016057957103426685467)
                    ·
                      rfl

theorem cell22_1513249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_1513249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513249 prefixEnd_1513249 := by exact prefixLift 1513249
  have htrace : WordTrace (prefixWord ++ tailWord_1513249) baseStart_1513249 baseEnd_1513249 := by
    simpa [prefixWord, tailWord_1513249, baseEnd_1513249] using wordTrace_append hprefix tailTrace_1513249
  have hstable : (prefixWord ++ tailWord_1513249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513249).length < 2 ^ (prefixWord ++ tailWord_1513249).sum := by decide
  have hdescent : baseEnd_1513249 < baseStart_1513249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513268 : List Nat := [2, 5, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1513268 : Nat := 118140960795 + 1513268 * 2 ^ 59
def prefixEnd_1513268 : Nat := 4983230072969 + 3 ^ 40 * 1513268 * 2
def baseEnd_1513268 : Nat := 518022562045393710460409

theorem tailTrace_1513268 : CollatzResearch.WordTrace tailWord_1513268 prefixEnd_1513268 518022562045393710460409 := by
  unfold tailWord_1513268
  simp only [CollatzResearch.WordTrace]
  refine ⟨27596709140847978221802229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36795612187797304295736305 27596709140847978221802229)
  ·
    refine ⟨2587191481954497958293959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27596709140847978221802229 2587191481954497958293959)
    ·
      refine ⟨3880787222931746937440939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2587191481954497958293959 3880787222931746937440939)
      ·
        refine ⟨5821180834397620406161409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3880787222931746937440939 5821180834397620406161409)
        ·
          refine ⟨4365885625798215304621057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5821180834397620406161409 4365885625798215304621057)
          ·
            refine ⟨3274414219348661478465793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4365885625798215304621057 3274414219348661478465793)
            ·
              refine ⟨2455810664511496108849345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3274414219348661478465793 2455810664511496108849345)
              ·
                refine ⟨1841857998383622081637009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455810664511496108849345 1841857998383622081637009)
                ·
                  refine ⟨1381393498787716561227757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1841857998383622081637009 1381393498787716561227757)
                  ·
                    refine ⟨518022562045393710460409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1381393498787716561227757 518022562045393710460409)
                    ·
                      rfl

theorem cell22_1513268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1513268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513268 prefixEnd_1513268 := by exact prefixLift 1513268
  have htrace : WordTrace (prefixWord ++ tailWord_1513268) baseStart_1513268 baseEnd_1513268 := by
    simpa [prefixWord, tailWord_1513268, baseEnd_1513268] using wordTrace_append hprefix tailTrace_1513268
  have hstable : (prefixWord ++ tailWord_1513268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513268).length < 2 ^ (prefixWord ++ tailWord_1513268).sum := by decide
  have hdescent : baseEnd_1513268 < baseStart_1513268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513270 : List Nat := [5, 1, 2, 2, 1, 3, 2, 2, 4]
def baseStart_1513270 : Nat := 118140960795 + 1513270 * 2 ^ 59
def prefixEnd_1513270 : Nat := 4983230072969 + 3 ^ 40 * 1513270 * 2
def baseEnd_1513270 : Nat := 172674415562088790636801

theorem tailTrace_1513270 : CollatzResearch.WordTrace tailWord_1513270 prefixEnd_1513270 172674415562088790636801 := by
  unfold tailWord_1513270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3449593201730544424073579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36795660818459140523451509 3449593201730544424073579)
  ·
    refine ⟨5174389802595816636110369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3449593201730544424073579 5174389802595816636110369)
    ·
      refine ⟨3880792351946862477082777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5174389802595816636110369 3880792351946862477082777)
      ·
        refine ⟨2910594263960146857812083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3880792351946862477082777 2910594263960146857812083)
        ·
          refine ⟨4365891395940220286718125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2910594263960146857812083 4365891395940220286718125)
          ·
            refine ⟨1637209273477582607519297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4365891395940220286718125 1637209273477582607519297)
            ·
              refine ⟨1227906955108186955639473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1637209273477582607519297 1227906955108186955639473)
              ·
                refine ⟨920930216331140216729605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1227906955108186955639473 920930216331140216729605)
                ·
                  refine ⟨172674415562088790636801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 920930216331140216729605 172674415562088790636801)
                  ·
                    rfl

theorem cell22_1513270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_1513270 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513270 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513270 prefixEnd_1513270 := by exact prefixLift 1513270
  have htrace : WordTrace (prefixWord ++ tailWord_1513270) baseStart_1513270 baseEnd_1513270 := by
    simpa [prefixWord, tailWord_1513270, baseEnd_1513270] using wordTrace_append hprefix tailTrace_1513270
  have hstable : (prefixWord ++ tailWord_1513270).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513270).length < 2 ^ (prefixWord ++ tailWord_1513270).sum := by decide
  have hdescent : baseEnd_1513270 < baseStart_1513270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513326 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_1513326 : Nat := 118140960795 + 1513326 * 2 ^ 59
def prefixEnd_1513326 : Nat := 4983230072969 + 3 ^ 40 * 1513326 * 2
def baseEnd_1513326 : Nat := 172680805543566964170077

theorem tailTrace_1513326 : CollatzResearch.WordTrace tailWord_1513326 prefixEnd_1513326 172680805543566964170077 := by
  unfold tailWord_1513326
  simp only [CollatzResearch.WordTrace]
  refine ⟨6899441714435729043651979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36797022476990554899477221 6899441714435729043651979)
  ·
    refine ⟨10349162571653593565477969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6899441714435729043651979 10349162571653593565477969)
    ·
      refine ⟨7761871928740195174108477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10349162571653593565477969 7761871928740195174108477)
      ·
        refine ⟨2910701973277573190290679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7761871928740195174108477 2910701973277573190290679)
        ·
          refine ⟨4366052959916359785436019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2910701973277573190290679 4366052959916359785436019)
          ·
            refine ⟨6549079439874539678154029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4366052959916359785436019 6549079439874539678154029)
            ·
              refine ⟨2455904789952952379307761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6549079439874539678154029 2455904789952952379307761)
              ·
                refine ⟨1841928592464714284480821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2455904789952952379307761 1841928592464714284480821)
                ·
                  refine ⟨172680805543566964170077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1841928592464714284480821 172680805543566964170077)
                  ·
                    rfl

theorem cell22_1513326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_1513326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513326 prefixEnd_1513326 := by exact prefixLift 1513326
  have htrace : WordTrace (prefixWord ++ tailWord_1513326) baseStart_1513326 baseEnd_1513326 := by
    simpa [prefixWord, tailWord_1513326, baseEnd_1513326] using wordTrace_append hprefix tailTrace_1513326
  have hstable : (prefixWord ++ tailWord_1513326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513326).length < 2 ^ (prefixWord ++ tailWord_1513326).sum := by decide
  have hdescent : baseEnd_1513326 < baseStart_1513326 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513369 : List Nat := [1, 2, 1, 2, 1, 3, 3, 2, 4, 3]
def baseStart_1513369 : Nat := 118140960795 + 1513369 * 2 ^ 59
def prefixEnd_1513369 : Nat := 4983230072969 + 3 ^ 40 * 1513369 * 2
def baseEnd_1513369 : Nat := 518057136409463113685099

theorem tailTrace_1513369 : CollatzResearch.WordTrace tailWord_1513369 prefixEnd_1513369 518057136409463113685099 := by
  unfold tailWord_1513369
  simp only [CollatzResearch.WordTrace]
  refine ⟨55197102054330050693031161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36798068036220033795354107 55197102054330050693031161)
  ·
    refine ⟨41397826540747538019773371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55197102054330050693031161 41397826540747538019773371)
    ·
      refine ⟨62096739811121307029660057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41397826540747538019773371 62096739811121307029660057)
      ·
        refine ⟨46572554858340980272245043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62096739811121307029660057 46572554858340980272245043)
        ·
          refine ⟨69858832287511470408367565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46572554858340980272245043 69858832287511470408367565)
          ·
            refine ⟨26197062107816801403137837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69858832287511470408367565 26197062107816801403137837)
            ·
              refine ⟨9823898290431300526176689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26197062107816801403137837 9823898290431300526176689)
              ·
                refine ⟨7367923717823475394632517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9823898290431300526176689 7367923717823475394632517)
                ·
                  refine ⟨1381485697091901636493597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7367923717823475394632517 1381485697091901636493597)
                  ·
                    refine ⟨518057136409463113685099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1381485697091901636493597 518057136409463113685099)
                    ·
                      rfl

theorem cell22_1513369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_1513369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513369 prefixEnd_1513369 := by exact prefixLift 1513369
  have htrace : WordTrace (prefixWord ++ tailWord_1513369) baseStart_1513369 baseEnd_1513369 := by
    simpa [prefixWord, tailWord_1513369, baseEnd_1513369] using wordTrace_append hprefix tailTrace_1513369
  have hstable : (prefixWord ++ tailWord_1513369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513369).length < 2 ^ (prefixWord ++ tailWord_1513369).sum := by decide
  have hdescent : baseEnd_1513369 < baseStart_1513369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513495 : List Nat := [1, 1, 3, 5, 3, 1, 1, 2, 5]
def baseStart_1513495 : Nat := 118140960795 + 1513495 * 2 ^ 59
def prefixEnd_1513495 : Nat := 4983230072969 + 3 ^ 40 * 1513495 * 2
def baseEnd_1513495 : Nat := 172700089594813595011571

theorem tailTrace_1513495 : CollatzResearch.WordTrace tailWord_1513495 prefixEnd_1513495 172700089594813595011571 := by
  unfold tailWord_1513495
  simp only [CollatzResearch.WordTrace]
  refine ⟨55201697651873574212117939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36801131767915716141411959 55201697651873574212117939)
  ·
    refine ⟨82802546477810361318176909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55201697651873574212117939 82802546477810361318176909)
    ·
      refine ⟨31050954929178885494316341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82802546477810361318176909 31050954929178885494316341)
      ·
        refine ⟨2911027024610520515092157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31050954929178885494316341 2911027024610520515092157)
        ·
          refine ⟨1091635134228945193159559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2911027024610520515092157 1091635134228945193159559)
          ·
            refine ⟨1637452701343417789739339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091635134228945193159559 1637452701343417789739339)
            ·
              refine ⟨2456179052015126684609009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637452701343417789739339 2456179052015126684609009)
              ·
                refine ⟨1842134289011345013456757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456179052015126684609009 1842134289011345013456757)
                ·
                  refine ⟨172700089594813595011571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1842134289011345013456757 172700089594813595011571)
                  ·
                    rfl

theorem cell22_1513495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 5].length) (baseStart_1513495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513495 prefixEnd_1513495 := by exact prefixLift 1513495
  have htrace : WordTrace (prefixWord ++ tailWord_1513495) baseStart_1513495 baseEnd_1513495 := by
    simpa [prefixWord, tailWord_1513495, baseEnd_1513495] using wordTrace_append hprefix tailTrace_1513495
  have hstable : (prefixWord ++ tailWord_1513495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513495).length < 2 ^ (prefixWord ++ tailWord_1513495).sum := by decide
  have hdescent : baseEnd_1513495 < baseStart_1513495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513506 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_1513506 : Nat := 118140960795 + 1513506 * 2 ^ 59
def prefixEnd_1513506 : Nat := 4983230072969 + 3 ^ 40 * 1513506 * 2
def baseEnd_1513506 : Nat := 172701344769746807669893

theorem tailTrace_1513506 : CollatzResearch.WordTrace tailWord_1513506 prefixEnd_1513506 172701344769746807669893 := by
  unfold tailWord_1513506
  simp only [CollatzResearch.WordTrace]
  refine ⟨13800524713708430772692093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36801399236555815393845581 13800524713708430772692093)
  ·
    refine ⟨5175196767640661539759535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13800524713708430772692093 5175196767640661539759535)
    ·
      refine ⟨7762795151460992309639303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5175196767640661539759535 7762795151460992309639303)
      ·
        refine ⟨11644192727191488464458955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7762795151460992309639303 11644192727191488464458955)
        ·
          refine ⟨17466289090787232696688433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11644192727191488464458955 17466289090787232696688433)
          ·
            refine ⟨13099716818090424522516325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17466289090787232696688433 13099716818090424522516325)
            ·
              refine ⟨2456196903391954597971811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13099716818090424522516325 2456196903391954597971811)
              ·
                refine ⟨3684295355087931896957717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456196903391954597971811 3684295355087931896957717)
                ·
                  refine ⟨172701344769746807669893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3684295355087931896957717 172701344769746807669893)
                  ·
                    rfl

theorem cell22_1513506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_1513506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513506 prefixEnd_1513506 := by exact prefixLift 1513506
  have htrace : WordTrace (prefixWord ++ tailWord_1513506) baseStart_1513506 baseEnd_1513506 := by
    simpa [prefixWord, tailWord_1513506, baseEnd_1513506] using wordTrace_append hprefix tailTrace_1513506
  have hstable : (prefixWord ++ tailWord_1513506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513506).length < 2 ^ (prefixWord ++ tailWord_1513506).sum := by decide
  have hdescent : baseEnd_1513506 < baseStart_1513506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513519 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 6, 4]
def baseStart_1513519 : Nat := 118140960795 + 1513519 * 2 ^ 59
def prefixEnd_1513519 : Nat := 4983230072969 + 3 ^ 40 * 1513519 * 2
def baseEnd_1513519 : Nat := 518108484474912722434639

theorem tailTrace_1513519 : CollatzResearch.WordTrace tailWord_1513519 prefixEnd_1513519 518108484474912722434639 := by
  unfold tailWord_1513519
  simp only [CollatzResearch.WordTrace]
  refine ⟨55202573003786626310991611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36801715335857750873994407 55202573003786626310991611)
  ·
    refine ⟨82803859505679939466487417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55202573003786626310991611 82803859505679939466487417)
    ·
      refine ⟨62102894629259954599865563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82803859505679939466487417 62102894629259954599865563)
      ·
        refine ⟨93154341943889931899798345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62102894629259954599865563 93154341943889931899798345)
        ·
          refine ⟨69865756457917448924848759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93154341943889931899798345 69865756457917448924848759)
          ·
            refine ⟨104798634686876173387273139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69865756457917448924848759 104798634686876173387273139)
            ·
              refine ⟨157197952030314260080909709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104798634686876173387273139 157197952030314260080909709)
              ·
                refine ⟨58949232011367847530341141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 157197952030314260080909709 58949232011367847530341141)
                ·
                  refine ⟨2763245250532867852984741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58949232011367847530341141 2763245250532867852984741)
                  ·
                    refine ⟨518108484474912722434639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2763245250532867852984741 518108484474912722434639)
                    ·
                      rfl

theorem cell22_1513519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 6, 4].length) (baseStart_1513519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513519 prefixEnd_1513519 := by exact prefixLift 1513519
  have htrace : WordTrace (prefixWord ++ tailWord_1513519) baseStart_1513519 baseEnd_1513519 := by
    simpa [prefixWord, tailWord_1513519, baseEnd_1513519] using wordTrace_append hprefix tailTrace_1513519
  have hstable : (prefixWord ++ tailWord_1513519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513519).length < 2 ^ (prefixWord ++ tailWord_1513519).sum := by decide
  have hdescent : baseEnd_1513519 < baseStart_1513519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513521 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 1, 5]
def baseStart_1513521 : Nat := 118140960795 + 1513521 * 2 ^ 59
def prefixEnd_1513521 : Nat := 4983230072969 + 3 ^ 40 * 1513521 * 2
def baseEnd_1513521 : Nat := 518109169115785383884633

theorem tailTrace_1513521 : CollatzResearch.WordTrace tailWord_1513521 prefixEnd_1513521 518109169115785383884633 := by
  unfold tailWord_1513521
  simp only [CollatzResearch.WordTrace]
  refine ⟨55202645949779380652564417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36801763966519587101709611 55202645949779380652564417)
  ·
    refine ⟨41401984462334535489423313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55202645949779380652564417 41401984462334535489423313)
    ·
      refine ⟨31051488346750901617067485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41401984462334535489423313 31051488346750901617067485)
      ·
        refine ⟨11644308130031588106400307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31051488346750901617067485 11644308130031588106400307)
        ·
          refine ⟨17466462195047382159600461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11644308130031588106400307 17466462195047382159600461)
          ·
            refine ⟨6549923323142768309850173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17466462195047382159600461 6549923323142768309850173)
            ·
              refine ⟨2456221246178538116193815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6549923323142768309850173 2456221246178538116193815)
              ·
                refine ⟨3684331869267807174290723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2456221246178538116193815 3684331869267807174290723)
                ·
                  refine ⟨5526497803901710761436085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684331869267807174290723 5526497803901710761436085)
                  ·
                    refine ⟨518109169115785383884633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5526497803901710761436085 518109169115785383884633)
                    ·
                      rfl

theorem cell22_1513521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_1513521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513521 prefixEnd_1513521 := by exact prefixLift 1513521
  have htrace : WordTrace (prefixWord ++ tailWord_1513521) baseStart_1513521 baseEnd_1513521 := by
    simpa [prefixWord, tailWord_1513521, baseEnd_1513521] using wordTrace_append hprefix tailTrace_1513521
  have hstable : (prefixWord ++ tailWord_1513521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513521).length < 2 ^ (prefixWord ++ tailWord_1513521).sum := by decide
  have hdescent : baseEnd_1513521 < baseStart_1513521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513656 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_1513656 : Nat := 118140960795 + 1513656 * 2 ^ 59
def prefixEnd_1513656 : Nat := 4983230072969 + 3 ^ 40 * 1513656 * 2
def baseEnd_1513656 : Nat := 518155382374690031759219

theorem tailTrace_1513656 : CollatzResearch.WordTrace tailWord_1513656 prefixEnd_1513656 518155382374690031759219 := by
  unfold tailWord_1513656
  simp only [CollatzResearch.WordTrace]
  refine ⟨27603784902145149354364411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36805046536193532472485881 27603784902145149354364411)
  ·
    refine ⟨41405677353217724031546617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27603784902145149354364411 41405677353217724031546617)
    ·
      refine ⟨31054258014913293023659963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41405677353217724031546617 31054258014913293023659963)
      ·
        refine ⟨46581387022369939535489945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31054258014913293023659963 46581387022369939535489945)
        ·
          refine ⟨34936040266777454651617459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46581387022369939535489945 34936040266777454651617459)
          ·
            refine ⟨52404060400166181977426189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34936040266777454651617459 52404060400166181977426189)
            ·
              refine ⟨19651522650062318241534821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52404060400166181977426189 19651522650062318241534821)
              ·
                refine ⟨3684660496886684670287779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19651522650062318241534821 3684660496886684670287779)
                ·
                  refine ⟨5526990745330027005431669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3684660496886684670287779 5526990745330027005431669)
                  ·
                    refine ⟨518155382374690031759219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5526990745330027005431669 518155382374690031759219)
                    ·
                      rfl

theorem cell22_1513656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_1513656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513656 prefixEnd_1513656 := by exact prefixLift 1513656
  have htrace : WordTrace (prefixWord ++ tailWord_1513656) baseStart_1513656 baseEnd_1513656 := by
    simpa [prefixWord, tailWord_1513656, baseEnd_1513656] using wordTrace_append hprefix tailTrace_1513656
  have hstable : (prefixWord ++ tailWord_1513656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513656).length < 2 ^ (prefixWord ++ tailWord_1513656).sum := by decide
  have hdescent : baseEnd_1513656 < baseStart_1513656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513658 : List Nat := [3, 1, 1, 1, 2, 2, 3, 5, 4]
def baseStart_1513658 : Nat := 118140960795 + 1513658 * 2 ^ 59
def prefixEnd_1513658 : Nat := 4983230072969 + 3 ^ 40 * 1513658 * 2
def baseEnd_1513658 : Nat := 172718689005187564403071

theorem tailTrace_1513658 : CollatzResearch.WordTrace tailWord_1513658 prefixEnd_1513658 172718689005187564403071 := by
  unfold tailWord_1513658
  simp only [CollatzResearch.WordTrace]
  refine ⟨13801910687570763262575407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36805095166855368700201085 13801910687570763262575407)
  ·
    refine ⟨20702866031356144893863111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13801910687570763262575407 20702866031356144893863111)
    ·
      refine ⟨31054299047034217340794667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20702866031356144893863111 31054299047034217340794667)
      ·
        refine ⟨46581448570551326011192001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31054299047034217340794667 46581448570551326011192001)
        ·
          refine ⟨34936086427913494508394001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46581448570551326011192001 34936086427913494508394001)
          ·
            refine ⟨26202064820935120881295501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34936086427913494508394001 26202064820935120881295501)
            ·
              refine ⟨9825774307850670330485813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26202064820935120881295501 9825774307850670330485813)
              ·
                refine ⟨921166341361000343483045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9825774307850670330485813 921166341361000343483045)
                ·
                  refine ⟨172718689005187564403071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921166341361000343483045 172718689005187564403071)
                  ·
                    rfl

theorem cell22_1513658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 5, 4].length) (baseStart_1513658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513658 prefixEnd_1513658 := by exact prefixLift 1513658
  have htrace : WordTrace (prefixWord ++ tailWord_1513658) baseStart_1513658 baseEnd_1513658 := by
    simpa [prefixWord, tailWord_1513658, baseEnd_1513658] using wordTrace_append hprefix tailTrace_1513658
  have hstable : (prefixWord ++ tailWord_1513658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513658).length < 2 ^ (prefixWord ++ tailWord_1513658).sum := by decide
  have hdescent : baseEnd_1513658 < baseStart_1513658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513660 : List Nat := [2, 2, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_1513660 : Nat := 118140960795 + 1513660 * 2 ^ 59
def prefixEnd_1513660 : Nat := 4983230072969 + 3 ^ 40 * 1513660 * 2
def baseEnd_1513660 : Nat := 518156751656435354659207

theorem tailTrace_1513660 : CollatzResearch.WordTrace tailWord_1513660 prefixEnd_1513660 518156751656435354659207 := by
  unfold tailWord_1513660
  simp only [CollatzResearch.WordTrace]
  refine ⟨27603857848137903695937217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36805143797517204927916289 27603857848137903695937217)
  ·
    refine ⟨20702893386103427771952913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27603857848137903695937217 20702893386103427771952913)
    ·
      refine ⟨15527170039577570828964685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20702893386103427771952913 15527170039577570828964685)
      ·
        refine ⟨5822688764841589060861757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15527170039577570828964685 5822688764841589060861757)
        ·
          refine ⟨2183508286815595897823159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5822688764841589060861757 2183508286815595897823159)
          ·
            refine ⟨3275262430223393846734739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183508286815595897823159 3275262430223393846734739)
            ·
              refine ⟨4912893645335090770102109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275262430223393846734739 4912893645335090770102109)
              ·
                refine ⟨1842335117000659038788291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4912893645335090770102109 1842335117000659038788291)
                ·
                  refine ⟨2763502675500988558182437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842335117000659038788291 2763502675500988558182437)
                  ·
                    refine ⟨518156751656435354659207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2763502675500988558182437 518156751656435354659207)
                    ·
                      rfl

theorem cell22_1513660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_1513660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513660 prefixEnd_1513660 := by exact prefixLift 1513660
  have htrace : WordTrace (prefixWord ++ tailWord_1513660) baseStart_1513660 baseEnd_1513660 := by
    simpa [prefixWord, tailWord_1513660, baseEnd_1513660] using wordTrace_append hprefix tailTrace_1513660
  have hstable : (prefixWord ++ tailWord_1513660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513660).length < 2 ^ (prefixWord ++ tailWord_1513660).sum := by decide
  have hdescent : baseEnd_1513660 < baseStart_1513660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513673 : List Nat := [1, 2, 1, 1, 2, 1, 1, 8, 2, 3]
def baseStart_1513673 : Nat := 118140960795 + 1513673 * 2 ^ 59
def prefixEnd_1513673 : Nat := 4983230072969 + 3 ^ 40 * 1513673 * 2
def baseEnd_1513673 : Nat := 518161201822107654084167

theorem tailTrace_1513673 : CollatzResearch.WordTrace tailWord_1513673 prefixEnd_1513673 518161201822107654084167 := by
  unfold tailWord_1513673
  simp only [CollatzResearch.WordTrace]
  refine ⟨55208189845228710612097673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36805459896819140408065115 55208189845228710612097673)
  ·
    refine ⟨41406142383921532959073255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55208189845228710612097673 41406142383921532959073255)
    ·
      refine ⟨62109213575882299438609883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41406142383921532959073255 62109213575882299438609883)
      ·
        refine ⟨93163820363823449157914825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62109213575882299438609883 93163820363823449157914825)
        ·
          refine ⟨69872865272867586868436119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93163820363823449157914825 69872865272867586868436119)
          ·
            refine ⟨104809297909301380302654179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69872865272867586868436119 104809297909301380302654179)
            ·
              refine ⟨157213946863952070453981269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104809297909301380302654179 157213946863952070453981269)
              ·
                refine ⟨1842350939811938325632593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 157213946863952070453981269 1842350939811938325632593)
                ·
                  refine ⟨1381763204858953744224445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1842350939811938325632593 1381763204858953744224445)
                  ·
                    refine ⟨518161201822107654084167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1381763204858953744224445 518161201822107654084167)
                    ·
                      rfl

theorem cell22_1513673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2, 3].length) (baseStart_1513673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513673 prefixEnd_1513673 := by exact prefixLift 1513673
  have htrace : WordTrace (prefixWord ++ tailWord_1513673) baseStart_1513673 baseEnd_1513673 := by
    simpa [prefixWord, tailWord_1513673, baseEnd_1513673] using wordTrace_append hprefix tailTrace_1513673
  have hstable : (prefixWord ++ tailWord_1513673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513673).length < 2 ^ (prefixWord ++ tailWord_1513673).sum := by decide
  have hdescent : baseEnd_1513673 < baseStart_1513673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513703 : List Nat := [1, 1, 5, 3, 1, 2, 1, 8]
def baseStart_1513703 : Nat := 118140960795 + 1513703 * 2 ^ 59
def prefixEnd_1513703 : Nat := 4983230072969 + 3 ^ 40 * 1513703 * 2
def baseEnd_1513703 : Nat := 57574607937244175092675

theorem tailTrace_1513703 : CollatzResearch.WordTrace tailWord_1513703 prefixEnd_1513703 57574607937244175092675 := by
  unfold tailWord_1513703
  simp only [CollatzResearch.WordTrace]
  refine ⟨55209284035120025735689763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36806189356746683823793175 55209284035120025735689763)
  ·
    refine ⟨82813926052680038603534645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55209284035120025735689763 82813926052680038603534645)
    ·
      refine ⟨7763805567438753619081373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82813926052680038603534645 7763805567438753619081373)
      ·
        refine ⟨2911427087789532607155515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7763805567438753619081373 2911427087789532607155515)
        ·
          refine ⟨4367140631684298910733273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2911427087789532607155515 4367140631684298910733273)
          ·
            refine ⟨3275355473763224183049955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4367140631684298910733273 3275355473763224183049955)
            ·
              refine ⟨4913033210644836274574933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3275355473763224183049955 4913033210644836274574933)
              ·
                refine ⟨57574607937244175092675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4913033210644836274574933 57574607937244175092675)
                ·
                  rfl

theorem cell22_1513703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 8].length) (baseStart_1513703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513703 prefixEnd_1513703 := by exact prefixLift 1513703
  have htrace : WordTrace (prefixWord ++ tailWord_1513703) baseStart_1513703 baseEnd_1513703 := by
    simpa [prefixWord, tailWord_1513703, baseEnd_1513703] using wordTrace_append hprefix tailTrace_1513703
  have hstable : (prefixWord ++ tailWord_1513703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513703).length < 2 ^ (prefixWord ++ tailWord_1513703).sum := by decide
  have hdescent : baseEnd_1513703 < baseStart_1513703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513709 : List Nat := [1, 5, 1, 2, 4, 1, 1, 3, 4]
def baseStart_1513709 : Nat := 118140960795 + 1513709 * 2 ^ 59
def prefixEnd_1513709 : Nat := 4983230072969 + 3 ^ 40 * 1513709 * 2
def baseEnd_1513709 : Nat := 172724508452605186728019

theorem tailTrace_1513709 : CollatzResearch.WordTrace tailWord_1513709 prefixEnd_1513709 172724508452605186728019 := by
  unfold tailWord_1513709
  simp only [CollatzResearch.WordTrace]
  refine ⟨55209502873098288760408181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36806335248732192506938787 55209502873098288760408181)
  ·
    refine ⟨5175890894352964571288267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55209502873098288760408181 5175890894352964571288267)
    ·
      refine ⟨7763836341529446856932401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5175890894352964571288267 7763836341529446856932401)
      ·
        refine ⟨5822877256147085142699301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7763836341529446856932401 5822877256147085142699301)
        ·
          refine ⟨1091789485527578464256119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5822877256147085142699301 1091789485527578464256119)
          ·
            refine ⟨1637684228291367696384179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1091789485527578464256119 1637684228291367696384179)
            ·
              refine ⟨2456526342437051544576269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1637684228291367696384179 2456526342437051544576269)
              ·
                refine ⟨921197378413894329216101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2456526342437051544576269 921197378413894329216101)
                ·
                  refine ⟨172724508452605186728019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921197378413894329216101 172724508452605186728019)
                  ·
                    rfl

theorem cell22_1513709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_1513709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513709 prefixEnd_1513709 := by exact prefixLift 1513709
  have htrace : WordTrace (prefixWord ++ tailWord_1513709) baseStart_1513709 baseEnd_1513709 := by
    simpa [prefixWord, tailWord_1513709, baseEnd_1513709] using wordTrace_append hprefix tailTrace_1513709
  have hstable : (prefixWord ++ tailWord_1513709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513709).length < 2 ^ (prefixWord ++ tailWord_1513709).sum := by decide
  have hdescent : baseEnd_1513709 < baseStart_1513709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513731 : List Nat := [1, 1, 1, 3, 2, 3, 1, 3, 7]
def baseStart_1513731 : Nat := 118140960795 + 1513731 * 2 ^ 59
def prefixEnd_1513731 : Nat := 4983230072969 + 3 ^ 40 * 1513731 * 2
def baseEnd_1513731 : Nat := 172727018802471612044663

theorem tailTrace_1513731 : CollatzResearch.WordTrace tailWord_1513731 prefixEnd_1513731 172727018802471612044663 := by
  unfold tailWord_1513731
  simp only [CollatzResearch.WordTrace]
  refine ⟨55210305279018586517709047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36806870186012391011806031 55210305279018586517709047)
  ·
    refine ⟨82815457918527879776563571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55210305279018586517709047 82815457918527879776563571)
    ·
      refine ⟨124223186877791819664845357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82815457918527879776563571 124223186877791819664845357)
      ·
        refine ⟨46583695079171932374317009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124223186877791819664845357 46583695079171932374317009)
        ·
          refine ⟨34937771309378949280737757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46583695079171932374317009 34937771309378949280737757)
          ·
            refine ⟨13101664241017105980276659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34937771309378949280737757 13101664241017105980276659)
            ·
              refine ⟨19652496361525658970414989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13101664241017105980276659 19652496361525658970414989)
              ·
                refine ⟨7369686135572122113905621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19652496361525658970414989 7369686135572122113905621)
                ·
                  refine ⟨172727018802471612044663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7369686135572122113905621 172727018802471612044663)
                  ·
                    rfl

theorem cell22_1513731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 3, 7].length) (baseStart_1513731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513731 prefixEnd_1513731 := by exact prefixLift 1513731
  have htrace : WordTrace (prefixWord ++ tailWord_1513731) baseStart_1513731 baseEnd_1513731 := by
    simpa [prefixWord, tailWord_1513731, baseEnd_1513731] using wordTrace_append hprefix tailTrace_1513731
  have hstable : (prefixWord ++ tailWord_1513731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513731).length < 2 ^ (prefixWord ++ tailWord_1513731).sum := by decide
  have hdescent : baseEnd_1513731 < baseStart_1513731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513776 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 10]
def baseStart_1513776 : Nat := 118140960795 + 1513776 * 2 ^ 59
def prefixEnd_1513776 : Nat := 4983230072969 + 3 ^ 40 * 1513776 * 2
def baseEnd_1513776 : Nat := 172732153609016572919617

theorem tailTrace_1513776 : CollatzResearch.WordTrace tailWord_1513776 prefixEnd_1513776 172732153609016572919617 := by
  unfold tailWord_1513776
  simp only [CollatzResearch.WordTrace]
  refine ⟨27605973281927779601548591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36807964375903706135398121 27605973281927779601548591)
  ·
    refine ⟨41408959922891669402322887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27605973281927779601548591 41408959922891669402322887)
    ·
      refine ⟨62113439884337504103484331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41408959922891669402322887 62113439884337504103484331)
      ·
        refine ⟨93170159826506256155226497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62113439884337504103484331 93170159826506256155226497)
        ·
          refine ⟨69877619869879692116419873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93170159826506256155226497 69877619869879692116419873)
          ·
            refine ⟨52408214902409769087314905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69877619869879692116419873 52408214902409769087314905)
            ·
              refine ⟨39306161176807326815486179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52408214902409769087314905 39306161176807326815486179)
              ·
                refine ⟨58959241765210990223229269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39306161176807326815486179 58959241765210990223229269)
                ·
                  refine ⟨172732153609016572919617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 58959241765210990223229269 172732153609016572919617)
                  ·
                    rfl

theorem cell22_1513776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_1513776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513776 prefixEnd_1513776 := by exact prefixLift 1513776
  have htrace : WordTrace (prefixWord ++ tailWord_1513776) baseStart_1513776 baseEnd_1513776 := by
    simpa [prefixWord, tailWord_1513776, baseEnd_1513776] using wordTrace_append hprefix tailTrace_1513776
  have hstable : (prefixWord ++ tailWord_1513776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513776).length < 2 ^ (prefixWord ++ tailWord_1513776).sum := by decide
  have hdescent : baseEnd_1513776 < baseStart_1513776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513808 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_1513808 : Nat := 118140960795 + 1513808 * 2 ^ 59
def prefixEnd_1513808 : Nat := 4983230072969 + 3 ^ 40 * 1513808 * 2
def baseEnd_1513808 : Nat := 518207415081012301958753

theorem tailTrace_1513808 : CollatzResearch.WordTrace tailWord_1513808 prefixEnd_1513808 518207415081012301958753 := by
  unfold tailWord_1513808
  simp only [CollatzResearch.WordTrace]
  refine ⟨27606556849869814334131039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36808742466493085778841385 27606556849869814334131039)
  ·
    refine ⟨41409835274804721501196559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27606556849869814334131039 41409835274804721501196559)
    ·
      refine ⟨62114752912207082251794839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41409835274804721501196559 62114752912207082251794839)
      ·
        refine ⟨93172129368310623377692259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62114752912207082251794839 93172129368310623377692259)
        ·
          refine ⟨139758194052465935066538389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93172129368310623377692259 139758194052465935066538389)
          ·
            refine ⟨6551165346209340706243987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139758194052465935066538389 6551165346209340706243987)
            ·
              refine ⟨9826748019314011059365981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6551165346209340706243987 9826748019314011059365981)
              ·
                refine ⟨3685030507242754147262243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9826748019314011059365981 3685030507242754147262243)
                ·
                  refine ⟨5527545760864131220893365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685030507242754147262243 5527545760864131220893365)
                  ·
                    refine ⟨518207415081012301958753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5527545760864131220893365 518207415081012301958753)
                    ·
                      rfl

theorem cell22_1513808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_1513808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513808 prefixEnd_1513808 := by exact prefixLift 1513808
  have htrace : WordTrace (prefixWord ++ tailWord_1513808) baseStart_1513808 baseEnd_1513808 := by
    simpa [prefixWord, tailWord_1513808, baseEnd_1513808] using wordTrace_append hprefix tailTrace_1513808
  have hstable : (prefixWord ++ tailWord_1513808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513808).length < 2 ^ (prefixWord ++ tailWord_1513808).sum := by decide
  have hdescent : baseEnd_1513808 < baseStart_1513808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513842 : List Nat := [3, 2, 1, 2, 1, 3, 3, 2, 2, 3]
def baseStart_1513842 : Nat := 118140960795 + 1513842 * 2 ^ 59
def prefixEnd_1513842 : Nat := 4983230072969 + 3 ^ 40 * 1513842 * 2
def baseEnd_1513842 : Nat := 518219053975847546608649

theorem tailTrace_1513842 : CollatzResearch.WordTrace tailWord_1513842 prefixEnd_1513842 518219053975847546608649 := by
  unfold tailWord_1513842
  simp only [CollatzResearch.WordTrace]
  refine ⟨13803588445404113118749945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36809569187744301649999853 13803588445404113118749945)
  ·
    refine ⟨10352691334053084839062459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13803588445404113118749945 10352691334053084839062459)
    ·
      refine ⟨15529037001079627258593689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10352691334053084839062459 15529037001079627258593689)
      ·
        refine ⟨11646777750809720443945267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15529037001079627258593689 11646777750809720443945267)
        ·
          refine ⟨17470166626214580665917901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11646777750809720443945267 17470166626214580665917901)
          ·
            refine ⟨6551312484830467749719213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17470166626214580665917901 6551312484830467749719213)
            ·
              refine ⟨2456742181811425406144705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6551312484830467749719213 2456742181811425406144705)
              ·
                refine ⟨1842556636358569054608529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2456742181811425406144705 1842556636358569054608529)
                ·
                  refine ⟨1381917477268926790956397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1842556636358569054608529 1381917477268926790956397)
                  ·
                    refine ⟨518219053975847546608649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1381917477268926790956397 518219053975847546608649)
                    ·
                      rfl

theorem cell22_1513842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2, 3].length) (baseStart_1513842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513842 prefixEnd_1513842 := by exact prefixLift 1513842
  have htrace : WordTrace (prefixWord ++ tailWord_1513842) baseStart_1513842 baseEnd_1513842 := by
    simpa [prefixWord, tailWord_1513842, baseEnd_1513842] using wordTrace_append hprefix tailTrace_1513842
  have hstable : (prefixWord ++ tailWord_1513842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513842).length < 2 ^ (prefixWord ++ tailWord_1513842).sum := by decide
  have hdescent : baseEnd_1513842 < baseStart_1513842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513859 : List Nat := [1, 1, 1, 3, 6, 1, 3, 1, 2, 3]
def baseStart_1513859 : Nat := 118140960795 + 1513859 * 2 ^ 59
def prefixEnd_1513859 : Nat := 4983230072969 + 3 ^ 40 * 1513859 * 2
def baseEnd_1513859 : Nat := 518224873423265168933597

theorem tailTrace_1513859 : CollatzResearch.WordTrace tailWord_1513859 prefixEnd_1513859 518224873423265168933597 := by
  unfold tailWord_1513859
  simp only [CollatzResearch.WordTrace]
  refine ⟨55214973822554864378368631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36809982548369909585579087 55214973822554864378368631)
  ·
    refine ⟨82822460733832296567552947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55214973822554864378368631 82822460733832296567552947)
    ·
      refine ⟨124233691100748444851329421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82822460733832296567552947 124233691100748444851329421)
      ·
        refine ⟨46587634162780666819248533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124233691100748444851329421 46587634162780666819248533)
        ·
          refine ⟨2183795351380343757152275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46587634162780666819248533 2183795351380343757152275)
          ·
            refine ⟨3275693027070515635728413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2183795351380343757152275 3275693027070515635728413)
            ·
              refine ⟨1228384885151443363398155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3275693027070515635728413 1228384885151443363398155)
              ·
                refine ⟨1842577327727165045097233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228384885151443363398155 1842577327727165045097233)
                ·
                  refine ⟨1381932995795373783822925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1842577327727165045097233 1381932995795373783822925)
                  ·
                    refine ⟨518224873423265168933597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1381932995795373783822925 518224873423265168933597)
                    ·
                      rfl

theorem cell22_1513859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 1, 2, 3].length) (baseStart_1513859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513859 prefixEnd_1513859 := by exact prefixLift 1513859
  have htrace : WordTrace (prefixWord ++ tailWord_1513859) baseStart_1513859 baseEnd_1513859 := by
    simpa [prefixWord, tailWord_1513859, baseEnd_1513859] using wordTrace_append hprefix tailTrace_1513859
  have hstable : (prefixWord ++ tailWord_1513859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513859).length < 2 ^ (prefixWord ++ tailWord_1513859).sum := by decide
  have hdescent : baseEnd_1513859 < baseStart_1513859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513917 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 5]
def baseStart_1513917 : Nat := 118140960795 + 1513917 * 2 ^ 59
def prefixEnd_1513917 : Nat := 4983230072969 + 3 ^ 40 * 1513917 * 2
def baseEnd_1513917 : Nat := 172748242669524116994473

theorem tailTrace_1513917 : CollatzResearch.WordTrace tailWord_1513917 prefixEnd_1513917 172748242669524116994473 := by
  unfold tailWord_1513917
  simp only [CollatzResearch.WordTrace]
  refine ⟨55217089256344740283980005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36811392837563160189320003 55217089256344740283980005)
  ·
    refine ⟨10353204235564638803246251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55217089256344740283980005 10353204235564638803246251)
    ·
      refine ⟨15529806353346958204869377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10353204235564638803246251 15529806353346958204869377)
      ·
        refine ⟨11647354765010218653652033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15529806353346958204869377 11647354765010218653652033)
        ·
          refine ⟨8735516073757663990239025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11647354765010218653652033 8735516073757663990239025)
          ·
            refine ⟨6551637055318247992679269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8735516073757663990239025 6551637055318247992679269)
            ·
              refine ⟨1228431947872171498627363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6551637055318247992679269 1228431947872171498627363)
              ·
                refine ⟨1842647921808257247941045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228431947872171498627363 1842647921808257247941045)
                ·
                  refine ⟨172748242669524116994473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1842647921808257247941045 172748242669524116994473)
                  ·
                    rfl

theorem cell22_1513917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_1513917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513917 prefixEnd_1513917 := by exact prefixLift 1513917
  have htrace : WordTrace (prefixWord ++ tailWord_1513917) baseStart_1513917 baseEnd_1513917 := by
    simpa [prefixWord, tailWord_1513917, baseEnd_1513917] using wordTrace_append hprefix tailTrace_1513917
  have hstable : (prefixWord ++ tailWord_1513917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513917).length < 2 ^ (prefixWord ++ tailWord_1513917).sum := by decide
  have hdescent : baseEnd_1513917 < baseStart_1513917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513930 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_1513930 : Nat := 118140960795 + 1513930 * 2 ^ 59
def prefixEnd_1513930 : Nat := 4983230072969 + 3 ^ 40 * 1513930 * 2
def baseEnd_1513930 : Nat := 518249178174244650408379

theorem tailTrace_1513930 : CollatzResearch.WordTrace tailWord_1513930 prefixEnd_1513930 518249178174244650408379 := by
  unfold tailWord_1513930
  simp only [CollatzResearch.WordTrace]
  refine ⟨13804390851324410876050811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36811708936865095669468829 13804390851324410876050811)
  ·
    refine ⟨20706586276986616314076217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13804390851324410876050811 20706586276986616314076217)
    ·
      refine ⟨15529939707739962235557163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20706586276986616314076217 15529939707739962235557163)
      ·
        refine ⟨23294909561609943353335745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15529939707739962235557163 23294909561609943353335745)
        ·
          refine ⟨17471182171207457515001809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23294909561609943353335745 17471182171207457515001809)
          ·
            refine ⟨13103386628405593136251357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17471182171207457515001809 13103386628405593136251357)
            ·
              refine ⟨4913769985652097426094259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13103386628405593136251357 4913769985652097426094259)
              ·
                refine ⟨7370654978478146139141389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4913769985652097426094259 7370654978478146139141389)
                ·
                  refine ⟨2763995616929304802178021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7370654978478146139141389 2763995616929304802178021)
                  ·
                    refine ⟨518249178174244650408379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2763995616929304802178021 518249178174244650408379)
                    ·
                      rfl

theorem cell22_1513930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_1513930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513930 prefixEnd_1513930 := by exact prefixLift 1513930
  have htrace : WordTrace (prefixWord ++ tailWord_1513930) baseStart_1513930 baseEnd_1513930 := by
    simpa [prefixWord, tailWord_1513930, baseEnd_1513930] using wordTrace_append hprefix tailTrace_1513930
  have hstable : (prefixWord ++ tailWord_1513930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513930).length < 2 ^ (prefixWord ++ tailWord_1513930).sum := by decide
  have hdescent : baseEnd_1513930 < baseStart_1513930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1513977 : List Nat := [1, 2, 1, 3, 1, 2, 4, 3, 2, 3]
def baseStart_1513977 : Nat := 118140960795 + 1513977 * 2 ^ 59
def prefixEnd_1513977 : Nat := 4983230072969 + 3 ^ 40 * 1513977 * 2
def baseEnd_1513977 : Nat := 518265267234752194483235

theorem tailTrace_1513977 : CollatzResearch.WordTrace tailWord_1513977 prefixEnd_1513977 518265267234752194483235 := by
  unfold tailWord_1513977
  simp only [CollatzResearch.WordTrace]
  refine ⟨55219277636127370531164185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36812851757418247020776123 55219277636127370531164185)
  ·
    refine ⟨41414458227095527898373139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55219277636127370531164185 41414458227095527898373139)
    ·
      refine ⟨62121687340643291847559709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41414458227095527898373139 62121687340643291847559709)
      ·
        refine ⟨23295632752741234442834891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62121687340643291847559709 23295632752741234442834891)
        ·
          refine ⟨34943449129111851664252337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23295632752741234442834891 34943449129111851664252337)
          ·
            refine ⟨26207586846833888748189253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34943449129111851664252337 26207586846833888748189253)
            ·
              refine ⟨4913922533781354140285485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26207586846833888748189253 4913922533781354140285485)
              ·
                refine ⟨1842720950168007802607057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4913922533781354140285485 1842720950168007802607057)
                ·
                  refine ⟨1382040712626005851955293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1842720950168007802607057 1382040712626005851955293)
                  ·
                    refine ⟨518265267234752194483235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1382040712626005851955293 518265267234752194483235)
                    ·
                      rfl

theorem cell22_1513977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2, 3].length) (baseStart_1513977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1513977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1513977 prefixEnd_1513977 := by exact prefixLift 1513977
  have htrace : WordTrace (prefixWord ++ tailWord_1513977) baseStart_1513977 baseEnd_1513977 := by
    simpa [prefixWord, tailWord_1513977, baseEnd_1513977] using wordTrace_append hprefix tailTrace_1513977
  have hstable : (prefixWord ++ tailWord_1513977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1513977).length < 2 ^ (prefixWord ++ tailWord_1513977).sum := by decide
  have hdescent : baseEnd_1513977 < baseStart_1513977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1513977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514007 : List Nat := [1, 1, 3, 6, 1, 1, 9]
def baseStart_1514007 : Nat := 118140960795 + 1514007 * 2 ^ 59
def prefixEnd_1514007 : Nat := 4983230072969 + 3 ^ 40 * 1514007 * 2
def baseEnd_1514007 : Nat := 19195390253623782082709

theorem tailTrace_1514007 : CollatzResearch.WordTrace tailWord_1514007 prefixEnd_1514007 19195390253623782082709 := by
  unfold tailWord_1514007
  simp only [CollatzResearch.WordTrace]
  refine ⟨55220371826018685654756275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36813581217345790436504183 55220371826018685654756275)
  ·
    refine ⟨82830557739028028482134413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55220371826018685654756275 82830557739028028482134413)
    ·
      refine ⟨31061459152135510680800405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82830557739028028482134413 31061459152135510680800405)
      ·
        refine ⟨1456005897756352063162519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31061459152135510680800405 1456005897756352063162519)
        ·
          refine ⟨2184008846634528094743779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456005897756352063162519 2184008846634528094743779)
          ·
            refine ⟨3276013269951792142115669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184008846634528094743779 3276013269951792142115669)
            ·
              refine ⟨19195390253623782082709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3276013269951792142115669 19195390253623782082709)
              ·
                rfl

theorem cell22_1514007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 9].length) (baseStart_1514007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514007 prefixEnd_1514007 := by exact prefixLift 1514007
  have htrace : WordTrace (prefixWord ++ tailWord_1514007) baseStart_1514007 baseEnd_1514007 := by
    simpa [prefixWord, tailWord_1514007, baseEnd_1514007] using wordTrace_append hprefix tailTrace_1514007
  have hstable : (prefixWord ++ tailWord_1514007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514007).length < 2 ^ (prefixWord ++ tailWord_1514007).sum := by decide
  have hdescent : baseEnd_1514007 < baseStart_1514007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514112 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_1514112 : Nat := 118140960795 + 1514112 * 2 ^ 59
def prefixEnd_1514112 : Nat := 4983230072969 + 3 ^ 40 * 1514112 * 2
def baseEnd_1514112 : Nat := 518311480493656842357821

theorem tailTrace_1514112 : CollatzResearch.WordTrace tailWord_1514112 prefixEnd_1514112 518311480493656842357821 := by
  unfold tailWord_1514112
  simp only [CollatzResearch.WordTrace]
  refine ⟨27612100745319144293664295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36816134327092192391552393 27612100745319144293664295)
  ·
    refine ⟨41418151117978716440496443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27612100745319144293664295 41418151117978716440496443)
    ·
      refine ⟨62127226676968074660744665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41418151117978716440496443 62127226676968074660744665)
      ·
        refine ⟨46595420007726055995558499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62127226676968074660744665 46595420007726055995558499)
        ·
          refine ⟨69893130011589083993337749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46595420007726055995558499 69893130011589083993337749)
          ·
            refine ⟨3276240469293238312187707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 69893130011589083993337749 3276240469293238312187707)
            ·
              refine ⟨4914360703939857468281561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3276240469293238312187707 4914360703939857468281561)
              ·
                refine ⟨3685770527954893101211171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4914360703939857468281561 3685770527954893101211171)
                ·
                  refine ⟨5528655791932339651816757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3685770527954893101211171 5528655791932339651816757)
                  ·
                    refine ⟨518311480493656842357821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5528655791932339651816757 518311480493656842357821)
                    ·
                      rfl

theorem cell22_1514112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_1514112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514112 prefixEnd_1514112 := by exact prefixLift 1514112
  have htrace : WordTrace (prefixWord ++ tailWord_1514112) baseStart_1514112 baseEnd_1514112 := by
    simpa [prefixWord, tailWord_1514112, baseEnd_1514112] using wordTrace_append hprefix tailTrace_1514112
  have hstable : (prefixWord ++ tailWord_1514112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514112).length < 2 ^ (prefixWord ++ tailWord_1514112).sum := by decide
  have hdescent : baseEnd_1514112 < baseStart_1514112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514116 : List Nat := [2, 3, 2, 1, 3, 2, 3, 1, 1, 4]
def baseStart_1514116 : Nat := 118140960795 + 1514116 * 2 ^ 59
def prefixEnd_1514116 : Nat := 4983230072969 + 3 ^ 40 * 1514116 * 2
def baseEnd_1514116 : Nat := 518312849775402165257809

theorem tailTrace_1514116 : CollatzResearch.WordTrace tailWord_1514116 prefixEnd_1514116 518312849775402165257809 := by
  unfold tailWord_1514116
  simp only [CollatzResearch.WordTrace]
  refine ⟨27612173691311898635237101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36816231588415864846982801 27612173691311898635237101)
  ·
    refine ⟨10354565134241961988213913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27612173691311898635237101 10354565134241961988213913)
    ·
      refine ⟨7765923850681471491160435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10354565134241961988213913 7765923850681471491160435)
      ·
        refine ⟨11648885776022207236740653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7765923850681471491160435 11648885776022207236740653)
        ·
          refine ⟨4368332166008327713777745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11648885776022207236740653 4368332166008327713777745)
          ·
            refine ⟨3276249124506245785333309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4368332166008327713777745 3276249124506245785333309)
            ·
              refine ⟨1228593421689842169499991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3276249124506245785333309 1228593421689842169499991)
              ·
                refine ⟨1842890132534763254249987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228593421689842169499991 1842890132534763254249987)
                ·
                  refine ⟨2764335198802144881374981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1842890132534763254249987 2764335198802144881374981)
                  ·
                    refine ⟨518312849775402165257809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2764335198802144881374981 518312849775402165257809)
                    ·
                      rfl

theorem cell22_1514116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_1514116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514116 prefixEnd_1514116 := by exact prefixLift 1514116
  have htrace : WordTrace (prefixWord ++ tailWord_1514116) baseStart_1514116 baseEnd_1514116 := by
    simpa [prefixWord, tailWord_1514116, baseEnd_1514116] using wordTrace_append hprefix tailTrace_1514116
  have hstable : (prefixWord ++ tailWord_1514116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514116).length < 2 ^ (prefixWord ++ tailWord_1514116).sum := by decide
  have hdescent : baseEnd_1514116 < baseStart_1514116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514174 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1514174 : Nat := 118140960795 + 1514174 * 2 ^ 59
def prefixEnd_1514174 : Nat := 4983230072969 + 3 ^ 40 * 1514174 * 2
def baseEnd_1514174 : Nat := 518332704360709347307631

theorem tailTrace_1514174 : CollatzResearch.WordTrace tailWord_1514174 prefixEnd_1514174 518332704360709347307631 := by
  unfold tailWord_1514174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6903307852051709147010697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36817641877609115450723717 6903307852051709147010697)
  ·
    refine ⟨5177480889038781860258023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6903307852051709147010697 5177480889038781860258023)
    ·
      refine ⟨7766221333558172790387035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5177480889038781860258023 7766221333558172790387035)
      ·
        refine ⟨11649332000337259185580553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7766221333558172790387035 11649332000337259185580553)
        ·
          refine ⟨8736999000252944389185415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11649332000337259185580553 8736999000252944389185415)
          ·
            refine ⟨13105498500379416583778123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8736999000252944389185415 13105498500379416583778123)
            ·
              refine ⟨19658247750569124875667185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13105498500379416583778123 19658247750569124875667185)
              ·
                refine ⟨14743685812926843656750389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19658247750569124875667185 14743685812926843656750389)
                ·
                  refine ⟨1382220544961891592820349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14743685812926843656750389 1382220544961891592820349)
                  ·
                    refine ⟨518332704360709347307631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1382220544961891592820349 518332704360709347307631)
                    ·
                      rfl

theorem cell22_1514174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1514174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514174 prefixEnd_1514174 := by exact prefixLift 1514174
  have htrace : WordTrace (prefixWord ++ tailWord_1514174) baseStart_1514174 baseEnd_1514174 := by
    simpa [prefixWord, tailWord_1514174, baseEnd_1514174] using wordTrace_append hprefix tailTrace_1514174
  have hstable : (prefixWord ++ tailWord_1514174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514174).length < 2 ^ (prefixWord ++ tailWord_1514174).sum := by decide
  have hdescent : baseEnd_1514174 < baseStart_1514174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514202 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 2, 5]
def baseStart_1514202 : Nat := 118140960795 + 1514202 * 2 ^ 59
def prefixEnd_1514202 : Nat := 4983230072969 + 3 ^ 40 * 1514202 * 2
def baseEnd_1514202 : Nat := 518342289332926607607545

theorem tailTrace_1514202 : CollatzResearch.WordTrace tailWord_1514202 prefixEnd_1514202 518342289332926607607545 := by
  unfold tailWord_1514202
  simp only [CollatzResearch.WordTrace]
  refine ⟨13806871015078058489526215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36818322706874822638736573 13806871015078058489526215)
  ·
    refine ⟨20710306522617087734289323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13806871015078058489526215 20710306522617087734289323)
    ·
      refine ⟨31065459783925631601433985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20710306522617087734289323 31065459783925631601433985)
      ·
        refine ⟨23299094837944223701075489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31065459783925631601433985 23299094837944223701075489)
        ·
          refine ⟨17474321128458167775806617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23299094837944223701075489 17474321128458167775806617)
          ·
            refine ⟨13105740846343625831854963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17474321128458167775806617 13105740846343625831854963)
            ·
              refine ⟨19658611269515438747782445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13105740846343625831854963 19658611269515438747782445)
              ·
                refine ⟨7371979226068289530418417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19658611269515438747782445 7371979226068289530418417)
                ·
                  refine ⟨5528984419551217147813813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7371979226068289530418417 5528984419551217147813813)
                  ·
                    refine ⟨518342289332926607607545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5528984419551217147813813 518342289332926607607545)
                    ·
                      rfl

theorem cell22_1514202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_1514202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514202 prefixEnd_1514202 := by exact prefixLift 1514202
  have htrace : WordTrace (prefixWord ++ tailWord_1514202) baseStart_1514202 baseEnd_1514202 := by
    simpa [prefixWord, tailWord_1514202, baseEnd_1514202] using wordTrace_append hprefix tailTrace_1514202
  have hstable : (prefixWord ++ tailWord_1514202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514202).length < 2 ^ (prefixWord ++ tailWord_1514202).sum := by decide
  have hdescent : baseEnd_1514202 < baseStart_1514202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514217 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 3, 4]
def baseStart_1514217 : Nat := 118140960795 + 1514217 * 2 ^ 59
def prefixEnd_1514217 : Nat := 4983230072969 + 3 ^ 40 * 1514217 * 2
def baseEnd_1514217 : Nat := 518347424139471568482499

theorem tailTrace_1514217 : CollatzResearch.WordTrace tailWord_1514217 prefixEnd_1514217 518347424139471568482499 := by
  unfold tailWord_1514217
  simp only [CollatzResearch.WordTrace]
  refine ⟨55228031155257891519900905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36818687436838594346600603 55228031155257891519900905)
  ·
    refine ⟨41421023366443418639925679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55228031155257891519900905 41421023366443418639925679)
    ·
      refine ⟨62131535049665127959888519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41421023366443418639925679 62131535049665127959888519)
      ·
        refine ⟨93197302574497691939832779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62131535049665127959888519 93197302574497691939832779)
        ·
          refine ⟨139795953861746537909749169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93197302574497691939832779 139795953861746537909749169)
          ·
            refine ⟨104846965396309903432311877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139795953861746537909749169 104846965396309903432311877)
            ·
              refine ⟨19658806011808106893558477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104846965396309903432311877 19658806011808106893558477)
              ·
                refine ⟨7372052254428040085084429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19658806011808106893558477 7372052254428040085084429)
                ·
                  refine ⟨2764519595410515031906661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7372052254428040085084429 2764519595410515031906661)
                  ·
                    refine ⟨518347424139471568482499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2764519595410515031906661 518347424139471568482499)
                    ·
                      rfl

theorem cell22_1514217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 3, 4].length) (baseStart_1514217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514217 prefixEnd_1514217 := by exact prefixLift 1514217
  have htrace : WordTrace (prefixWord ++ tailWord_1514217) baseStart_1514217 baseEnd_1514217 := by
    simpa [prefixWord, tailWord_1514217, baseEnd_1514217] using wordTrace_append hprefix tailTrace_1514217
  have hstable : (prefixWord ++ tailWord_1514217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514217).length < 2 ^ (prefixWord ++ tailWord_1514217).sum := by decide
  have hdescent : baseEnd_1514217 < baseStart_1514217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514234 : List Nat := [3, 1, 1, 1, 1, 3, 4, 3, 1, 4]
def baseStart_1514234 : Nat := 118140960795 + 1514234 * 2 ^ 59
def prefixEnd_1514234 : Nat := 4983230072969 + 3 ^ 40 * 1514234 * 2
def baseEnd_1514234 : Nat := 518353243586889190807447

theorem tailTrace_1514234 : CollatzResearch.WordTrace tailWord_1514234 prefixEnd_1514234 518353243586889190807447 := by
  unfold tailWord_1514234
  simp only [CollatzResearch.WordTrace]
  refine ⟨13807162799049075855817439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36819100797464202282179837 13807162799049075855817439)
  ·
    refine ⟨20710744198573613783726159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13807162799049075855817439 20710744198573613783726159)
    ·
      refine ⟨31066116297860420675589239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20710744198573613783726159 31066116297860420675589239)
      ·
        refine ⟨46599174446790631013383859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31066116297860420675589239 46599174446790631013383859)
        ·
          refine ⟨69898761670185946520075789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46599174446790631013383859 69898761670185946520075789)
          ·
            refine ⟨26212035626319729945028421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69898761670185946520075789 26212035626319729945028421)
            ·
              refine ⟨4914756679934949364692829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26212035626319729945028421 4914756679934949364692829)
              ·
                refine ⟨1843033754975606011759811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4914756679934949364692829 1843033754975606011759811)
                ·
                  refine ⟨2764550632463409017639717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1843033754975606011759811 2764550632463409017639717)
                  ·
                    refine ⟨518353243586889190807447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2764550632463409017639717 518353243586889190807447)
                    ·
                      rfl

theorem cell22_1514234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_1514234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514234 prefixEnd_1514234 := by exact prefixLift 1514234
  have htrace : WordTrace (prefixWord ++ tailWord_1514234) baseStart_1514234 baseEnd_1514234 := by
    simpa [prefixWord, tailWord_1514234, baseEnd_1514234] using wordTrace_append hprefix tailTrace_1514234
  have hstable : (prefixWord ++ tailWord_1514234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514234).length < 2 ^ (prefixWord ++ tailWord_1514234).sum := by decide
  have hdescent : baseEnd_1514234 < baseStart_1514234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514249 : List Nat := [1, 2, 1, 1, 3, 2, 2, 6, 4]
def baseStart_1514249 : Nat := 118140960795 + 1514249 * 2 ^ 59
def prefixEnd_1514249 : Nat := 4983230072969 + 3 ^ 40 * 1514249 * 2
def baseEnd_1514249 : Nat := 172786126131144717227467

theorem tailTrace_1514249 : CollatzResearch.WordTrace tailWord_1514249 prefixEnd_1514249 172786126131144717227467 := by
  unfold tailWord_1514249
  simp only [CollatzResearch.WordTrace]
  refine ⟨55229198291141960985065801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36819465527427973990043867 55229198291141960985065801)
  ·
    refine ⟨41421898718356470738799351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55229198291141960985065801 41421898718356470738799351)
    ·
      refine ⟨62132848077534706108199027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41421898718356470738799351 62132848077534706108199027)
      ·
        refine ⟨93199272116302059162298541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62132848077534706108199027 93199272116302059162298541)
        ·
          refine ⟨34949727043613272185861953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 93199272116302059162298541 34949727043613272185861953)
          ·
            refine ⟨26212295282709954139396465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34949727043613272185861953 26212295282709954139396465)
            ·
              refine ⟨19659221462032465604547349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26212295282709954139396465 19659221462032465604547349)
              ·
                refine ⟨921526006032771825213157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 19659221462032465604547349 921526006032771825213157)
                ·
                  refine ⟨172786126131144717227467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921526006032771825213157 172786126131144717227467)
                  ·
                    rfl

theorem cell22_1514249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6, 4].length) (baseStart_1514249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514249 prefixEnd_1514249 := by exact prefixLift 1514249
  have htrace : WordTrace (prefixWord ++ tailWord_1514249) baseStart_1514249 baseEnd_1514249 := by
    simpa [prefixWord, tailWord_1514249, baseEnd_1514249] using wordTrace_append hprefix tailTrace_1514249
  have hstable : (prefixWord ++ tailWord_1514249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514249).length < 2 ^ (prefixWord ++ tailWord_1514249).sum := by decide
  have hdescent : baseEnd_1514249 < baseStart_1514249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514277 : List Nat := [1, 3, 1, 2, 3, 1, 1, 10]
def baseStart_1514277 : Nat := 118140960795 + 1514277 * 2 ^ 59
def prefixEnd_1514277 : Nat := 4983230072969 + 3 ^ 40 * 1514277 * 2
def baseEnd_1514277 : Nat := 57596440373961267998035

theorem tailTrace_1514277 : CollatzResearch.WordTrace tailWord_1514277 prefixEnd_1514277 57596440373961267998035 := by
  unfold tailWord_1514277
  simp only [CollatzResearch.WordTrace]
  refine ⟨55230219535040521767085085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36820146356693681178056723 55230219535040521767085085)
  ·
    refine ⟨20711332325640195662656907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55230219535040521767085085 20711332325640195662656907)
    ·
      refine ⟨31066998488460293493985361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20711332325640195662656907 31066998488460293493985361)
      ·
        refine ⟨23300248866345220120489021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31066998488460293493985361 23300248866345220120489021)
        ·
          refine ⟨8737593324879457545183383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23300248866345220120489021 8737593324879457545183383)
          ·
            refine ⟨13106389987319186317775075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8737593324879457545183383 13106389987319186317775075)
            ·
              refine ⟨19659584980978779476662613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13106389987319186317775075 19659584980978779476662613)
              ·
                refine ⟨57596440373961267998035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19659584980978779476662613 57596440373961267998035)
                ·
                  rfl

theorem cell22_1514277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 10].length) (baseStart_1514277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514277 prefixEnd_1514277 := by exact prefixLift 1514277
  have htrace : WordTrace (prefixWord ++ tailWord_1514277) baseStart_1514277 baseEnd_1514277 := by
    simpa [prefixWord, tailWord_1514277, baseEnd_1514277] using wordTrace_append hprefix tailTrace_1514277
  have hstable : (prefixWord ++ tailWord_1514277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514277).length < 2 ^ (prefixWord ++ tailWord_1514277).sum := by decide
  have hdescent : baseEnd_1514277 < baseStart_1514277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514294 : List Nat := [5, 1, 2, 2, 12]
def baseStart_1514294 : Nat := 118140960795 + 1514294 * 2 ^ 59
def prefixEnd_1514294 : Nat := 4983230072969 + 3 ^ 40 * 1514294 * 2
def baseEnd_1514294 : Nat := 2133225443675181211141

theorem tailTrace_1514294 : CollatzResearch.WordTrace tailWord_1514294 prefixEnd_1514294 2133225443675181211141 := by
  unfold tailWord_1514294
  simp only [CollatzResearch.WordTrace]
  refine ⟨3451927473498683354403371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36820559717319289113635957 3451927473498683354403371)
  ·
    refine ⟨5177891210248025031605057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3451927473498683354403371 5177891210248025031605057)
    ·
      refine ⟨3883418407686018773703793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5177891210248025031605057 3883418407686018773703793)
      ·
        refine ⟨2912563805764514080277845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3883418407686018773703793 2912563805764514080277845)
        ·
          refine ⟨2133225443675181211141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2912563805764514080277845 2133225443675181211141)
          ·
            rfl

theorem cell22_1514294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 12].length) (baseStart_1514294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514294 prefixEnd_1514294 := by exact prefixLift 1514294
  have htrace : WordTrace (prefixWord ++ tailWord_1514294) baseStart_1514294 baseEnd_1514294 := by
    simpa [prefixWord, tailWord_1514294, baseEnd_1514294] using wordTrace_append hprefix tailTrace_1514294
  have hstable : (prefixWord ++ tailWord_1514294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514294).length < 2 ^ (prefixWord ++ tailWord_1514294).sum := by decide
  have hdescent : baseEnd_1514294 < baseStart_1514294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514298 : List Nat := [3, 1, 1, 1, 6, 1, 2, 2, 2, 3]
def baseStart_1514298 : Nat := 118140960795 + 1514298 * 2 ^ 59
def prefixEnd_1514298 : Nat := 4983230072969 + 3 ^ 40 * 1514298 * 2
def baseEnd_1514298 : Nat := 518375152094814357207251

theorem tailTrace_1514298 : CollatzResearch.WordTrace tailWord_1514298 prefixEnd_1514298 518375152094814357207251 := by
  unfold tailWord_1514298
  simp only [CollatzResearch.WordTrace]
  refine ⟨13807746366991110588399887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36820656978642961569066365 13807746366991110588399887)
  ·
    refine ⟨20711619550486665882599831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13807746366991110588399887 20711619550486665882599831)
    ·
      refine ⟨31067429325729998823899747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20711619550486665882599831 31067429325729998823899747)
      ·
        refine ⟨46601143988594998235849621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31067429325729998823899747 46601143988594998235849621)
        ·
          refine ⟨2184428624465390542305451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46601143988594998235849621 2184428624465390542305451)
          ·
            refine ⟨3276642936698085813458177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184428624465390542305451 3276642936698085813458177)
            ·
              refine ⟨2457482202523564360093633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3276642936698085813458177 2457482202523564360093633)
              ·
                refine ⟨1843111651892673270070225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2457482202523564360093633 1843111651892673270070225)
                ·
                  refine ⟨1382333738919504952552669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1843111651892673270070225 1382333738919504952552669)
                  ·
                    refine ⟨518375152094814357207251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1382333738919504952552669 518375152094814357207251)
                    ·
                      rfl

theorem cell22_1514298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 2, 2, 3].length) (baseStart_1514298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514298 prefixEnd_1514298 := by exact prefixLift 1514298
  have htrace : WordTrace (prefixWord ++ tailWord_1514298) baseStart_1514298 baseEnd_1514298 := by
    simpa [prefixWord, tailWord_1514298, baseEnd_1514298] using wordTrace_append hprefix tailTrace_1514298
  have hstable : (prefixWord ++ tailWord_1514298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514298).length < 2 ^ (prefixWord ++ tailWord_1514298).sum := by decide
  have hdescent : baseEnd_1514298 < baseStart_1514298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514307 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 1, 8]
def baseStart_1514307 : Nat := 118140960795 + 1514307 * 2 ^ 59
def prefixEnd_1514307 : Nat := 4983230072969 + 3 ^ 40 * 1514307 * 2
def baseEnd_1514307 : Nat := 518378232978741333732223

theorem tailTrace_1514307 : CollatzResearch.WordTrace tailWord_1514307 prefixEnd_1514307 518378232978741333732223 := by
  unfold tailWord_1514307
  simp only [CollatzResearch.WordTrace]
  refine ⟨55231313724931836890677175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36820875816621224593784783 55231313724931836890677175)
  ·
    refine ⟨82846970587397755336015763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55231313724931836890677175 82846970587397755336015763)
    ·
      refine ⟨124270455881096633004023645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82846970587397755336015763 124270455881096633004023645)
      ·
        refine ⟨46601420955411237376508867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124270455881096633004023645 46601420955411237376508867)
        ·
          refine ⟨69902131433116856064763301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46601420955411237376508867 69902131433116856064763301)
          ·
            refine ⟨13106649643709410512143119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69902131433116856064763301 13106649643709410512143119)
            ·
              refine ⟨19659974465564115768214679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13106649643709410512143119 19659974465564115768214679)
              ·
                refine ⟨29489961698346173652322019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19659974465564115768214679 29489961698346173652322019)
                ·
                  refine ⟨44234942547519260478483029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29489961698346173652322019 44234942547519260478483029)
                  ·
                    refine ⟨518378232978741333732223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 44234942547519260478483029 518378232978741333732223)
                    ·
                      rfl

theorem cell22_1514307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 8].length) (baseStart_1514307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514307 prefixEnd_1514307 := by exact prefixLift 1514307
  have htrace : WordTrace (prefixWord ++ tailWord_1514307) baseStart_1514307 baseEnd_1514307 := by
    simpa [prefixWord, tailWord_1514307, baseEnd_1514307] using wordTrace_append hprefix tailTrace_1514307
  have hstable : (prefixWord ++ tailWord_1514307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514307).length < 2 ^ (prefixWord ++ tailWord_1514307).sum := by decide
  have hdescent : baseEnd_1514307 < baseStart_1514307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514343 : List Nat := [1, 1, 5, 1, 2, 2, 1, 5, 1, 3]
def baseStart_1514343 : Nat := 118140960795 + 1514343 * 2 ^ 59
def prefixEnd_1514343 : Nat := 4983230072969 + 3 ^ 40 * 1514343 * 2
def baseEnd_1514343 : Nat := 518390556514449239832113

theorem tailTrace_1514343 : CollatzResearch.WordTrace tailWord_1514343 prefixEnd_1514343 518390556514449239832113 := by
  unfold tailWord_1514343
  simp only [CollatzResearch.WordTrace]
  refine ⟨55232626752801415038987683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36821751168534276692658455 55232626752801415038987683)
  ·
    refine ⟨82848940129202122558481525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55232626752801415038987683 82848940129202122558481525)
    ·
      refine ⟨7767088137112698989857643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82848940129202122558481525 7767088137112698989857643)
      ·
        refine ⟨11650632205669048484786465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7767088137112698989857643 11650632205669048484786465)
        ·
          refine ⟨8737974154251786363589849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11650632205669048484786465 8737974154251786363589849)
          ·
            refine ⟨6553480615688839772692387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8737974154251786363589849 6553480615688839772692387)
            ·
              refine ⟨9830220923533259659038581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6553480615688839772692387 9830220923533259659038581)
              ·
                refine ⟨921583211581243093034867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9830220923533259659038581 921583211581243093034867)
                ·
                  refine ⟨1382374817371864639552301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921583211581243093034867 1382374817371864639552301)
                  ·
                    refine ⟨518390556514449239832113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1382374817371864639552301 518390556514449239832113)
                    ·
                      rfl

theorem cell22_1514343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_1514343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514343 prefixEnd_1514343 := by exact prefixLift 1514343
  have htrace : WordTrace (prefixWord ++ tailWord_1514343) baseStart_1514343 baseEnd_1514343 := by
    simpa [prefixWord, tailWord_1514343, baseEnd_1514343] using wordTrace_append hprefix tailTrace_1514343
  have hstable : (prefixWord ++ tailWord_1514343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514343).length < 2 ^ (prefixWord ++ tailWord_1514343).sum := by decide
  have hdescent : baseEnd_1514343 < baseStart_1514343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514354 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 2, 5]
def baseStart_1514354 : Nat := 118140960795 + 1514354 * 2 ^ 59
def prefixEnd_1514354 : Nat := 4983230072969 + 3 ^ 40 * 1514354 * 2
def baseEnd_1514354 : Nat := 518394322039248877807079

theorem tailTrace_1514354 : CollatzResearch.WordTrace tailWord_1514354 prefixEnd_1514354 518394322039248877807079 := by
  unfold tailWord_1514354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13808256988940390979409529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36822018637174375945092077 13808256988940390979409529)
  ·
    refine ⟨10356192741705293234557147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13808256988940390979409529 10356192741705293234557147)
    ·
      refine ⟨15534289112557939851835721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10356192741705293234557147 15534289112557939851835721)
      ·
        refine ⟨11650716834418454888876791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15534289112557939851835721 11650716834418454888876791)
        ·
          refine ⟨17476075251627682333315187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11650716834418454888876791 17476075251627682333315187)
          ·
            refine ⟨26214112877441523499972781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17476075251627682333315187 26214112877441523499972781)
            ·
              refine ⟨9830292329040571312489793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26214112877441523499972781 9830292329040571312489793)
              ·
                refine ⟨7372719246780428484367345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9830292329040571312489793 7372719246780428484367345)
                ·
                  refine ⟨5529539435085321363275509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7372719246780428484367345 5529539435085321363275509)
                  ·
                    refine ⟨518394322039248877807079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5529539435085321363275509 518394322039248877807079)
                    ·
                      rfl

theorem cell22_1514354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 2, 5].length) (baseStart_1514354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514354 prefixEnd_1514354 := by exact prefixLift 1514354
  have htrace : WordTrace (prefixWord ++ tailWord_1514354) baseStart_1514354 baseEnd_1514354 := by
    simpa [prefixWord, tailWord_1514354, baseEnd_1514354] using wordTrace_append hprefix tailTrace_1514354
  have hstable : (prefixWord ++ tailWord_1514354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514354).length < 2 ^ (prefixWord ++ tailWord_1514354).sum := by decide
  have hdescent : baseEnd_1514354 < baseStart_1514354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514469 : List Nat := [1, 3, 1, 6, 2, 1, 2, 2, 4]
def baseStart_1514469 : Nat := 118140960795 + 1514469 * 2 ^ 59
def prefixEnd_1514469 : Nat := 4983230072969 + 3 ^ 40 * 1514469 * 2
def baseEnd_1514469 : Nat := 172811229629808970393909

theorem tailTrace_1514469 : CollatzResearch.WordTrace tailWord_1514469 prefixEnd_1514469 172811229629808970393909 := by
  unfold tailWord_1514469
  simp only [CollatzResearch.WordTrace]
  refine ⟨55237222350344938558074461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36824814900229959038716307 55237222350344938558074461)
  ·
    refine ⟨20713958381379351959277923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55237222350344938558074461 20713958381379351959277923)
    ·
      refine ⟨31070937572069027938916885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20713958381379351959277923 31070937572069027938916885)
      ·
        refine ⟨1456450198690735684636729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31070937572069027938916885 1456450198690735684636729)
        ·
          refine ⟨1092337649018051763477547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1456450198690735684636729 1092337649018051763477547)
          ·
            refine ⟨1638506473527077645216321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092337649018051763477547 1638506473527077645216321)
            ·
              refine ⟨1228879855145308233912241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1638506473527077645216321 1228879855145308233912241)
              ·
                refine ⟨921659891358981175434181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1228879855145308233912241 921659891358981175434181)
                ·
                  refine ⟨172811229629808970393909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921659891358981175434181 172811229629808970393909)
                  ·
                    rfl

theorem cell22_1514469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_1514469 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514469 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514469 prefixEnd_1514469 := by exact prefixLift 1514469
  have htrace : WordTrace (prefixWord ++ tailWord_1514469) baseStart_1514469 baseEnd_1514469 := by
    simpa [prefixWord, tailWord_1514469, baseEnd_1514469] using wordTrace_append hprefix tailTrace_1514469
  have hstable : (prefixWord ++ tailWord_1514469).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514469).length < 2 ^ (prefixWord ++ tailWord_1514469).sum := by decide
  have hdescent : baseEnd_1514469 < baseStart_1514469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514484 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_1514484 : Nat := 118140960795 + 1514484 * 2 ^ 59
def prefixEnd_1514484 : Nat := 4983230072969 + 3 ^ 40 * 1514484 * 2
def baseEnd_1514484 : Nat := 518438823695971872056681

theorem tailTrace_1514484 : CollatzResearch.WordTrace tailWord_1514484 prefixEnd_1514484 518438823695971872056681 := by
  unfold tailWord_1514484
  simp only [CollatzResearch.WordTrace]
  refine ⟨27618884722645298059935253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36825179630193730746580337 27618884722645298059935253)
  ·
    refine ⟨1294635221373998346559465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 27618884722645298059935253 1294635221373998346559465)
    ·
      refine ⟨970976416030498759919599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1294635221373998346559465 970976416030498759919599)
      ·
        refine ⟨1456464624045748139879399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 970976416030498759919599 1456464624045748139879399)
        ·
          refine ⟨2184696936068622209819099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456464624045748139879399 2184696936068622209819099)
          ·
            refine ⟨3277045404102933314728649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184696936068622209819099 3277045404102933314728649)
            ·
              refine ⟨2457784053077199986046487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3277045404102933314728649 2457784053077199986046487)
              ·
                refine ⟨3686676079615799979069731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2457784053077199986046487 3686676079615799979069731)
                ·
                  refine ⟨5530014119423699968604597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3686676079615799979069731 5530014119423699968604597)
                  ·
                    refine ⟨518438823695971872056681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5530014119423699968604597 518438823695971872056681)
                    ·
                      rfl

theorem cell22_1514484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_1514484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514484 prefixEnd_1514484 := by exact prefixLift 1514484
  have htrace : WordTrace (prefixWord ++ tailWord_1514484) baseStart_1514484 baseEnd_1514484 := by
    simpa [prefixWord, tailWord_1514484, baseEnd_1514484] using wordTrace_append hprefix tailTrace_1514484
  have hstable : (prefixWord ++ tailWord_1514484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514484).length < 2 ^ (prefixWord ++ tailWord_1514484).sum := by decide
  have hdescent : baseEnd_1514484 < baseStart_1514484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514525 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 5]
def baseStart_1514525 : Nat := 118140960795 + 1514525 * 2 ^ 59
def prefixEnd_1514525 : Nat := 4983230072969 + 3 ^ 40 * 1514525 * 2
def baseEnd_1514525 : Nat := 172817619611287143927185

theorem tailTrace_1514525 : CollatzResearch.WordTrace tailWord_1514525 prefixEnd_1514525 172817619611287143927185 := by
  unfold tailWord_1514525
  simp only [CollatzResearch.WordTrace]
  refine ⟨55239264838142060122113029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36826176558761373414742019 55239264838142060122113029)
  ·
    refine ⟨10357362157151636272896193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55239264838142060122113029 10357362157151636272896193)
    ·
      refine ⟨7768021617863727204672145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10357362157151636272896193 7768021617863727204672145)
      ·
        refine ⟨5826016213397795403504109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7768021617863727204672145 5826016213397795403504109)
        ·
          refine ⟨2184756080024173276314041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5826016213397795403504109 2184756080024173276314041)
          ·
            refine ⟨1638567060018129957235531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2184756080024173276314041 1638567060018129957235531)
            ·
              refine ⟨2457850590027194935853297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638567060018129957235531 2457850590027194935853297)
              ·
                refine ⟨1843387942520396201889973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2457850590027194935853297 1843387942520396201889973)
                ·
                  refine ⟨172817619611287143927185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1843387942520396201889973 172817619611287143927185)
                  ·
                    rfl

theorem cell22_1514525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_1514525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514525 prefixEnd_1514525 := by exact prefixLift 1514525
  have htrace : WordTrace (prefixWord ++ tailWord_1514525) baseStart_1514525 baseEnd_1514525 := by
    simpa [prefixWord, tailWord_1514525, baseEnd_1514525] using wordTrace_append hprefix tailTrace_1514525
  have hstable : (prefixWord ++ tailWord_1514525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514525).length < 2 ^ (prefixWord ++ tailWord_1514525).sum := by decide
  have hdescent : baseEnd_1514525 < baseStart_1514525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514602 : List Nat := [3, 1, 3, 2, 2, 1, 4, 1, 2, 3]
def baseStart_1514602 : Nat := 118140960795 + 1514602 * 2 ^ 59
def prefixEnd_1514602 : Nat := 4983230072969 + 3 ^ 40 * 1514602 * 2
def baseEnd_1514602 : Nat := 518479217507458897606319

theorem tailTrace_1514602 : CollatzResearch.WordTrace tailWord_1514602 prefixEnd_1514602 518479217507458897606319 := by
  unfold tailWord_1514602
  simp only [CollatzResearch.WordTrace]
  refine ⟨13810518314715775568166515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36828048839242068181777373 13810518314715775568166515)
  ·
    refine ⟨20715777472073663352249773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13810518314715775568166515 20715777472073663352249773)
    ·
      refine ⟨7768416552027623757093665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20715777472073663352249773 7768416552027623757093665)
      ·
        refine ⟨5826312414020717817820249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7768416552027623757093665 5826312414020717817820249)
        ·
          refine ⟨4369734310515538363365187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5826312414020717817820249 4369734310515538363365187)
          ·
            refine ⟨6554601465773307545047781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4369734310515538363365187 6554601465773307545047781)
            ·
              refine ⟨1228987774832495164696459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6554601465773307545047781 1228987774832495164696459)
              ·
                refine ⟨1843481662248742747044689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1228987774832495164696459 1843481662248742747044689)
                ·
                  refine ⟨1382611246686557060283517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1843481662248742747044689 1382611246686557060283517)
                  ·
                    refine ⟨518479217507458897606319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1382611246686557060283517 518479217507458897606319)
                    ·
                      rfl

theorem cell22_1514602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 2, 3].length) (baseStart_1514602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514602 prefixEnd_1514602 := by exact prefixLift 1514602
  have htrace : WordTrace (prefixWord ++ tailWord_1514602) baseStart_1514602 baseEnd_1514602 := by
    simpa [prefixWord, tailWord_1514602, baseEnd_1514602] using wordTrace_append hprefix tailTrace_1514602
  have hstable : (prefixWord ++ tailWord_1514602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514602).length < 2 ^ (prefixWord ++ tailWord_1514602).sum := by decide
  have hdescent : baseEnd_1514602 < baseStart_1514602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514647 : List Nat := [1, 1, 3, 3, 3, 2, 1, 4, 1, 3]
def baseStart_1514647 : Nat := 118140960795 + 1514647 * 2 ^ 59
def prefixEnd_1514647 : Nat := 4983230072969 + 3 ^ 40 * 1514647 * 2
def baseEnd_1514647 : Nat := 518494621927093780231181

theorem tailTrace_1514647 : CollatzResearch.WordTrace tailWord_1514647 prefixEnd_1514647 518494621927093780231181 := by
  unfold tailWord_1514647
  simp only [CollatzResearch.WordTrace]
  refine ⟨55243714543700074958054195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36829143029133383305369463 55243714543700074958054195)
  ·
    refine ⟨82865571815550112437081293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55243714543700074958054195 82865571815550112437081293)
    ·
      refine ⟨31074589430831292163905485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82865571815550112437081293 31074589430831292163905485)
      ·
        refine ⟨11652971036561734561464557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31074589430831292163905485 11652971036561734561464557)
        ·
          refine ⟨4369864138710650460549209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11652971036561734561464557 4369864138710650460549209)
          ·
            refine ⟨3277398104032987845411907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4369864138710650460549209 3277398104032987845411907)
            ·
              refine ⟨4916097156049481768117861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277398104032987845411907 4916097156049481768117861)
              ·
                refine ⟨921768216759277831522099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4916097156049481768117861 921768216759277831522099)
                ·
                  refine ⟨1382652325138916747283149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 921768216759277831522099 1382652325138916747283149)
                  ·
                    refine ⟨518494621927093780231181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1382652325138916747283149 518494621927093780231181)
                    ·
                      rfl

theorem cell22_1514647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 1, 3].length) (baseStart_1514647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514647 prefixEnd_1514647 := by exact prefixLift 1514647
  have htrace : WordTrace (prefixWord ++ tailWord_1514647) baseStart_1514647 baseEnd_1514647 := by
    simpa [prefixWord, tailWord_1514647, baseEnd_1514647] using wordTrace_append hprefix tailTrace_1514647
  have hstable : (prefixWord ++ tailWord_1514647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514647).length < 2 ^ (prefixWord ++ tailWord_1514647).sum := by decide
  have hdescent : baseEnd_1514647 < baseStart_1514647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514671 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 8]
def baseStart_1514671 : Nat := 118140960795 + 1514671 * 2 ^ 59
def prefixEnd_1514671 : Nat := 4983230072969 + 3 ^ 40 * 1514671 * 2
def baseEnd_1514671 : Nat := 172834279205855239210369

theorem tailTrace_1514671 : CollatzResearch.WordTrace tailWord_1514671 prefixEnd_1514671 172834279205855239210369 := by
  unfold tailWord_1514671
  simp only [CollatzResearch.WordTrace]
  refine ⟨55244589895613127056927867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36829726597075418037951911 55244589895613127056927867)
  ·
    refine ⟨82866884843419690585391801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55244589895613127056927867 82866884843419690585391801)
    ·
      refine ⟨62150163632564767939043851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82866884843419690585391801 62150163632564767939043851)
      ·
        refine ⟨93225245448847151908565777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62150163632564767939043851 93225245448847151908565777)
        ·
          refine ⟨69918934086635363931424333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93225245448847151908565777 69918934086635363931424333)
          ·
            refine ⟨26219600282488261474284125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69918934086635363931424333 26219600282488261474284125)
            ·
              refine ⟨9832350105933098052856547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26219600282488261474284125 9832350105933098052856547)
              ·
                refine ⟨14748525158899647079284821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9832350105933098052856547 14748525158899647079284821)
                ·
                  refine ⟨172834279205855239210369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14748525158899647079284821 172834279205855239210369)
                  ·
                    rfl

theorem cell22_1514671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 8].length) (baseStart_1514671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514671 prefixEnd_1514671 := by exact prefixLift 1514671
  have htrace : WordTrace (prefixWord ++ tailWord_1514671) baseStart_1514671 baseEnd_1514671 := by
    simpa [prefixWord, tailWord_1514671, baseEnd_1514671] using wordTrace_append hprefix tailTrace_1514671
  have hstable : (prefixWord ++ tailWord_1514671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514671).length < 2 ^ (prefixWord ++ tailWord_1514671).sum := by decide
  have hdescent : baseEnd_1514671 < baseStart_1514671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514694 : List Nat := [6, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_1514694 : Nat := 118140960795 + 1514694 * 2 ^ 59
def prefixEnd_1514694 : Nat := 4983230072969 + 3 ^ 40 * 1514694 * 2
def baseEnd_1514694 : Nat := 172836903662533774768679

theorem tailTrace_1514694 : CollatzResearch.WordTrace tailWord_1514694 prefixEnd_1514694 172836903662533774768679 := by
  unfold tailWord_1514694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1726419649204056312031723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36830285849686534656676757 1726419649204056312031723)
  ·
    refine ⟨2589629473806084468047585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1726419649204056312031723 2589629473806084468047585)
    ·
      refine ⟨1942222105354563351035689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2589629473806084468047585 1942222105354563351035689)
      ·
        refine ⟨1456666579015922513276767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1942222105354563351035689 1456666579015922513276767)
        ·
          refine ⟨2184999868523883769915151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1456666579015922513276767 2184999868523883769915151)
          ·
            refine ⟨3277499802785825654872727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2184999868523883769915151 3277499802785825654872727)
            ·
              refine ⟨4916249704178738482309091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3277499802785825654872727 4916249704178738482309091)
              ·
                refine ⟨7374374556268107723463637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4916249704178738482309091 7374374556268107723463637)
                ·
                  refine ⟨172836903662533774768679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7374374556268107723463637 172836903662533774768679)
                  ·
                    rfl

theorem cell22_1514694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_1514694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514694 prefixEnd_1514694 := by exact prefixLift 1514694
  have htrace : WordTrace (prefixWord ++ tailWord_1514694) baseStart_1514694 baseEnd_1514694 := by
    simpa [prefixWord, tailWord_1514694, baseEnd_1514694] using wordTrace_append hprefix tailTrace_1514694
  have hstable : (prefixWord ++ tailWord_1514694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514694).length < 2 ^ (prefixWord ++ tailWord_1514694).sum := by decide
  have hdescent : baseEnd_1514694 < baseStart_1514694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514720 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 1, 5]
def baseStart_1514720 : Nat := 118140960795 + 1514720 * 2 ^ 59
def prefixEnd_1514720 : Nat := 4983230072969 + 3 ^ 40 * 1514720 * 2
def baseEnd_1514720 : Nat := 518519611318945923155957

theorem tailTrace_1514720 : CollatzResearch.WordTrace tailWord_1514720 prefixEnd_1514720 518519611318945923155957 := by
  unfold tailWord_1514720
  simp only [CollatzResearch.WordTrace]
  refine ⟨27623188536217804212730807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36830918048290405616974409 27623188536217804212730807)
  ·
    refine ⟨41434782804326706319096211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27623188536217804212730807 41434782804326706319096211)
    ·
      refine ⟨62152174206490059478644317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41434782804326706319096211 62152174206490059478644317)
      ·
        refine ⟨23307065327433772304491619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62152174206490059478644317 23307065327433772304491619)
        ·
          refine ⟨34960597991150658456737429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23307065327433772304491619 34960597991150658456737429)
          ·
            refine ⟨1638778030835187115159567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 34960597991150658456737429 1638778030835187115159567)
            ·
              refine ⟨2458167046252780672739351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638778030835187115159567 2458167046252780672739351)
              ·
                refine ⟨3687250569379171009109027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458167046252780672739351 3687250569379171009109027)
                ·
                  refine ⟨5530875854068756513663541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687250569379171009109027 5530875854068756513663541)
                  ·
                    refine ⟨518519611318945923155957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5530875854068756513663541 518519611318945923155957)
                    ·
                      rfl

theorem cell22_1514720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 1, 5].length) (baseStart_1514720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514720 prefixEnd_1514720 := by exact prefixLift 1514720
  have htrace : WordTrace (prefixWord ++ tailWord_1514720) baseStart_1514720 baseEnd_1514720 := by
    simpa [prefixWord, tailWord_1514720, baseEnd_1514720] using wordTrace_append hprefix tailTrace_1514720
  have hstable : (prefixWord ++ tailWord_1514720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514720).length < 2 ^ (prefixWord ++ tailWord_1514720).sum := by decide
  have hdescent : baseEnd_1514720 < baseStart_1514720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514750 : List Nat := [4, 2, 2, 1, 1, 4, 8]
def baseStart_1514750 : Nat := 118140960795 + 1514750 * 2 ^ 59
def prefixEnd_1514750 : Nat := 4983230072969 + 3 ^ 40 * 1514750 * 2
def baseEnd_1514750 : Nat := 19204810404890216477995

theorem tailTrace_1514750 : CollatzResearch.WordTrace tailWord_1514750 prefixEnd_1514750 19204810404890216477995 := by
  unfold tailWord_1514750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6905933907790865443631713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36831647508217949032702469 6905933907790865443631713)
  ·
    refine ⟨5179450430843149082723785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6905933907790865443631713 5179450430843149082723785)
    ·
      refine ⟨3884587823132361812042839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5179450430843149082723785 3884587823132361812042839)
      ·
        refine ⟨5826881734698542718064259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3884587823132361812042839 5826881734698542718064259)
        ·
          refine ⟨8740322602047814077096389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5826881734698542718064259 8740322602047814077096389)
          ·
            refine ⟨1638810487883965139455573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8740322602047814077096389 1638810487883965139455573)
            ·
              refine ⟨19204810404890216477995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1638810487883965139455573 19204810404890216477995)
              ·
                rfl

theorem cell22_1514750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 8].length) (baseStart_1514750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514750 prefixEnd_1514750 := by exact prefixLift 1514750
  have htrace : WordTrace (prefixWord ++ tailWord_1514750) baseStart_1514750 baseEnd_1514750 := by
    simpa [prefixWord, tailWord_1514750, baseEnd_1514750] using wordTrace_append hprefix tailTrace_1514750
  have hstable : (prefixWord ++ tailWord_1514750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514750).length < 2 ^ (prefixWord ++ tailWord_1514750).sum := by decide
  have hdescent : baseEnd_1514750 < baseStart_1514750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514889 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 1, 5]
def baseStart_1514889 : Nat := 118140960795 + 1514889 * 2 ^ 59
def prefixEnd_1514889 : Nat := 4983230072969 + 3 ^ 40 * 1514889 * 2
def baseEnd_1514889 : Nat := 518577463472685815680439

theorem tailTrace_1514889 : CollatzResearch.WordTrace tailWord_1514889 prefixEnd_1514889 518577463472685815680439 := by
  unfold tailWord_1514889
  simp only [CollatzResearch.WordTrace]
  refine ⟨55252541008823350288363721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36835027339215566858909147 55252541008823350288363721)
  ·
    refine ⟨41439405756617512716272791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55252541008823350288363721 41439405756617512716272791)
    ·
      refine ⟨62159108634926269074409187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41439405756617512716272791 62159108634926269074409187)
      ·
        refine ⟨93238662952389403611613781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62159108634926269074409187 93238662952389403611613781)
        ·
          refine ⟨1092640581473313323573599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 93238662952389403611613781 1092640581473313323573599)
          ·
            refine ⟨1638960872209969985360399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092640581473313323573599 1638960872209969985360399)
            ·
              refine ⟨2458441308314954978040599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638960872209969985360399 2458441308314954978040599)
              ·
                refine ⟨3687661962472432467060899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458441308314954978040599 3687661962472432467060899)
                ·
                  refine ⟨5531492943708648700591349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3687661962472432467060899 5531492943708648700591349)
                  ·
                    refine ⟨518577463472685815680439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5531492943708648700591349 518577463472685815680439)
                    ·
                      rfl

theorem cell22_1514889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 1, 5].length) (baseStart_1514889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514889 prefixEnd_1514889 := by exact prefixLift 1514889
  have htrace : WordTrace (prefixWord ++ tailWord_1514889) baseStart_1514889 baseEnd_1514889 := by
    simpa [prefixWord, tailWord_1514889, baseEnd_1514889] using wordTrace_append hprefix tailTrace_1514889
  have hstable : (prefixWord ++ tailWord_1514889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514889).length < 2 ^ (prefixWord ++ tailWord_1514889).sum := by decide
  have hdescent : baseEnd_1514889 < baseStart_1514889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514908 : List Nat := [2, 2, 3, 4, 2, 1, 1, 3, 4]
def baseStart_1514908 : Nat := 118140960795 + 1514908 * 2 ^ 59
def prefixEnd_1514908 : Nat := 4983230072969 + 3 ^ 40 * 1514908 * 2
def baseEnd_1514908 : Nat := 172861322520325366485127

theorem tailTrace_1514908 : CollatzResearch.WordTrace tailWord_1514908 prefixEnd_1514908 172861322520325366485127 := by
  unfold tailWord_1514908
  simp only [CollatzResearch.WordTrace]
  refine ⟨27626616997877258266652689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36835489330503011022203585 27626616997877258266652689)
  ·
    refine ⟨20719962748407943699989517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27626616997877258266652689 20719962748407943699989517)
    ·
      refine ⟨7769986030652978887496069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20719962748407943699989517 7769986030652978887496069)
      ·
        refine ⟨1456872380747433541405513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7769986030652978887496069 1456872380747433541405513)
        ·
          refine ⟨1092654285560575156054135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1456872380747433541405513 1092654285560575156054135)
          ·
            refine ⟨1638981428340862734081203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092654285560575156054135 1638981428340862734081203)
            ·
              refine ⟨2458472142511294101121805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1638981428340862734081203 2458472142511294101121805)
              ·
                refine ⟨921927053441735287920677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2458472142511294101121805 921927053441735287920677)
                ·
                  refine ⟨172861322520325366485127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 921927053441735287920677 172861322520325366485127)
                  ·
                    rfl

theorem cell22_1514908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 4].length) (baseStart_1514908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514908 prefixEnd_1514908 := by exact prefixLift 1514908
  have htrace : WordTrace (prefixWord ++ tailWord_1514908) baseStart_1514908 baseEnd_1514908 := by
    simpa [prefixWord, tailWord_1514908, baseEnd_1514908] using wordTrace_append hprefix tailTrace_1514908
  have hstable : (prefixWord ++ tailWord_1514908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514908).length < 2 ^ (prefixWord ++ tailWord_1514908).sum := by decide
  have hdescent : baseEnd_1514908 < baseStart_1514908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514947 : List Nat := [1, 1, 1, 3, 1, 1, 8, 1, 5]
def baseStart_1514947 : Nat := 118140960795 + 1514947 * 2 ^ 59
def prefixEnd_1514947 : Nat := 4983230072969 + 3 ^ 40 * 1514947 * 2
def baseEnd_1514947 : Nat := 172865772685997665910087

theorem tailTrace_1514947 : CollatzResearch.WordTrace tailWord_1514947 prefixEnd_1514947 172865772685997665910087 := by
  unfold tailWord_1514947
  simp only [CollatzResearch.WordTrace]
  refine ⟨55254656442613226193975095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36836437628408817462650063 55254656442613226193975095)
  ·
    refine ⟨82881984663919839290962643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55254656442613226193975095 82881984663919839290962643)
    ·
      refine ⟨124322976995879758936443965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82881984663919839290962643 124322976995879758936443965)
      ·
        refine ⟨46621116373454909601166487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124322976995879758936443965 46621116373454909601166487)
        ·
          refine ⟨69931674560182364401749731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46621116373454909601166487 69931674560182364401749731)
          ·
            refine ⟨104897511840273546602624597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69931674560182364401749731 104897511840273546602624597)
            ·
              refine ⟨1229267716878205624249507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 104897511840273546602624597 1229267716878205624249507)
              ·
                refine ⟨1843901575317308436374261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229267716878205624249507 1843901575317308436374261)
                ·
                  refine ⟨172865772685997665910087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1843901575317308436374261 172865772685997665910087)
                  ·
                    rfl

theorem cell22_1514947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 5].length) (baseStart_1514947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514947 prefixEnd_1514947 := by exact prefixLift 1514947
  have htrace : WordTrace (prefixWord ++ tailWord_1514947) baseStart_1514947 baseEnd_1514947 := by
    simpa [prefixWord, tailWord_1514947, baseEnd_1514947] using wordTrace_append hprefix tailTrace_1514947
  have hstable : (prefixWord ++ tailWord_1514947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514947).length < 2 ^ (prefixWord ++ tailWord_1514947).sum := by decide
  have hdescent : baseEnd_1514947 < baseStart_1514947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1514960 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 3, 4]
def baseStart_1514960 : Nat := 118140960795 + 1514960 * 2 ^ 59
def prefixEnd_1514960 : Nat := 4983230072969 + 3 ^ 40 * 1514960 * 2
def baseEnd_1514960 : Nat := 518601768223665297155221

theorem tailTrace_1514960 : CollatzResearch.WordTrace tailWord_1514960 prefixEnd_1514960 518601768223665297155221 := by
  unfold tailWord_1514960
  simp only [CollatzResearch.WordTrace]
  refine ⟨27627565295783064707099167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36836753727710752942798889 27627565295783064707099167)
  ·
    refine ⟨41441347943674597060648751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27627565295783064707099167 41441347943674597060648751)
    ·
      refine ⟨62162021915511895590973127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41441347943674597060648751 62162021915511895590973127)
      ·
        refine ⟨93243032873267843386459691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62162021915511895590973127 93243032873267843386459691)
        ·
          refine ⟨139864549309901765079689537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93243032873267843386459691 139864549309901765079689537)
          ·
            refine ⟨104898411982426323809767153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139864549309901765079689537 104898411982426323809767153)
            ·
              refine ⟨78673808986819742857325365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104898411982426323809767153 78673808986819742857325365)
              ·
                refine ⟨7375669592514350892874253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78673808986819742857325365 7375669592514350892874253)
                ·
                  refine ⟨2765876097192881584827845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7375669592514350892874253 2765876097192881584827845)
                  ·
                    refine ⟨518601768223665297155221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2765876097192881584827845 518601768223665297155221)
                    ·
                      rfl

theorem cell22_1514960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_1514960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1514960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1514960 prefixEnd_1514960 := by exact prefixLift 1514960
  have htrace : WordTrace (prefixWord ++ tailWord_1514960) baseStart_1514960 baseEnd_1514960 := by
    simpa [prefixWord, tailWord_1514960, baseEnd_1514960] using wordTrace_append hprefix tailTrace_1514960
  have hstable : (prefixWord ++ tailWord_1514960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1514960).length < 2 ^ (prefixWord ++ tailWord_1514960).sum := by decide
  have hdescent : baseEnd_1514960 < baseStart_1514960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1514960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515041 : List Nat := [1, 2, 3, 2, 2, 4, 1, 2, 2, 3]
def baseStart_1515041 : Nat := 118140960795 + 1515041 * 2 ^ 59
def prefixEnd_1515041 : Nat := 4983230072969 + 3 ^ 40 * 1515041 * 2
def baseEnd_1515041 : Nat := 518629496179008085879973

theorem tailTrace_1515041 : CollatzResearch.WordTrace tailWord_1515041 prefixEnd_1515041 518629496179008085879973 := by
  unfold tailWord_1515041
  simp only [CollatzResearch.WordTrace]
  refine ⟨55258084904272680247896977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36838723269515120165264651 55258084904272680247896977)
  ·
    refine ⟨41443563678204510185922733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55258084904272680247896977 41443563678204510185922733)
    ·
      refine ⟨15541336379326691319721025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41443563678204510185922733 15541336379326691319721025)
      ·
        refine ⟨11656002284495018489790769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15541336379326691319721025 11656002284495018489790769)
        ·
          refine ⟨8742001713371263867343077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11656002284495018489790769 8742001713371263867343077)
          ·
            refine ⟨1639125321257111975126827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8742001713371263867343077 1639125321257111975126827)
            ·
              refine ⟨2458687981885667962690241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639125321257111975126827 2458687981885667962690241)
              ·
                refine ⟨1844015986414250972017681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458687981885667962690241 1844015986414250972017681)
                ·
                  refine ⟨1383011989810688229013261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1844015986414250972017681 1383011989810688229013261)
                  ·
                    refine ⟨518629496179008085879973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1383011989810688229013261 518629496179008085879973)
                    ·
                      rfl

theorem cell22_1515041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_1515041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515041 prefixEnd_1515041 := by exact prefixLift 1515041
  have htrace : WordTrace (prefixWord ++ tailWord_1515041) baseStart_1515041 baseEnd_1515041 := by
    simpa [prefixWord, tailWord_1515041, baseEnd_1515041] using wordTrace_append hprefix tailTrace_1515041
  have hstable : (prefixWord ++ tailWord_1515041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515041).length < 2 ^ (prefixWord ++ tailWord_1515041).sum := by decide
  have hdescent : baseEnd_1515041 < baseStart_1515041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515191 : List Nat := [1, 1, 3, 1, 5, 3, 1, 1, 2, 4]
def baseStart_1515191 : Nat := 118140960795 + 1515191 * 2 ^ 59
def prefixEnd_1515191 : Nat := 4983230072969 + 3 ^ 40 * 1515191 * 2
def baseEnd_1515191 : Nat := 518680844244457694629513

theorem tailTrace_1515191 : CollatzResearch.WordTrace tailWord_1515191 prefixEnd_1515191 518680844244457694629513 := by
  unfold tailWord_1515191
  simp only [CollatzResearch.WordTrace]
  refine ⟨55263555853729255865857427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36842370569152837243904951 55263555853729255865857427)
  ·
    refine ⟨82895333780593883798786141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55263555853729255865857427 82895333780593883798786141)
    ·
      refine ⟨31085750167722706424544803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82895333780593883798786141 31085750167722706424544803)
      ·
        refine ⟨46628625251584059636817205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31085750167722706424544803 46628625251584059636817205)
        ·
          refine ⟨4371433617336005590951613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46628625251584059636817205 4371433617336005590951613)
          ·
            refine ⟨1639287606501002096606855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4371433617336005590951613 1639287606501002096606855)
            ·
              refine ⟨2458931409751503144910283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639287606501002096606855 2458931409751503144910283)
              ·
                refine ⟨3688397114627254717365425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2458931409751503144910283 3688397114627254717365425)
                ·
                  refine ⟨2766297835970441038024069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3688397114627254717365425 2766297835970441038024069)
                  ·
                    refine ⟨518680844244457694629513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2766297835970441038024069 518680844244457694629513)
                    ·
                      rfl

theorem cell22_1515191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 1, 2, 4].length) (baseStart_1515191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515191 prefixEnd_1515191 := by exact prefixLift 1515191
  have htrace : WordTrace (prefixWord ++ tailWord_1515191) baseStart_1515191 baseEnd_1515191 := by
    simpa [prefixWord, tailWord_1515191, baseEnd_1515191] using wordTrace_append hprefix tailTrace_1515191
  have hstable : (prefixWord ++ tailWord_1515191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515191).length < 2 ^ (prefixWord ++ tailWord_1515191).sum := by decide
  have hdescent : baseEnd_1515191 < baseStart_1515191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515210 : List Nat := [3, 1, 2, 1, 6, 1, 1, 2, 2, 3]
def baseStart_1515210 : Nat := 118140960795 + 1515210 * 2 ^ 59
def prefixEnd_1515210 : Nat := 4983230072969 + 3 ^ 40 * 1515210 * 2
def baseEnd_1515210 : Nat := 518687348332747978404455

theorem tailTrace_1515210 : CollatzResearch.WordTrace tailWord_1515210 prefixEnd_1515210 518687348332747978404455 := by
  unfold tailWord_1515210
  simp only [CollatzResearch.WordTrace]
  refine ⟨13816062210165105527699771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36842832560440281407199389 13816062210165105527699771)
  ·
    refine ⟨20724093315247658291549657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13816062210165105527699771 20724093315247658291549657)
    ·
      refine ⟨15543069986435743718662243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20724093315247658291549657 15543069986435743718662243)
      ·
        refine ⟨23314604979653615577993365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15543069986435743718662243 23314604979653615577993365)
        ·
          refine ⟨1092872108421263230218439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 23314604979653615577993365 1092872108421263230218439)
          ·
            refine ⟨1639308162631894845327659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1092872108421263230218439 1639308162631894845327659)
            ·
              refine ⟨2458962243947842267991489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639308162631894845327659 2458962243947842267991489)
              ·
                refine ⟨1844221682960881700993617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2458962243947842267991489 1844221682960881700993617)
                ·
                  refine ⟨1383166262220661275745213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1844221682960881700993617 1383166262220661275745213)
                  ·
                    refine ⟨518687348332747978404455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1383166262220661275745213 518687348332747978404455)
                    ·
                      rfl

theorem cell22_1515210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 2, 2, 3].length) (baseStart_1515210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515210 prefixEnd_1515210 := by exact prefixLift 1515210
  have htrace : WordTrace (prefixWord ++ tailWord_1515210) baseStart_1515210 baseEnd_1515210 := by
    simpa [prefixWord, tailWord_1515210, baseEnd_1515210] using wordTrace_append hprefix tailTrace_1515210
  have hstable : (prefixWord ++ tailWord_1515210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515210).length < 2 ^ (prefixWord ++ tailWord_1515210).sum := by decide
  have hdescent : baseEnd_1515210 < baseStart_1515210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515354 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 2, 6]
def baseStart_1515354 : Nat := 118140960795 + 1515354 * 2 ^ 59
def prefixEnd_1515354 : Nat := 4983230072969 + 3 ^ 40 * 1515354 * 2
def baseEnd_1515354 : Nat := 518736642475579602804013

theorem tailTrace_1515354 : CollatzResearch.WordTrace tailWord_1515354 prefixEnd_1515354 518736642475579602804013 := by
  unfold tailWord_1515354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817375238034683676010279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36846333968092489802694077 13817375238034683676010279)
  ·
    refine ⟨20726062857052025514015419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13817375238034683676010279 20726062857052025514015419)
    ·
      refine ⟨31089094285578038271023129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20726062857052025514015419 31089094285578038271023129)
      ·
        refine ⟨23316820714183528703267347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31089094285578038271023129 23316820714183528703267347)
        ·
          refine ⟨34975231071275293054901021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23316820714183528703267347 34975231071275293054901021)
          ·
            refine ⟨13115711651728234895587883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34975231071275293054901021 13115711651728234895587883)
            ·
              refine ⟨19673567477592352343381825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13115711651728234895587883 19673567477592352343381825)
              ·
                refine ⟨14755175608194264257536369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19673567477592352343381825 14755175608194264257536369)
                ·
                  refine ⟨11066381706145698193152277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14755175608194264257536369 11066381706145698193152277)
                  ·
                    refine ⟨518736642475579602804013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11066381706145698193152277 518736642475579602804013)
                    ·
                      rfl

theorem cell22_1515354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 2, 6].length) (baseStart_1515354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515354 prefixEnd_1515354 := by exact prefixLift 1515354
  have htrace : WordTrace (prefixWord ++ tailWord_1515354) baseStart_1515354 baseEnd_1515354 := by
    simpa [prefixWord, tailWord_1515354, baseEnd_1515354] using wordTrace_append hprefix tailTrace_1515354
  have hstable : (prefixWord ++ tailWord_1515354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515354).length < 2 ^ (prefixWord ++ tailWord_1515354).sum := by decide
  have hdescent : baseEnd_1515354 < baseStart_1515354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515386 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 5]
def baseStart_1515386 : Nat := 118140960795 + 1515386 * 2 ^ 59
def prefixEnd_1515386 : Nat := 4983230072969 + 3 ^ 40 * 1515386 * 2
def baseEnd_1515386 : Nat := 172915865576514062001305

theorem tailTrace_1515386 : CollatzResearch.WordTrace tailWord_1515386 prefixEnd_1515386 172915865576514062001305 := by
  unfold tailWord_1515386
  simp only [CollatzResearch.WordTrace]
  refine ⟨13817667022005701042301503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36847112058681869446137341 13817667022005701042301503)
  ·
    refine ⟨20726500533008551563452255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13817667022005701042301503 20726500533008551563452255)
    ·
      refine ⟨31089750799512827345178383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20726500533008551563452255 31089750799512827345178383)
      ·
        refine ⟨46634626199269241017767575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31089750799512827345178383 46634626199269241017767575)
        ·
          refine ⟨69951939298903861526651363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46634626199269241017767575 69951939298903861526651363)
          ·
            refine ⟨104927908948355792289977045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69951939298903861526651363 104927908948355792289977045)
            ·
              refine ⟨2459247865977088881796337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 104927908948355792289977045 2459247865977088881796337)
              ·
                refine ⟨1844435899482816661347253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2459247865977088881796337 1844435899482816661347253)
                ·
                  refine ⟨172915865576514062001305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1844435899482816661347253 172915865576514062001305)
                  ·
                    rfl

theorem cell22_1515386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 5].length) (baseStart_1515386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515386 prefixEnd_1515386 := by exact prefixLift 1515386
  have htrace : WordTrace (prefixWord ++ tailWord_1515386) baseStart_1515386 baseEnd_1515386 := by
    simpa [prefixWord, tailWord_1515386, baseEnd_1515386] using wordTrace_append hprefix tailTrace_1515386
  have hstable : (prefixWord ++ tailWord_1515386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515386).length < 2 ^ (prefixWord ++ tailWord_1515386).sum := by decide
  have hdescent : baseEnd_1515386 < baseStart_1515386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515390 : List Nat := [4, 2, 3, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1515390 : Nat := 118140960795 + 1515390 * 2 ^ 59
def prefixEnd_1515390 : Nat := 4983230072969 + 3 ^ 40 * 1515390 * 2
def baseEnd_1515390 : Nat := 518748966011287508903903

theorem tailTrace_1515390 : CollatzResearch.WordTrace tailWord_1515390 prefixEnd_1515390 518748966011287508903903 := by
  unfold tailWord_1515390
  simp only [CollatzResearch.WordTrace]
  refine ⟨6908851747501039106543953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36847209320005541901567749 6908851747501039106543953)
  ·
    refine ⟨5181638810625779329907965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6908851747501039106543953 5181638810625779329907965)
    ·
      refine ⟨1943114553984667248715487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5181638810625779329907965 1943114553984667248715487)
      ·
        refine ⟨2914671830977000873073231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1943114553984667248715487 2914671830977000873073231)
        ·
          refine ⟨4372007746465501309609847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2914671830977000873073231 4372007746465501309609847)
          ·
            refine ⟨6558011619698251964414771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372007746465501309609847 6558011619698251964414771)
            ·
              refine ⟨9837017429547377946622157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558011619698251964414771 9837017429547377946622157)
              ·
                refine ⟨3688881536080266729983309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9837017429547377946622157 3688881536080266729983309)
                ·
                  refine ⟨1383330576030100023743741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3688881536080266729983309 1383330576030100023743741)
                  ·
                    refine ⟨518748966011287508903903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1383330576030100023743741 518748966011287508903903)
                    ·
                      rfl

theorem cell22_1515390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1515390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515390 prefixEnd_1515390 := by exact prefixLift 1515390
  have htrace : WordTrace (prefixWord ++ tailWord_1515390) baseStart_1515390 baseEnd_1515390 := by
    simpa [prefixWord, tailWord_1515390, baseEnd_1515390] using wordTrace_append hprefix tailTrace_1515390
  have hstable : (prefixWord ++ tailWord_1515390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515390).length < 2 ^ (prefixWord ++ tailWord_1515390).sum := by decide
  have hdescent : baseEnd_1515390 < baseStart_1515390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515476 : List Nat := [2, 4, 1, 2, 1, 1, 1, 10]
def baseStart_1515476 : Nat := 118140960795 + 1515476 * 2 ^ 59
def prefixEnd_1515476 : Nat := 4983230072969 + 3 ^ 40 * 1515476 * 2
def baseEnd_1515476 : Nat := 57642045063201327917071

theorem tailTrace_1515476 : CollatzResearch.WordTrace tailWord_1515476 prefixEnd_1515476 57642045063201327917071 := by
  unfold tailWord_1515476
  simp only [CollatzResearch.WordTrace]
  refine ⟨27636975328848374769991141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36849300438464499693321521 27636975328848374769991141)
  ·
    refine ⟨5181932874159070269373339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27636975328848374769991141 5181932874159070269373339)
    ·
      refine ⟨7772899311238605404060009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5181932874159070269373339 7772899311238605404060009)
      ·
        refine ⟨5829674483428954053045007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7772899311238605404060009 5829674483428954053045007)
        ·
          refine ⟨8744511725143431079567511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5829674483428954053045007 8744511725143431079567511)
          ·
            refine ⟨13116767587715146619351267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8744511725143431079567511 13116767587715146619351267)
            ·
              refine ⟨19675151381572719929026901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13116767587715146619351267 19675151381572719929026901)
              ·
                refine ⟨57642045063201327917071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19675151381572719929026901 57642045063201327917071)
                ·
                  rfl

theorem cell22_1515476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 10].length) (baseStart_1515476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515476 prefixEnd_1515476 := by exact prefixLift 1515476
  have htrace : WordTrace (prefixWord ++ tailWord_1515476) baseStart_1515476 baseEnd_1515476 := by
    simpa [prefixWord, tailWord_1515476, baseEnd_1515476] using wordTrace_append hprefix tailTrace_1515476
  have hstable : (prefixWord ++ tailWord_1515476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515476).length < 2 ^ (prefixWord ++ tailWord_1515476).sum := by decide
  have hdescent : baseEnd_1515476 < baseStart_1515476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515510 : List Nat := [5, 1, 1, 1, 4, 2, 1, 7]
def baseStart_1515510 : Nat := 118140960795 + 1515510 * 2 ^ 59
def prefixEnd_1515510 : Nat := 4983230072969 + 3 ^ 40 * 1515510 * 2
def baseEnd_1515510 : Nat := 57643338273738577322615

theorem tailTrace_1515510 : CollatzResearch.WordTrace tailWord_1515510 prefixEnd_1515510 57643338273738577322615 := by
  unfold tailWord_1515510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3454699421223348334169999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36850127159715715564479989 3454699421223348334169999)
  ·
    refine ⟨5182049131835022501254999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3454699421223348334169999 5182049131835022501254999)
    ·
      refine ⟨7773073697752533751882499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5182049131835022501254999 7773073697752533751882499)
      ·
        refine ⟨11659610546628800627823749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7773073697752533751882499 11659610546628800627823749)
        ·
          refine ⟨2186176977492900117716953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11659610546628800627823749 2186176977492900117716953)
          ·
            refine ⟨1639632733119675088287715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186176977492900117716953 1639632733119675088287715)
            ·
              refine ⟨2459449099679512632431573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639632733119675088287715 2459449099679512632431573)
              ·
                refine ⟨57643338273738577322615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2459449099679512632431573 57643338273738577322615)
                ·
                  rfl

theorem cell22_1515510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_1515510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515510 prefixEnd_1515510 := by exact prefixLift 1515510
  have htrace : WordTrace (prefixWord ++ tailWord_1515510) baseStart_1515510 baseEnd_1515510 := by
    simpa [prefixWord, tailWord_1515510, baseEnd_1515510] using wordTrace_append hprefix tailTrace_1515510
  have hstable : (prefixWord ++ tailWord_1515510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515510).length < 2 ^ (prefixWord ++ tailWord_1515510).sum := by decide
  have hdescent : baseEnd_1515510 < baseStart_1515510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515585 : List Nat := [1, 2, 5, 1, 2, 1, 1, 4, 1, 4]
def baseStart_1515585 : Nat := 118140960795 + 1515585 * 2 ^ 59
def prefixEnd_1515585 : Nat := 4983230072969 + 3 ^ 40 * 1515585 * 2
def baseEnd_1515585 : Nat := 518815718496372000278305

theorem tailTrace_1515585 : CollatzResearch.WordTrace tailWord_1515585 prefixEnd_1515585 518815718496372000278305 := by
  unfold tailWord_1515585
  simp only [CollatzResearch.WordTrace]
  refine ⟨55277926214301861155700209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36851950809534574103800139 55277926214301861155700209)
  ·
    refine ⟨41458444660726395866775157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55277926214301861155700209 41458444660726395866775157)
    ·
      refine ⟨3886729186943099612510171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41458444660726395866775157 3886729186943099612510171)
      ·
        refine ⟨5830093780414649418765257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3886729186943099612510171 5830093780414649418765257)
        ·
          refine ⟨4372570335310987064073943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5830093780414649418765257 4372570335310987064073943)
          ·
            refine ⟨6558855502966480596110915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4372570335310987064073943 6558855502966480596110915)
            ·
              refine ⟨9838283254449720894166373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6558855502966480596110915 9838283254449720894166373)
              ·
                refine ⟨1844678110209322667656195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9838283254449720894166373 1844678110209322667656195)
                ·
                  refine ⟨2767017165313984001484293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1844678110209322667656195 2767017165313984001484293)
                  ·
                    refine ⟨518815718496372000278305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2767017165313984001484293 518815718496372000278305)
                    ·
                      rfl

theorem cell22_1515585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_1515585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515585 prefixEnd_1515585 := by exact prefixLift 1515585
  have htrace : WordTrace (prefixWord ++ tailWord_1515585) baseStart_1515585 baseEnd_1515585 := by
    simpa [prefixWord, tailWord_1515585, baseEnd_1515585] using wordTrace_append hprefix tailTrace_1515585
  have hstable : (prefixWord ++ tailWord_1515585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515585).length < 2 ^ (prefixWord ++ tailWord_1515585).sum := by decide
  have hdescent : baseEnd_1515585 < baseStart_1515585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515628 : List Nat := [2, 2, 1, 1, 3, 4, 2, 7]
def baseStart_1515628 : Nat := 118140960795 + 1515628 * 2 ^ 59
def prefixEnd_1515628 : Nat := 4983230072969 + 3 ^ 40 * 1515628 * 2
def baseEnd_1515628 : Nat := 57647826475014913494797

theorem tailTrace_1515628 : CollatzResearch.WordTrace tailWord_1515628 prefixEnd_1515628 57647826475014913494797 := by
  unfold tailWord_1515628
  simp only [CollatzResearch.WordTrace]
  refine ⟨27639747276573039749757769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36852996368764052999677025 27639747276573039749757769)
  ·
    refine ⟨20729810457429779812318327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27639747276573039749757769 20729810457429779812318327)
    ·
      refine ⟨31094715686144669718477491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20729810457429779812318327 31094715686144669718477491)
      ·
        refine ⟨46642073529217004577716237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31094715686144669718477491 46642073529217004577716237)
        ·
          refine ⟨17490777573456376716643589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46642073529217004577716237 17490777573456376716643589)
          ·
            refine ⟨3279520795023070634370673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17490777573456376716643589 3279520795023070634370673)
            ·
              refine ⟨2459640596267302975778005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3279520795023070634370673 2459640596267302975778005)
              ·
                refine ⟨57647826475014913494797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2459640596267302975778005 57647826475014913494797)
                ·
                  rfl

theorem cell22_1515628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 7].length) (baseStart_1515628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515628 prefixEnd_1515628 := by exact prefixLift 1515628
  have htrace : WordTrace (prefixWord ++ tailWord_1515628) baseStart_1515628 baseEnd_1515628 := by
    simpa [prefixWord, tailWord_1515628, baseEnd_1515628] using wordTrace_append hprefix tailTrace_1515628
  have hstable : (prefixWord ++ tailWord_1515628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515628).length < 2 ^ (prefixWord ++ tailWord_1515628).sum := by decide
  have hdescent : baseEnd_1515628 < baseStart_1515628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515632 : List Nat := [2, 1, 1, 1, 5, 2, 4, 1, 2, 3]
def baseStart_1515632 : Nat := 118140960795 + 1515632 * 2 ^ 59
def prefixEnd_1515632 : Nat := 4983230072969 + 3 ^ 40 * 1515632 * 2
def baseEnd_1515632 : Nat := 518831807556879544353161

theorem tailTrace_1515632 : CollatzResearch.WordTrace tailWord_1515632 prefixEnd_1515632 518831807556879544353161 := by
  unfold tailWord_1515632
  simp only [CollatzResearch.WordTrace]
  refine ⟨27639820222565794091330575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36853093630087725455107433 27639820222565794091330575)
  ·
    refine ⟨41459730333848691136995863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27639820222565794091330575 41459730333848691136995863)
    ·
      refine ⟨62189595500773036705493795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41459730333848691136995863 62189595500773036705493795)
      ·
        refine ⟨93284393251159555058240693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 62189595500773036705493795 93284393251159555058240693)
        ·
          refine ⟨8745411867296208286710065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 93284393251159555058240693 8745411867296208286710065)
          ·
            refine ⟨6559058900472156215032549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8745411867296208286710065 6559058900472156215032549)
            ·
              refine ⟨1229823543838529290318603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6559058900472156215032549 1229823543838529290318603)
              ·
                refine ⟨1844735315757793935477905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1229823543838529290318603 1844735315757793935477905)
                ·
                  refine ⟨1383551486818345451608429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1844735315757793935477905 1383551486818345451608429)
                  ·
                    refine ⟨518831807556879544353161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1383551486818345451608429 518831807556879544353161)
                    ·
                      rfl

theorem cell22_1515632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 4, 1, 2, 3].length) (baseStart_1515632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515632 prefixEnd_1515632 := by exact prefixLift 1515632
  have htrace : WordTrace (prefixWord ++ tailWord_1515632) baseStart_1515632 baseEnd_1515632 := by
    simpa [prefixWord, tailWord_1515632, baseEnd_1515632] using wordTrace_append hprefix tailTrace_1515632
  have hstable : (prefixWord ++ tailWord_1515632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515632).length < 2 ^ (prefixWord ++ tailWord_1515632).sum := by decide
  have hdescent : baseEnd_1515632 < baseStart_1515632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515668 : List Nat := [2, 4, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1515668 : Nat := 118140960795 + 1515668 * 2 ^ 59
def prefixEnd_1515668 : Nat := 4983230072969 + 3 ^ 40 * 1515668 * 2
def baseEnd_1515668 : Nat := 172948043697529150151017

theorem tailTrace_1515668 : CollatzResearch.WordTrace tailWord_1515668 prefixEnd_1515668 172948043697529150151017 := by
  unfold tailWord_1515668
  simp only [CollatzResearch.WordTrace]
  refine ⟨27640476736500583165485829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36853968982000777553981105 27640476736500583165485829)
  ·
    refine ⟨5182589388093859343528593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27640476736500583165485829 5182589388093859343528593)
    ·
      refine ⟨3886942041070394507646445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5182589388093859343528593 3886942041070394507646445)
      ·
        refine ⟨1457603265401397940367417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3886942041070394507646445 1457603265401397940367417)
        ·
          refine ⟨1093202449051048455275563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1457603265401397940367417 1093202449051048455275563)
          ·
            refine ⟨1639803673576572682913345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1093202449051048455275563 1639803673576572682913345)
            ·
              refine ⟨1229852755182429512185009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1639803673576572682913345 1229852755182429512185009)
              ·
                refine ⟨922389566386822134138757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1229852755182429512185009 922389566386822134138757)
                ·
                  refine ⟨172948043697529150151017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 922389566386822134138757 172948043697529150151017)
                  ·
                    rfl

theorem cell22_1515668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1515668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515668 prefixEnd_1515668 := by exact prefixLift 1515668
  have htrace : WordTrace (prefixWord ++ tailWord_1515668) baseStart_1515668 baseEnd_1515668 := by
    simpa [prefixWord, tailWord_1515668, baseEnd_1515668] using wordTrace_append hprefix tailTrace_1515668
  have hstable : (prefixWord ++ tailWord_1515668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515668).length < 2 ^ (prefixWord ++ tailWord_1515668).sum := by decide
  have hdescent : baseEnd_1515668 < baseStart_1515668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515724 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 5]
def baseStart_1515724 : Nat := 118140960795 + 1515724 * 2 ^ 59
def prefixEnd_1515724 : Nat := 4983230072969 + 3 ^ 40 * 1515724 * 2
def baseEnd_1515724 : Nat := 172954433679007323684293

theorem tailTrace_1515724 : CollatzResearch.WordTrace tailWord_1515724 prefixEnd_1515724 172954433679007323684293 := by
  unfold tailWord_1515724
  simp only [CollatzResearch.WordTrace]
  refine ⟨27641497980399143947505113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36855330640532191930006817 27641497980399143947505113)
  ·
    refine ⟨20731123485299357960628835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27641497980399143947505113 20731123485299357960628835)
    ·
      refine ⟨31096685227949036940943253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20731123485299357960628835 31096685227949036940943253)
      ·
        refine ⟨1457657120060111106606715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 31096685227949036940943253 1457657120060111106606715)
        ·
          refine ⟨2186485680090166659910073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1457657120060111106606715 2186485680090166659910073)
          ·
            refine ⟨1639864260067624994932555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186485680090166659910073 1639864260067624994932555)
            ·
              refine ⟨2459796390101437492398833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1639864260067624994932555 2459796390101437492398833)
              ·
                refine ⟨1844847292576078119299125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2459796390101437492398833 1844847292576078119299125)
                ·
                  refine ⟨172954433679007323684293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1844847292576078119299125 172954433679007323684293)
                  ·
                    rfl

theorem cell22_1515724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 5].length) (baseStart_1515724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515724 prefixEnd_1515724 := by exact prefixLift 1515724
  have htrace : WordTrace (prefixWord ++ tailWord_1515724) baseStart_1515724 baseEnd_1515724 := by
    simpa [prefixWord, tailWord_1515724, baseEnd_1515724] using wordTrace_append hprefix tailTrace_1515724
  have hstable : (prefixWord ++ tailWord_1515724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515724).length < 2 ^ (prefixWord ++ tailWord_1515724).sum := by decide
  have hdescent : baseEnd_1515724 < baseStart_1515724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515763 : List Nat := [1, 1, 1, 2, 2, 4, 3, 8]
def baseStart_1515763 : Nat := 118140960795 + 1515763 * 2 ^ 59
def prefixEnd_1515763 : Nat := 4983230072969 + 3 ^ 40 * 1515763 * 2
def baseEnd_1515763 : Nat := 57652961281559874369751

theorem tailTrace_1515763 : CollatzResearch.WordTrace tailWord_1515763 prefixEnd_1515763 57652961281559874369751 := by
  unfold tailWord_1515763
  simp only [CollatzResearch.WordTrace]
  refine ⟨55284418407656997555679943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36856278938437998370453295 55284418407656997555679943)
  ·
    refine ⟨82926627611485496333519915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55284418407656997555679943 82926627611485496333519915)
    ·
      refine ⟨124389941417228244500279873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82926627611485496333519915 124389941417228244500279873)
      ·
        refine ⟨93292456062921183375209905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124389941417228244500279873 93292456062921183375209905)
        ·
          refine ⟨69969342047190887531407429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 93292456062921183375209905 69969342047190887531407429)
          ·
            refine ⟨13119251633848291412138893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69969342047190887531407429 13119251633848291412138893)
            ·
              refine ⟨4919719362693109279552085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13119251633848291412138893 4919719362693109279552085)
              ·
                refine ⟨57652961281559874369751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4919719362693109279552085 57652961281559874369751)
                ·
                  rfl

theorem cell22_1515763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 8].length) (baseStart_1515763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515763 prefixEnd_1515763 := by exact prefixLift 1515763
  have htrace : WordTrace (prefixWord ++ tailWord_1515763) baseStart_1515763 baseEnd_1515763 := by
    simpa [prefixWord, tailWord_1515763, baseEnd_1515763] using wordTrace_append hprefix tailTrace_1515763
  have hstable : (prefixWord ++ tailWord_1515763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515763).length < 2 ^ (prefixWord ++ tailWord_1515763).sum := by decide
  have hdescent : baseEnd_1515763 < baseStart_1515763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515829 : List Nat := [1, 3, 3, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1515829 : Nat := 118140960795 + 1515829 * 2 ^ 59
def prefixEnd_1515829 : Nat := 4983230072969 + 3 ^ 40 * 1515829 * 2
def baseEnd_1515829 : Nat := 518899244682836697177557

theorem tailTrace_1515829 : CollatzResearch.WordTrace tailWord_1515829 prefixEnd_1515829 518899244682836697177557 := by
  unfold tailWord_1515829
  simp only [CollatzResearch.WordTrace]
  refine ⟨55286825625417890827582541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36857883750278593885055027 55286825625417890827582541)
  ·
    refine ⟨20732559609531709060343453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55286825625417890827582541 20732559609531709060343453)
    ·
      refine ⟨7774709853574390897628795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20732559609531709060343453 7774709853574390897628795)
      ·
        refine ⟨11662064780361586346443193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7774709853574390897628795 11662064780361586346443193)
        ·
          refine ⟨8746548585271189759832395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11662064780361586346443193 8746548585271189759832395)
          ·
            refine ⟨13119822877906784639748593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8746548585271189759832395 13119822877906784639748593)
            ·
              refine ⟨9839867158430088479811445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13119822877906784639748593 9839867158430088479811445)
              ·
                refine ⟨922487546102820794982323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9839867158430088479811445 922487546102820794982323)
                ·
                  refine ⟨1383731319154231192473485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 922487546102820794982323 1383731319154231192473485)
                  ·
                    refine ⟨518899244682836697177557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1383731319154231192473485 518899244682836697177557)
                    ·
                      rfl

theorem cell22_1515829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1515829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515829 prefixEnd_1515829 := by exact prefixLift 1515829
  have htrace : WordTrace (prefixWord ++ tailWord_1515829) baseStart_1515829 baseEnd_1515829 := by
    simpa [prefixWord, tailWord_1515829, baseEnd_1515829] using wordTrace_append hprefix tailTrace_1515829
  have hstable : (prefixWord ++ tailWord_1515829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515829).length < 2 ^ (prefixWord ++ tailWord_1515829).sum := by decide
  have hdescent : baseEnd_1515829 < baseStart_1515829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515934 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1515934 : Nat := 118140960795 + 1515934 * 2 ^ 59
def prefixEnd_1515934 : Nat := 4983230072969 + 3 ^ 40 * 1515934 * 2
def baseEnd_1515934 : Nat := 518935188328651423302235

theorem tailTrace_1515934 : CollatzResearch.WordTrace tailWord_1515934 prefixEnd_1515934 518935188328651423302235 := by
  unfold tailWord_1515934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6911331911254686720019357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36860436860024995840103237 6911331911254686720019357)
  ·
    refine ⟨2591749466720507520007259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6911331911254686720019357 2591749466720507520007259)
    ·
      refine ⟨3887624200080761280010889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2591749466720507520007259 3887624200080761280010889)
      ·
        refine ⟨2915718150060570960008167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3887624200080761280010889 2915718150060570960008167)
        ·
          refine ⟨4373577225090856440012251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2915718150060570960008167 4373577225090856440012251)
          ·
            refine ⟨6560365837636284660018377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4373577225090856440012251 6560365837636284660018377)
            ·
              refine ⟨4920274378227213495013783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6560365837636284660018377 4920274378227213495013783)
              ·
                refine ⟨7380411567340820242520675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4920274378227213495013783 7380411567340820242520675)
                ·
                  refine ⟨11070617351011230363781013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7380411567340820242520675 11070617351011230363781013)
                  ·
                    refine ⟨518935188328651423302235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11070617351011230363781013 518935188328651423302235)
                    ·
                      rfl

theorem cell22_1515934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1515934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515934 prefixEnd_1515934 := by exact prefixLift 1515934
  have htrace : WordTrace (prefixWord ++ tailWord_1515934) baseStart_1515934 baseEnd_1515934 := by
    simpa [prefixWord, tailWord_1515934, baseEnd_1515934] using wordTrace_append hprefix tailTrace_1515934
  have hstable : (prefixWord ++ tailWord_1515934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515934).length < 2 ^ (prefixWord ++ tailWord_1515934).sum := by decide
  have hdescent : baseEnd_1515934 < baseStart_1515934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1515949 : List Nat := [1, 5, 2, 2, 2, 2, 8]
def baseStart_1515949 : Nat := 118140960795 + 1515949 * 2 ^ 59
def prefixEnd_1515949 : Nat := 4983230072969 + 3 ^ 40 * 1515949 * 2
def baseEnd_1515949 : Nat := 19220011967970236451007

theorem tailTrace_1515949 : CollatzResearch.WordTrace tailWord_1515949 prefixEnd_1515949 19220011967970236451007 := by
  unfold tailWord_1515949
  simp only [CollatzResearch.WordTrace]
  refine ⟨55291202384983151321950901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36860801589988767547967267 55291202384983151321950901)
  ·
    refine ⟨5183550223592170436432897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55291202384983151321950901 5183550223592170436432897)
    ·
      refine ⟨3887662667694127827324673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5183550223592170436432897 3887662667694127827324673)
      ·
        refine ⟨2915747000770595870493505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3887662667694127827324673 2915747000770595870493505)
        ·
          refine ⟨2186810250577946902870129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2915747000770595870493505 2186810250577946902870129)
          ·
            refine ⟨1640107687933460177152597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2186810250577946902870129 1640107687933460177152597)
            ·
              refine ⟨19220011967970236451007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1640107687933460177152597 19220011967970236451007)
              ·
                rfl

theorem cell22_1515949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 8].length) (baseStart_1515949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1515949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1515949 prefixEnd_1515949 := by exact prefixLift 1515949
  have htrace : WordTrace (prefixWord ++ tailWord_1515949) baseStart_1515949 baseEnd_1515949 := by
    simpa [prefixWord, tailWord_1515949, baseEnd_1515949] using wordTrace_append hprefix tailTrace_1515949
  have hstable : (prefixWord ++ tailWord_1515949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1515949).length < 2 ^ (prefixWord ++ tailWord_1515949).sum := by decide
  have hdescent : baseEnd_1515949 < baseStart_1515949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1515949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516037 : List Nat := [1, 3, 1, 1, 2, 2, 3, 3, 1, 5]
def baseStart_1516037 : Nat := 118140960795 + 1516037 * 2 ^ 59
def prefixEnd_1516037 : Nat := 4983230072969 + 3 ^ 40 * 1516037 * 2
def baseEnd_1516037 : Nat := 518970447333593487976919

theorem tailTrace_1516037 : CollatzResearch.WordTrace tailWord_1516037 prefixEnd_1516037 518970447333593487976919 := by
  unfold tailWord_1516037
  simp only [CollatzResearch.WordTrace]
  refine ⟨55294412008664342351154365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36862941339109561567436243 55294412008664342351154365)
  ·
    refine ⟨20735404503249128381682887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55294412008664342351154365 20735404503249128381682887)
    ·
      refine ⟨31103106754873692572524331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20735404503249128381682887 31103106754873692572524331)
      ·
        refine ⟨46654660132310538858786497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31103106754873692572524331 46654660132310538858786497)
        ·
          refine ⟨34990995099232904144089873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46654660132310538858786497 34990995099232904144089873)
          ·
            refine ⟨26243246324424678108067405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34990995099232904144089873 26243246324424678108067405)
            ·
              refine ⟨9841217371659254290525277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26243246324424678108067405 9841217371659254290525277)
              ·
                refine ⟨3690456514372220358946979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9841217371659254290525277 3690456514372220358946979)
                ·
                  refine ⟨5535684771558330538420469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3690456514372220358946979 5535684771558330538420469)
                  ·
                    refine ⟨518970447333593487976919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5535684771558330538420469 518970447333593487976919)
                    ·
                      rfl

theorem cell22_1516037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_1516037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516037 prefixEnd_1516037 := by exact prefixLift 1516037
  have htrace : WordTrace (prefixWord ++ tailWord_1516037) baseStart_1516037 baseEnd_1516037 := by
    simpa [prefixWord, tailWord_1516037, baseEnd_1516037] using wordTrace_append hprefix tailTrace_1516037
  have hstable : (prefixWord ++ tailWord_1516037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516037).length < 2 ^ (prefixWord ++ tailWord_1516037).sum := by decide
  have hdescent : baseEnd_1516037 < baseStart_1516037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516039 : List Nat := [1, 1, 4, 3, 3, 1, 1, 2, 6]
def baseStart_1516039 : Nat := 118140960795 + 1516039 * 2 ^ 59
def prefixEnd_1516039 : Nat := 4983230072969 + 3 ^ 40 * 1516039 * 2
def baseEnd_1516039 : Nat := 172990377324822049808971

theorem tailTrace_1516039 : CollatzResearch.WordTrace tailWord_1516039 prefixEnd_1516039 172990377324822049808971 := by
  unfold tailWord_1516039
  simp only [CollatzResearch.WordTrace]
  refine ⟨55294484954657096692727171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36862989969771397795151447 55294484954657096692727171)
  ·
    refine ⟨82941727431985645039090757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55294484954657096692727171 82941727431985645039090757)
    ·
      refine ⟨15551573893497308444829517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82941727431985645039090757 15551573893497308444829517)
      ·
        refine ⟨5831840210061490666811069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15551573893497308444829517 5831840210061490666811069)
        ·
          refine ⟨2186940078773059000054151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5831840210061490666811069 2186940078773059000054151)
          ·
            refine ⟨3280410118159588500081227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2186940078773059000054151 3280410118159588500081227)
            ·
              refine ⟨4920615177239382750121841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280410118159588500081227 4920615177239382750121841)
              ·
                refine ⟨3690461382929537062591381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4920615177239382750121841 3690461382929537062591381)
                ·
                  refine ⟨172990377324822049808971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3690461382929537062591381 172990377324822049808971)
                  ·
                    rfl

theorem cell22_1516039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 6].length) (baseStart_1516039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516039 prefixEnd_1516039 := by exact prefixLift 1516039
  have htrace : WordTrace (prefixWord ++ tailWord_1516039) baseStart_1516039 baseEnd_1516039 := by
    simpa [prefixWord, tailWord_1516039, baseEnd_1516039] using wordTrace_append hprefix tailTrace_1516039
  have hstable : (prefixWord ++ tailWord_1516039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516039).length < 2 ^ (prefixWord ++ tailWord_1516039).sum := by decide
  have hdescent : baseEnd_1516039 < baseStart_1516039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516056 : List Nat := [2, 1, 2, 3, 3, 2, 2, 3, 4]
def baseStart_1516056 : Nat := 118140960795 + 1516056 * 2 ^ 59
def prefixEnd_1516056 : Nat := 4983230072969 + 3 ^ 40 * 1516056 * 2
def baseEnd_1516056 : Nat := 172992317140627923917287

theorem tailTrace_1516056 : CollatzResearch.WordTrace tailWord_1516056 prefixEnd_1516056 172992317140627923917287 := by
  unfold tailWord_1516056
  simp only [CollatzResearch.WordTrace]
  refine ⟨27647552497797754298048011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36863403330397005730730681 27647552497797754298048011)
  ·
    refine ⟨41471328746696631447072017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27647552497797754298048011 41471328746696631447072017)
    ·
      refine ⟨31103496560022473585304013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41471328746696631447072017 31103496560022473585304013)
      ·
        refine ⟨11663811210008427594489005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31103496560022473585304013 11663811210008427594489005)
        ·
          refine ⟨4373929203753160347933377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11663811210008427594489005 4373929203753160347933377)
          ·
            refine ⟨3280446902814870260950033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4373929203753160347933377 3280446902814870260950033)
            ·
              refine ⟨2460335177111152695712525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3280446902814870260950033 2460335177111152695712525)
              ·
                refine ⟨922625691416682260892197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2460335177111152695712525 922625691416682260892197)
                ·
                  refine ⟨172992317140627923917287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 922625691416682260892197 172992317140627923917287)
                  ·
                    rfl

theorem cell22_1516056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 2, 3, 4].length) (baseStart_1516056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516056 prefixEnd_1516056 := by exact prefixLift 1516056
  have htrace : WordTrace (prefixWord ++ tailWord_1516056) baseStart_1516056 baseEnd_1516056 := by
    simpa [prefixWord, tailWord_1516056, baseEnd_1516056] using wordTrace_append hprefix tailTrace_1516056
  have hstable : (prefixWord ++ tailWord_1516056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516056).length < 2 ^ (prefixWord ++ tailWord_1516056).sum := by decide
  have hdescent : baseEnd_1516056 < baseStart_1516056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516067 : List Nat := [1, 1, 1, 4, 4, 2, 9]
def baseStart_1516067 : Nat := 118140960795 + 1516067 * 2 ^ 59
def prefixEnd_1516067 : Nat := 4983230072969 + 3 ^ 40 * 1516067 * 2
def baseEnd_1516067 : Nat := 19221508035062348508401

theorem tailTrace_1516067 : CollatzResearch.WordTrace tailWord_1516067 prefixEnd_1516067 19221508035062348508401 := by
  unfold tailWord_1516067
  simp only [CollatzResearch.WordTrace]
  refine ⟨55295506198555657474746455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36863670799037104983164303 55295506198555657474746455)
  ·
    refine ⟨82943259297833486212119683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55295506198555657474746455 82943259297833486212119683)
    ·
      refine ⟨124414888946750229318179525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82943259297833486212119683 124414888946750229318179525)
      ·
        refine ⟨23327791677515667997158661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124414888946750229318179525 23327791677515667997158661)
        ·
          refine ⟨4373960939534187749467249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23327791677515667997158661 4373960939534187749467249)
          ·
            refine ⟨3280470704650640812100437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4373960939534187749467249 3280470704650640812100437)
            ·
              refine ⟨19221508035062348508401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3280470704650640812100437 19221508035062348508401)
              ·
                rfl

theorem cell22_1516067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 9].length) (baseStart_1516067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516067 prefixEnd_1516067 := by exact prefixLift 1516067
  have htrace : WordTrace (prefixWord ++ tailWord_1516067) baseStart_1516067 baseEnd_1516067 := by
    simpa [prefixWord, tailWord_1516067, baseEnd_1516067] using wordTrace_append hprefix tailTrace_1516067
  have hstable : (prefixWord ++ tailWord_1516067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516067).length < 2 ^ (prefixWord ++ tailWord_1516067).sum := by decide
  have hdescent : baseEnd_1516067 < baseStart_1516067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516127 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 4, 5]
def baseStart_1516127 : Nat := 118140960795 + 1516127 * 2 ^ 59
def prefixEnd_1516127 : Nat := 4983230072969 + 3 ^ 40 * 1516127 * 2
def baseEnd_1516127 : Nat := 519001256172863253226643

theorem tailTrace_1516127 : CollatzResearch.WordTrace tailWord_1516127 prefixEnd_1516127 519001256172863253226643 := by
  unfold tailWord_1516127
  simp only [CollatzResearch.WordTrace]
  refine ⟨55297694578338287721930635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36865129718892191814620423 55297694578338287721930635)
  ·
    refine ⟨82946541867507431582895953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55297694578338287721930635 82946541867507431582895953)
    ·
      refine ⟨62209906400630573687171965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82946541867507431582895953 62209906400630573687171965)
      ·
        refine ⟨23328714900236465132689487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62209906400630573687171965 23328714900236465132689487)
        ·
          refine ⟨34993072350354697699034231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23328714900236465132689487 34993072350354697699034231)
          ·
            refine ⟨52489608525532046548551347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34993072350354697699034231 52489608525532046548551347)
            ·
              refine ⟨78734412788298069822827021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52489608525532046548551347 78734412788298069822827021)
              ·
                refine ⟨29525404795611776183560133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78734412788298069822827021 29525404795611776183560133)
                ·
                  refine ⟨5536013399177208034417525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29525404795611776183560133 5536013399177208034417525)
                  ·
                    refine ⟨519001256172863253226643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5536013399177208034417525 519001256172863253226643)
                    ·
                      rfl

theorem cell22_1516127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 4, 5].length) (baseStart_1516127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516127 prefixEnd_1516127 := by exact prefixLift 1516127
  have htrace : WordTrace (prefixWord ++ tailWord_1516127) baseStart_1516127 baseEnd_1516127 := by
    simpa [prefixWord, tailWord_1516127, baseEnd_1516127] using wordTrace_append hprefix tailTrace_1516127
  have hstable : (prefixWord ++ tailWord_1516127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516127).length < 2 ^ (prefixWord ++ tailWord_1516127).sum := by decide
  have hdescent : baseEnd_1516127 < baseStart_1516127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516133 : List Nat := [1, 3, 1, 3, 4, 2, 1, 1, 3, 3]
def baseStart_1516133 : Nat := 118140960795 + 1516133 * 2 ^ 59
def prefixEnd_1516133 : Nat := 4983230072969 + 3 ^ 40 * 1516133 * 2
def baseEnd_1516133 : Nat := 519003310095481237576625

theorem tailTrace_1516133 : CollatzResearch.WordTrace tailWord_1516133 prefixEnd_1516133 519003310095481237576625 := by
  unfold tailWord_1516133
  simp only [CollatzResearch.WordTrace]
  refine ⟨55297913416316550746649053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36865275610877700497766035 55297913416316550746649053)
  ·
    refine ⟨20736717531118706529993395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55297913416316550746649053 20736717531118706529993395)
    ·
      refine ⟨31105076296678059794990093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20736717531118706529993395 31105076296678059794990093)
      ·
        refine ⟨11664403611254272423121285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31105076296678059794990093 11664403611254272423121285)
        ·
          refine ⟨2187075677110176079335241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11664403611254272423121285 2187075677110176079335241)
          ·
            refine ⟨1640306757832632059501431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2187075677110176079335241 1640306757832632059501431)
            ·
              refine ⟨2460460136748948089252147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1640306757832632059501431 2460460136748948089252147)
              ·
                refine ⟨3690690205123422133878221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460460136748948089252147 3690690205123422133878221)
                ·
                  refine ⟨1384008826921283300204333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3690690205123422133878221 1384008826921283300204333)
                  ·
                    refine ⟨519003310095481237576625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384008826921283300204333 519003310095481237576625)
                    ·
                      rfl

theorem cell22_1516133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_1516133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516133 prefixEnd_1516133 := by exact prefixLift 1516133
  have htrace : WordTrace (prefixWord ++ tailWord_1516133) baseStart_1516133 baseEnd_1516133 := by
    simpa [prefixWord, tailWord_1516133, baseEnd_1516133] using wordTrace_append hprefix tailTrace_1516133
  have hstable : (prefixWord ++ tailWord_1516133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516133).length < 2 ^ (prefixWord ++ tailWord_1516133).sum := by decide
  have hdescent : baseEnd_1516133 < baseStart_1516133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516146 : List Nat := [3, 2, 1, 2, 4, 1, 1, 3, 5]
def baseStart_1516146 : Nat := 118140960795 + 1516146 * 2 ^ 59
def prefixEnd_1516146 : Nat := 4983230072969 + 3 ^ 40 * 1516146 * 2
def baseEnd_1516146 : Nat := 173002586753717845667195

theorem tailTrace_1516146 : CollatzResearch.WordTrace tailWord_1516146 prefixEnd_1516146 173002586753717845667195 := by
  unfold tailWord_1516146
  simp only [CollatzResearch.WordTrace]
  refine ⟨13824596891317363491718073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36865591710179635977914861 13824596891317363491718073)
  ·
    refine ⟨10368447668488022618788555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13824596891317363491718073 10368447668488022618788555)
    ·
      refine ⟨15552671502732033928182833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10368447668488022618788555 15552671502732033928182833)
      ·
        refine ⟨11664503627049025446137125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15552671502732033928182833 11664503627049025446137125)
        ·
          refine ⟨2187094430071692271150711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11664503627049025446137125 2187094430071692271150711)
          ·
            refine ⟨3280641645107538406726067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187094430071692271150711 3280641645107538406726067)
            ·
              refine ⟨4920962467661307610089101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3280641645107538406726067 4920962467661307610089101)
              ·
                refine ⟨1845360925372990353783413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4920962467661307610089101 1845360925372990353783413)
                ·
                  refine ⟨173002586753717845667195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1845360925372990353783413 173002586753717845667195)
                  ·
                    rfl

theorem cell22_1516146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_1516146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516146 prefixEnd_1516146 := by exact prefixLift 1516146
  have htrace : WordTrace (prefixWord ++ tailWord_1516146) baseStart_1516146 baseEnd_1516146 := by
    simpa [prefixWord, tailWord_1516146, baseEnd_1516146] using wordTrace_append hprefix tailTrace_1516146
  have hstable : (prefixWord ++ tailWord_1516146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516146).length < 2 ^ (prefixWord ++ tailWord_1516146).sum := by decide
  have hdescent : baseEnd_1516146 < baseStart_1516146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516159 : List Nat := [1, 1, 2, 2, 1, 1, 1, 8, 1, 4]
def baseStart_1516159 : Nat := 118140960795 + 1516159 * 2 ^ 59
def prefixEnd_1516159 : Nat := 4983230072969 + 3 ^ 40 * 1516159 * 2
def baseEnd_1516159 : Nat := 519012210426825836426545

theorem tailTrace_1516159 : CollatzResearch.WordTrace tailWord_1516159 prefixEnd_1516159 519012210426825836426545 := by
  unfold tailWord_1516159
  simp only [CollatzResearch.WordTrace]
  refine ⟨55298861714222357187095531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36865907809481571458063687 55298861714222357187095531)
  ·
    refine ⟨82948292571333535780643297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55298861714222357187095531 82948292571333535780643297)
    ·
      refine ⟨62211219428500151835482473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82948292571333535780643297 62211219428500151835482473)
      ·
        refine ⟨46658414571375113876611855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62211219428500151835482473 46658414571375113876611855)
        ·
          refine ⟨69987621857062670814917783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46658414571375113876611855 69987621857062670814917783)
          ·
            refine ⟨104981432785594006222376675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69987621857062670814917783 104981432785594006222376675)
            ·
              refine ⟨157472149178391009333565013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104981432785594006222376675 157472149178391009333565013)
              ·
                refine ⟨1845376748184269640627715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 157472149178391009333565013 1845376748184269640627715)
                ·
                  refine ⟨2768065122276404460941573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845376748184269640627715 2768065122276404460941573)
                  ·
                    refine ⟨519012210426825836426545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2768065122276404460941573 519012210426825836426545)
                    ·
                      rfl

theorem cell22_1516159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 8, 1, 4].length) (baseStart_1516159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516159 prefixEnd_1516159 := by exact prefixLift 1516159
  have htrace : WordTrace (prefixWord ++ tailWord_1516159) baseStart_1516159 baseEnd_1516159 := by
    simpa [prefixWord, tailWord_1516159, baseEnd_1516159] using wordTrace_append hprefix tailTrace_1516159
  have hstable : (prefixWord ++ tailWord_1516159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516159).length < 2 ^ (prefixWord ++ tailWord_1516159).sum := by decide
  have hdescent : baseEnd_1516159 < baseStart_1516159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516221 : List Nat := [1, 4, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1516221 : Nat := 118140960795 + 1516221 * 2 ^ 59
def prefixEnd_1516221 : Nat := 4983230072969 + 3 ^ 40 * 1516221 * 2
def baseEnd_1516221 : Nat := 519033434293878341376355

theorem tailTrace_1516221 : CollatzResearch.WordTrace tailWord_1516221 prefixEnd_1516221 519033434293878341376355 := by
  unfold tailWord_1516221
  simp only [CollatzResearch.WordTrace]
  refine ⟨55301123039997741775852517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36867415359998494517235011 55301123039997741775852517)
  ·
    refine ⟨10368960569999576582972347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55301123039997741775852517 10368960569999576582972347)
    ·
      refine ⟨15553440854999364874458521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10368960569999576582972347 15553440854999364874458521)
      ·
        refine ⟨11665080641249523655843891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15553440854999364874458521 11665080641249523655843891)
        ·
          refine ⟨17497620961874285483765837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11665080641249523655843891 17497620961874285483765837)
          ·
            refine ⟨6561607860702857056412189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17497620961874285483765837 6561607860702857056412189)
            ·
              refine ⟨2460602947763571396154571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6561607860702857056412189 2460602947763571396154571)
              ·
                refine ⟨3690904421645357094231857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2460602947763571396154571 3690904421645357094231857)
                ·
                  refine ⟨2768178316234017820673893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3690904421645357094231857 2768178316234017820673893)
                  ·
                    refine ⟨519033434293878341376355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2768178316234017820673893 519033434293878341376355)
                    ·
                      rfl

theorem cell22_1516221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1516221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516221 prefixEnd_1516221 := by exact prefixLift 1516221
  have htrace : WordTrace (prefixWord ++ tailWord_1516221) baseStart_1516221 baseEnd_1516221 := by
    simpa [prefixWord, tailWord_1516221, baseEnd_1516221] using wordTrace_append hprefix tailTrace_1516221
  have hstable : (prefixWord ++ tailWord_1516221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516221).length < 2 ^ (prefixWord ++ tailWord_1516221).sum := by decide
  have hdescent : baseEnd_1516221 < baseStart_1516221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516341 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1516341 : Nat := 118140960795 + 1516341 * 2 ^ 59
def prefixEnd_1516341 : Nat := 4983230072969 + 3 ^ 40 * 1516341 * 2
def baseEnd_1516341 : Nat := 519074512746238028375987

theorem tailTrace_1516341 : CollatzResearch.WordTrace tailWord_1516341 prefixEnd_1516341 519074512746238028375987 := by
  unfold tailWord_1516341
  simp only [CollatzResearch.WordTrace]
  refine ⟨55305499799563002270220877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36870333199708668180147251 55305499799563002270220877)
  ·
    refine ⟨20739562424836125851332829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55305499799563002270220877 20739562424836125851332829)
    ·
      refine ⟨7777335909313547194249811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20739562424836125851332829 7777335909313547194249811)
      ·
        refine ⟨11666003863970320791374717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7777335909313547194249811 11666003863970320791374717)
        ·
          refine ⟨4374751448988870296765519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11666003863970320791374717 4374751448988870296765519)
          ·
            refine ⟨6562127173483305445148279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4374751448988870296765519 6562127173483305445148279)
            ·
              refine ⟨9843190760224958167722419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6562127173483305445148279 9843190760224958167722419)
              ·
                refine ⟨14764786140337437251583629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9843190760224958167722419 14764786140337437251583629)
                ·
                  refine ⟨5536794802626538969343861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14764786140337437251583629 5536794802626538969343861)
                  ·
                    refine ⟨519074512746238028375987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5536794802626538969343861 519074512746238028375987)
                    ·
                      rfl

theorem cell22_1516341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1516341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516341 prefixEnd_1516341 := by exact prefixLift 1516341
  have htrace : WordTrace (prefixWord ++ tailWord_1516341) baseStart_1516341 baseEnd_1516341 := by
    simpa [prefixWord, tailWord_1516341, baseEnd_1516341] using wordTrace_append hprefix tailTrace_1516341
  have hstable : (prefixWord ++ tailWord_1516341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516341).length < 2 ^ (prefixWord ++ tailWord_1516341).sum := by decide
  have hdescent : baseEnd_1516341 < baseStart_1516341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516388 : List Nat := [2, 3, 1, 1, 4, 2, 3, 6]
def baseStart_1516388 : Nat := 118140960795 + 1516388 * 2 ^ 59
def prefixEnd_1516388 : Nat := 4983230072969 + 3 ^ 40 * 1516388 * 2
def baseEnd_1516388 : Nat := 57676733534082841383427

theorem tailTrace_1516388 : CollatzResearch.WordTrace tailWord_1516388 prefixEnd_1516388 57676733534082841383427 := by
  unfold tailWord_1516388
  simp only [CollatzResearch.WordTrace]
  refine ⟨27653607015196364648590909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36871476020261819531454545 27653607015196364648590909)
  ·
    refine ⟨10370102630698636743221591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27653607015196364648590909 10370102630698636743221591)
    ·
      refine ⟨15555153946047955114832387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10370102630698636743221591 15555153946047955114832387)
      ·
        refine ⟨23332730919071932672248581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15555153946047955114832387 23332730919071932672248581)
        ·
          refine ⟨4374887047325987376046609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23332730919071932672248581 4374887047325987376046609)
          ·
            refine ⟨3281165285494490532034957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4374887047325987376046609 3281165285494490532034957)
            ·
              refine ⟨1230436982060433949513109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3281165285494490532034957 1230436982060433949513109)
              ·
                refine ⟨57676733534082841383427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1230436982060433949513109 57676733534082841383427)
                ·
                  rfl

theorem cell22_1516388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 6].length) (baseStart_1516388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516388 prefixEnd_1516388 := by exact prefixLift 1516388
  have htrace : WordTrace (prefixWord ++ tailWord_1516388) baseStart_1516388 baseEnd_1516388 := by
    simpa [prefixWord, tailWord_1516388, baseEnd_1516388] using wordTrace_append hprefix tailTrace_1516388
  have hstable : (prefixWord ++ tailWord_1516388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516388).length < 2 ^ (prefixWord ++ tailWord_1516388).sum := by decide
  have hdescent : baseEnd_1516388 < baseStart_1516388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516416 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 5]
def baseStart_1516416 : Nat := 118140960795 + 1516416 * 2 ^ 59
def prefixEnd_1516416 : Nat := 4983230072969 + 3 ^ 40 * 1516416 * 2
def baseEnd_1516416 : Nat := 173033395592987610916919

theorem tailTrace_1516416 : CollatzResearch.WordTrace tailWord_1516416 prefixEnd_1516416 173033395592987610916919 := by
  unfold tailWord_1516416
  simp only [CollatzResearch.WordTrace]
  refine ⟨27654117637145645039600551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36872156849527526719467401 27654117637145645039600551)
  ·
    refine ⟨41481176455718467559400827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27654117637145645039600551 41481176455718467559400827)
    ·
      refine ⟨62221764683577701339101241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41481176455718467559400827 62221764683577701339101241)
      ·
        refine ⟨46666323512683276004325931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62221764683577701339101241 46666323512683276004325931)
        ·
          refine ⟨69999485269024914006488897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46666323512683276004325931 69999485269024914006488897)
          ·
            refine ⟨52499613951768685504866673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69999485269024914006488897 52499613951768685504866673)
            ·
              refine ⟨39374710463826514128650005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52499613951768685504866673 39374710463826514128650005)
              ·
                refine ⟨1845689552991867849780469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 39374710463826514128650005 1845689552991867849780469)
                ·
                  refine ⟨173033395592987610916919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1845689552991867849780469 173033395592987610916919)
                  ·
                    rfl

theorem cell22_1516416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 5].length) (baseStart_1516416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516416 prefixEnd_1516416 := by exact prefixLift 1516416
  have htrace : WordTrace (prefixWord ++ tailWord_1516416) baseStart_1516416 baseEnd_1516416 := by
    simpa [prefixWord, tailWord_1516416, baseEnd_1516416] using wordTrace_append hprefix tailTrace_1516416
  have hstable : (prefixWord ++ tailWord_1516416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516416).length < 2 ^ (prefixWord ++ tailWord_1516416).sum := by decide
  have hdescent : baseEnd_1516416 < baseStart_1516416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516484 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 5]
def baseStart_1516484 : Nat := 118140960795 + 1516484 * 2 ^ 59
def prefixEnd_1516484 : Nat := 4983230072969 + 3 ^ 40 * 1516484 * 2
def baseEnd_1516484 : Nat := 173041154856211107350183

theorem tailTrace_1516484 : CollatzResearch.WordTrace tailWord_1516484 prefixEnd_1516484 173041154856211107350183 := by
  unfold tailWord_1516484
  simp only [CollatzResearch.WordTrace]
  refine ⟨27655357719022468846338253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36873810292029958461784337 27655357719022468846338253)
  ·
    refine ⟨10370759144633425817376845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27655357719022468846338253 10370759144633425817376845)
    ·
      refine ⟨3889034679237534681516317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10370759144633425817376845 3889034679237534681516317)
      ·
        refine ⟨1458388004714075505568619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3889034679237534681516317 1458388004714075505568619)
        ·
          refine ⟨2187582007071113258352929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458388004714075505568619 2187582007071113258352929)
          ·
            refine ⟨1640686505303334943764697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2187582007071113258352929 1640686505303334943764697)
            ·
              refine ⟨1230514878977501207823523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1640686505303334943764697 1230514878977501207823523)
              ·
                refine ⟨1845772318466251811735285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230514878977501207823523 1845772318466251811735285)
                ·
                  refine ⟨173041154856211107350183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1845772318466251811735285 173041154856211107350183)
                  ·
                    rfl

theorem cell22_1516484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_1516484 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516484 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516484 prefixEnd_1516484 := by exact prefixLift 1516484
  have htrace : WordTrace (prefixWord ++ tailWord_1516484) baseStart_1516484 baseEnd_1516484 := by
    simpa [prefixWord, tailWord_1516484, baseEnd_1516484] using wordTrace_append hprefix tailTrace_1516484
  have hstable : (prefixWord ++ tailWord_1516484).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516484).length < 2 ^ (prefixWord ++ tailWord_1516484).sum := by decide
  have hdescent : baseEnd_1516484 < baseStart_1516484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516514 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1516514 : Nat := 118140960795 + 1516514 * 2 ^ 59
def prefixEnd_1516514 : Nat := 4983230072969 + 3 ^ 40 * 1516514 * 2
def baseEnd_1516514 : Nat := 519133734181723243800457

theorem tailTrace_1516514 : CollatzResearch.WordTrace tailWord_1516514 prefixEnd_1516514 519133734181723243800457 := by
  unfold tailWord_1516514
  simp only [CollatzResearch.WordTrace]
  refine ⟨13827952406984063204067149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36874539751957501877512397 13827952406984063204067149)
  ·
    refine ⟨5185482152619023701525181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13827952406984063204067149 5185482152619023701525181)
    ·
      refine ⟨1944555807232133888071943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5185482152619023701525181 1944555807232133888071943)
      ·
        refine ⟨2916833710848200832107915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1944555807232133888071943 2916833710848200832107915)
        ·
          refine ⟨4375250566272301248161873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2916833710848200832107915 4375250566272301248161873)
          ·
            refine ⟨3281437924704225936121405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4375250566272301248161873 3281437924704225936121405)
            ·
              refine ⟨1230539221764084726045527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3281437924704225936121405 1230539221764084726045527)
              ·
                refine ⟨1845808832646127089068291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1230539221764084726045527 1845808832646127089068291)
                ·
                  refine ⟨2768713248969190633602437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845808832646127089068291 2768713248969190633602437)
                  ·
                    refine ⟨519133734181723243800457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2768713248969190633602437 519133734181723243800457)
                    ·
                      rfl

theorem cell22_1516514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1516514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516514 prefixEnd_1516514 := by exact prefixLift 1516514
  have htrace : WordTrace (prefixWord ++ tailWord_1516514) baseStart_1516514 baseEnd_1516514 := by
    simpa [prefixWord, tailWord_1516514, baseEnd_1516514] using wordTrace_append hprefix tailTrace_1516514
  have hstable : (prefixWord ++ tailWord_1516514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516514).length < 2 ^ (prefixWord ++ tailWord_1516514).sum := by decide
  have hdescent : baseEnd_1516514 < baseStart_1516514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516538 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 7, 3]
def baseStart_1516538 : Nat := 118140960795 + 1516538 * 2 ^ 59
def prefixEnd_1516538 : Nat := 4983230072969 + 3 ^ 40 * 1516538 * 2
def baseEnd_1516538 : Nat := 519141949872195181200383

theorem tailTrace_1516538 : CollatzResearch.WordTrace tailWord_1516538 prefixEnd_1516538 519141949872195181200383 := by
  unfold tailWord_1516538
  simp only [CollatzResearch.WordTrace]
  refine ⟨13828171244962326228785567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 36875123319899536610094845 13828171244962326228785567)
  ·
    refine ⟨20742256867443489343178351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13828171244962326228785567 20742256867443489343178351)
    ·
      refine ⟨31113385301165234014767527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20742256867443489343178351 31113385301165234014767527)
      ·
        refine ⟨46670077951747851022151291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31113385301165234014767527 46670077951747851022151291)
        ·
          refine ⟨70005116927621776533226937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46670077951747851022151291 70005116927621776533226937)
          ·
            refine ⟨52503837695716332399920203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 70005116927621776533226937 52503837695716332399920203)
            ·
              refine ⟨78755756543574498599880305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52503837695716332399920203 78755756543574498599880305)
              ·
                refine ⟨59066817407680873949910229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78755756543574498599880305 59066817407680873949910229)
                ·
                  refine ⟨1384378532992520483201021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 59066817407680873949910229 1384378532992520483201021)
                  ·
                    refine ⟨519141949872195181200383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384378532992520483201021 519141949872195181200383)
                    ·
                      rfl

theorem cell22_1516538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 7, 3].length) (baseStart_1516538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516538 prefixEnd_1516538 := by exact prefixLift 1516538
  have htrace : WordTrace (prefixWord ++ tailWord_1516538) baseStart_1516538 baseEnd_1516538 := by
    simpa [prefixWord, tailWord_1516538, baseEnd_1516538] using wordTrace_append hprefix tailTrace_1516538
  have hstable : (prefixWord ++ tailWord_1516538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516538).length < 2 ^ (prefixWord ++ tailWord_1516538).sum := by decide
  have hdescent : baseEnd_1516538 < baseStart_1516538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516555 : List Nat := [1, 1, 1, 1, 6, 3, 1, 2, 3, 3]
def baseStart_1516555 : Nat := 118140960795 + 1516555 * 2 ^ 59
def prefixEnd_1516555 : Nat := 4983230072969 + 3 ^ 40 * 1516555 * 2
def baseEnd_1516555 : Nat := 519147769319612803525331

theorem tailTrace_1516555 : CollatzResearch.WordTrace tailWord_1516555 prefixEnd_1516555 519147769319612803525331 := by
  unfold tailWord_1516555
  simp only [CollatzResearch.WordTrace]
  refine ⟨55313305020787716818511119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36875536680525144545674079 55313305020787716818511119)
  ·
    refine ⟨82969957531181575227766679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55313305020787716818511119 82969957531181575227766679)
    ·
      refine ⟨124454936296772362841650019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82969957531181575227766679 124454936296772362841650019)
      ·
        refine ⟨186682404445158544262475029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124454936296772362841650019 186682404445158544262475029)
        ·
          refine ⟨8750737708366806762303517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 186682404445158544262475029 8750737708366806762303517)
          ·
            refine ⟨3281526640637552535863819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8750737708366806762303517 3281526640637552535863819)
            ·
              refine ⟨4922289960956328803795729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3281526640637552535863819 4922289960956328803795729)
              ·
                refine ⟨3691717470717246602846797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4922289960956328803795729 3691717470717246602846797)
                ·
                  refine ⟨1384394051518967476067549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3691717470717246602846797 1384394051518967476067549)
                  ·
                    refine ⟨519147769319612803525331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384394051518967476067549 519147769319612803525331)
                    ·
                      rfl

theorem cell22_1516555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 3, 3].length) (baseStart_1516555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516555 prefixEnd_1516555 := by exact prefixLift 1516555
  have htrace : WordTrace (prefixWord ++ tailWord_1516555) baseStart_1516555 baseEnd_1516555 := by
    simpa [prefixWord, tailWord_1516555, baseEnd_1516555] using wordTrace_append hprefix tailTrace_1516555
  have hstable : (prefixWord ++ tailWord_1516555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516555).length < 2 ^ (prefixWord ++ tailWord_1516555).sum := by decide
  have hdescent : baseEnd_1516555 < baseStart_1516555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516613 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 6]
def baseStart_1516613 : Nat := 118140960795 + 1516613 * 2 ^ 59
def prefixEnd_1516613 : Nat := 4983230072969 + 3 ^ 40 * 1516613 * 2
def baseEnd_1516613 : Nat := 173055874634973328525051

theorem tailTrace_1516613 : CollatzResearch.WordTrace tailWord_1516613 prefixEnd_1516613 173055874634973328525051 := by
  unfold tailWord_1516613
  simp only [CollatzResearch.WordTrace]
  refine ⟨55315420454577592724122493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36876946969718395149414995 55315420454577592724122493)
  ·
    refine ⟨20743282670466597271545935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55315420454577592724122493 20743282670466597271545935)
    ·
      refine ⟨31114924005699895907318903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20743282670466597271545935 31114924005699895907318903)
      ·
        refine ⟨46672386008549843860978355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31114924005699895907318903 46672386008549843860978355)
        ·
          refine ⟨70008579012824765791467533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46672386008549843860978355 70008579012824765791467533)
          ·
            refine ⟨26253217129809287171800325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 70008579012824765791467533 26253217129809287171800325)
            ·
              refine ⟨4922478211839241344712561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26253217129809287171800325 4922478211839241344712561)
              ·
                refine ⟨3691858658879431008534421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4922478211839241344712561 3691858658879431008534421)
                ·
                  refine ⟨173055874634973328525051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3691858658879431008534421 173055874634973328525051)
                  ·
                    rfl

theorem cell22_1516613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 6].length) (baseStart_1516613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516613 prefixEnd_1516613 := by exact prefixLift 1516613
  have htrace : WordTrace (prefixWord ++ tailWord_1516613) baseStart_1516613 baseEnd_1516613 := by
    simpa [prefixWord, tailWord_1516613, baseEnd_1516613] using wordTrace_append hprefix tailTrace_1516613
  have hstable : (prefixWord ++ tailWord_1516613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516613).length < 2 ^ (prefixWord ++ tailWord_1516613).sum := by decide
  have hdescent : baseEnd_1516613 < baseStart_1516613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516615 : List Nat := [1, 1, 4, 1, 3, 2, 1, 4, 1, 4]
def baseStart_1516615 : Nat := 118140960795 + 1516615 * 2 ^ 59
def prefixEnd_1516615 : Nat := 4983230072969 + 3 ^ 40 * 1516615 * 2
def baseEnd_1516615 : Nat := 519168308545792647025147

theorem tailTrace_1516615 : CollatzResearch.WordTrace tailWord_1516615 prefixEnd_1516615 519168308545792647025147 := by
  unfold tailWord_1516615
  simp only [CollatzResearch.WordTrace]
  refine ⟨55315493400570347065695299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36876995600380231377130199 55315493400570347065695299)
  ·
    refine ⟨82973240100855520598542949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55315493400570347065695299 82973240100855520598542949)
    ·
      refine ⟨15557482518910410112226803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82973240100855520598542949 15557482518910410112226803)
      ·
        refine ⟨23336223778365615168340205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15557482518910410112226803 23336223778365615168340205)
        ·
          refine ⟨8751083916887105688127577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23336223778365615168340205 8751083916887105688127577)
          ·
            refine ⟨6563312937665329266095683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8751083916887105688127577 6563312937665329266095683)
            ·
              refine ⟨9844969406497993899143525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6563312937665329266095683 9844969406497993899143525)
              ·
                refine ⟨1845931763718373856089411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9844969406497993899143525 1845931763718373856089411)
                ·
                  refine ⟨2768897645577560784134117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1845931763718373856089411 2768897645577560784134117)
                  ·
                    refine ⟨519168308545792647025147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2768897645577560784134117 519168308545792647025147)
                    ·
                      rfl

theorem cell22_1516615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_1516615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516615 prefixEnd_1516615 := by exact prefixLift 1516615
  have htrace : WordTrace (prefixWord ++ tailWord_1516615) baseStart_1516615 baseEnd_1516615 := by
    simpa [prefixWord, tailWord_1516615, baseEnd_1516615] using wordTrace_append hprefix tailTrace_1516615
  have hstable : (prefixWord ++ tailWord_1516615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516615).length < 2 ^ (prefixWord ++ tailWord_1516615).sum := by decide
  have hdescent : baseEnd_1516615 < baseStart_1516615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516645 : List Nat := [1, 3, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_1516645 : Nat := 118140960795 + 1516645 * 2 ^ 59
def prefixEnd_1516645 : Nat := 4983230072969 + 3 ^ 40 * 1516645 * 2
def baseEnd_1516645 : Nat := 519178578158882568775055

theorem tailTrace_1516645 : CollatzResearch.WordTrace tailWord_1516645 prefixEnd_1516645 519178578158882568775055 := by
  unfold tailWord_1516645
  simp only [CollatzResearch.WordTrace]
  refine ⟨55316587590461662189287389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36877725060307774792858259 55316587590461662189287389)
  ·
    refine ⟨20743720346423123320982771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55316587590461662189287389 20743720346423123320982771)
    ·
      refine ⟨31115580519634684981474157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20743720346423123320982771 31115580519634684981474157)
      ·
        refine ⟨11668342694863006868052809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31115580519634684981474157 11668342694863006868052809)
        ·
          refine ⟨8751257021147255151039607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11668342694863006868052809 8751257021147255151039607)
          ·
            refine ⟨13126885531720882726559411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8751257021147255151039607 13126885531720882726559411)
            ·
              refine ⟨19690328297581324089839117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13126885531720882726559411 19690328297581324089839117)
              ·
                refine ⟨7383873111592996533689669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19690328297581324089839117 7383873111592996533689669)
                ·
                  refine ⟨1384476208423686850066813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7383873111592996533689669 1384476208423686850066813)
                  ·
                    refine ⟨519178578158882568775055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384476208423686850066813 519178578158882568775055)
                    ·
                      rfl

theorem cell22_1516645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_1516645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516645 prefixEnd_1516645 := by exact prefixLift 1516645
  have htrace : WordTrace (prefixWord ++ tailWord_1516645) baseStart_1516645 baseEnd_1516645 := by
    simpa [prefixWord, tailWord_1516645, baseEnd_1516645] using wordTrace_append hprefix tailTrace_1516645
  have hstable : (prefixWord ++ tailWord_1516645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516645).length < 2 ^ (prefixWord ++ tailWord_1516645).sum := by decide
  have hdescent : baseEnd_1516645 < baseStart_1516645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516677 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 2, 4]
def baseStart_1516677 : Nat := 118140960795 + 1516677 * 2 ^ 59
def prefixEnd_1516677 : Nat := 4983230072969 + 3 ^ 40 * 1516677 * 2
def baseEnd_1516677 : Nat := 519189532412845151974957

theorem tailTrace_1516677 : CollatzResearch.WordTrace tailWord_1516677 prefixEnd_1516677 519189532412845151974957 := by
  unfold tailWord_1516677
  simp only [CollatzResearch.WordTrace]
  refine ⟨55317754726345731654452285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36878503150897154436301523 55317754726345731654452285)
  ·
    refine ⟨20744158022379649370419607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55317754726345731654452285 20744158022379649370419607)
    ·
      refine ⟨31116237033569474055629411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20744158022379649370419607 31116237033569474055629411)
      ·
        refine ⟨46674355550354211083444117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31116237033569474055629411 46674355550354211083444117)
        ·
          refine ⟨2187860416422853644536443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46674355550354211083444117 2187860416422853644536443)
          ·
            refine ⟨3281790624634280466804665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187860416422853644536443 3281790624634280466804665)
            ·
              refine ⟨2461342968475710350103499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3281790624634280466804665 2461342968475710350103499)
              ·
                refine ⟨3692014452713565525155249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2461342968475710350103499 3692014452713565525155249)
                ·
                  refine ⟨2769010839535174143866437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3692014452713565525155249 2769010839535174143866437)
                  ·
                    refine ⟨519189532412845151974957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2769010839535174143866437 519189532412845151974957)
                    ·
                      rfl

theorem cell22_1516677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_1516677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516677 prefixEnd_1516677 := by exact prefixLift 1516677
  have htrace : WordTrace (prefixWord ++ tailWord_1516677) baseStart_1516677 baseEnd_1516677 := by
    simpa [prefixWord, tailWord_1516677, baseEnd_1516677] using wordTrace_append hprefix tailTrace_1516677
  have hstable : (prefixWord ++ tailWord_1516677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516677).length < 2 ^ (prefixWord ++ tailWord_1516677).sum := by decide
  have hdescent : baseEnd_1516677 < baseStart_1516677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516726 : List Nat := [5, 1, 3, 2, 1, 1, 3, 6]
def baseStart_1516726 : Nat := 118140960795 + 1516726 * 2 ^ 59
def prefixEnd_1516726 : Nat := 4983230072969 + 3 ^ 40 * 1516726 * 2
def baseEnd_1516726 : Nat := 57689589568247261944423

theorem tailTrace_1516726 : CollatzResearch.WordTrace tailWord_1516726 prefixEnd_1516726 57689589568247261944423 := by
  unfold tailWord_1516726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3457471368948013313936627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 36879694602112142015324021 3457471368948013313936627)
  ·
    refine ⟨5186207053422019970904941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3457471368948013313936627 5186207053422019970904941)
    ·
      refine ⟨1944827645033257489089353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5186207053422019970904941 1944827645033257489089353)
      ·
        refine ⟨1458620733774943116817015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1944827645033257489089353 1458620733774943116817015)
        ·
          refine ⟨2187931100662414675225523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458620733774943116817015 2187931100662414675225523)
          ·
            refine ⟨3281896650993622012838285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2187931100662414675225523 3281896650993622012838285)
            ·
              refine ⟨1230711244122608254814357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3281896650993622012838285 1230711244122608254814357)
              ·
                refine ⟨57689589568247261944423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1230711244122608254814357 57689589568247261944423)
                ·
                  rfl

theorem cell22_1516726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 6].length) (baseStart_1516726 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516726 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516726 prefixEnd_1516726 := by exact prefixLift 1516726
  have htrace : WordTrace (prefixWord ++ tailWord_1516726) baseStart_1516726 baseEnd_1516726 := by
    simpa [prefixWord, tailWord_1516726, baseEnd_1516726] using wordTrace_append hprefix tailTrace_1516726
  have hstable : (prefixWord ++ tailWord_1516726).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516726).length < 2 ^ (prefixWord ++ tailWord_1516726).sum := by decide
  have hdescent : baseEnd_1516726 < baseStart_1516726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516799 : List Nat := [1, 1, 2, 2, 1, 7, 1, 3, 4]
def baseStart_1516799 : Nat := 118140960795 + 1516799 * 2 ^ 59
def prefixEnd_1516799 : Nat := 4983230072969 + 3 ^ 40 * 1516799 * 2
def baseEnd_1516799 : Nat := 173077098502025833474861

theorem tailTrace_1516799 : CollatzResearch.WordTrace tailWord_1516799 prefixEnd_1516799 173077098502025833474861 := by
  unfold tailWord_1516799
  simp only [CollatzResearch.WordTrace]
  refine ⟨55322204431903746490393451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36881469621269164326928967 55322204431903746490393451)
  ·
    refine ⟨82983306647855619735590177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55322204431903746490393451 82983306647855619735590177)
    ·
      refine ⟨62237479985891714801692633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82983306647855619735590177 62237479985891714801692633)
      ·
        refine ⟨46678109989418786101269475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62237479985891714801692633 46678109989418786101269475)
        ·
          refine ⟨70017164984128179151904213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46678109989418786101269475 70017164984128179151904213)
          ·
            refine ⟨1641027304315504198872755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 70017164984128179151904213 1641027304315504198872755)
            ·
              refine ⟨2461540956473256298309133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1641027304315504198872755 2461540956473256298309133)
              ·
                refine ⟨923077858677471111865925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2461540956473256298309133 923077858677471111865925)
                ·
                  refine ⟨173077098502025833474861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 923077858677471111865925 173077098502025833474861)
                  ·
                    rfl

theorem cell22_1516799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 1, 3, 4].length) (baseStart_1516799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516799 prefixEnd_1516799 := by exact prefixLift 1516799
  have htrace : WordTrace (prefixWord ++ tailWord_1516799) baseStart_1516799 baseEnd_1516799 := by
    simpa [prefixWord, tailWord_1516799, baseEnd_1516799] using wordTrace_append hprefix tailTrace_1516799
  have hstable : (prefixWord ++ tailWord_1516799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516799).length < 2 ^ (prefixWord ++ tailWord_1516799).sum := by decide
  have hdescent : baseEnd_1516799 < baseStart_1516799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516812 : List Nat := [2, 2, 1, 2, 2, 4, 1, 2, 2, 4]
def baseStart_1516812 : Nat := 118140960795 + 1516812 * 2 ^ 59
def prefixEnd_1516812 : Nat := 4983230072969 + 3 ^ 40 * 1516812 * 2
def baseEnd_1516812 : Nat := 519235745671749799849543

theorem tailTrace_1516812 : CollatzResearch.WordTrace tailWord_1516812 prefixEnd_1516812 519235745671749799849543 := by
  unfold tailWord_1516812
  simp only [CollatzResearch.WordTrace]
  refine ⟨27661339290428324855308345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36881785720571099807077793 27661339290428324855308345)
  ·
    refine ⟨20746004467821243641481259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27661339290428324855308345 20746004467821243641481259)
    ·
      refine ⟨31119006701731865462221889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20746004467821243641481259 31119006701731865462221889)
      ·
        refine ⟨23339255026298899096666417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31119006701731865462221889 23339255026298899096666417)
        ·
          refine ⟨17504441269724174322499813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23339255026298899096666417 17504441269724174322499813)
          ·
            refine ⟨3282082738073282685468715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17504441269724174322499813 3282082738073282685468715)
            ·
              refine ⟨4923124107109924028203073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282082738073282685468715 4923124107109924028203073)
              ·
                refine ⟨3692343080332443021152305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923124107109924028203073 3692343080332443021152305)
                ·
                  refine ⟨2769257310249332265864229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3692343080332443021152305 2769257310249332265864229)
                  ·
                    refine ⟨519235745671749799849543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2769257310249332265864229 519235745671749799849543)
                    ·
                      rfl

theorem cell22_1516812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_1516812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516812 prefixEnd_1516812 := by exact prefixLift 1516812
  have htrace : WordTrace (prefixWord ++ tailWord_1516812) baseStart_1516812 baseEnd_1516812 := by
    simpa [prefixWord, tailWord_1516812, baseEnd_1516812] using wordTrace_append hprefix tailTrace_1516812
  have hstable : (prefixWord ++ tailWord_1516812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516812).length < 2 ^ (prefixWord ++ tailWord_1516812).sum := by decide
  have hdescent : baseEnd_1516812 < baseStart_1516812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516876 : List Nat := [2, 2, 1, 3, 2, 3, 1, 4, 1, 3]
def baseStart_1516876 : Nat := 118140960795 + 1516876 * 2 ^ 59
def prefixEnd_1516876 : Nat := 4983230072969 + 3 ^ 40 * 1516876 * 2
def baseEnd_1516876 : Nat := 519257654179674966249347

theorem tailTrace_1516876 : CollatzResearch.WordTrace tailWord_1516876 prefixEnd_1516876 519257654179674966249347 := by
  unfold tailWord_1516876
  simp only [CollatzResearch.WordTrace]
  refine ⟨27662506426312394320473241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36883341901749859093964321 27662506426312394320473241)
  ·
    refine ⟨20746879819734295740354931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27662506426312394320473241 20746879819734295740354931)
    ·
      refine ⟨31120319729601443610532397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20746879819734295740354931 31120319729601443610532397)
      ·
        refine ⟨11670119898600541353949649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 31120319729601443610532397 11670119898600541353949649)
        ·
          refine ⟨8752589923950406015462237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11670119898600541353949649 8752589923950406015462237)
          ·
            refine ⟨3282221221481402255798339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8752589923950406015462237 3282221221481402255798339)
            ·
              refine ⟨4923331832222103383697509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282221221481402255798339 4923331832222103383697509)
              ·
                refine ⟨923124718541644384443283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4923331832222103383697509 923124718541644384443283)
                ·
                  refine ⟨1384687077812466576664925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923124718541644384443283 1384687077812466576664925)
                  ·
                    refine ⟨519257654179674966249347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384687077812466576664925 519257654179674966249347)
                    ·
                      rfl

theorem cell22_1516876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_1516876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516876 prefixEnd_1516876 := by exact prefixLift 1516876
  have htrace : WordTrace (prefixWord ++ tailWord_1516876) baseStart_1516876 baseEnd_1516876 := by
    simpa [prefixWord, tailWord_1516876, baseEnd_1516876] using wordTrace_append hprefix tailTrace_1516876
  have hstable : (prefixWord ++ tailWord_1516876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516876).length < 2 ^ (prefixWord ++ tailWord_1516876).sum := by decide
  have hdescent : baseEnd_1516876 < baseStart_1516876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516887 : List Nat := [1, 1, 3, 2, 3, 3, 1, 1, 2, 5]
def baseStart_1516887 : Nat := 118140960795 + 1516887 * 2 ^ 59
def prefixEnd_1516887 : Nat := 4983230072969 + 3 ^ 40 * 1516887 * 2
def baseEnd_1516887 : Nat := 519261419704474604224313

theorem tailTrace_1516887 : CollatzResearch.WordTrace tailWord_1516887 prefixEnd_1516887 519261419704474604224313 := by
  unfold tailWord_1516887
  simp only [CollatzResearch.WordTrace]
  refine ⟨55325414055584937519596915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36883609370389958346397943 55325414055584937519596915)
  ·
    refine ⟨82988121083377406279395373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55325414055584937519596915 82988121083377406279395373)
    ·
      refine ⟨31120545406266527354773265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82988121083377406279395373 31120545406266527354773265)
      ·
        refine ⟨23340409054699895516079949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31120545406266527354773265 23340409054699895516079949)
        ·
          refine ⟨8752653395512460818529981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23340409054699895516079949 8752653395512460818529981)
          ·
            refine ⟨3282245023317172806948743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8752653395512460818529981 3282245023317172806948743)
            ·
              refine ⟨4923367534975759210423115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282245023317172806948743 4923367534975759210423115)
              ·
                refine ⟨7385051302463638815634673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4923367534975759210423115 7385051302463638815634673)
                ·
                  refine ⟨5538788476847729111726005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7385051302463638815634673 5538788476847729111726005)
                  ·
                    refine ⟨519261419704474604224313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5538788476847729111726005 519261419704474604224313)
                    ·
                      rfl

theorem cell22_1516887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_1516887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516887 prefixEnd_1516887 := by exact prefixLift 1516887
  have htrace : WordTrace (prefixWord ++ tailWord_1516887) baseStart_1516887 baseEnd_1516887 := by
    simpa [prefixWord, tailWord_1516887, baseEnd_1516887] using wordTrace_append hprefix tailTrace_1516887
  have hstable : (prefixWord ++ tailWord_1516887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516887).length < 2 ^ (prefixWord ++ tailWord_1516887).sum := by decide
  have hdescent : baseEnd_1516887 < baseStart_1516887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516910 : List Nat := [4, 1, 2, 4, 1, 1, 2, 3, 1, 3]
def baseStart_1516910 : Nat := 118140960795 + 1516910 * 2 ^ 59
def prefixEnd_1516910 : Nat := 4983230072969 + 3 ^ 40 * 1516910 * 2
def baseEnd_1516910 : Nat := 519269293074510210899243

theorem tailTrace_1516910 : CollatzResearch.WordTrace tailWord_1516910 prefixEnd_1516910 519269293074510210899243 := by
  unfold tailWord_1516910
  simp only [CollatzResearch.WordTrace]
  refine ⟨6915781616812701555960523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 36884168623001074965122789 6915781616812701555960523)
  ·
    refine ⟨10373672425219052333940785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6915781616812701555960523 10373672425219052333940785)
    ·
      refine ⟨7780254318914289250455589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10373672425219052333940785 7780254318914289250455589)
      ·
        refine ⟨1458797684796429234460423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7780254318914289250455589 1458797684796429234460423)
        ·
          refine ⟨2188196527194643851690635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1458797684796429234460423 2188196527194643851690635)
          ·
            refine ⟨3282294790791965777535953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188196527194643851690635 3282294790791965777535953)
            ·
              refine ⟨2461721093093974333151965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3282294790791965777535953 2461721093093974333151965)
              ·
                refine ⟨923145409910240374931987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2461721093093974333151965 923145409910240374931987)
                ·
                  refine ⟨1384718114865360562397981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923145409910240374931987 1384718114865360562397981)
                  ·
                    refine ⟨519269293074510210899243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384718114865360562397981 519269293074510210899243)
                    ·
                      rfl

theorem cell22_1516910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_1516910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516910 prefixEnd_1516910 := by exact prefixLift 1516910
  have htrace : WordTrace (prefixWord ++ tailWord_1516910) baseStart_1516910 baseEnd_1516910 := by
    simpa [prefixWord, tailWord_1516910, baseEnd_1516910] using wordTrace_append hprefix tailTrace_1516910
  have hstable : (prefixWord ++ tailWord_1516910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516910).length < 2 ^ (prefixWord ++ tailWord_1516910).sum := by decide
  have hdescent : baseEnd_1516910 < baseStart_1516910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1516949 : List Nat := [1, 3, 2, 1, 1, 2, 2, 5, 2, 3]
def baseStart_1516949 : Nat := 118140960795 + 1516949 * 2 ^ 59
def prefixEnd_1516949 : Nat := 4983230072969 + 3 ^ 40 * 1516949 * 2
def baseEnd_1516949 : Nat := 519282643571527109174123

theorem tailTrace_1516949 : CollatzResearch.WordTrace tailWord_1516949 prefixEnd_1516949 519282643571527109174123 := by
  unfold tailWord_1516949
  simp only [CollatzResearch.WordTrace]
  refine ⟨55327675381360322108353901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36885116920906881405569267 55327675381360322108353901)
  ·
    refine ⟨20747878268010120790632713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55327675381360322108353901 20747878268010120790632713)
    ·
      refine ⟨15560908701007590592974535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20747878268010120790632713 15560908701007590592974535)
      ·
        refine ⟨23341363051511385889461803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15560908701007590592974535 23341363051511385889461803)
        ·
          refine ⟨35012044577267078834192705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23341363051511385889461803 35012044577267078834192705)
          ·
            refine ⟨26259033432950309125644529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 35012044577267078834192705 26259033432950309125644529)
            ·
              refine ⟨19694275074712731844233397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26259033432950309125644529 19694275074712731844233397)
              ·
                refine ⟨1846338288254318610396881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19694275074712731844233397 1846338288254318610396881)
                ·
                  refine ⟨1384753716190738957797661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1846338288254318610396881 1384753716190738957797661)
                  ·
                    refine ⟨519282643571527109174123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384753716190738957797661 519282643571527109174123)
                    ·
                      rfl

theorem cell22_1516949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_1516949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1516949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1516949 prefixEnd_1516949 := by exact prefixLift 1516949
  have htrace : WordTrace (prefixWord ++ tailWord_1516949) baseStart_1516949 baseEnd_1516949 := by
    simpa [prefixWord, tailWord_1516949, baseEnd_1516949] using wordTrace_append hprefix tailTrace_1516949
  have hstable : (prefixWord ++ tailWord_1516949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1516949).length < 2 ^ (prefixWord ++ tailWord_1516949).sum := by decide
  have hdescent : baseEnd_1516949 < baseStart_1516949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1516949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517045 : List Nat := [1, 3, 5, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1517045 : Nat := 118140960795 + 1517045 * 2 ^ 59
def prefixEnd_1517045 : Nat := 4983230072969 + 3 ^ 40 * 1517045 * 2
def baseEnd_1517045 : Nat := 519315506333414858773829

theorem tailTrace_1517045 : CollatzResearch.WordTrace tailWord_1517045 prefixEnd_1517045 519315506333414858773829 := by
  unfold tailWord_1517045
  simp only [CollatzResearch.WordTrace]
  refine ⟨55331176789012530503848589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 36887451192675020335899059 55331176789012530503848589)
  ·
    refine ⟨20749191295879698938943221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55331176789012530503848589 20749191295879698938943221)
    ·
      refine ⟨1945236683988721775525927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20749191295879698938943221 1945236683988721775525927)
      ·
        refine ⟨2917855025983082663288891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945236683988721775525927 2917855025983082663288891)
        ·
          refine ⟨4376782538974623994933337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917855025983082663288891 4376782538974623994933337)
          ·
            refine ⟨3282586904230967996200003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4376782538974623994933337 3282586904230967996200003)
            ·
              refine ⟨4923880356346451994300005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282586904230967996200003 4923880356346451994300005)
              ·
                refine ⟨923227566814959748931251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4923880356346451994300005 923227566814959748931251)
                ·
                  refine ⟨1384841350222439623396877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 923227566814959748931251 1384841350222439623396877)
                  ·
                    refine ⟨519315506333414858773829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384841350222439623396877 519315506333414858773829)
                    ·
                      rfl

theorem cell22_1517045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1517045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517045 prefixEnd_1517045 := by exact prefixLift 1517045
  have htrace : WordTrace (prefixWord ++ tailWord_1517045) baseStart_1517045 baseEnd_1517045 := by
    simpa [prefixWord, tailWord_1517045, baseEnd_1517045] using wordTrace_append hprefix tailTrace_1517045
  have hstable : (prefixWord ++ tailWord_1517045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517045).length < 2 ^ (prefixWord ++ tailWord_1517045).sum := by decide
  have hdescent : baseEnd_1517045 < baseStart_1517045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517062 : List Nat := [6, 2, 1, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1517062 : Nat := 118140960795 + 1517062 * 2 ^ 59
def prefixEnd_1517062 : Nat := 4983230072969 + 3 ^ 40 * 1517062 * 2
def baseEnd_1517062 : Nat := 519321325780832481098777

theorem tailTrace_1517062 : CollatzResearch.WordTrace tailWord_1517062 prefixEnd_1517062 519321325780832481098777 := by
  unfold tailWord_1517062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1729118650935966950225545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 36887864553300628271478293 1729118650935966950225545)
  ·
    refine ⟨1296838988201975212669159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1729118650935966950225545 1296838988201975212669159)
    ·
      refine ⟨1945258482302962819003739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1296838988201975212669159 1945258482302962819003739)
      ·
        refine ⟨2917887723454444228505609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1945258482302962819003739 2917887723454444228505609)
        ·
          refine ⟨2188415792590833171379207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2917887723454444228505609 2188415792590833171379207)
          ·
            refine ⟨3282623688886249757068811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2188415792590833171379207 3282623688886249757068811)
            ·
              refine ⟨4923935533329374635603217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3282623688886249757068811 4923935533329374635603217)
              ·
                refine ⟨3692951649997030976702413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4923935533329374635603217 3692951649997030976702413)
                ·
                  refine ⟨1384856868748886616263405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3692951649997030976702413 1384856868748886616263405)
                  ·
                    refine ⟨519321325780832481098777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1384856868748886616263405 519321325780832481098777)
                    ·
                      rfl

theorem cell22_1517062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1517062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517062 prefixEnd_1517062 := by exact prefixLift 1517062
  have htrace : WordTrace (prefixWord ++ tailWord_1517062) baseStart_1517062 baseEnd_1517062 := by
    simpa [prefixWord, tailWord_1517062, baseEnd_1517062] using wordTrace_append hprefix tailTrace_1517062
  have hstable : (prefixWord ++ tailWord_1517062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517062).length < 2 ^ (prefixWord ++ tailWord_1517062).sum := by decide
  have hdescent : baseEnd_1517062 < baseStart_1517062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517084 : List Nat := [2, 2, 3, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1517084 : Nat := 118140960795 + 1517084 * 2 ^ 59
def prefixEnd_1517084 : Nat := 4983230072969 + 3 ^ 40 * 1517084 * 2
def baseEnd_1517084 : Nat := 519328856830431757048709

theorem tailTrace_1517084 : CollatzResearch.WordTrace tailWord_1517084 prefixEnd_1517084 519328856830431757048709 := by
  unfold tailWord_1517084
  simp only [CollatzResearch.WordTrace]
  refine ⟨27666299617935620082259153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36888399490580826776345537 27666299617935620082259153)
  ·
    refine ⟨20749724713451715061694365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27666299617935620082259153 20749724713451715061694365)
    ·
      refine ⟨7781146767544393148135387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20749724713451715061694365 7781146767544393148135387)
      ·
        refine ⟨11671720151316589722203081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7781146767544393148135387 11671720151316589722203081)
        ·
          refine ⟨8753790113487442291652311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11671720151316589722203081 8753790113487442291652311)
          ·
            refine ⟨13130685170231163437478467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8753790113487442291652311 13130685170231163437478467)
            ·
              refine ⟨19696027755346745156217701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13130685170231163437478467 19696027755346745156217701)
              ·
                refine ⟨3693005204127514716790819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19696027755346745156217701 3693005204127514716790819)
                ·
                  refine ⟨5539507806191272075186229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3693005204127514716790819 5539507806191272075186229)
                  ·
                    refine ⟨519328856830431757048709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5539507806191272075186229 519328856830431757048709)
                    ·
                      rfl

theorem cell22_1517084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1517084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517084 prefixEnd_1517084 := by exact prefixLift 1517084
  have htrace : WordTrace (prefixWord ++ tailWord_1517084) baseStart_1517084 baseEnd_1517084 := by
    simpa [prefixWord, tailWord_1517084, baseEnd_1517084] using wordTrace_append hprefix tailTrace_1517084
  have hstable : (prefixWord ++ tailWord_1517084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517084).length < 2 ^ (prefixWord ++ tailWord_1517084).sum := by decide
  have hdescent : baseEnd_1517084 < baseStart_1517084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1517088 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 1, 4]
def baseStart_1517088 : Nat := 118140960795 + 1517088 * 2 ^ 59
def prefixEnd_1517088 : Nat := 4983230072969 + 3 ^ 40 * 1517088 * 2
def baseEnd_1517088 : Nat := 519330226112177079948697

theorem tailTrace_1517088 : CollatzResearch.WordTrace tailWord_1517088 prefixEnd_1517088 519330226112177079948697 := by
  unfold tailWord_1517088
  simp only [CollatzResearch.WordTrace]
  refine ⟨27666372563928374423831959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 36888496751904499231775945 27666372563928374423831959)
  ·
    refine ⟨41499558845892561635747939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27666372563928374423831959 41499558845892561635747939)
    ·
      refine ⟨62249338268838842453621909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41499558845892561635747939 62249338268838842453621909)
      ·
        refine ⟨2917937731351820740013527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 62249338268838842453621909 2917937731351820740013527)
        ·
          refine ⟨4376906597027731110020291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2917937731351820740013527 4376906597027731110020291)
          ·
            refine ⟨6565359895541596665030437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4376906597027731110020291 6565359895541596665030437)
            ·
              refine ⟨1231004980414049374693207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6565359895541596665030437 1231004980414049374693207)
              ·
                refine ⟨1846507470621074062039811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1231004980414049374693207 1846507470621074062039811)
                ·
                  refine ⟨2769761205931611093059717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1846507470621074062039811 2769761205931611093059717)
                  ·
                    refine ⟨519330226112177079948697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2769761205931611093059717 519330226112177079948697)
                    ·
                      rfl

theorem cell22_1517088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 1, 4].length) (baseStart_1517088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1517088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1517088 prefixEnd_1517088 := by exact prefixLift 1517088
  have htrace : WordTrace (prefixWord ++ tailWord_1517088) baseStart_1517088 baseEnd_1517088 := by
    simpa [prefixWord, tailWord_1517088, baseEnd_1517088] using wordTrace_append hprefix tailTrace_1517088
  have hstable : (prefixWord ++ tailWord_1517088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1517088).length < 2 ^ (prefixWord ++ tailWord_1517088).sum := by decide
  have hdescent : baseEnd_1517088 < baseStart_1517088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1517088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
