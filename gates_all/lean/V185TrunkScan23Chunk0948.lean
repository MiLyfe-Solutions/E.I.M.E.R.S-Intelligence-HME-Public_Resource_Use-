import V185TrunkScan23Chunk0947

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5611751 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5611751 : Nat := 118140960795 + 5611751 * 2 ^ 59
def prefixEnd_5611751 : Nat := 4983230072969 + 3 ^ 40 * 5611751 * 2
def baseEnd_5611751 : Nat := 2881525576349178732104533

theorem tailTrace_5611751 : CollatzResearch.WordTrace tailWord_5611751 prefixEnd_5611751 2881525576349178732104533 := by
  unfold tailWord_5611751
  simp only [CollatzResearch.WordTrace]
  refine ⟨204677373892592012612931107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136451582595061341741954071 204677373892592012612931107)
  ·
    refine ⟨307016060838888018919396661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204677373892592012612931107 307016060838888018919396661)
    ·
      refine ⟨28782755703645751773693437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 307016060838888018919396661 28782755703645751773693437)
      ·
        refine ⟨10793533388867156915135039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28782755703645751773693437 10793533388867156915135039)
        ·
          refine ⟨16190300083300735372702559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10793533388867156915135039 16190300083300735372702559)
          ·
            refine ⟨24285450124951103059053839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16190300083300735372702559 24285450124951103059053839)
            ·
              refine ⟨36428175187426654588580759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24285450124951103059053839 36428175187426654588580759)
              ·
                refine ⟨54642262781139981882871139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36428175187426654588580759 54642262781139981882871139)
                ·
                  refine ⟨81963394171709972824306709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54642262781139981882871139 81963394171709972824306709)
                  ·
                    refine ⟨3842034101798904976139377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81963394171709972824306709 3842034101798904976139377)
                    ·
                      refine ⟨2881525576349178732104533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842034101798904976139377 2881525576349178732104533)
                      ·
                        rfl

theorem cell23_5611751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5611751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611751 prefixEnd_5611751 := by exact prefixLift 5611751
  have htrace : WordTrace (prefixWord ++ tailWord_5611751) baseStart_5611751 baseEnd_5611751 := by
    simpa [prefixWord, tailWord_5611751, baseEnd_5611751] using wordTrace_append hprefix tailTrace_5611751
  have hstable : (prefixWord ++ tailWord_5611751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611751).length < 2 ^ (prefixWord ++ tailWord_5611751).sum := by decide
  have hdescent : baseEnd_5611751 < baseStart_5611751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611754 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3]
def baseStart_5611754 : Nat := 118140960795 + 5611754 * 2 ^ 59
def prefixEnd_5611754 : Nat := 4983230072969 + 3 ^ 40 * 5611754 * 2
def baseEnd_5611754 : Nat := 2881527116791142220367019

theorem tailTrace_5611754 : CollatzResearch.WordTrace tailWord_5611754 prefixEnd_5611754 2881527116791142220367019 := by
  unfold tailWord_5611754
  simp only [CollatzResearch.WordTrace]
  refine ⟨51169370827895286031322579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136451655541054096083526877 51169370827895286031322579)
  ·
    refine ⟨76754056241842929046983869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51169370827895286031322579 76754056241842929046983869)
    ·
      refine ⟨28782771090691098392618951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76754056241842929046983869 28782771090691098392618951)
      ·
        refine ⟨43174156636036647588928427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28782771090691098392618951 43174156636036647588928427)
        ·
          refine ⟨64761234954054971383392641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43174156636036647588928427 64761234954054971383392641)
          ·
            refine ⟨48570926215541228537544481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64761234954054971383392641 48570926215541228537544481)
            ·
              refine ⟨36428194661655921403158361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48570926215541228537544481 36428194661655921403158361)
              ·
                refine ⟨27321145996241941052368771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36428194661655921403158361 27321145996241941052368771)
                ·
                  refine ⟨40981718994362911578553157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27321145996241941052368771 40981718994362911578553157)
                  ·
                    refine ⟨7684072311443045920978717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40981718994362911578553157 7684072311443045920978717)
                    ·
                      refine ⟨2881527116791142220367019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7684072311443045920978717 2881527116791142220367019)
                      ·
                        rfl

theorem cell23_5611754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 4, 3].length) (baseStart_5611754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611754 prefixEnd_5611754 := by exact prefixLift 5611754
  have htrace : WordTrace (prefixWord ++ tailWord_5611754) baseStart_5611754 baseEnd_5611754 := by
    simpa [prefixWord, tailWord_5611754, baseEnd_5611754] using wordTrace_append hprefix tailTrace_5611754
  have hstable : (prefixWord ++ tailWord_5611754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611754).length < 2 ^ (prefixWord ++ tailWord_5611754).sum := by decide
  have hdescent : baseEnd_5611754 < baseStart_5611754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611774 : List Nat := [4, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_5611774 : Nat := 118140960795 + 5611774 * 2 ^ 59
def prefixEnd_5611774 : Nat := 4983230072969 + 3 ^ 40 * 5611774 * 2
def baseEnd_5611774 : Nat := 320170820711581349124103

theorem tailTrace_5611774 : CollatzResearch.WordTrace tailWord_5611774 prefixEnd_5611774 320170820711581349124103 := by
  unfold tailWord_5611774
  simp only [CollatzResearch.WordTrace]
  refine ⟨25584776596438585942627297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136452141847672458360678917 25584776596438585942627297)
  ·
    refine ⟨19188582447328939456970473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25584776596438585942627297 19188582447328939456970473)
    ·
      refine ⟨14391436835496704592727855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19188582447328939456970473 14391436835496704592727855)
      ·
        refine ⟨21587155253245056889091783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14391436835496704592727855 21587155253245056889091783)
        ·
          refine ⟨32380732879867585333637675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21587155253245056889091783 32380732879867585333637675)
          ·
            refine ⟨48571099319801378000456513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32380732879867585333637675 48571099319801378000456513)
            ·
              refine ⟨36428324489851033500342385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48571099319801378000456513 36428324489851033500342385)
              ·
                refine ⟨27321243367388275125256789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36428324489851033500342385 27321243367388275125256789)
                ·
                  refine ⟨320170820711581349124103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27321243367388275125256789 320170820711581349124103)
                  ·
                    rfl

theorem cell23_5611774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_5611774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611774 prefixEnd_5611774 := by exact prefixLift 5611774
  have htrace : WordTrace (prefixWord ++ tailWord_5611774) baseStart_5611774 baseEnd_5611774 := by
    simpa [prefixWord, tailWord_5611774, baseEnd_5611774] using wordTrace_append hprefix tailTrace_5611774
  have hstable : (prefixWord ++ tailWord_5611774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611774).length < 2 ^ (prefixWord ++ tailWord_5611774).sum := by decide
  have hdescent : baseEnd_5611774 < baseStart_5611774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611828 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_5611828 : Nat := 118140960795 + 5611828 * 2 ^ 59
def prefixEnd_5611828 : Nat := 4983230072969 + 3 ^ 40 * 5611828 * 2
def baseEnd_5611828 : Nat := 2881565114359574930841679

theorem tailTrace_5611828 : CollatzResearch.WordTrace tailWord_5611828 prefixEnd_5611828 2881565114359574930841679 := by
  unfold tailWord_5611828
  simp only [CollatzResearch.WordTrace]
  refine ⟨102340091156656527381742069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136453454875542036508989425 102340091156656527381742069)
  ·
    refine ⟨9594383545936549442038319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 102340091156656527381742069 9594383545936549442038319)
    ·
      refine ⟨14391575318904824163057479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9594383545936549442038319 14391575318904824163057479)
      ·
        refine ⟨21587362978357236244586219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14391575318904824163057479 21587362978357236244586219)
        ·
          refine ⟨32381044467535854366879329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21587362978357236244586219 32381044467535854366879329)
          ·
            refine ⟨24285783350651890775159497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32381044467535854366879329 24285783350651890775159497)
            ·
              refine ⟨18214337512988918081369623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24285783350651890775159497 18214337512988918081369623)
              ·
                refine ⟨27321506269483377122054435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18214337512988918081369623 27321506269483377122054435)
                ·
                  refine ⟨40982259404225065683081653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27321506269483377122054435 40982259404225065683081653)
                  ·
                    refine ⟨3842086819146099907788905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40982259404225065683081653 3842086819146099907788905)
                    ·
                      refine ⟨2881565114359574930841679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842086819146099907788905 2881565114359574930841679)
                      ·
                        rfl

theorem cell23_5611828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_5611828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611828 prefixEnd_5611828 := by exact prefixLift 5611828
  have htrace : WordTrace (prefixWord ++ tailWord_5611828) baseStart_5611828 baseEnd_5611828 := by
    simpa [prefixWord, tailWord_5611828, baseEnd_5611828] using wordTrace_append hprefix tailTrace_5611828
  have hstable : (prefixWord ++ tailWord_5611828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611828).length < 2 ^ (prefixWord ++ tailWord_5611828).sum := by decide
  have hdescent : baseEnd_5611828 < baseStart_5611828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611854 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4]
def baseStart_5611854 : Nat := 118140960795 + 5611854 * 2 ^ 59
def prefixEnd_5611854 : Nat := 4983230072969 + 3 ^ 40 * 5611854 * 2
def baseEnd_5611854 : Nat := 2881578464856591829116559

theorem tailTrace_5611854 : CollatzResearch.WordTrace tailWord_5611854 prefixEnd_5611854 2881578464856591829116559 := by
  unfold tailWord_5611854
  simp only [CollatzResearch.WordTrace]
  refine ⟨25585141326402357650491327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136454087074145907469287077 25585141326402357650491327)
  ·
    refine ⟨38377711989603536475736991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25585141326402357650491327 38377711989603536475736991)
    ·
      refine ⟨57566567984405304713605487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38377711989603536475736991 57566567984405304713605487)
      ·
        refine ⟨86349851976607957070408231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57566567984405304713605487 86349851976607957070408231)
        ·
          refine ⟨129524777964911935605612347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86349851976607957070408231 129524777964911935605612347)
          ·
            refine ⟨194287166947367903408418521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129524777964911935605612347 194287166947367903408418521)
            ·
              refine ⟨145715375210525927556313891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194287166947367903408418521 145715375210525927556313891)
              ·
                refine ⟨218573062815788891334470837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145715375210525927556313891 218573062815788891334470837)
                ·
                  refine ⟨20491224638980208562606641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218573062815788891334470837 20491224638980208562606641)
                  ·
                    refine ⟨15368418479235156421954981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20491224638980208562606641 15368418479235156421954981)
                    ·
                      refine ⟨2881578464856591829116559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15368418479235156421954981 2881578464856591829116559)
                      ·
                        rfl

theorem cell23_5611854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_5611854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611854 prefixEnd_5611854 := by exact prefixLift 5611854
  have htrace : WordTrace (prefixWord ++ tailWord_5611854) baseStart_5611854 baseEnd_5611854 := by
    simpa [prefixWord, tailWord_5611854, baseEnd_5611854] using wordTrace_append hprefix tailTrace_5611854
  have hstable : (prefixWord ++ tailWord_5611854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611854).length < 2 ^ (prefixWord ++ tailWord_5611854).sum := by decide
  have hdescent : baseEnd_5611854 < baseStart_5611854 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611926 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5611926 : Nat := 118140960795 + 5611926 * 2 ^ 59
def prefixEnd_5611926 : Nat := 4983230072969 + 3 ^ 40 * 5611926 * 2
def baseEnd_5611926 : Nat := 2881615435463715547416229

theorem tailTrace_5611926 : CollatzResearch.WordTrace tailWord_5611926 prefixEnd_5611926 2881615435463715547416229 := by
  unfold tailWord_5611926
  simp only [CollatzResearch.WordTrace]
  refine ⟨12792734791684876093784477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136455837777972011667034421 12792734791684876093784477)
  ·
    refine ⟨4797275546881828535169179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12792734791684876093784477 4797275546881828535169179)
    ·
      refine ⟨7195913320322742802753769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4797275546881828535169179 7195913320322742802753769)
      ·
        refine ⟨5396934990242057102065327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7195913320322742802753769 5396934990242057102065327)
        ·
          refine ⟨8095402485363085653097991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5396934990242057102065327 8095402485363085653097991)
          ·
            refine ⟨12143103728044628479646987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8095402485363085653097991 12143103728044628479646987)
            ·
              refine ⟨18214655592066942719470481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12143103728044628479646987 18214655592066942719470481)
              ·
                refine ⟨13660991694050207039602861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18214655592066942719470481 13660991694050207039602861)
                ·
                  refine ⟨5122871885268827639851073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13660991694050207039602861 5122871885268827639851073)
                  ·
                    refine ⟨3842153913951620729888305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5122871885268827639851073 3842153913951620729888305)
                    ·
                      refine ⟨2881615435463715547416229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842153913951620729888305 2881615435463715547416229)
                      ·
                        rfl

theorem cell23_5611926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5611926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611926 prefixEnd_5611926 := by exact prefixLift 5611926
  have htrace : WordTrace (prefixWord ++ tailWord_5611926) baseStart_5611926 baseEnd_5611926 := by
    simpa [prefixWord, tailWord_5611926, baseEnd_5611926] using wordTrace_append hprefix tailTrace_5611926
  have hstable : (prefixWord ++ tailWord_5611926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611926).length < 2 ^ (prefixWord ++ tailWord_5611926).sum := by decide
  have hdescent : baseEnd_5611926 < baseStart_5611926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611946 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3]
def baseStart_5611946 : Nat := 118140960795 + 5611946 * 2 ^ 59
def prefixEnd_5611946 : Nat := 4983230072969 + 3 ^ 40 * 5611946 * 2
def baseEnd_5611946 : Nat := 2881625705076805469166137

theorem tailTrace_5611946 : CollatzResearch.WordTrace tailWord_5611946 prefixEnd_5611946 2881625705076805469166137 := by
  unfold tailWord_5611946
  simp only [CollatzResearch.WordTrace]
  refine ⟨51171121531721390229069923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136456324084590373944186461 51171121531721390229069923)
  ·
    refine ⟨76756682297582085343604885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51171121531721390229069923 76756682297582085343604885)
    ·
      refine ⟨3597969482699160250481479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 76756682297582085343604885 3597969482699160250481479)
      ·
        refine ⟨5396954224048740375722219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3597969482699160250481479 5396954224048740375722219)
        ·
          refine ⟨8095431336073110563583329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5396954224048740375722219 8095431336073110563583329)
          ·
            refine ⟨6071573502054832922687497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8095431336073110563583329 6071573502054832922687497)
            ·
              refine ⟨4553680126541124692015623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6071573502054832922687497 4553680126541124692015623)
              ·
                refine ⟨6830520189811687038023435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4553680126541124692015623 6830520189811687038023435)
                ·
                  refine ⟨10245780284717530557035153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6830520189811687038023435 10245780284717530557035153)
                  ·
                    refine ⟨7684335213538147917776365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10245780284717530557035153 7684335213538147917776365)
                    ·
                      refine ⟨2881625705076805469166137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7684335213538147917776365 2881625705076805469166137)
                      ·
                        rfl

theorem cell23_5611946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_5611946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611946 prefixEnd_5611946 := by exact prefixLift 5611946
  have htrace : WordTrace (prefixWord ++ tailWord_5611946) baseStart_5611946 baseEnd_5611946 := by
    simpa [prefixWord, tailWord_5611946, baseEnd_5611946] using wordTrace_append hprefix tailTrace_5611946
  have hstable : (prefixWord ++ tailWord_5611946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611946).length < 2 ^ (prefixWord ++ tailWord_5611946).sum := by decide
  have hdescent : baseEnd_5611946 < baseStart_5611946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611948 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 4, 2, 2]
def baseStart_5611948 : Nat := 118140960795 + 5611948 * 2 ^ 59
def prefixEnd_5611948 : Nat := 4983230072969 + 3 ^ 40 * 5611948 * 2
def baseEnd_5611948 : Nat := 2881626732038114461341127

theorem tailTrace_5611948 : CollatzResearch.WordTrace tailWord_5611948 prefixEnd_5611948 2881626732038114461341127 := by
  unfold tailWord_5611948
  simp only [CollatzResearch.WordTrace]
  refine ⟨102342279536439157628926249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136456372715252210171901665 102342279536439157628926249)
  ·
    refine ⟨76756709652329368221694687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102342279536439157628926249 76756709652329368221694687)
    ·
      refine ⟨115135064478494052332542031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76756709652329368221694687 115135064478494052332542031)
      ·
        refine ⟨172702596717741078498813047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115135064478494052332542031 172702596717741078498813047)
        ·
          refine ⟨259053895076611617748219571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172702596717741078498813047 259053895076611617748219571)
          ·
            refine ⟨388580842614917426622329357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259053895076611617748219571 388580842614917426622329357)
            ·
              refine ⟨145717815980594034983373509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388580842614917426622329357 145717815980594034983373509)
              ·
                refine ⟨27322090496361381559382533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145717815980594034983373509 27322090496361381559382533)
                ·
                  refine ⟨5122891968067759042384225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27322090496361381559382533 5122891968067759042384225)
                  ·
                    refine ⟨3842168976050819281788169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5122891968067759042384225 3842168976050819281788169)
                    ·
                      refine ⟨2881626732038114461341127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842168976050819281788169 2881626732038114461341127)
                      ·
                        rfl

theorem cell23_5611948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_5611948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611948 prefixEnd_5611948 := by exact prefixLift 5611948
  have htrace : WordTrace (prefixWord ++ tailWord_5611948) baseStart_5611948 baseEnd_5611948 := by
    simpa [prefixWord, tailWord_5611948, baseEnd_5611948] using wordTrace_append hprefix tailTrace_5611948
  have hstable : (prefixWord ++ tailWord_5611948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611948).length < 2 ^ (prefixWord ++ tailWord_5611948).sum := by decide
  have hdescent : baseEnd_5611948 < baseStart_5611948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611954 : List Nat := [3, 2, 1, 1, 1, 1, 3, 2, 9]
def baseStart_5611954 : Nat := 118140960795 + 5611954 * 2 ^ 59
def prefixEnd_5611954 : Nat := 4983230072969 + 3 ^ 40 * 5611954 * 2
def baseEnd_5611954 : Nat := 320181090324671270874011

theorem tailTrace_5611954 : CollatzResearch.WordTrace tailWord_5611954 prefixEnd_5611954 320181090324671270874011 := by
  unfold tailWord_5611954
  simp only [CollatzResearch.WordTrace]
  refine ⟨51171194477714144570642729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136456518607237718855047277 51171194477714144570642729)
  ·
    refine ⟨38378395858285608427982047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51171194477714144570642729 38378395858285608427982047)
    ·
      refine ⟨57567593787428412641973071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38378395858285608427982047 57567593787428412641973071)
      ·
        refine ⟨86351390681142618962959607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57567593787428412641973071 86351390681142618962959607)
        ·
          refine ⟨129527086021713928444439411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86351390681142618962959607 129527086021713928444439411)
          ·
            refine ⟨194290629032570892666659117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129527086021713928444439411 194290629032570892666659117)
            ·
              refine ⟨72858985887214084749997169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194290629032570892666659117 72858985887214084749997169)
              ·
                refine ⟨54644239415410563562497877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72858985887214084749997169 54644239415410563562497877)
                ·
                  refine ⟨320181090324671270874011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 54644239415410563562497877 320181090324671270874011)
                  ·
                    rfl

theorem cell23_5611954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_5611954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611954 prefixEnd_5611954 := by exact prefixLift 5611954
  have htrace : WordTrace (prefixWord ++ tailWord_5611954) baseStart_5611954 baseEnd_5611954 := by
    simpa [prefixWord, tailWord_5611954, baseEnd_5611954] using wordTrace_append hprefix tailTrace_5611954
  have hstable : (prefixWord ++ tailWord_5611954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611954).length < 2 ^ (prefixWord ++ tailWord_5611954).sum := by decide
  have hdescent : baseEnd_5611954 < baseStart_5611954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611961 : List Nat := [1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 4]
def baseStart_5611961 : Nat := 118140960795 + 5611961 * 2 ^ 59
def prefixEnd_5611961 : Nat := 4983230072969 + 3 ^ 40 * 5611961 * 2
def baseEnd_5611961 : Nat := 2881633407286622910478567

theorem tailTrace_5611961 : CollatzResearch.WordTrace tailWord_5611961 prefixEnd_5611961 2881633407286622910478567 := by
  unfold tailWord_5611961
  simp only [CollatzResearch.WordTrace]
  refine ⟨204685033221831218478075737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136456688814554145652050491 204685033221831218478075737)
  ·
    refine ⟨153513774916373413858556803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204685033221831218478075737 153513774916373413858556803)
    ·
      refine ⟨230270662374560120787835205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153513774916373413858556803 230270662374560120787835205)
      ·
        refine ⟨43175749195230022647719101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230270662374560120787835205 43175749195230022647719101)
        ·
          refine ⟨16190905948211258492894663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43175749195230022647719101 16190905948211258492894663)
          ·
            refine ⟨24286358922316887739341995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16190905948211258492894663 24286358922316887739341995)
            ·
              refine ⟨36429538383475331609012993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24286358922316887739341995 36429538383475331609012993)
              ·
                refine ⟨27322153787606498706759745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36429538383475331609012993 27322153787606498706759745)
                ·
                  refine ⟨20491615340704874030069809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27322153787606498706759745 20491615340704874030069809)
                  ·
                    refine ⟨15368711505528655522552357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20491615340704874030069809 15368711505528655522552357)
                    ·
                      refine ⟨2881633407286622910478567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15368711505528655522552357 2881633407286622910478567)
                      ·
                        rfl

theorem cell23_5611961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_5611961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611961 prefixEnd_5611961 := by exact prefixLift 5611961
  have htrace : WordTrace (prefixWord ++ tailWord_5611961) baseStart_5611961 baseEnd_5611961 := by
    simpa [prefixWord, tailWord_5611961, baseEnd_5611961] using wordTrace_append hprefix tailTrace_5611961
  have hstable : (prefixWord ++ tailWord_5611961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611961).length < 2 ^ (prefixWord ++ tailWord_5611961).sum := by decide
  have hdescent : baseEnd_5611961 < baseStart_5611961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5611965 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 4, 2, 2]
def baseStart_5611965 : Nat := 118140960795 + 5611965 * 2 ^ 59
def prefixEnd_5611965 : Nat := 4983230072969 + 3 ^ 40 * 5611965 * 2
def baseEnd_5611965 : Nat := 2881635461209240894828549

theorem tailTrace_5611965 : CollatzResearch.WordTrace tailWord_5611965 prefixEnd_5611965 2881635461209240894828549 := by
  unfold tailWord_5611965
  simp only [CollatzResearch.WordTrace]
  refine ⟨204685179113816727161221349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136456786075877818107480899 204685179113816727161221349)
  ·
    refine ⟨38378471083840636342729003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204685179113816727161221349 38378471083840636342729003)
    ·
      refine ⟨57567706625760954514093505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38378471083840636342729003 57567706625760954514093505)
      ·
        refine ⟨43175779969320715885570129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57567706625760954514093505 43175779969320715885570129)
        ·
          refine ⟨32381834976990536914177597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43175779969320715885570129 32381834976990536914177597)
          ·
            refine ⟨12143188116371451342816599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32381834976990536914177597 12143188116371451342816599)
            ·
              refine ⟨18214782174557177014224899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12143188116371451342816599 18214782174557177014224899)
              ·
                refine ⟨27322173261835765521337349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18214782174557177014224899 27322173261835765521337349)
                ·
                  refine ⟨5122907486594206035250753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27322173261835765521337349 5122907486594206035250753)
                  ·
                    refine ⟨3842180614945654526438065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5122907486594206035250753 3842180614945654526438065)
                    ·
                      refine ⟨2881635461209240894828549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842180614945654526438065 2881635461209240894828549)
                      ·
                        rfl

theorem cell23_5611965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_5611965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5611965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5611965 prefixEnd_5611965 := by exact prefixLift 5611965
  have htrace : WordTrace (prefixWord ++ tailWord_5611965) baseStart_5611965 baseEnd_5611965 := by
    simpa [prefixWord, tailWord_5611965, baseEnd_5611965] using wordTrace_append hprefix tailTrace_5611965
  have hstable : (prefixWord ++ tailWord_5611965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5611965).length < 2 ^ (prefixWord ++ tailWord_5611965).sum := by decide
  have hdescent : baseEnd_5611965 < baseStart_5611965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5611965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612001 : List Nat := [1, 2, 3, 1, 2, 2, 2, 3, 2, 5]
def baseStart_5612001 : Nat := 118140960795 + 5612001 * 2 ^ 59
def prefixEnd_5612001 : Nat := 4983230072969 + 3 ^ 40 * 5612001 * 2
def baseEnd_5612001 : Nat := 960551315504267584659461

theorem tailTrace_5612001 : CollatzResearch.WordTrace tailWord_5612001 prefixEnd_5612001 960551315504267584659461 := by
  unfold tailWord_5612001
  simp only [CollatzResearch.WordTrace]
  refine ⟨204686492141686305309531857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136457661427790870206354571 204686492141686305309531857)
  ·
    refine ⟨153514869106264728982148893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204686492141686305309531857 153514869106264728982148893)
    ·
      refine ⟨57568075914849273368305835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153514869106264728982148893 57568075914849273368305835)
      ·
        refine ⟨86352113872273910052458753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57568075914849273368305835 86352113872273910052458753)
        ·
          refine ⟨64764085404205432539344065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86352113872273910052458753 64764085404205432539344065)
          ·
            refine ⟨48573064053154074404508049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64764085404205432539344065 48573064053154074404508049)
            ·
              refine ⟨36429798039865555803381037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48573064053154074404508049 36429798039865555803381037)
              ·
                refine ⟨13661174264949583426267889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36429798039865555803381037 13661174264949583426267889)
                ·
                  refine ⟨10245880698712187569700917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13661174264949583426267889 10245880698712187569700917)
                  ·
                    refine ⟨960551315504267584659461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10245880698712187569700917 960551315504267584659461)
                    ·
                      rfl

theorem cell23_5612001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_5612001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612001 prefixEnd_5612001 := by exact prefixLift 5612001
  have htrace : WordTrace (prefixWord ++ tailWord_5612001) baseStart_5612001 baseEnd_5612001 := by
    simpa [prefixWord, tailWord_5612001, baseEnd_5612001] using wordTrace_append hprefix tailTrace_5612001
  have hstable : (prefixWord ++ tailWord_5612001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612001).length < 2 ^ (prefixWord ++ tailWord_5612001).sum := by decide
  have hdescent : baseEnd_5612001 < baseStart_5612001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612041 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 3]
def baseStart_5612041 : Nat := 118140960795 + 5612041 * 2 ^ 59
def prefixEnd_5612041 : Nat := 4983230072969 + 3 ^ 40 * 5612041 * 2
def baseEnd_5612041 : Nat := 2881674485738982597478199

theorem tailTrace_5612041 : CollatzResearch.WordTrace tailWord_5612041 prefixEnd_5612041 2881674485738982597478199 := by
  unfold tailWord_5612041
  simp only [CollatzResearch.WordTrace]
  refine ⟨204687951061541392140987977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136458634041027594760658651 204687951061541392140987977)
  ·
    refine ⟨153515963296156044105740983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204687951061541392140987977 153515963296156044105740983)
    ·
      refine ⟨230273944944234066158611475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153515963296156044105740983 230273944944234066158611475)
      ·
        refine ⟨345410917416351099237917213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230273944944234066158611475 345410917416351099237917213)
        ·
          refine ⟨129529094031131662214218955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345410917416351099237917213 129529094031131662214218955)
          ·
            refine ⟨194293641046697493321328433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129529094031131662214218955 194293641046697493321328433)
            ·
              refine ⟨145720230785023119990996325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194293641046697493321328433 145720230785023119990996325)
              ·
                refine ⟨27322543272191834998311811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 145720230785023119990996325 27322543272191834998311811)
                ·
                  refine ⟨40983814908287752497467717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27322543272191834998311811 40983814908287752497467717)
                  ·
                    refine ⟨7684465295303953593275197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40983814908287752497467717 7684465295303953593275197)
                    ·
                      refine ⟨2881674485738982597478199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7684465295303953593275197 2881674485738982597478199)
                      ·
                        rfl

theorem cell23_5612041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 4, 3].length) (baseStart_5612041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612041 prefixEnd_5612041 := by exact prefixLift 5612041
  have htrace : WordTrace (prefixWord ++ tailWord_5612041) baseStart_5612041 baseEnd_5612041 := by
    simpa [prefixWord, tailWord_5612041, baseEnd_5612041] using wordTrace_append hprefix tailTrace_5612041
  have hstable : (prefixWord ++ tailWord_5612041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612041).length < 2 ^ (prefixWord ++ tailWord_5612041).sum := by decide
  have hdescent : baseEnd_5612041 < baseStart_5612041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612058 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3]
def baseStart_5612058 : Nat := 118140960795 + 5612058 * 2 ^ 59
def prefixEnd_5612058 : Nat := 4983230072969 + 3 ^ 40 * 5612058 * 2
def baseEnd_5612058 : Nat := 2881683214910109030965621

theorem tailTrace_5612058 : CollatzResearch.WordTrace tailWord_5612058 prefixEnd_5612058 2881683214910109030965621 := by
  unfold tailWord_5612058
  simp only [CollatzResearch.WordTrace]
  refine ⟨51172142775619951011089207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136459047401653202696237885 51172142775619951011089207)
  ·
    refine ⟨76758214163429926516633811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51172142775619951011089207 76758214163429926516633811)
    ·
      refine ⟨115137321245144889774950717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76758214163429926516633811 115137321245144889774950717)
      ·
        refine ⟨43176495466929333665606519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115137321245144889774950717 43176495466929333665606519)
        ·
          refine ⟨64764743200394000498409779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43176495466929333665606519 64764743200394000498409779)
          ·
            refine ⟨97147114800591000747614669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64764743200394000498409779 97147114800591000747614669)
            ·
              refine ⟨36430168050221625280355501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97147114800591000747614669 36430168050221625280355501)
              ·
                refine ⟨13661313018833109480133313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36430168050221625280355501 13661313018833109480133313)
                ·
                  refine ⟨10245984764124832110099985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13661313018833109480133313 10245984764124832110099985)
                  ·
                    refine ⟨7684488573093624082574989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10245984764124832110099985 7684488573093624082574989)
                    ·
                      refine ⟨2881683214910109030965621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7684488573093624082574989 2881683214910109030965621)
                      ·
                        rfl

theorem cell23_5612058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_5612058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612058 prefixEnd_5612058 := by exact prefixLift 5612058
  have htrace : WordTrace (prefixWord ++ tailWord_5612058) baseStart_5612058 baseEnd_5612058 := by
    simpa [prefixWord, tailWord_5612058, baseEnd_5612058] using wordTrace_append hprefix tailTrace_5612058
  have hstable : (prefixWord ++ tailWord_5612058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612058).length < 2 ^ (prefixWord ++ tailWord_5612058).sum := by decide
  have hdescent : baseEnd_5612058 < baseStart_5612058 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612065 : List Nat := [1, 2, 3, 2, 2, 1, 2, 5, 1, 4]
def baseStart_5612065 : Nat := 118140960795 + 5612065 * 2 ^ 59
def prefixEnd_5612065 : Nat := 4983230072969 + 3 ^ 40 * 5612065 * 2
def baseEnd_5612065 : Nat := 960562269758230167859363

theorem tailTrace_5612065 : CollatzResearch.WordTrace tailWord_5612065 prefixEnd_5612065 960562269758230167859363 := by
  unfold tailWord_5612065
  simp only [CollatzResearch.WordTrace]
  refine ⟨204688826413454444239861649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136459217608969629493241099 204688826413454444239861649)
  ·
    refine ⟨153516619810090833179896237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204688826413454444239861649 153516619810090833179896237)
    ·
      refine ⟨57568732428784062442461089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153516619810090833179896237 57568732428784062442461089)
      ·
        refine ⟨43176549321588046831845817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57568732428784062442461089 43176549321588046831845817)
        ·
          refine ⟨32382411991191035123884363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43176549321588046831845817 32382411991191035123884363)
          ·
            refine ⟨48573617986786552685826545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32382411991191035123884363 48573617986786552685826545)
            ·
              refine ⟨36430213490089914514369909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48573617986786552685826545 36430213490089914514369909)
              ·
                refine ⟨3415332514695929485722179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36430213490089914514369909 3415332514695929485722179)
                ·
                  refine ⟨5122998772043894228583269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415332514695929485722179 5122998772043894228583269)
                  ·
                    refine ⟨960562269758230167859363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5122998772043894228583269 960562269758230167859363)
                    ·
                      rfl

theorem cell23_5612065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_5612065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612065 prefixEnd_5612065 := by exact prefixLift 5612065
  have htrace : WordTrace (prefixWord ++ tailWord_5612065) baseStart_5612065 baseEnd_5612065 := by
    simpa [prefixWord, tailWord_5612065, baseEnd_5612065] using wordTrace_append hprefix tailTrace_5612065
  have hstable : (prefixWord ++ tailWord_5612065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612065).length < 2 ^ (prefixWord ++ tailWord_5612065).sum := by decide
  have hdescent : baseEnd_5612065 < baseStart_5612065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612082 : List Nat := [3, 2, 1, 1, 2, 1, 6, 2, 1, 4]
def baseStart_5612082 : Nat := 118140960795 + 5612082 * 2 ^ 59
def prefixEnd_5612082 : Nat := 4983230072969 + 3 ^ 40 * 5612082 * 2
def baseEnd_5612082 : Nat := 960565179481938979021837

theorem tailTrace_5612082 : CollatzResearch.WordTrace tailWord_5612082 prefixEnd_5612082 960565179481938979021837 := by
  unfold tailWord_5612082
  simp only [CollatzResearch.WordTrace]
  refine ⟨51172361613598214035807625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136459630969595237428820333 51172361613598214035807625)
  ·
    refine ⟨38379271210198660526855719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51172361613598214035807625 38379271210198660526855719)
    ·
      refine ⟨57568906815297990790283579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38379271210198660526855719 57568906815297990790283579)
      ·
        refine ⟨86353360222946986185425369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57568906815297990790283579 86353360222946986185425369)
        ·
          refine ⟨64765020167210239639069027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86353360222946986185425369 64765020167210239639069027)
          ·
            refine ⟨97147530250815359458603541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64765020167210239639069027 97147530250815359458603541)
            ·
              refine ⟨4553790480506969974622041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97147530250815359458603541 4553790480506969974622041)
              ·
                refine ⟨3415342860380227480966531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4553790480506969974622041 3415342860380227480966531)
                ·
                  refine ⟨5123014290570341221449797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415342860380227480966531 5123014290570341221449797)
                  ·
                    refine ⟨960565179481938979021837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5123014290570341221449797 960565179481938979021837)
                    ·
                      rfl

theorem cell23_5612082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_5612082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612082 prefixEnd_5612082 := by exact prefixLift 5612082
  have htrace : WordTrace (prefixWord ++ tailWord_5612082) baseStart_5612082 baseEnd_5612082 := by
    simpa [prefixWord, tailWord_5612082, baseEnd_5612082] using wordTrace_append hprefix tailTrace_5612082
  have hstable : (prefixWord ++ tailWord_5612082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612082).length < 2 ^ (prefixWord ++ tailWord_5612082).sum := by decide
  have hdescent : baseEnd_5612082 < baseStart_5612082 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612108 : List Nat := [2, 2, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_5612108 : Nat := 118140960795 + 5612108 * 2 ^ 59
def prefixEnd_5612108 : Nat := 4983230072969 + 3 ^ 40 * 5612108 * 2
def baseEnd_5612108 : Nat := 960569629647611278446797

theorem tailTrace_5612108 : CollatzResearch.WordTrace tailWord_5612108 prefixEnd_5612108 960569629647611278446797 := by
  unfold tailWord_5612108
  simp only [CollatzResearch.WordTrace]
  refine ⟨102345197376149331291838489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136460263168199108389117985 102345197376149331291838489)
  ·
    refine ⟨76758898032111998468878867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102345197376149331291838489 76758898032111998468878867)
    ·
      refine ⟨115138347048167997703318301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76758898032111998468878867 115138347048167997703318301)
      ·
        refine ⟨43176880143062999138744363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115138347048167997703318301 43176880143062999138744363)
        ·
          refine ⟨64765320214594498708116545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43176880143062999138744363 64765320214594498708116545)
          ·
            refine ⟨48573990160945874031087409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64765320214594498708116545 48573990160945874031087409)
            ·
              refine ⟨36430492620709405523315557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48573990160945874031087409 36430492620709405523315557)
              ·
                refine ⟨6830717366383013535621667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36430492620709405523315557 6830717366383013535621667)
                ·
                  refine ⟨10246076049574520303432501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6830717366383013535621667 10246076049574520303432501)
                  ·
                    refine ⟨960569629647611278446797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10246076049574520303432501 960569629647611278446797)
                    ·
                      rfl

theorem cell23_5612108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_5612108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612108 prefixEnd_5612108 := by exact prefixLift 5612108
  have htrace : WordTrace (prefixWord ++ tailWord_5612108) baseStart_5612108 baseEnd_5612108 := by
    simpa [prefixWord, tailWord_5612108, baseEnd_5612108] using wordTrace_append hprefix tailTrace_5612108
  have hstable : (prefixWord ++ tailWord_5612108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612108).length < 2 ^ (prefixWord ++ tailWord_5612108).sum := by decide
  have hdescent : baseEnd_5612108 < baseStart_5612108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612165 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 3]
def baseStart_5612165 : Nat := 118140960795 + 5612165 * 2 ^ 59
def prefixEnd_5612165 : Nat := 4983230072969 + 3 ^ 40 * 5612165 * 2
def baseEnd_5612165 : Nat := 2881738157340140112327629

theorem tailTrace_5612165 : CollatzResearch.WordTrace tailWord_5612165 prefixEnd_5612165 2881738157340140112327629 := by
  unfold tailWord_5612165
  simp only [CollatzResearch.WordTrace]
  refine ⟨204692473713092161318501949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136461649142061440879001299 204692473713092161318501949)
  ·
    refine ⟨76759677642409560494438231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204692473713092161318501949 76759677642409560494438231)
    ·
      refine ⟨115139516463614340741657347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76759677642409560494438231 115139516463614340741657347)
      ·
        refine ⟨172709274695421511112486021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115139516463614340741657347 172709274695421511112486021)
        ·
          refine ⟨32382989005391533333591129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172709274695421511112486021 32382989005391533333591129)
          ·
            refine ⟨24287241754043650000193347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32382989005391533333591129 24287241754043650000193347)
            ·
              refine ⟨36430862631065475000290021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24287241754043650000193347 36430862631065475000290021)
              ·
                refine ⟨6830786743324776562554379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36430862631065475000290021 6830786743324776562554379)
                ·
                  refine ⟨10246180114987164843831569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6830786743324776562554379 10246180114987164843831569)
                  ·
                    refine ⟨7684635086240373632873677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10246180114987164843831569 7684635086240373632873677)
                    ·
                      refine ⟨2881738157340140112327629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7684635086240373632873677 2881738157340140112327629)
                      ·
                        rfl

theorem cell23_5612165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_5612165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612165 prefixEnd_5612165 := by exact prefixLift 5612165
  have htrace : WordTrace (prefixWord ++ tailWord_5612165) baseStart_5612165 baseEnd_5612165 := by
    simpa [prefixWord, tailWord_5612165, baseEnd_5612165] using wordTrace_append hprefix tailTrace_5612165
  have hstable : (prefixWord ++ tailWord_5612165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612165).length < 2 ^ (prefixWord ++ tailWord_5612165).sum := by decide
  have hdescent : baseEnd_5612165 < baseStart_5612165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612181 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 3, 9]
def baseStart_5612181 : Nat := 118140960795 + 5612181 * 2 ^ 59
def prefixEnd_5612181 : Nat := 4983230072969 + 3 ^ 40 * 5612181 * 2
def baseEnd_5612181 : Nat := 960582124343537349909185

theorem tailTrace_5612181 : CollatzResearch.WordTrace tailWord_5612181 prefixEnd_5612181 960582124343537349909185 := by
  unfold tailWord_5612181
  simp only [CollatzResearch.WordTrace]
  refine ⟨204693057281034196051084397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136462038187356130700722931 204693057281034196051084397)
  ·
    refine ⟨76759896480387823519156649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204693057281034196051084397 76759896480387823519156649)
    ·
      refine ⟨57569922360290867639367487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76759896480387823519156649 57569922360290867639367487)
      ·
        refine ⟨86354883540436301459051231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57569922360290867639367487 86354883540436301459051231)
        ·
          refine ⟨129532325310654452188576847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86354883540436301459051231 129532325310654452188576847)
          ·
            refine ⟨194298487965981678282865271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129532325310654452188576847 194298487965981678282865271)
            ·
              refine ⟨291447731948972517424297907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194298487965981678282865271 291447731948972517424297907)
              ·
                refine ⟨437171597923458776136446861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291447731948972517424297907 437171597923458776136446861)
                ·
                  refine ⟨163939349221297041051167573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437171597923458776136446861 163939349221297041051167573)
                  ·
                    refine ⟨960582124343537349909185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 163939349221297041051167573 960582124343537349909185)
                    ·
                      rfl

theorem cell23_5612181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_5612181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612181 prefixEnd_5612181 := by exact prefixLift 5612181
  have htrace : WordTrace (prefixWord ++ tailWord_5612181) baseStart_5612181 baseEnd_5612181 := by
    simpa [prefixWord, tailWord_5612181, baseEnd_5612181] using wordTrace_append hprefix tailTrace_5612181
  have hstable : (prefixWord ++ tailWord_5612181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612181).length < 2 ^ (prefixWord ++ tailWord_5612181).sum := by decide
  have hdescent : baseEnd_5612181 < baseStart_5612181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612196 : List Nat := [2, 3, 1, 2, 2, 1, 5, 2, 1, 2, 2]
def baseStart_5612196 : Nat := 118140960795 + 5612196 * 2 ^ 59
def prefixEnd_5612196 : Nat := 4983230072969 + 3 ^ 40 * 5612196 * 2
def baseEnd_5612196 : Nat := 2881754075240429491039987

theorem tailTrace_5612196 : CollatzResearch.WordTrace tailWord_5612196 prefixEnd_5612196 2881754075240429491039987 := by
  unfold tailWord_5612196
  simp only [CollatzResearch.WordTrace]
  refine ⟨102346802187989926806440221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136462402917319902408586961 102346802187989926806440221)
  ·
    refine ⟨38380050820496222552415083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102346802187989926806440221 38380050820496222552415083)
    ·
      refine ⟨57570076230744333828622625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38380050820496222552415083 57570076230744333828622625)
      ·
        refine ⟨43177557173058250371466969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57570076230744333828622625 43177557173058250371466969)
        ·
          refine ⟨32383167879793687778600227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43177557173058250371466969 32383167879793687778600227)
          ·
            refine ⟨48574751819690531667900341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32383167879793687778600227 48574751819690531667900341)
            ·
              refine ⟨4553882983095987343865657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48574751819690531667900341 4553882983095987343865657)
              ·
                refine ⟨3415412237321990507899243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4553882983095987343865657 3415412237321990507899243)
                ·
                  refine ⟨5123118355982985761848865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415412237321990507899243 5123118355982985761848865)
                  ·
                    refine ⟨3842338766987239321386649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5123118355982985761848865 3842338766987239321386649)
                    ·
                      refine ⟨2881754075240429491039987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842338766987239321386649 2881754075240429491039987)
                      ·
                        rfl

theorem cell23_5612196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_5612196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612196 prefixEnd_5612196 := by exact prefixLift 5612196
  have htrace : WordTrace (prefixWord ++ tailWord_5612196) baseStart_5612196 baseEnd_5612196 := by
    simpa [prefixWord, tailWord_5612196, baseEnd_5612196] using wordTrace_append hprefix tailTrace_5612196
  have hstable : (prefixWord ++ tailWord_5612196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612196).length < 2 ^ (prefixWord ++ tailWord_5612196).sum := by decide
  have hdescent : baseEnd_5612196 < baseStart_5612196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612202 : List Nat := [3, 1, 5, 2, 1, 1, 2, 8]
def baseStart_5612202 : Nat := 118140960795 + 5612202 * 2 ^ 59
def prefixEnd_5612202 : Nat := 4983230072969 + 3 ^ 40 * 5612202 * 2
def baseEnd_5612202 : Nat := 106731746523124313613517

theorem tailTrace_5612202 : CollatzResearch.WordTrace tailWord_5612202 prefixEnd_5612202 106731746523124313613517 := by
  unfold tailWord_5612202
  simp only [CollatzResearch.WordTrace]
  refine ⟨51173455803489529159399715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136462548809305411091732573 51173455803489529159399715)
  ·
    refine ⟨76760183705234293739099573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51173455803489529159399715 76760183705234293739099573)
    ·
      refine ⟨7196267222365715038040585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76760183705234293739099573 7196267222365715038040585)
      ·
        refine ⟨5397200416774286278530439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7196267222365715038040585 5397200416774286278530439)
        ·
          refine ⟨8095800625161429417795659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5397200416774286278530439 8095800625161429417795659)
          ·
            refine ⟨12143700937742144126693489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8095800625161429417795659 12143700937742144126693489)
            ·
              refine ⟨9107775703306608095020117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12143700937742144126693489 9107775703306608095020117)
              ·
                refine ⟨106731746523124313613517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9107775703306608095020117 106731746523124313613517)
                ·
                  rfl

theorem cell23_5612202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 2, 8].length) (baseStart_5612202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612202 prefixEnd_5612202 := by exact prefixLift 5612202
  have htrace : WordTrace (prefixWord ++ tailWord_5612202) baseStart_5612202 baseEnd_5612202 := by
    simpa [prefixWord, tailWord_5612202, baseEnd_5612202] using wordTrace_append hprefix tailTrace_5612202
  have hstable : (prefixWord ++ tailWord_5612202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612202).length < 2 ^ (prefixWord ++ tailWord_5612202).sum := by decide
  have hdescent : baseEnd_5612202 < baseStart_5612202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612206 : List Nat := [4, 1, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_5612206 : Nat := 118140960795 + 5612206 * 2 ^ 59
def prefixEnd_5612206 : Nat := 4983230072969 + 3 ^ 40 * 5612206 * 2
def baseEnd_5612206 : Nat := 960586403348991483971647

theorem tailTrace_5612206 : CollatzResearch.WordTrace tailWord_5612206 prefixEnd_5612206 960586403348991483971647 := by
  unfold tailWord_5612206
  simp only [CollatzResearch.WordTrace]
  refine ⟨25586746138242953165093059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136462646070629083547162981 25586746138242953165093059)
  ·
    refine ⟨38380119207364429747639589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25586746138242953165093059 38380119207364429747639589)
    ·
      refine ⟨7196272351380830577682423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38380119207364429747639589 7196272351380830577682423)
      ·
        refine ⟨10794408527071245866523635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7196272351380830577682423 10794408527071245866523635)
        ·
          refine ⟨16191612790606868799785453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10794408527071245866523635 16191612790606868799785453)
          ·
            refine ⟨6071854796477575799919545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16191612790606868799785453 6071854796477575799919545)
            ·
              refine ⟨4553891097358181849939659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6071854796477575799919545 4553891097358181849939659)
              ·
                refine ⟨6830836646037272774909489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4553891097358181849939659 6830836646037272774909489)
                ·
                  refine ⟨5123127484527954581182117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6830836646037272774909489 5123127484527954581182117)
                  ·
                    refine ⟨960586403348991483971647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5123127484527954581182117 960586403348991483971647)
                    ·
                      rfl

theorem cell23_5612206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_5612206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612206 prefixEnd_5612206 := by exact prefixLift 5612206
  have htrace : WordTrace (prefixWord ++ tailWord_5612206) baseStart_5612206 baseEnd_5612206 := by
    simpa [prefixWord, tailWord_5612206, baseEnd_5612206] using wordTrace_append hprefix tailTrace_5612206
  have hstable : (prefixWord ++ tailWord_5612206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612206).length < 2 ^ (prefixWord ++ tailWord_5612206).sum := by decide
  have hdescent : baseEnd_5612206 < baseStart_5612206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612222 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2]
def baseStart_5612222 : Nat := 118140960795 + 5612222 * 2 ^ 59
def prefixEnd_5612222 : Nat := 4983230072969 + 3 ^ 40 * 5612222 * 2
def baseEnd_5612222 : Nat := 2881767425737446389314867

theorem tailTrace_5612222 : CollatzResearch.WordTrace tailWord_5612222 prefixEnd_5612222 2881767425737446389314867 := by
  unfold tailWord_5612222
  simp only [CollatzResearch.WordTrace]
  refine ⟨25586819084235707506665865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136463035115923773368884613 25586819084235707506665865)
  ·
    refine ⟨19190114313176780629999399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25586819084235707506665865 19190114313176780629999399)
    ·
      refine ⟨28785171469765170944999099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19190114313176780629999399 28785171469765170944999099)
      ·
        refine ⟨43177757204647756417498649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28785171469765170944999099 43177757204647756417498649)
        ·
          refine ⟨32383317903485817313123987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43177757204647756417498649 32383317903485817313123987)
          ·
            refine ⟨48574976855228725969685981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32383317903485817313123987 48574976855228725969685981)
            ·
              refine ⟨18215616320710772238632243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48574976855228725969685981 18215616320710772238632243)
              ·
                refine ⟨27323424481066158357948365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18215616320710772238632243 27323424481066158357948365)
                ·
                  refine ⟨10246284180399809384230637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27323424481066158357948365 10246284180399809384230637)
                  ·
                    refine ⟨3842356567649928519086489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10246284180399809384230637 3842356567649928519086489)
                    ·
                      refine ⟨2881767425737446389314867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842356567649928519086489 2881767425737446389314867)
                      ·
                        rfl

theorem cell23_5612222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_5612222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612222 prefixEnd_5612222 := by exact prefixLift 5612222
  have htrace : WordTrace (prefixWord ++ tailWord_5612222) baseStart_5612222 baseEnd_5612222 := by
    simpa [prefixWord, tailWord_5612222, baseEnd_5612222] using wordTrace_append hprefix tailTrace_5612222
  have hstable : (prefixWord ++ tailWord_5612222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612222).length < 2 ^ (prefixWord ++ tailWord_5612222).sum := by decide
  have hdescent : baseEnd_5612222 < baseStart_5612222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612269 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 2, 2, 2]
def baseStart_5612269 : Nat := 118140960795 + 5612269 * 2 ^ 59
def prefixEnd_5612269 : Nat := 4983230072969 + 3 ^ 40 * 5612269 * 2
def baseEnd_5612269 : Nat := 2881791559328207705427151

theorem tailTrace_5612269 : CollatzResearch.WordTrace tailWord_5612269 prefixEnd_5612269 2881791559328207705427151 := by
  unfold tailWord_5612269
  simp only [CollatzResearch.WordTrace]
  refine ⟨204696266904715387080287861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136464177936476924720191907 204696266904715387080287861)
  ·
    refine ⟨19190275022317067538776987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204696266904715387080287861 19190275022317067538776987)
    ·
      refine ⟨28785412533475601308165481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19190275022317067538776987 28785412533475601308165481)
      ·
        refine ⟨21589059400106700981124111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28785412533475601308165481 21589059400106700981124111)
        ·
          refine ⟨32383589100160051471686167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21589059400106700981124111 32383589100160051471686167)
          ·
            refine ⟨48575383650240077207529251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32383589100160051471686167 48575383650240077207529251)
            ·
              refine ⟨72863075475360115811293877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48575383650240077207529251 72863075475360115811293877)
              ·
                refine ⟨6830913325815010857308801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72863075475360115811293877 6830913325815010857308801)
                ·
                  refine ⟨5123184994361258142981601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6830913325815010857308801 5123184994361258142981601)
                  ·
                    refine ⟨3842388745770943607236201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5123184994361258142981601 3842388745770943607236201)
                    ·
                      refine ⟨2881791559328207705427151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842388745770943607236201 2881791559328207705427151)
                      ·
                        rfl

theorem cell23_5612269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_5612269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612269 prefixEnd_5612269 := by exact prefixLift 5612269
  have htrace : WordTrace (prefixWord ++ tailWord_5612269) baseStart_5612269 baseEnd_5612269 := by
    simpa [prefixWord, tailWord_5612269, baseEnd_5612269] using wordTrace_append hprefix tailTrace_5612269
  have hstable : (prefixWord ++ tailWord_5612269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612269).length < 2 ^ (prefixWord ++ tailWord_5612269).sum := by decide
  have hdescent : baseEnd_5612269 < baseStart_5612269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612292 : List Nat := [2, 3, 2, 2, 1, 1, 4, 3, 5]
def baseStart_5612292 : Nat := 118140960795 + 5612292 * 2 ^ 59
def prefixEnd_5612292 : Nat := 4983230072969 + 3 ^ 40 * 5612292 * 2
def baseEnd_5612292 : Nat := 320200374375917901715505

theorem tailTrace_5612292 : CollatzResearch.WordTrace tailWord_5612292 prefixEnd_5612292 320200374375917901715505 := by
  unfold tailWord_5612292
  simp only [CollatzResearch.WordTrace]
  refine ⟨102348552891816031004187565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136464737189088041338916753 102348552891816031004187565)
  ·
    refine ⟨38380707334431011626570337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102348552891816031004187565 38380707334431011626570337)
    ·
      refine ⟨28785530500823258719927753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38380707334431011626570337 28785530500823258719927753)
      ·
        refine ⟨21589147875617444039945815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28785530500823258719927753 21589147875617444039945815)
        ·
          refine ⟨32383721813426166059918723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21589147875617444039945815 32383721813426166059918723)
          ·
            refine ⟨48575582720139249089878085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32383721813426166059918723 48575582720139249089878085)
            ·
              refine ⟨9107921760026109204352141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48575582720139249089878085 9107921760026109204352141)
              ·
                refine ⟨3415470660009790951632053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9107921760026109204352141 3415470660009790951632053)
                ·
                  refine ⟨320200374375917901715505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3415470660009790951632053 320200374375917901715505)
                  ·
                    rfl

theorem cell23_5612292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 4, 3, 5].length) (baseStart_5612292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612292 prefixEnd_5612292 := by exact prefixLift 5612292
  have htrace : WordTrace (prefixWord ++ tailWord_5612292) baseStart_5612292 baseEnd_5612292 := by
    simpa [prefixWord, tailWord_5612292, baseEnd_5612292] using wordTrace_append hprefix tailTrace_5612292
  have hstable : (prefixWord ++ tailWord_5612292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612292).length < 2 ^ (prefixWord ++ tailWord_5612292).sum := by decide
  have hdescent : baseEnd_5612292 < baseStart_5612292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612368 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 8]
def baseStart_5612368 : Nat := 118140960795 + 5612368 * 2 ^ 59
def prefixEnd_5612368 : Nat := 4983230072969 + 3 ^ 40 * 5612368 * 2
def baseEnd_5612368 : Nat := 2881842393913002818089195

theorem tailTrace_5612368 : CollatzResearch.WordTrace tailWord_5612368 prefixEnd_5612368 2881842393913002818089195 := by
  unfold tailWord_5612368
  simp only [CollatzResearch.WordTrace]
  refine ⟨102349938865678363494070879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136466585154237817992094505 102349938865678363494070879)
  ·
    refine ⟨153524908298517545241106319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102349938865678363494070879 153524908298517545241106319)
    ·
      refine ⟨230287362447776317861659479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153524908298517545241106319 230287362447776317861659479)
      ·
        refine ⟨345431043671664476792489219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230287362447776317861659479 345431043671664476792489219)
        ·
          refine ⟨518146565507496715188733829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345431043671664476792489219 518146565507496715188733829)
          ·
            refine ⟨97152481032655634097887593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 518146565507496715188733829 97152481032655634097887593)
            ·
              refine ⟨72864360774491725573415695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97152481032655634097887593 72864360774491725573415695)
              ·
                refine ⟨109296541161737588360123543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72864360774491725573415695 109296541161737588360123543)
                ·
                  refine ⟨163944811742606382540185315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109296541161737588360123543 163944811742606382540185315)
                  ·
                    refine ⟨245917217613909573810277973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 163944811742606382540185315 245917217613909573810277973)
                    ·
                      refine ⟨2881842393913002818089195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 245917217613909573810277973 2881842393913002818089195)
                      ·
                        rfl

theorem cell23_5612368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_5612368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612368 prefixEnd_5612368 := by exact prefixLift 5612368
  have htrace : WordTrace (prefixWord ++ tailWord_5612368) baseStart_5612368 baseEnd_5612368 := by
    simpa [prefixWord, tailWord_5612368, baseEnd_5612368] using wordTrace_append hprefix tailTrace_5612368
  have hstable : (prefixWord ++ tailWord_5612368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612368).length < 2 ^ (prefixWord ++ tailWord_5612368).sum := by decide
  have hdescent : baseEnd_5612368 < baseStart_5612368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612369 : List Nat := [1, 2, 2, 1, 6, 2, 1, 1, 3, 4]
def baseStart_5612369 : Nat := 118140960795 + 5612369 * 2 ^ 59
def prefixEnd_5612369 : Nat := 4983230072969 + 3 ^ 40 * 5612369 * 2
def baseEnd_5612369 : Nat := 960614302464552438058897

theorem tailTrace_5612369 : CollatzResearch.WordTrace tailWord_5612369 prefixEnd_5612369 960614302464552438058897 := by
  unfold tailWord_5612369
  simp only [CollatzResearch.WordTrace]
  refine ⟨204699914204353104158928161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136466609469568736105952107 204699914204353104158928161)
  ·
    refine ⟨153524935653264828119196121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204699914204353104158928161 153524935653264828119196121)
    ·
      refine ⟨115143701739948621089397091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153524935653264828119196121 115143701739948621089397091)
      ·
        refine ⟨172715552609922931634095637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115143701739948621089397091 172715552609922931634095637)
        ·
          refine ⟨8096041528590137420348233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 172715552609922931634095637 8096041528590137420348233)
          ·
            refine ⟨6072031146442603065261175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8096041528590137420348233 6072031146442603065261175)
            ·
              refine ⟨9108046719663904597891763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072031146442603065261175 9108046719663904597891763)
              ·
                refine ⟨13662070079495856896837645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9108046719663904597891763 13662070079495856896837645)
                ·
                  refine ⟨5123276279810946336314117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13662070079495856896837645 5123276279810946336314117)
                  ·
                    refine ⟨960614302464552438058897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5123276279810946336314117 960614302464552438058897)
                    ·
                      rfl

theorem cell23_5612369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 3, 4].length) (baseStart_5612369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612369 prefixEnd_5612369 := by exact prefixLift 5612369
  have htrace : WordTrace (prefixWord ++ tailWord_5612369) baseStart_5612369 baseEnd_5612369 := by
    simpa [prefixWord, tailWord_5612369, baseEnd_5612369] using wordTrace_append hprefix tailTrace_5612369
  have hstable : (prefixWord ++ tailWord_5612369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612369).length < 2 ^ (prefixWord ++ tailWord_5612369).sum := by decide
  have hdescent : baseEnd_5612369 < baseStart_5612369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612402 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_5612402 : Nat := 118140960795 + 5612402 * 2 ^ 59
def prefixEnd_5612402 : Nat := 4983230072969 + 3 ^ 40 * 5612402 * 2
def baseEnd_5612402 : Nat := 2881859852255255685064039

theorem tailTrace_5612402 : CollatzResearch.WordTrace tailWord_5612402 prefixEnd_5612402 2881859852255255685064039 := by
  unfold tailWord_5612402
  simp only [CollatzResearch.WordTrace]
  refine ⟨51175279453308387698719865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136467411875489033863252973 51175279453308387698719865)
  ·
    refine ⟨38381459589981290774039899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51175279453308387698719865 38381459589981290774039899)
    ·
      refine ⟨57572189384971936161059849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38381459589981290774039899 57572189384971936161059849)
      ·
        refine ⟨43179142038728952120794887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57572189384971936161059849 43179142038728952120794887)
        ·
          refine ⟨64768713058093428181192331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43179142038728952120794887 64768713058093428181192331)
          ·
            refine ⟨97153069587140142271788497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64768713058093428181192331 97153069587140142271788497)
            ·
              refine ⟨72864802190355106703841373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97153069587140142271788497 72864802190355106703841373)
              ·
                refine ⟨27324300821383165013940515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72864802190355106703841373 27324300821383165013940515)
                ·
                  refine ⟨40986451232074747520910773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27324300821383165013940515 40986451232074747520910773)
                  ·
                    refine ⟨3842479803007007580085385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40986451232074747520910773 3842479803007007580085385)
                    ·
                      refine ⟨2881859852255255685064039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842479803007007580085385 2881859852255255685064039)
                      ·
                        rfl

theorem cell23_5612402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_5612402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612402 prefixEnd_5612402 := by exact prefixLift 5612402
  have htrace : WordTrace (prefixWord ++ tailWord_5612402) baseStart_5612402 baseEnd_5612402 := by
    simpa [prefixWord, tailWord_5612402, baseEnd_5612402] using wordTrace_append hprefix tailTrace_5612402
  have hstable : (prefixWord ++ tailWord_5612402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612402).length < 2 ^ (prefixWord ++ tailWord_5612402).sum := by decide
  have hdescent : baseEnd_5612402 < baseStart_5612402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612452 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 3, 2, 3]
def baseStart_5612452 : Nat := 118140960795 + 5612452 * 2 ^ 59
def prefixEnd_5612452 : Nat := 4983230072969 + 3 ^ 40 * 5612452 * 2
def baseEnd_5612452 : Nat := 2881885526287980489438809

theorem tailTrace_5612452 : CollatzResearch.WordTrace tailWord_5612452 prefixEnd_5612452 2881885526287980489438809 := by
  unfold tailWord_5612452
  simp only [CollatzResearch.WordTrace]
  refine ⟨102351470731526204667099805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136468627642034939556133073 102351470731526204667099805)
  ·
    refine ⟨38381801524322326750162427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102351470731526204667099805 38381801524322326750162427)
    ·
      refine ⟨57572702286483490125243641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38381801524322326750162427 57572702286483490125243641)
      ·
        refine ⟨43179526714862617593932731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57572702286483490125243641 43179526714862617593932731)
        ·
          refine ⟨64769290072293926390899097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43179526714862617593932731 64769290072293926390899097)
          ·
            refine ⟨48576967554220444793174323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64769290072293926390899097 48576967554220444793174323)
            ·
              refine ⟨72865451331330667189761485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48576967554220444793174323 72865451331330667189761485)
              ·
                refine ⟨27324544249249000196160557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72865451331330667189761485 27324544249249000196160557)
                ·
                  refine ⟨10246704093468375073560209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27324544249249000196160557 10246704093468375073560209)
                  ·
                    refine ⟨7685028070101281305170157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10246704093468375073560209 7685028070101281305170157)
                    ·
                      refine ⟨2881885526287980489438809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7685028070101281305170157 2881885526287980489438809)
                      ·
                        rfl

theorem cell23_5612452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_5612452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612452 prefixEnd_5612452 := by exact prefixLift 5612452
  have htrace : WordTrace (prefixWord ++ tailWord_5612452) baseStart_5612452 baseEnd_5612452 := by
    simpa [prefixWord, tailWord_5612452, baseEnd_5612452] using wordTrace_append hprefix tailTrace_5612452
  have hstable : (prefixWord ++ tailWord_5612452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612452).length < 2 ^ (prefixWord ++ tailWord_5612452).sum := by decide
  have hdescent : baseEnd_5612452 < baseStart_5612452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612469 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_5612469 : Nat := 118140960795 + 5612469 * 2 ^ 59
def prefixEnd_5612469 : Nat := 4983230072969 + 3 ^ 40 * 5612469 * 2
def baseEnd_5612469 : Nat := 2881894255459106922926231

theorem tailTrace_5612469 : CollatzResearch.WordTrace tailWord_5612469 prefixEnd_5612469 2881894255459106922926231 := by
  unfold tailWord_5612469
  simp only [CollatzResearch.WordTrace]
  refine ⟨204703561503990821237568461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136469041002660547491712307 204703561503990821237568461)
  ·
    refine ⟨76763835563996557964088173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204703561503990821237568461 76763835563996557964088173)
    ·
      refine ⟨28786438336498709236533065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76763835563996557964088173 28786438336498709236533065)
      ·
        refine ⟨21589828752374031927399799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28786438336498709236533065 21589828752374031927399799)
        ·
          refine ⟨32384743128561047891099699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21589828752374031927399799 32384743128561047891099699)
          ·
            refine ⟨48577114692841571836649549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32384743128561047891099699 48577114692841571836649549)
            ·
              refine ⟨18216418009815589438743581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48577114692841571836649549 18216418009815589438743581)
              ·
                refine ⟨6831156753680846039528843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18216418009815589438743581 6831156753680846039528843)
                ·
                  refine ⟨10246735130521269059293265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6831156753680846039528843 10246735130521269059293265)
                  ·
                    refine ⟨7685051347890951794469949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10246735130521269059293265 7685051347890951794469949)
                    ·
                      refine ⟨2881894255459106922926231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7685051347890951794469949 2881894255459106922926231)
                      ·
                        rfl

theorem cell23_5612469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_5612469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612469 prefixEnd_5612469 := by exact prefixLift 5612469
  have htrace : WordTrace (prefixWord ++ tailWord_5612469) baseStart_5612469 baseEnd_5612469 := by
    simpa [prefixWord, tailWord_5612469, baseEnd_5612469] using wordTrace_append hprefix tailTrace_5612469
  have hstable : (prefixWord ++ tailWord_5612469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612469).length < 2 ^ (prefixWord ++ tailWord_5612469).sum := by decide
  have hdescent : baseEnd_5612469 < baseStart_5612469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612517 : List Nat := [1, 3, 1, 6, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5612517 : Nat := 118140960795 + 5612517 * 2 ^ 59
def prefixEnd_5612517 : Nat := 4983230072969 + 3 ^ 40 * 5612517 * 2
def baseEnd_5612517 : Nat := 2881918902530522735126011

theorem tailTrace_5612517 : CollatzResearch.WordTrace tailWord_5612517 prefixEnd_5612517 2881918902530522735126011 := by
  unfold tailWord_5612517
  simp only [CollatzResearch.WordTrace]
  refine ⟨204705312207816925435315805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136470208138544616956877203 204705312207816925435315805)
  ·
    refine ⟨76764492077931347038243427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204705312207816925435315805 76764492077931347038243427)
    ·
      refine ⟨115146738116897020557365141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76764492077931347038243427 115146738116897020557365141)
      ·
        refine ⟨5397503349229547838626491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 115146738116897020557365141 5397503349229547838626491)
        ·
          refine ⟨8096255023844321757939737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5397503349229547838626491 8096255023844321757939737)
          ·
            refine ⟨6072191267883241318454803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8096255023844321757939737 6072191267883241318454803)
            ·
              refine ⟨9108286901824861977682205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072191267883241318454803 9108286901824861977682205)
              ·
                refine ⟨3415607588184323241630827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9108286901824861977682205 3415607588184323241630827)
                ·
                  refine ⟨5123411382276484862446241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415607588184323241630827 5123411382276484862446241)
                  ·
                    refine ⟨3842558536707363646834681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5123411382276484862446241 3842558536707363646834681)
                    ·
                      refine ⟨2881918902530522735126011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842558536707363646834681 2881918902530522735126011)
                      ·
                        rfl

theorem cell23_5612517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5612517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612517 prefixEnd_5612517 := by exact prefixLift 5612517
  have htrace : WordTrace (prefixWord ++ tailWord_5612517) baseStart_5612517 baseEnd_5612517 := by
    simpa [prefixWord, tailWord_5612517, baseEnd_5612517] using wordTrace_append hprefix tailTrace_5612517
  have hstable : (prefixWord ++ tailWord_5612517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612517).length < 2 ^ (prefixWord ++ tailWord_5612517).sum := by decide
  have hdescent : baseEnd_5612517 < baseStart_5612517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612585 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 7]
def baseStart_5612585 : Nat := 118140960795 + 5612585 * 2 ^ 59
def prefixEnd_5612585 : Nat := 4983230072969 + 3 ^ 40 * 5612585 * 2
def baseEnd_5612585 : Nat := 2881953819215028469075697

theorem tailTrace_5612585 : CollatzResearch.WordTrace tailWord_5612585 prefixEnd_5612585 2881953819215028469075697 := by
  unfold tailWord_5612585
  simp only [CollatzResearch.WordTrace]
  refine ⟨204707792371570573048791209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136471861581047048699194139 204707792371570573048791209)
  ·
    refine ⟨153530844278677929786593407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204707792371570573048791209 153530844278677929786593407)
    ·
      refine ⟨230296266418016894679890111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153530844278677929786593407 230296266418016894679890111)
      ·
        refine ⟨345444399627025342019835167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230296266418016894679890111 345444399627025342019835167)
        ·
          refine ⟨518166599440538013029752751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345444399627025342019835167 518166599440538013029752751)
          ·
            refine ⟨777249899160807019544629127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518166599440538013029752751 777249899160807019544629127)
            ·
              refine ⟨1165874848741210529316943691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777249899160807019544629127 1165874848741210529316943691)
              ·
                refine ⟨1748812273111815793975415537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1165874848741210529316943691 1748812273111815793975415537)
                ·
                  refine ⟨1311609204833861845481561653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1748812273111815793975415537 1311609204833861845481561653)
                  ·
                    refine ⟨122963362953174548013896405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1311609204833861845481561653 122963362953174548013896405)
                    ·
                      refine ⟨2881953819215028469075697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122963362953174548013896405 2881953819215028469075697)
                      ·
                        rfl

theorem cell23_5612585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 2, 5, 7].length) (baseStart_5612585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612585 prefixEnd_5612585 := by exact prefixLift 5612585
  have htrace : WordTrace (prefixWord ++ tailWord_5612585) baseStart_5612585 baseEnd_5612585 := by
    simpa [prefixWord, tailWord_5612585, baseEnd_5612585] using wordTrace_append hprefix tailTrace_5612585
  have hstable : (prefixWord ++ tailWord_5612585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612585).length < 2 ^ (prefixWord ++ tailWord_5612585).sum := by decide
  have hdescent : baseEnd_5612585 < baseStart_5612585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612592 : List Nat := [2, 1, 1, 1, 2, 4, 1, 4, 2, 5]
def baseStart_5612592 : Nat := 118140960795 + 5612592 * 2 ^ 59
def prefixEnd_5612592 : Nat := 4983230072969 + 3 ^ 40 * 5612592 * 2
def baseEnd_5612592 : Nat := 960652471193203313896055

theorem tailTrace_5612592 : CollatzResearch.WordTrace tailWord_5612592 prefixEnd_5612592 960652471193203313896055 := by
  unfold tailWord_5612592
  simp only [CollatzResearch.WordTrace]
  refine ⟨102354023841272606622148015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136472031788363475496197353 102354023841272606622148015)
  ·
    refine ⟨153531035761908909933222023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102354023841272606622148015 153531035761908909933222023)
    ·
      refine ⟨230296553642863364899833035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153531035761908909933222023 230296553642863364899833035)
      ·
        refine ⟨345444830464295047349749553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230296553642863364899833035 345444830464295047349749553)
        ·
          refine ⟨259083622848221285512312165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345444830464295047349749553 259083622848221285512312165)
          ·
            refine ⟨48578179284041491033558531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259083622848221285512312165 48578179284041491033558531)
            ·
              refine ⟨72867268926062236550337797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48578179284041491033558531 72867268926062236550337797)
              ·
                refine ⟨13662612923636669353188337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72867268926062236550337797 13662612923636669353188337)
                ·
                  refine ⟨10246959692727502014891253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13662612923636669353188337 10246959692727502014891253)
                  ·
                    refine ⟨960652471193203313896055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10246959692727502014891253 960652471193203313896055)
                    ·
                      rfl

theorem cell23_5612592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 4, 2, 5].length) (baseStart_5612592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612592 prefixEnd_5612592 := by exact prefixLift 5612592
  have htrace : WordTrace (prefixWord ++ tailWord_5612592) baseStart_5612592 baseEnd_5612592 := by
    simpa [prefixWord, tailWord_5612592, baseEnd_5612592] using wordTrace_append hprefix tailTrace_5612592
  have hstable : (prefixWord ++ tailWord_5612592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612592).length < 2 ^ (prefixWord ++ tailWord_5612592).sum := by decide
  have hdescent : baseEnd_5612592 < baseStart_5612592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612602 : List Nat := [3, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5]
def baseStart_5612602 : Nat := 118140960795 + 5612602 * 2 ^ 59
def prefixEnd_5612602 : Nat := 4983230072969 + 3 ^ 40 * 5612602 * 2
def baseEnd_5612602 : Nat := 2881962548386154902563119

theorem tailTrace_5612602 : CollatzResearch.WordTrace tailWord_5612602 prefixEnd_5612602 2881962548386154902563119 := by
  unfold tailWord_5612602
  simp only [CollatzResearch.WordTrace]
  refine ⟨51177103103127246238040015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136472274941672656634773373 51177103103127246238040015)
  ·
    refine ⟨76765654654690869357060023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51177103103127246238040015 76765654654690869357060023)
    ·
      refine ⟨115148481982036304035590035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76765654654690869357060023 115148481982036304035590035)
      ·
        refine ⟨172722722973054456053385053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115148481982036304035590035 172722722973054456053385053)
        ·
          refine ⟨64771021114895421020019395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172722722973054456053385053 64771021114895421020019395)
          ·
            refine ⟨97156531672343131530029093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64771021114895421020019395 97156531672343131530029093)
            ·
              refine ⟨18216849688564337161880455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97156531672343131530029093 18216849688564337161880455)
              ·
                refine ⟨27325274532846505742820683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18216849688564337161880455 27325274532846505742820683)
                ·
                  refine ⟨40987911799269758614231025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27325274532846505742820683 40987911799269758614231025)
                  ·
                    refine ⟨30740933849452318960673269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40987911799269758614231025 30740933849452318960673269)
                    ·
                      refine ⟨2881962548386154902563119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30740933849452318960673269 2881962548386154902563119)
                      ·
                        rfl

theorem cell23_5612602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_5612602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612602 prefixEnd_5612602 := by exact prefixLift 5612602
  have htrace : WordTrace (prefixWord ++ tailWord_5612602) baseStart_5612602 baseEnd_5612602 := by
    simpa [prefixWord, tailWord_5612602, baseEnd_5612602] using wordTrace_append hprefix tailTrace_5612602
  have hstable : (prefixWord ++ tailWord_5612602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612602).length < 2 ^ (prefixWord ++ tailWord_5612602).sum := by decide
  have hdescent : baseEnd_5612602 < baseStart_5612602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612606 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 2, 3, 3]
def baseStart_5612606 : Nat := 118140960795 + 5612606 * 2 ^ 59
def prefixEnd_5612606 : Nat := 4983230072969 + 3 ^ 40 * 5612606 * 2
def baseEnd_5612606 : Nat := 2881964602308772886913101

theorem tailTrace_5612606 : CollatzResearch.WordTrace tailWord_5612606 prefixEnd_5612606 2881964602308772886913101 := by
  unfold tailWord_5612606
  simp only [CollatzResearch.WordTrace]
  refine ⟨25588569788061811704413209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136472372202996329090203781 25588569788061811704413209)
  ·
    refine ⟨19191427341046358778309907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25588569788061811704413209 19191427341046358778309907)
    ·
      refine ⟨28787141011569538167464861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19191427341046358778309907 28787141011569538167464861)
      ·
        refine ⟨10795177879338576812799323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28787141011569538167464861 10795177879338576812799323)
        ·
          refine ⟨16192766819007865219198985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10795177879338576812799323 16192766819007865219198985)
          ·
            refine ⟨12144575114255898914399239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16192766819007865219198985 12144575114255898914399239)
            ·
              refine ⟨18216862671383848371598859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12144575114255898914399239 18216862671383848371598859)
              ·
                refine ⟨27325294007075772557398289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18216862671383848371598859 27325294007075772557398289)
                ·
                  refine ⟨20493970505306829418048717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27325294007075772557398289 20493970505306829418048717)
                  ·
                    refine ⟨7685238939490061031768269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20493970505306829418048717 7685238939490061031768269)
                    ·
                      refine ⟨2881964602308772886913101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7685238939490061031768269 2881964602308772886913101)
                      ·
                        rfl

theorem cell23_5612606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_5612606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612606 prefixEnd_5612606 := by exact prefixLift 5612606
  have htrace : WordTrace (prefixWord ++ tailWord_5612606) baseStart_5612606 baseEnd_5612606 := by
    simpa [prefixWord, tailWord_5612606, baseEnd_5612606] using wordTrace_append hprefix tailTrace_5612606
  have hstable : (prefixWord ++ tailWord_5612606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612606).length < 2 ^ (prefixWord ++ tailWord_5612606).sum := by decide
  have hdescent : baseEnd_5612606 < baseStart_5612606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612626 : List Nat := [3, 2, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_5612626 : Nat := 118140960795 + 5612626 * 2 ^ 59
def prefixEnd_5612626 : Nat := 4983230072969 + 3 ^ 40 * 5612626 * 2
def baseEnd_5612626 : Nat := 960658290640620936221003

theorem tailTrace_5612626 : CollatzResearch.WordTrace tailWord_5612626 prefixEnd_5612626 960658290640620936221003 := by
  unfold tailWord_5612626
  simp only [CollatzResearch.WordTrace]
  refine ⟨51177321941105509262758433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136472858509614691367355821 51177321941105509262758433)
  ·
    refine ⟨38382991455829131947068825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51177321941105509262758433 38382991455829131947068825)
    ·
      refine ⟨28787243591871848960301619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38382991455829131947068825 28787243591871848960301619)
      ·
        refine ⟨43180865387807773440452429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28787243591871848960301619 43180865387807773440452429)
        ·
          refine ⟨16192824520427915040169661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43180865387807773440452429 16192824520427915040169661)
          ·
            refine ⟨6072309195160468140063623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16192824520427915040169661 6072309195160468140063623)
            ·
              refine ⟨9108463792740702210095435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072309195160468140063623 9108463792740702210095435)
              ·
                refine ⟨13662695689111053315143153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9108463792740702210095435 13662695689111053315143153)
                ·
                  refine ⟨10247021766833289986357365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13662695689111053315143153 10247021766833289986357365)
                  ·
                    refine ⟨960658290640620936221003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10247021766833289986357365 960658290640620936221003)
                    ·
                      rfl

theorem cell23_5612626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_5612626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612626 prefixEnd_5612626 := by exact prefixLift 5612626
  have htrace : WordTrace (prefixWord ++ tailWord_5612626) baseStart_5612626 baseEnd_5612626 := by
    simpa [prefixWord, tailWord_5612626, baseEnd_5612626] using wordTrace_append hprefix tailTrace_5612626
  have hstable : (prefixWord ++ tailWord_5612626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612626).length < 2 ^ (prefixWord ++ tailWord_5612626).sum := by decide
  have hdescent : baseEnd_5612626 < baseStart_5612626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612629 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 1, 6, 2]
def baseStart_5612629 : Nat := 118140960795 + 5612629 * 2 ^ 59
def prefixEnd_5612629 : Nat := 4983230072969 + 3 ^ 40 * 5612629 * 2
def baseEnd_5612629 : Nat := 2881976412363826296925495

theorem tailTrace_5612629 : CollatzResearch.WordTrace tailWord_5612629 prefixEnd_5612629 2881976412363826296925495 := by
  unfold tailWord_5612629
  simp only [CollatzResearch.WordTrace]
  refine ⟨204709397183411168563392941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136472931455607445708928627 204709397183411168563392941)
  ·
    refine ⟨76766023943779188211272353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204709397183411168563392941 76766023943779188211272353)
    ·
      refine ⟨57574517957834391158454265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76766023943779188211272353 57574517957834391158454265)
      ·
        refine ⟨43180888468375793368840699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57574517957834391158454265 43180888468375793368840699)
        ·
          refine ⟨64771332702563690053261049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43180888468375793368840699 64771332702563690053261049)
          ·
            refine ⟨48578499526922767539945787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64771332702563690053261049 48578499526922767539945787)
            ·
              refine ⟨72867749290384151309918681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48578499526922767539945787 72867749290384151309918681)
              ·
                refine ⟨54650811967788113482439011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72867749290384151309918681 54650811967788113482439011)
                ·
                  refine ⟨81976217951682170223658517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54650811967788113482439011 81976217951682170223658517)
                  ·
                    refine ⟨3842635216485101729233993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81976217951682170223658517 3842635216485101729233993)
                    ·
                      refine ⟨2881976412363826296925495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842635216485101729233993 2881976412363826296925495)
                      ·
                        rfl

theorem cell23_5612629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 6, 2].length) (baseStart_5612629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612629 prefixEnd_5612629 := by exact prefixLift 5612629
  have htrace : WordTrace (prefixWord ++ tailWord_5612629) baseStart_5612629 baseEnd_5612629 := by
    simpa [prefixWord, tailWord_5612629, baseEnd_5612629] using wordTrace_append hprefix tailTrace_5612629
  have hstable : (prefixWord ++ tailWord_5612629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612629).length < 2 ^ (prefixWord ++ tailWord_5612629).sum := by decide
  have hdescent : baseEnd_5612629 < baseStart_5612629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612630 : List Nat := [5, 2, 2, 1, 2, 1, 2, 3, 5]
def baseStart_5612630 : Nat := 118140960795 + 5612630 * 2 ^ 59
def prefixEnd_5612630 : Nat := 4983230072969 + 3 ^ 40 * 5612630 * 2
def baseEnd_5612630 : Nat := 320219658427164532556999

theorem tailTrace_5612630 : CollatzResearch.WordTrace tailWord_5612630 prefixEnd_5612630 320219658427164532556999 := by
  unfold tailWord_5612630
  simp only [CollatzResearch.WordTrace]
  refine ⟨12794339603525471608386209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136472955770938363822786229 12794339603525471608386209)
  ·
    refine ⟨9595754702644103706289657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12794339603525471608386209 9595754702644103706289657)
    ·
      refine ⟨7196816026983077779717243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9595754702644103706289657 7196816026983077779717243)
      ·
        refine ⟨10795224040474616669575865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7196816026983077779717243 10795224040474616669575865)
        ·
          refine ⟨8096418030355962502181899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10795224040474616669575865 8096418030355962502181899)
          ·
            refine ⟨12144627045533943753272849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8096418030355962502181899 12144627045533943753272849)
            ·
              refine ⟨9108470284150457814954637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12144627045533943753272849 9108470284150457814954637)
              ·
                refine ⟨3415676356556421680607989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9108470284150457814954637 3415676356556421680607989)
                ·
                  refine ⟨320219658427164532556999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3415676356556421680607989 320219658427164532556999)
                  ·
                    rfl

theorem cell23_5612630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_5612630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612630 prefixEnd_5612630 := by exact prefixLift 5612630
  have htrace : WordTrace (prefixWord ++ tailWord_5612630) baseStart_5612630 baseEnd_5612630 := by
    simpa [prefixWord, tailWord_5612630, baseEnd_5612630] using wordTrace_append hprefix tailTrace_5612630
  have hstable : (prefixWord ++ tailWord_5612630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612630).length < 2 ^ (prefixWord ++ tailWord_5612630).sum := by decide
  have hdescent : baseEnd_5612630 < baseStart_5612630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612652 : List Nat := [2, 2, 1, 1, 3, 2, 3, 1, 8]
def baseStart_5612652 : Nat := 118140960795 + 5612652 * 2 ^ 59
def prefixEnd_5612652 : Nat := 4983230072969 + 3 ^ 40 * 5612652 * 2
def baseEnd_5612652 : Nat := 320220913602097745215321

theorem tailTrace_5612652 : CollatzResearch.WordTrace tailWord_5612652 prefixEnd_5612652 320220913602097745215321 := by
  unfold tailWord_5612652
  simp only [CollatzResearch.WordTrace]
  refine ⟨102355118031163921745740105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136473490708218562327653473 102355118031163921745740105)
  ·
    refine ⟨76766338523372941309305079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102355118031163921745740105 76766338523372941309305079)
    ·
      refine ⟨115149507785059411963957619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76766338523372941309305079 115149507785059411963957619)
      ·
        refine ⟨172724261677589117945936429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115149507785059411963957619 172724261677589117945936429)
        ·
          refine ⟨64771598129095919229726161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172724261677589117945936429 64771598129095919229726161)
          ·
            refine ⟨48578698596821939422294621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64771598129095919229726161 48578698596821939422294621)
            ·
              refine ⟨18217011973808227283360483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48578698596821939422294621 18217011973808227283360483)
              ·
                refine ⟨27325517960712340925040725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18217011973808227283360483 27325517960712340925040725)
                ·
                  refine ⟨320220913602097745215321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27325517960712340925040725 320220913602097745215321)
                  ·
                    rfl

theorem cell23_5612652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 8].length) (baseStart_5612652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612652 prefixEnd_5612652 := by exact prefixLift 5612652
  have htrace : WordTrace (prefixWord ++ tailWord_5612652) baseStart_5612652 baseEnd_5612652 := by
    simpa [prefixWord, tailWord_5612652, baseEnd_5612652] using wordTrace_append hprefix tailTrace_5612652
  have hstable : (prefixWord ++ tailWord_5612652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612652).length < 2 ^ (prefixWord ++ tailWord_5612652).sum := by decide
  have hdescent : baseEnd_5612652 < baseStart_5612652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612656 : List Nat := [2, 1, 1, 1, 5, 1, 1, 6, 1, 4]
def baseStart_5612656 : Nat := 118140960795 + 5612656 * 2 ^ 59
def prefixEnd_5612656 : Nat := 4983230072969 + 3 ^ 40 * 5612656 * 2
def baseEnd_5612656 : Nat := 960663425447165897095957

theorem tailTrace_5612656 : CollatzResearch.WordTrace tailWord_5612656 prefixEnd_5612656 960663425447165897095957 := by
  unfold tailWord_5612656
  simp only [CollatzResearch.WordTrace]
  refine ⟨102355190977156676087312911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136473587969542234783083881 102355190977156676087312911)
  ·
    refine ⟨153532786465735014130969367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102355190977156676087312911 153532786465735014130969367)
    ·
      refine ⟨230299179698602521196454051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153532786465735014130969367 230299179698602521196454051)
      ·
        refine ⟨345448769547903781794681077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230299179698602521196454051 345448769547903781794681077)
        ·
          refine ⟨32385822145115979543251351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 345448769547903781794681077 32385822145115979543251351)
          ·
            refine ⟨48578733217673969314877027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32385822145115979543251351 48578733217673969314877027)
            ·
              refine ⟨72868099826510953972315541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48578733217673969314877027 72868099826510953972315541)
              ·
                refine ⟨3415692179367700967452291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72868099826510953972315541 3415692179367700967452291)
                ·
                  refine ⟨5123538269051551451178437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415692179367700967452291 5123538269051551451178437)
                  ·
                    refine ⟨960663425447165897095957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5123538269051551451178437 960663425447165897095957)
                    ·
                      rfl

theorem cell23_5612656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 6, 1, 4].length) (baseStart_5612656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612656 prefixEnd_5612656 := by exact prefixLift 5612656
  have htrace : WordTrace (prefixWord ++ tailWord_5612656) baseStart_5612656 baseEnd_5612656 := by
    simpa [prefixWord, tailWord_5612656, baseEnd_5612656] using wordTrace_append hprefix tailTrace_5612656
  have hstable : (prefixWord ++ tailWord_5612656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612656).length < 2 ^ (prefixWord ++ tailWord_5612656).sum := by decide
  have hdescent : baseEnd_5612656 < baseStart_5612656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612690 : List Nat := [3, 2, 3, 1, 1, 4, 1, 3, 1, 4]
def baseStart_5612690 : Nat := 118140960795 + 5612690 * 2 ^ 59
def prefixEnd_5612690 : Nat := 4983230072969 + 3 ^ 40 * 5612690 * 2
def baseEnd_5612690 : Nat := 960669244894583519420905

theorem tailTrace_5612690 : CollatzResearch.WordTrace tailWord_5612690 prefixEnd_5612690 960669244894583519420905 := by
  unfold tailWord_5612690
  simp only [CollatzResearch.WordTrace]
  refine ⟨51177905509047543995340881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136474414690793450654242349 51177905509047543995340881)
  ·
    refine ⟨38383429131785657996505661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51177905509047543995340881 38383429131785657996505661)
    ·
      refine ⟨14393785924419621748689623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38383429131785657996505661 14393785924419621748689623)
      ·
        refine ⟨21590678886629432623034435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14393785924419621748689623 21590678886629432623034435)
        ·
          refine ⟨32386018329944148934551653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21590678886629432623034435 32386018329944148934551653)
          ·
            refine ⟨6072378436864527925228435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32386018329944148934551653 6072378436864527925228435)
            ·
              refine ⟨9108567655296791887842653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072378436864527925228435 9108567655296791887842653)
              ·
                refine ⟨3415712870736296957940995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9108567655296791887842653 3415712870736296957940995)
                ·
                  refine ⟨5123569306104445436911493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3415712870736296957940995 5123569306104445436911493)
                  ·
                    refine ⟨960669244894583519420905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5123569306104445436911493 960669244894583519420905)
                    ·
                      rfl

theorem cell23_5612690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_5612690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612690 prefixEnd_5612690 := by exact prefixLift 5612690
  have htrace : WordTrace (prefixWord ++ tailWord_5612690) baseStart_5612690 baseEnd_5612690 := by
    simpa [prefixWord, tailWord_5612690, baseEnd_5612690] using wordTrace_append hprefix tailTrace_5612690
  have hstable : (prefixWord ++ tailWord_5612690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612690).length < 2 ^ (prefixWord ++ tailWord_5612690).sum := by decide
  have hdescent : baseEnd_5612690 < baseStart_5612690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612736 : List Nat := [2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 4]
def baseStart_5612736 : Nat := 118140960795 + 5612736 * 2 ^ 59
def prefixEnd_5612736 : Nat := 4983230072969 + 3 ^ 40 * 5612736 * 2
def baseEnd_5612736 : Nat := 2882031354793857378287503

theorem tailTrace_5612736 : CollatzResearch.WordTrace tailWord_5612736 prefixEnd_5612736 2882031354793857378287503 := by
  unfold tailWord_5612736
  simp only [CollatzResearch.WordTrace]
  refine ⟨102356649897011762918769031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136475533196015683891692041 102356649897011762918769031)
  ·
    refine ⟨153534974845517644378153547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102356649897011762918769031 153534974845517644378153547)
    ·
      refine ⟨230302462268276466567230321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153534974845517644378153547 230302462268276466567230321)
      ·
        refine ⟨172726846701207349925422741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230302462268276466567230321 172726846701207349925422741)
        ·
          refine ⟨8096570939119094527754191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 172726846701207349925422741 8096570939119094527754191)
          ·
            refine ⟨12144856408678641791631287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8096570939119094527754191 12144856408678641791631287)
            ·
              refine ⟨18217284613017962687446931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12144856408678641791631287 18217284613017962687446931)
              ·
                refine ⟨27325926919526944031170397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18217284613017962687446931 27325926919526944031170397)
                ·
                  refine ⟨10247222594822604011688899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27325926919526944031170397 10247222594822604011688899)
                  ·
                    refine ⟨15370833892233906017533349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10247222594822604011688899 15370833892233906017533349)
                    ·
                      refine ⟨2882031354793857378287503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15370833892233906017533349 2882031354793857378287503)
                      ·
                        rfl

theorem cell23_5612736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 4].length) (baseStart_5612736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612736 prefixEnd_5612736 := by exact prefixLift 5612736
  have htrace : WordTrace (prefixWord ++ tailWord_5612736) baseStart_5612736 baseEnd_5612736 := by
    simpa [prefixWord, tailWord_5612736, baseEnd_5612736] using wordTrace_append hprefix tailTrace_5612736
  have hstable : (prefixWord ++ tailWord_5612736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612736).length < 2 ^ (prefixWord ++ tailWord_5612736).sum := by decide
  have hdescent : baseEnd_5612736 < baseStart_5612736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612740 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 2, 3, 2]
def baseStart_5612740 : Nat := 118140960795 + 5612740 * 2 ^ 59
def prefixEnd_5612740 : Nat := 4983230072969 + 3 ^ 40 * 5612740 * 2
def baseEnd_5612740 : Nat := 2882033408716475362637485

theorem tailTrace_5612740 : CollatzResearch.WordTrace tailWord_5612740 prefixEnd_5612740 2882033408716475362637485 := by
  unfold tailWord_5612740
  simp only [CollatzResearch.WordTrace]
  refine ⟨102356722843004517260341837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136475630457339356347122449 102356722843004517260341837)
  ·
    refine ⟨38383771066126693972628189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102356722843004517260341837 38383771066126693972628189)
    ·
      refine ⟨14393914149797510239735571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38383771066126693972628189 14393914149797510239735571)
      ·
        refine ⟨21590871224696265359603357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14393914149797510239735571 21590871224696265359603357)
        ·
          refine ⟨8096576709261099509851259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21590871224696265359603357 8096576709261099509851259)
          ·
            refine ⟨12144865063891649264776889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8096576709261099509851259 12144865063891649264776889)
            ·
              refine ⟨9108648797918736948582667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12144865063891649264776889 9108648797918736948582667)
              ·
                refine ⟨13662973196878105422874001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9108648797918736948582667 13662973196878105422874001)
                ·
                  refine ⟨10247229897658579067155501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13662973196878105422874001 10247229897658579067155501)
                  ·
                    refine ⟨3842711211621967150183313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10247229897658579067155501 3842711211621967150183313)
                    ·
                      refine ⟨2882033408716475362637485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842711211621967150183313 2882033408716475362637485)
                      ·
                        rfl

theorem cell23_5612740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_5612740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612740 prefixEnd_5612740 := by exact prefixLift 5612740
  have htrace : WordTrace (prefixWord ++ tailWord_5612740) baseStart_5612740 baseEnd_5612740 := by
    simpa [prefixWord, tailWord_5612740, baseEnd_5612740] using wordTrace_append hprefix tailTrace_5612740
  have hstable : (prefixWord ++ tailWord_5612740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612740).length < 2 ^ (prefixWord ++ tailWord_5612740).sum := by decide
  have hdescent : baseEnd_5612740 < baseStart_5612740 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612883 : List Nat := [1, 1, 1, 2, 1, 1, 9, 2, 5]
def baseStart_5612883 : Nat := 118140960795 + 5612883 * 2 ^ 59
def prefixEnd_5612883 : Nat := 4983230072969 + 3 ^ 40 * 5612883 * 2
def baseEnd_5612883 : Nat := 320234092938896478127703

theorem tailTrace_5612883 : CollatzResearch.WordTrace tailWord_5612883 prefixEnd_5612883 320234092938896478127703 := by
  unfold tailWord_5612883
  simp only [CollatzResearch.WordTrace]
  refine ⟨204718661324490969943139303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136479107549660646628759535 204718661324490969943139303)
  ·
    refine ⟨307077991986736454914708955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204718661324490969943139303 307077991986736454914708955)
    ·
      refine ⟨460616987980104682372063433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307077991986736454914708955 460616987980104682372063433)
      ·
        refine ⟨345462740985078511779047575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460616987980104682372063433 345462740985078511779047575)
        ·
          refine ⟨518194111477617767668571363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345462740985078511779047575 518194111477617767668571363)
          ·
            refine ⟨777291167216426651502857045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518194111477617767668571363 777291167216426651502857045)
            ·
              refine ⟨4554440432908749911149553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 777291167216426651502857045 4554440432908749911149553)
              ·
                refine ⟨3415830324681562433362165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4554440432908749911149553 3415830324681562433362165)
                ·
                  refine ⟨320234092938896478127703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3415830324681562433362165 320234092938896478127703)
                  ·
                    rfl

theorem cell23_5612883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 9, 2, 5].length) (baseStart_5612883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612883 prefixEnd_5612883 := by exact prefixLift 5612883
  have htrace : WordTrace (prefixWord ++ tailWord_5612883) baseStart_5612883 baseEnd_5612883 := by
    simpa [prefixWord, tailWord_5612883, baseEnd_5612883] using wordTrace_append hprefix tailTrace_5612883
  have hstable : (prefixWord ++ tailWord_5612883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612883).length < 2 ^ (prefixWord ++ tailWord_5612883).sum := by decide
  have hdescent : baseEnd_5612883 < baseStart_5612883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612889 : List Nat := [1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 7]
def baseStart_5612889 : Nat := 118140960795 + 5612889 * 2 ^ 59
def prefixEnd_5612889 : Nat := 4983230072969 + 3 ^ 40 * 5612889 * 2
def baseEnd_5612889 : Nat := 2882109917333995279674299

theorem tailTrace_5612889 : CollatzResearch.WordTrace tailWord_5612889 prefixEnd_5612889 2882109917333995279674299 := by
  unfold tailWord_5612889
  simp only [CollatzResearch.WordTrace]
  refine ⟨204718880162469232967857721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136479253441646155311905147 204718880162469232967857721)
  ·
    refine ⟨153539160121851924725893291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204718880162469232967857721 153539160121851924725893291)
    ·
      refine ⟨230308740182777887088839937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153539160121851924725893291 230308740182777887088839937)
      ·
        refine ⟨172731555137083415316629953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230308740182777887088839937 172731555137083415316629953)
        ·
          refine ⟨129548666352812561487472465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172731555137083415316629953 129548666352812561487472465)
          ·
            refine ⟨97161499764609421115604349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129548666352812561487472465 97161499764609421115604349)
            ·
              refine ⟨36435562411728532918351631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97161499764609421115604349 36435562411728532918351631)
              ·
                refine ⟨54653343617592799377527447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36435562411728532918351631 54653343617592799377527447)
                ·
                  refine ⟨81980015426389199066291171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54653343617592799377527447 81980015426389199066291171)
                  ·
                    refine ⟨122970023139583798599436757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81980015426389199066291171 122970023139583798599436757)
                    ·
                      refine ⟨2882109917333995279674299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 122970023139583798599436757 2882109917333995279674299)
                      ·
                        rfl

theorem cell23_5612889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_5612889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612889 prefixEnd_5612889 := by exact prefixLift 5612889
  have htrace : WordTrace (prefixWord ++ tailWord_5612889) baseStart_5612889 baseEnd_5612889 := by
    simpa [prefixWord, tailWord_5612889, baseEnd_5612889] using wordTrace_append hprefix tailTrace_5612889
  have hstable : (prefixWord ++ tailWord_5612889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612889).length < 2 ^ (prefixWord ++ tailWord_5612889).sum := by decide
  have hdescent : baseEnd_5612889 < baseStart_5612889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612930 : List Nat := [3, 4, 2, 1, 1, 1, 2, 2, 2, 5]
def baseStart_5612930 : Nat := 118140960795 + 5612930 * 2 ^ 59
def prefixEnd_5612930 : Nat := 4983230072969 + 3 ^ 40 * 5612930 * 2
def baseEnd_5612930 : Nat := 960710323346943206420537

theorem tailTrace_5612930 : CollatzResearch.WordTrace tailWord_5612930 prefixEnd_5612930 960710323346943206420537 := by
  unfold tailWord_5612930
  simp only [CollatzResearch.WordTrace]
  refine ⟨51180093888830174242525061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136480250370213797980066829 51180093888830174242525061)
  ·
    refine ⟨9596267604155657670473449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51180093888830174242525061 9596267604155657670473449)
    ·
      refine ⟨7197200703116743252855087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9596267604155657670473449 7197200703116743252855087)
      ·
        refine ⟨10795801054675114879282631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7197200703116743252855087 10795801054675114879282631)
        ·
          refine ⟨16193701582012672318923947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10795801054675114879282631 16193701582012672318923947)
          ·
            refine ⟨24290552373019008478385921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16193701582012672318923947 24290552373019008478385921)
            ·
              refine ⟨18217914279764256358789441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24290552373019008478385921 18217914279764256358789441)
              ·
                refine ⟨13663435709823192269092081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18217914279764256358789441 13663435709823192269092081)
                ·
                  refine ⟨10247576782367394201819061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13663435709823192269092081 10247576782367394201819061)
                  ·
                    refine ⟨960710323346943206420537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10247576782367394201819061 960710323346943206420537)
                    ·
                      rfl

theorem cell23_5612930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_5612930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612930 prefixEnd_5612930 := by exact prefixLift 5612930
  have htrace : WordTrace (prefixWord ++ tailWord_5612930) baseStart_5612930 baseEnd_5612930 := by
    simpa [prefixWord, tailWord_5612930, baseEnd_5612930] using wordTrace_append hprefix tailTrace_5612930
  have hstable : (prefixWord ++ tailWord_5612930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612930).length < 2 ^ (prefixWord ++ tailWord_5612930).sum := by decide
  have hdescent : baseEnd_5612930 < baseStart_5612930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5612983 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 3]
def baseStart_5612983 : Nat := 118140960795 + 5612983 * 2 ^ 59
def prefixEnd_5612983 : Nat := 4983230072969 + 3 ^ 40 * 5612983 * 2
def baseEnd_5612983 : Nat := 2882158184515517911898867

theorem tailTrace_5612983 : CollatzResearch.WordTrace tailWord_5612983 prefixEnd_5612983 2882158184515517911898867 := by
  unfold tailWord_5612983
  simp only [CollatzResearch.WordTrace]
  refine ⟨204722308624128687021779603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136481539082752458014519735 204722308624128687021779603)
  ·
    refine ⟨307083462936193030532669405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204722308624128687021779603 307083462936193030532669405)
    ·
      refine ⟨115156298601072386449751027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307083462936193030532669405 115156298601072386449751027)
      ·
        refine ⟨172734447901608579674626541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115156298601072386449751027 172734447901608579674626541)
        ·
          refine ⟨64775417963103217377984953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172734447901608579674626541 64775417963103217377984953)
          ·
            refine ⟨48581563472327413033488715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64775417963103217377984953 48581563472327413033488715)
            ·
              refine ⟨72872345208491119550233073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48581563472327413033488715 72872345208491119550233073)
              ·
                refine ⟨54654258906368339662674805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72872345208491119550233073 54654258906368339662674805)
                ·
                  refine ⟨5123836772472031843375763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54654258906368339662674805 5123836772472031843375763)
                  ·
                    refine ⟨7685755158708047765063645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5123836772472031843375763 7685755158708047765063645)
                    ·
                      refine ⟨2882158184515517911898867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7685755158708047765063645 2882158184515517911898867)
                      ·
                        rfl

theorem cell23_5612983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_5612983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5612983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5612983 prefixEnd_5612983 := by exact prefixLift 5612983
  have htrace : WordTrace (prefixWord ++ tailWord_5612983) baseStart_5612983 baseEnd_5612983 := by
    simpa [prefixWord, tailWord_5612983, baseEnd_5612983] using wordTrace_append hprefix tailTrace_5612983
  have hstable : (prefixWord ++ tailWord_5612983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5612983).length < 2 ^ (prefixWord ++ tailWord_5612983).sum := by decide
  have hdescent : baseEnd_5612983 < baseStart_5612983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5612983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613000 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 3, 1, 3]
def baseStart_5613000 : Nat := 118140960795 + 5613000 * 2 ^ 59
def prefixEnd_5613000 : Nat := 4983230072969 + 3 ^ 40 * 5613000 * 2
def baseEnd_5613000 : Nat := 2882166913686644345386289

theorem tailTrace_5613000 : CollatzResearch.WordTrace tailWord_5613000 prefixEnd_5613000 2882166913686644345386289 := by
  unfold tailWord_5613000
  simp only [CollatzResearch.WordTrace]
  refine ⟨102361464332533549462574227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136481952443378065950098969 102361464332533549462574227)
  ·
    refine ⟨153542196498800324193861341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102361464332533549462574227 153542196498800324193861341)
    ·
      refine ⟨57578323687050121572698003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153542196498800324193861341 57578323687050121572698003)
      ·
        refine ⟨86367485530575182359047005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57578323687050121572698003 86367485530575182359047005)
        ·
          refine ⟨32387807073965693384642627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86367485530575182359047005 32387807073965693384642627)
          ·
            refine ⟨48581710610948540076963941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32387807073965693384642627 48581710610948540076963941)
            ·
              refine ⟨9109070739552851264430739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48581710610948540076963941 9109070739552851264430739)
              ·
                refine ⟨13663606109329276896646109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9109070739552851264430739 13663606109329276896646109)
                ·
                  refine ⟨5123852290998478836242291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13663606109329276896646109 5123852290998478836242291)
                  ·
                    refine ⟨7685778436497718254363437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5123852290998478836242291 7685778436497718254363437)
                    ·
                      refine ⟨2882166913686644345386289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7685778436497718254363437 2882166913686644345386289)
                      ·
                        rfl

theorem cell23_5613000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 1, 3].length) (baseStart_5613000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613000 prefixEnd_5613000 := by exact prefixLift 5613000
  have htrace : WordTrace (prefixWord ++ tailWord_5613000) baseStart_5613000 baseEnd_5613000 := by
    simpa [prefixWord, tailWord_5613000, baseEnd_5613000] using wordTrace_append hprefix tailTrace_5613000
  have hstable : (prefixWord ++ tailWord_5613000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613000).length < 2 ^ (prefixWord ++ tailWord_5613000).sum := by decide
  have hdescent : baseEnd_5613000 < baseStart_5613000 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613023 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 2, 6, 2]
def baseStart_5613023 : Nat := 118140960795 + 5613023 * 2 ^ 59
def prefixEnd_5613023 : Nat := 4983230072969 + 3 ^ 40 * 5613023 * 2
def baseEnd_5613023 : Nat := 2882178723741697755398683

theorem tailTrace_5613023 : CollatzResearch.WordTrace tailWord_5613023 prefixEnd_5613023 2882178723741697755398683 := by
  unfold tailWord_5613023
  simp only [CollatzResearch.WordTrace]
  refine ⟨204723767543983773853235723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136482511695989182568823815 204723767543983773853235723)
  ·
    refine ⟨307085651315975660779853585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204723767543983773853235723 307085651315975660779853585)
    ·
      refine ⟨230314238486981745584890189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307085651315975660779853585 230314238486981745584890189)
      ·
        refine ⟨86367839432618154594333821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230314238486981745584890189 86367839432618154594333821)
        ·
          refine ⟨32387939787231807972875183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86367839432618154594333821 32387939787231807972875183)
          ·
            refine ⟨48581909680847711959312775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32387939787231807972875183 48581909680847711959312775)
            ·
              refine ⟨72872864521271567938969163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48581909680847711959312775 72872864521271567938969163)
              ·
                refine ⟨109309296781907351908453745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72872864521271567938969163 109309296781907351908453745)
                ·
                  refine ⟨81981972586430513931340309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109309296781907351908453745 81981972586430513931340309)
                  ·
                    refine ⟨3842904964988930340531577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81981972586430513931340309 3842904964988930340531577)
                    ·
                      refine ⟨2882178723741697755398683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3842904964988930340531577 2882178723741697755398683)
                      ·
                        rfl

theorem cell23_5613023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_5613023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613023 prefixEnd_5613023 := by exact prefixLift 5613023
  have htrace : WordTrace (prefixWord ++ tailWord_5613023) baseStart_5613023 baseEnd_5613023 := by
    simpa [prefixWord, tailWord_5613023, baseEnd_5613023] using wordTrace_append hprefix tailTrace_5613023
  have hstable : (prefixWord ++ tailWord_5613023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613023).length < 2 ^ (prefixWord ++ tailWord_5613023).sum := by decide
  have hdescent : baseEnd_5613023 < baseStart_5613023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613063 : List Nat := [1, 1, 4, 3, 2, 2, 2, 8]
def baseStart_5613063 : Nat := 118140960795 + 5613063 * 2 ^ 59
def prefixEnd_5613063 : Nat := 4983230072969 + 3 ^ 40 * 5613063 * 2
def baseEnd_5613063 : Nat := 106748120850662133292537

theorem tailTrace_5613063 : CollatzResearch.WordTrace tailWord_5613063 prefixEnd_5613063 106748120850662133292537 := by
  unfold tailWord_5613063
  simp only [CollatzResearch.WordTrace]
  refine ⟨204725226463838860684691843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136483484309225907123127895 204725226463838860684691843)
  ·
    refine ⟨307087839695758291027037765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204725226463838860684691843 307087839695758291027037765)
    ·
      refine ⟨57578969942954679567569581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307087839695758291027037765 57578969942954679567569581)
      ·
        refine ⟨21592113728608004837838593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57578969942954679567569581 21592113728608004837838593)
        ·
          refine ⟨16194085296456003628378945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21592113728608004837838593 16194085296456003628378945)
          ·
            refine ⟨12145563972342002721284209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16194085296456003628378945 12145563972342002721284209)
            ·
              refine ⟨9109172979256502040963157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12145563972342002721284209 9109172979256502040963157)
              ·
                refine ⟨106748120850662133292537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9109172979256502040963157 106748120850662133292537)
                ·
                  rfl

theorem cell23_5613063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 2, 8].length) (baseStart_5613063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613063 prefixEnd_5613063 := by exact prefixLift 5613063
  have htrace : WordTrace (prefixWord ++ tailWord_5613063) baseStart_5613063 baseEnd_5613063 := by
    simpa [prefixWord, tailWord_5613063, baseEnd_5613063] using wordTrace_append hprefix tailTrace_5613063
  have hstable : (prefixWord ++ tailWord_5613063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613063).length < 2 ^ (prefixWord ++ tailWord_5613063).sum := by decide
  have hdescent : baseEnd_5613063 < baseStart_5613063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613073 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 3]
def baseStart_5613073 : Nat := 118140960795 + 5613073 * 2 ^ 59
def prefixEnd_5613073 : Nat := 4983230072969 + 3 ^ 40 * 5613073 * 2
def baseEnd_5613073 : Nat := 2882204397774422559773453

theorem tailTrace_5613073 : CollatzResearch.WordTrace tailWord_5613073 prefixEnd_5613073 2882204397774422559773453 := by
  unfold tailWord_5613073
  simp only [CollatzResearch.WordTrace]
  refine ⟨204725591193802632392555873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136483727462535088261703915 204725591193802632392555873)
  ·
    refine ⟨153544193395351974294416905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204725591193802632392555873 153544193395351974294416905)
    ·
      refine ⟨115158145046513980720812679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153544193395351974294416905 115158145046513980720812679)
      ·
        refine ⟨172737217569770971081219019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115158145046513980720812679 172737217569770971081219019)
        ·
          refine ⟨259105826354656456621828529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172737217569770971081219019 259105826354656456621828529)
          ·
            refine ⟨194329369765992342466371397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259105826354656456621828529 194329369765992342466371397)
            ·
              refine ⟨36436756831123564212444637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194329369765992342466371397 36436756831123564212444637)
              ·
                refine ⟨13663783811671336579666739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36436756831123564212444637 13663783811671336579666739)
                ·
                  refine ⟨20495675717507004869500109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13663783811671336579666739 20495675717507004869500109)
                  ·
                    refine ⟨7685878394065126826062541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20495675717507004869500109 7685878394065126826062541)
                    ·
                      refine ⟨2882204397774422559773453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7685878394065126826062541 2882204397774422559773453)
                      ·
                        rfl

theorem cell23_5613073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 3].length) (baseStart_5613073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613073 prefixEnd_5613073 := by exact prefixLift 5613073
  have htrace : WordTrace (prefixWord ++ tailWord_5613073) baseStart_5613073 baseEnd_5613073 := by
    simpa [prefixWord, tailWord_5613073, baseEnd_5613073] using wordTrace_append hprefix tailTrace_5613073
  have hstable : (prefixWord ++ tailWord_5613073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613073).length < 2 ^ (prefixWord ++ tailWord_5613073).sum := by decide
  have hdescent : baseEnd_5613073 < baseStart_5613073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613077 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_5613077 : Nat := 118140960795 + 5613077 * 2 ^ 59
def prefixEnd_5613077 : Nat := 4983230072969 + 3 ^ 40 * 5613077 * 2
def baseEnd_5613077 : Nat := 2882206451697040544123435

theorem tailTrace_5613077 : CollatzResearch.WordTrace tailWord_5613077 prefixEnd_5613077 2882206451697040544123435 := by
  unfold tailWord_5613077
  simp only [CollatzResearch.WordTrace]
  refine ⟨204725737085788141075701485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136483824723858760717134323 204725737085788141075701485)
  ·
    refine ⟨76772151407170552903388057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204725737085788141075701485 76772151407170552903388057)
    ·
      refine ⟨57579113555377914677541043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76772151407170552903388057 57579113555377914677541043)
      ·
        refine ⟨86368670333066872016311565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57579113555377914677541043 86368670333066872016311565)
        ·
          refine ⟨32388251374900077006116837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86368670333066872016311565 32388251374900077006116837)
          ·
            refine ⟨6072797132793764438646907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32388251374900077006116837 6072797132793764438646907)
            ·
              refine ⟨9109195699190646657970361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6072797132793764438646907 9109195699190646657970361)
              ·
                refine ⟨6831896774392984993477771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9109195699190646657970361 6831896774392984993477771)
                ·
                  refine ⟨10247845161589477490216657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6831896774392984993477771 10247845161589477490216657)
                  ·
                    refine ⟨7685883871192108117662493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10247845161589477490216657 7685883871192108117662493)
                    ·
                      refine ⟨2882206451697040544123435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7685883871192108117662493 2882206451697040544123435)
                      ·
                        rfl

theorem cell23_5613077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_5613077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613077 prefixEnd_5613077 := by exact prefixLift 5613077
  have htrace : WordTrace (prefixWord ++ tailWord_5613077) baseStart_5613077 baseEnd_5613077 := by
    simpa [prefixWord, tailWord_5613077, baseEnd_5613077] using wordTrace_append hprefix tailTrace_5613077
  have hstable : (prefixWord ++ tailWord_5613077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613077).length < 2 ^ (prefixWord ++ tailWord_5613077).sum := by decide
  have hdescent : baseEnd_5613077 < baseStart_5613077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613090 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 6, 1, 3]
def baseStart_5613090 : Nat := 118140960795 + 5613090 * 2 ^ 59
def prefixEnd_5613090 : Nat := 4983230072969 + 3 ^ 40 * 5613090 * 2
def baseEnd_5613090 : Nat := 2882213126945548993260875

theorem tailTrace_5613090 : CollatzResearch.WordTrace tailWord_5613090 prefixEnd_5613090 2882213126945548993260875 := by
  unfold tailWord_5613090
  simp only [CollatzResearch.WordTrace]
  refine ⟨51181552808685261073981181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136484140823160696197283149 51181552808685261073981181)
  ·
    refine ⟨19193082303256972902742943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51181552808685261073981181 19193082303256972902742943)
    ·
      refine ⟨28789623454885459354114415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19193082303256972902742943 28789623454885459354114415)
      ·
        refine ⟨43184435182328189031171623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28789623454885459354114415 43184435182328189031171623)
        ·
          refine ⟨64776652773492283546757435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43184435182328189031171623 64776652773492283546757435)
          ·
            refine ⟨97164979160238425320136153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64776652773492283546757435 97164979160238425320136153)
            ·
              refine ⟨72873734370178818990102115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97164979160238425320136153 72873734370178818990102115)
              ·
                refine ⟨109310601555268228485153173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72873734370178818990102115 109310601555268228485153173)
                ·
                  refine ⟨5123934447903198210241555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109310601555268228485153173 5123934447903198210241555)
                  ·
                    refine ⟨7685901671854797315362333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5123934447903198210241555 7685901671854797315362333)
                    ·
                      refine ⟨2882213126945548993260875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7685901671854797315362333 2882213126945548993260875)
                      ·
                        rfl

theorem cell23_5613090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_5613090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613090 prefixEnd_5613090 := by exact prefixLift 5613090
  have htrace : WordTrace (prefixWord ++ tailWord_5613090) baseStart_5613090 baseEnd_5613090 := by
    simpa [prefixWord, tailWord_5613090, baseEnd_5613090] using wordTrace_append hprefix tailTrace_5613090
  have hstable : (prefixWord ++ tailWord_5613090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613090).length < 2 ^ (prefixWord ++ tailWord_5613090).sum := by decide
  have hdescent : baseEnd_5613090 < baseStart_5613090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613107 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 3]
def baseStart_5613107 : Nat := 118140960795 + 5613107 * 2 ^ 59
def prefixEnd_5613107 : Nat := 4983230072969 + 3 ^ 40 * 5613107 * 2
def baseEnd_5613107 : Nat := 2882221856116675426748297

theorem tailTrace_5613107 : CollatzResearch.WordTrace tailWord_5613107 prefixEnd_5613107 2882221856116675426748297 := by
  unfold tailWord_5613107
  simp only [CollatzResearch.WordTrace]
  refine ⟨204726831275679456199293575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136484554183786304132862383 204726831275679456199293575)
  ·
    refine ⟨307090246913519184298940363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204726831275679456199293575 307090246913519184298940363)
    ·
      refine ⟨460635370370278776448410545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307090246913519184298940363 460635370370278776448410545)
      ·
        refine ⟨345476527777709082336307909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460635370370278776448410545 345476527777709082336307909)
        ·
          refine ⟨64776848958320452938057733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345476527777709082336307909 64776848958320452938057733)
          ·
            refine ⟨12145659179685084925885825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64776848958320452938057733 12145659179685084925885825)
            ·
              refine ⟨9109244384763813694414369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12145659179685084925885825 9109244384763813694414369)
              ·
                refine ⟨6831933288572860270810777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9109244384763813694414369 6831933288572860270810777)
                ·
                  refine ⟨5123949966429645203108083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6831933288572860270810777 5123949966429645203108083)
                  ·
                    refine ⟨7685924949644467804662125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5123949966429645203108083 7685924949644467804662125)
                    ·
                      refine ⟨2882221856116675426748297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7685924949644467804662125 2882221856116675426748297)
                      ·
                        rfl

theorem cell23_5613107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 1, 3].length) (baseStart_5613107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613107 prefixEnd_5613107 := by exact prefixLift 5613107
  have htrace : WordTrace (prefixWord ++ tailWord_5613107) baseStart_5613107 baseEnd_5613107 := by
    simpa [prefixWord, tailWord_5613107, baseEnd_5613107] using wordTrace_append hprefix tailTrace_5613107
  have hstable : (prefixWord ++ tailWord_5613107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613107).length < 2 ^ (prefixWord ++ tailWord_5613107).sum := by decide
  have hdescent : baseEnd_5613107 < baseStart_5613107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613113 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5613113 : Nat := 118140960795 + 5613113 * 2 ^ 59
def prefixEnd_5613113 : Nat := 4983230072969 + 3 ^ 40 * 5613113 * 2
def baseEnd_5613113 : Nat := 2882224937000602403273269

theorem tailTrace_5613113 : CollatzResearch.WordTrace tailWord_5613113 prefixEnd_5613113 2882224937000602403273269 := by
  unfold tailWord_5613113
  simp only [CollatzResearch.WordTrace]
  refine ⟨204727050113657719224011993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136484700075771812816007995 204727050113657719224011993)
  ·
    refine ⟨153545287585243289418008995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204727050113657719224011993 153545287585243289418008995)
    ·
      refine ⟨230317931377864934127013493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153545287585243289418008995 230317931377864934127013493)
      ·
        refine ⟨21592306066674837574407515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230317931377864934127013493 21592306066674837574407515)
        ·
          refine ⟨32388459100012256361611273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21592306066674837574407515 32388459100012256361611273)
          ·
            refine ⟨24291344325009192271208455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32388459100012256361611273 24291344325009192271208455)
            ·
              refine ⟨36437016487513788406812683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24291344325009192271208455 36437016487513788406812683)
              ·
                refine ⟨54655524731270682610219025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36437016487513788406812683 54655524731270682610219025)
                ·
                  refine ⟨40991643548453011957664269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54655524731270682610219025 40991643548453011957664269)
                  ·
                    refine ⟨15371866330669879484124101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40991643548453011957664269 15371866330669879484124101)
                    ·
                      refine ⟨2882224937000602403273269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15371866330669879484124101 2882224937000602403273269)
                      ·
                        rfl

theorem cell23_5613113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5613113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613113 prefixEnd_5613113 := by exact prefixLift 5613113
  have htrace : WordTrace (prefixWord ++ tailWord_5613113) baseStart_5613113 baseEnd_5613113 := by
    simpa [prefixWord, tailWord_5613113, baseEnd_5613113] using wordTrace_append hprefix tailTrace_5613113
  have hstable : (prefixWord ++ tailWord_5613113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613113).length < 2 ^ (prefixWord ++ tailWord_5613113).sum := by decide
  have hdescent : baseEnd_5613113 < baseStart_5613113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613160 : List Nat := [2, 1, 4, 3, 1, 1, 1, 2, 2, 2, 4]
def baseStart_5613160 : Nat := 118140960795 + 5613160 * 2 ^ 59
def prefixEnd_5613160 : Nat := 4983230072969 + 3 ^ 40 * 5613160 * 2
def baseEnd_5613160 : Nat := 2882249070591363719385553

theorem tailTrace_5613160 : CollatzResearch.WordTrace tailWord_5613160 prefixEnd_5613160 2882249070591363719385553 := by
  unfold tailWord_5613160
  simp only [CollatzResearch.WordTrace]
  refine ⟨102364382172243723125486467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136485842896324964167315289 102364382172243723125486467)
  ·
    refine ⟨153546573258365584688229701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102364382172243723125486467 153546573258365584688229701)
    ·
      refine ⟨28789982485943547129043069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153546573258365584688229701 28789982485943547129043069)
      ·
        refine ⟨10796243432228830173391151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28789982485943547129043069 10796243432228830173391151)
        ·
          refine ⟨16194365148343245260086727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10796243432228830173391151 16194365148343245260086727)
          ·
            refine ⟨24291547722514867890130091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16194365148343245260086727 24291547722514867890130091)
            ·
              refine ⟨36437321583772301835195137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24291547722514867890130091 36437321583772301835195137)
              ·
                refine ⟨27327991187829226376396353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36437321583772301835195137 27327991187829226376396353)
                ·
                  refine ⟨20495993390871919782297265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27327991187829226376396353 20495993390871919782297265)
                  ·
                    refine ⟨15371995043153939836722949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20495993390871919782297265 15371995043153939836722949)
                    ·
                      refine ⟨2882249070591363719385553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15371995043153939836722949 2882249070591363719385553)
                      ·
                        rfl

theorem cell23_5613160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_5613160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613160 prefixEnd_5613160 := by exact prefixLift 5613160
  have htrace : WordTrace (prefixWord ++ tailWord_5613160) baseStart_5613160 baseEnd_5613160 := by
    simpa [prefixWord, tailWord_5613160, baseEnd_5613160] using wordTrace_append hprefix tailTrace_5613160
  have hstable : (prefixWord ++ tailWord_5613160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613160).length < 2 ^ (prefixWord ++ tailWord_5613160).sum := by decide
  have hdescent : baseEnd_5613160 < baseStart_5613160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613170 : List Nat := [3, 2, 1, 2, 3, 2, 2, 1, 7]
def baseStart_5613170 : Nat := 118140960795 + 5613170 * 2 ^ 59
def prefixEnd_5613170 : Nat := 4983230072969 + 3 ^ 40 * 5613170 * 2
def baseEnd_5613170 : Nat := 320250467266434297806723

theorem tailTrace_5613170 : CollatzResearch.WordTrace tailWord_5613170 prefixEnd_5613170 320250467266434297806723 := by
  unfold tailWord_5613170
  simp only [CollatzResearch.WordTrace]
  refine ⟨51182282268612804489709241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136486086049634145305891309 51182282268612804489709241)
  ·
    refine ⟨38386711701459603367281931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51182282268612804489709241 38386711701459603367281931)
    ·
      refine ⟨57580067552189405050922897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38386711701459603367281931 57580067552189405050922897)
      ·
        refine ⟨43185050664142053788192173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57580067552189405050922897 43185050664142053788192173)
        ·
          refine ⟨16194393999053270170572065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43185050664142053788192173 16194393999053270170572065)
          ·
            refine ⟨12145795499289952627929049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16194393999053270170572065 12145795499289952627929049)
            ·
              refine ⟨9109346624467464470946787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12145795499289952627929049 9109346624467464470946787)
              ·
                refine ⟨13664019936701196706420181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9109346624467464470946787 13664019936701196706420181)
                ·
                  refine ⟨320250467266434297806723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13664019936701196706420181 320250467266434297806723)
                  ·
                    rfl

theorem cell23_5613170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 7].length) (baseStart_5613170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613170 prefixEnd_5613170 := by exact prefixLift 5613170
  have htrace : WordTrace (prefixWord ++ tailWord_5613170) baseStart_5613170 baseEnd_5613170 := by
    simpa [prefixWord, tailWord_5613170, baseEnd_5613170] using wordTrace_append hprefix tailTrace_5613170
  have hstable : (prefixWord ++ tailWord_5613170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613170).length < 2 ^ (prefixWord ++ tailWord_5613170).sum := by decide
  have hdescent : baseEnd_5613170 < baseStart_5613170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613181 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 2, 2, 2]
def baseStart_5613181 : Nat := 118140960795 + 5613181 * 2 ^ 59
def prefixEnd_5613181 : Nat := 4983230072969 + 3 ^ 40 * 5613181 * 2
def baseEnd_5613181 : Nat := 2882259853685108137222957

theorem tailTrace_5613181 : CollatzResearch.WordTrace tailWord_5613181 prefixEnd_5613181 2882259853685108137222957 := by
  unfold tailWord_5613181
  simp only [CollatzResearch.WordTrace]
  refine ⟨204729530277411366837487397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136486353518274244558324931 204729530277411366837487397)
  ·
    refine ⟨38386786927014631282028887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204729530277411366837487397 38386786927014631282028887)
    ·
      refine ⟨57580180390521946923043331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38386786927014631282028887 57580180390521946923043331)
      ·
        refine ⟨86370270585782920384564997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57580180390521946923043331 86370270585782920384564997)
        ·
          refine ⟨16194425734834297572105937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86370270585782920384564997 16194425734834297572105937)
          ·
            refine ⟨12145819301125723179079453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16194425734834297572105937 12145819301125723179079453)
            ·
              refine ⟨4554682237922146192154795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12145819301125723179079453 4554682237922146192154795)
              ·
                refine ⟨6832023356883219288232193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4554682237922146192154795 6832023356883219288232193)
                ·
                  refine ⟨5124017517662414466174145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6832023356883219288232193 5124017517662414466174145)
                  ·
                    refine ⟨3843013138246810849630609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5124017517662414466174145 3843013138246810849630609)
                    ·
                      refine ⟨2882259853685108137222957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843013138246810849630609 2882259853685108137222957)
                      ·
                        rfl

theorem cell23_5613181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 2, 2].length) (baseStart_5613181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613181 prefixEnd_5613181 := by exact prefixLift 5613181
  have htrace : WordTrace (prefixWord ++ tailWord_5613181) baseStart_5613181 baseEnd_5613181 := by
    simpa [prefixWord, tailWord_5613181, baseEnd_5613181] using wordTrace_append hprefix tailTrace_5613181
  have hstable : (prefixWord ++ tailWord_5613181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613181).length < 2 ^ (prefixWord ++ tailWord_5613181).sum := by decide
  have hdescent : baseEnd_5613181 < baseStart_5613181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613220 : List Nat := [2, 3, 1, 2, 2, 2, 1, 1, 4, 1, 4]
def baseStart_5613220 : Nat := 118140960795 + 5613220 * 2 ^ 59
def prefixEnd_5613220 : Nat := 4983230072969 + 3 ^ 40 * 5613220 * 2
def baseEnd_5613220 : Nat := 2882279879430633484635277

theorem tailTrace_5613220 : CollatzResearch.WordTrace tailWord_5613220 prefixEnd_5613220 2882279879430633484635277 := by
  unfold tailWord_5613220
  simp only [CollatzResearch.WordTrace]
  refine ⟨102365476362135038249078557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136487301816180050998771409 102365476362135038249078557)
  ·
    refine ⟨38387053635800639343404459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102365476362135038249078557 38387053635800639343404459)
    ·
      refine ⟨57580580453700959015106689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38387053635800639343404459 57580580453700959015106689)
      ·
        refine ⟨43185435340275719261330017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57580580453700959015106689 43185435340275719261330017)
        ·
          refine ⟨32389076505206789445997513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43185435340275719261330017 32389076505206789445997513)
          ·
            refine ⟨24291807378905092084498135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32389076505206789445997513 24291807378905092084498135)
            ·
              refine ⟨36437711068357638126747203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24291807378905092084498135 36437711068357638126747203)
              ·
                refine ⟨54656566602536457190120805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36437711068357638126747203 54656566602536457190120805)
                ·
                  refine ⟨10248106237975585723147651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54656566602536457190120805 10248106237975585723147651)
                  ·
                    refine ⟨15372159356963378584721477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10248106237975585723147651 15372159356963378584721477)
                    ·
                      refine ⟨2882279879430633484635277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15372159356963378584721477 2882279879430633484635277)
                      ·
                        rfl

theorem cell23_5613220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_5613220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613220 prefixEnd_5613220 := by exact prefixLift 5613220
  have htrace : WordTrace (prefixWord ++ tailWord_5613220) baseStart_5613220 baseEnd_5613220 := by
    simpa [prefixWord, tailWord_5613220, baseEnd_5613220] using wordTrace_append hprefix tailTrace_5613220
  have hstable : (prefixWord ++ tailWord_5613220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613220).length < 2 ^ (prefixWord ++ tailWord_5613220).sum := by decide
  have hdescent : baseEnd_5613220 < baseStart_5613220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613290 : List Nat := [3, 1, 3, 1, 1, 1, 3, 2, 3, 5]
def baseStart_5613290 : Nat := 118140960795 + 5613290 * 2 ^ 59
def prefixEnd_5613290 : Nat := 4983230072969 + 3 ^ 40 * 5613290 * 2
def baseEnd_5613290 : Nat := 960771941025482736919985

theorem tailTrace_5613290 : CollatzResearch.WordTrace tailWord_5613290 prefixEnd_5613290 960771941025482736919985 := by
  unfold tailWord_5613290
  simp only [CollatzResearch.WordTrace]
  refine ⟨51183376458504119613301331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136489003889344318968803549 51183376458504119613301331)
  ·
    refine ⟨76775064687756179419951997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51183376458504119613301331 76775064687756179419951997)
    ·
      refine ⟨28790649257908567282481999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76775064687756179419951997 28790649257908567282481999)
      ·
        refine ⟨43185973886862850923722999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28790649257908567282481999 43185973886862850923722999)
        ·
          refine ⟨64778960830294276385584499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43185973886862850923722999 64778960830294276385584499)
          ·
            refine ⟨97168441245441414578376749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64778960830294276385584499 97168441245441414578376749)
            ·
              refine ⟨36438165467040530466891281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97168441245441414578376749 36438165467040530466891281)
              ·
                refine ⟨27328624100280397850168461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36438165467040530466891281 27328624100280397850168461)
                ·
                  refine ⟨10248234037605149193813173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27328624100280397850168461 10248234037605149193813173)
                  ·
                    refine ⟨960771941025482736919985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10248234037605149193813173 960771941025482736919985)
                    ·
                      rfl

theorem cell23_5613290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_5613290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613290 prefixEnd_5613290 := by exact prefixLift 5613290
  have htrace : WordTrace (prefixWord ++ tailWord_5613290) baseStart_5613290 baseEnd_5613290 := by
    simpa [prefixWord, tailWord_5613290, baseEnd_5613290] using wordTrace_append hprefix tailTrace_5613290
  have hstable : (prefixWord ++ tailWord_5613290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613290).length < 2 ^ (prefixWord ++ tailWord_5613290).sum := by decide
  have hdescent : baseEnd_5613290 < baseStart_5613290 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613314 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_5613314 : Nat := 118140960795 + 5613314 * 2 ^ 59
def prefixEnd_5613314 : Nat := 4983230072969 + 3 ^ 40 * 5613314 * 2
def baseEnd_5613314 : Nat := 2882328146612156116859845

theorem tailTrace_5613314 : CollatzResearch.WordTrace tailWord_5613314 prefixEnd_5613314 2882328146612156116859845 := by
  unfold tailWord_5613314
  simp only [CollatzResearch.WordTrace]
  refine ⟨51183595296482382638019749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136489587457286353701385997 51183595296482382638019749)
  ·
    refine ⟨9596924118090446744628703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51183595296482382638019749 9596924118090446744628703)
    ·
      refine ⟨14395386177135670116943055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9596924118090446744628703 14395386177135670116943055)
      ·
        refine ⟨21593079265703505175414583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14395386177135670116943055 21593079265703505175414583)
        ·
          refine ⟨32389618898555257763121875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21593079265703505175414583 32389618898555257763121875)
          ·
            refine ⟨48584428347832886644682813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32389618898555257763121875 48584428347832886644682813)
            ·
              refine ⟨18219160630437332491756055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48584428347832886644682813 18219160630437332491756055)
              ·
                refine ⟨27328740945655998737634083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18219160630437332491756055 27328740945655998737634083)
                ·
                  refine ⟨40993111418483998106451125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27328740945655998737634083 40993111418483998106451125)
                  ·
                    refine ⟨3843104195482874822479793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40993111418483998106451125 3843104195482874822479793)
                    ·
                      refine ⟨2882328146612156116859845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843104195482874822479793 2882328146612156116859845)
                      ·
                        rfl

theorem cell23_5613314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_5613314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613314 prefixEnd_5613314 := by exact prefixLift 5613314
  have htrace : WordTrace (prefixWord ++ tailWord_5613314) baseStart_5613314 baseEnd_5613314 := by
    simpa [prefixWord, tailWord_5613314, baseEnd_5613314] using wordTrace_append hprefix tailTrace_5613314
  have hstable : (prefixWord ++ tailWord_5613314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613314).length < 2 ^ (prefixWord ++ tailWord_5613314).sum := by decide
  have hdescent : baseEnd_5613314 < baseStart_5613314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613320 : List Nat := [2, 1, 3, 2, 2, 1, 1, 4, 1, 6]
def baseStart_5613320 : Nat := 118140960795 + 5613320 * 2 ^ 59
def prefixEnd_5613320 : Nat := 4983230072969 + 3 ^ 40 * 5613320 * 2
def baseEnd_5613320 : Nat := 960777075832027697794939

theorem tailTrace_5613320 : CollatzResearch.WordTrace tailWord_5613320 prefixEnd_5613320 960777075832027697794939 := by
  unfold tailWord_5613320
  simp only [CollatzResearch.WordTrace]
  refine ⟨102367300011953896788398707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136489733349271862384531609 102367300011953896788398707)
  ·
    refine ⟨153550950017930845182598061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102367300011953896788398707 153550950017930845182598061)
    ·
      refine ⟨57581606256724066943474273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153550950017930845182598061 57581606256724066943474273)
      ·
        refine ⟨43186204692543050207605705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57581606256724066943474273 43186204692543050207605705)
        ·
          refine ⟨32389653519407287655704279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43186204692543050207605705 32389653519407287655704279)
          ·
            refine ⟨48584480279110931483556419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32389653519407287655704279 48584480279110931483556419)
            ·
              refine ⟨72876720418666397225334629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48584480279110931483556419 72876720418666397225334629)
              ·
                refine ⟨13664385078499949479750243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72876720418666397225334629 13664385078499949479750243)
                ·
                  refine ⟨20496577617749924219625365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13664385078499949479750243 20496577617749924219625365)
                  ·
                    refine ⟨960777075832027697794939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20496577617749924219625365 960777075832027697794939)
                    ·
                      rfl

theorem cell23_5613320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_5613320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613320 prefixEnd_5613320 := by exact prefixLift 5613320
  have htrace : WordTrace (prefixWord ++ tailWord_5613320) baseStart_5613320 baseEnd_5613320 := by
    simpa [prefixWord, tailWord_5613320, baseEnd_5613320] using wordTrace_append hprefix tailTrace_5613320
  have hstable : (prefixWord ++ tailWord_5613320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613320).length < 2 ^ (prefixWord ++ tailWord_5613320).sum := by decide
  have hdescent : baseEnd_5613320 < baseStart_5613320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613340 : List Nat := [2, 2, 3, 1, 1, 2, 2, 2, 1, 1, 6]
def baseStart_5613340 : Nat := 118140960795 + 5613340 * 2 ^ 59
def prefixEnd_5613340 : Nat := 4983230072969 + 3 ^ 40 * 5613340 * 2
def baseEnd_5613340 : Nat := 2882341497109173015134725

theorem tailTrace_5613340 : CollatzResearch.WordTrace tailWord_5613340 prefixEnd_5613340 2882341497109173015134725 := by
  unfold tailWord_5613340
  simp only [CollatzResearch.WordTrace]
  refine ⟨102367664741917668496262737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136490219655890224661683649 102367664741917668496262737)
  ·
    refine ⟨76775748556438251372197053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102367664741917668496262737 76775748556438251372197053)
    ·
      refine ⟨28790905708664344264573895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76775748556438251372197053 28790905708664344264573895)
      ·
        refine ⟨43186358562996516396860843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28790905708664344264573895 43186358562996516396860843)
        ·
          refine ⟨64779537844494774595291265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43186358562996516396860843 64779537844494774595291265)
          ·
            refine ⟨48584653383371080946468449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64779537844494774595291265 48584653383371080946468449)
            ·
              refine ⟨36438490037528310709851337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48584653383371080946468449 36438490037528310709851337)
              ·
                refine ⟨27328867528146233032388503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36438490037528310709851337 27328867528146233032388503)
                ·
                  refine ⟨40993301292219349548582755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27328867528146233032388503 40993301292219349548582755)
                  ·
                    refine ⟨61489951938329024322874133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40993301292219349548582755 61489951938329024322874133)
                    ·
                      refine ⟨2882341497109173015134725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61489951938329024322874133 2882341497109173015134725)
                      ·
                        rfl

theorem cell23_5613340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_5613340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613340 prefixEnd_5613340 := by exact prefixLift 5613340
  have htrace : WordTrace (prefixWord ++ tailWord_5613340) baseStart_5613340 baseEnd_5613340 := by
    simpa [prefixWord, tailWord_5613340, baseEnd_5613340] using wordTrace_append hprefix tailTrace_5613340
  have hstable : (prefixWord ++ tailWord_5613340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613340).length < 2 ^ (prefixWord ++ tailWord_5613340).sum := by decide
  have hdescent : baseEnd_5613340 < baseStart_5613340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613394 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_5613394 : Nat := 118140960795 + 5613394 * 2 ^ 59
def prefixEnd_5613394 : Nat := 4983230072969 + 3 ^ 40 * 5613394 * 2
def baseEnd_5613394 : Nat := 2882369225064515803859477

theorem tailTrace_5613394 : CollatzResearch.WordTrace tailWord_5613394 prefixEnd_5613394 2882369225064515803859477 := by
  unfold tailWord_5613394
  simp only [CollatzResearch.WordTrace]
  refine ⟨51184324756409926053747809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136491532683759802809994157 51184324756409926053747809)
  ·
    refine ⟨38388243567307444540310857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51184324756409926053747809 38388243567307444540310857)
    ·
      refine ⟨28791182675480583405233143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38388243567307444540310857 28791182675480583405233143)
      ·
        refine ⟨43186774013220875107849715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28791182675480583405233143 43186774013220875107849715)
        ·
          refine ⟨64780161019831312661774573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43186774013220875107849715 64780161019831312661774573)
          ·
            refine ⟨24292560382436742248165465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64780161019831312661774573 24292560382436742248165465)
            ·
              refine ⟨18219420286827556686124099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24292560382436742248165465 18219420286827556686124099)
              ·
                refine ⟨27329130430241335029186149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18219420286827556686124099 27329130430241335029186149)
                ·
                  refine ⟨5124211955670250317972403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27329130430241335029186149 5124211955670250317972403)
                  ·
                    refine ⟨7686317933505375476958605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5124211955670250317972403 7686317933505375476958605)
                    ·
                      refine ⟨2882369225064515803859477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7686317933505375476958605 2882369225064515803859477)
                      ·
                        rfl

theorem cell23_5613394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_5613394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613394 prefixEnd_5613394 := by exact prefixLift 5613394
  have htrace : WordTrace (prefixWord ++ tailWord_5613394) baseStart_5613394 baseEnd_5613394 := by
    simpa [prefixWord, tailWord_5613394, baseEnd_5613394] using wordTrace_append hprefix tailTrace_5613394
  have hstable : (prefixWord ++ tailWord_5613394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613394).length < 2 ^ (prefixWord ++ tailWord_5613394).sum := by decide
  have hdescent : baseEnd_5613394 < baseStart_5613394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613411 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 3]
def baseStart_5613411 : Nat := 118140960795 + 5613411 * 2 ^ 59
def prefixEnd_5613411 : Nat := 4983230072969 + 3 ^ 40 * 5613411 * 2
def baseEnd_5613411 : Nat := 2882377954235642237346899

theorem tailTrace_5613411 : CollatzResearch.WordTrace tailWord_5613411 prefixEnd_5613411 2882377954235642237346899 := by
  unfold tailWord_5613411
  simp only [CollatzResearch.WordTrace]
  refine ⟨204737919066578116118360087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136491946044385410745573391 204737919066578116118360087)
  ·
    refine ⟨307106878599867174177540131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204737919066578116118360087 307106878599867174177540131)
    ·
      refine ⟨460660317899800761266310197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307106878599867174177540131 460660317899800761266310197)
      ·
        refine ⟨43186904803106321368716581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 460660317899800761266310197 43186904803106321368716581)
        ·
          refine ⟨8097544650582435256634359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43186904803106321368716581 8097544650582435256634359)
          ·
            refine ⟨12146316975873652884951539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8097544650582435256634359 12146316975873652884951539)
            ·
              refine ⟨18219475463810479327427309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12146316975873652884951539 18219475463810479327427309)
              ·
                refine ⟨6832303298928929747785241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18219475463810479327427309 6832303298928929747785241)
                ·
                  refine ⟨5124227474196697310838931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6832303298928929747785241 5124227474196697310838931)
                  ·
                    refine ⟨7686341211295045966258397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5124227474196697310838931 7686341211295045966258397)
                    ·
                      refine ⟨2882377954235642237346899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7686341211295045966258397 2882377954235642237346899)
                      ·
                        rfl

theorem cell23_5613411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 1, 3].length) (baseStart_5613411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613411 prefixEnd_5613411 := by exact prefixLift 5613411
  have htrace : WordTrace (prefixWord ++ tailWord_5613411) baseStart_5613411 baseEnd_5613411 := by
    simpa [prefixWord, tailWord_5613411, baseEnd_5613411] using wordTrace_append hprefix tailTrace_5613411
  have hstable : (prefixWord ++ tailWord_5613411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613411).length < 2 ^ (prefixWord ++ tailWord_5613411).sum := by decide
  have hdescent : baseEnd_5613411 < baseStart_5613411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613417 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 5, 4, 2]
def baseStart_5613417 : Nat := 118140960795 + 5613417 * 2 ^ 59
def prefixEnd_5613417 : Nat := 4983230072969 + 3 ^ 40 * 5613417 * 2
def baseEnd_5613417 : Nat := 2882381035119569213871871

theorem tailTrace_5613417 : CollatzResearch.WordTrace tailWord_5613417 prefixEnd_5613417 2882381035119569213871871 := by
  unfold tailWord_5613417
  simp only [CollatzResearch.WordTrace]
  refine ⟨204738137904556379143078505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136492091936370919428719003 204738137904556379143078505)
  ·
    refine ⟨153553603428417284357308879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204738137904556379143078505 153553603428417284357308879)
    ·
      refine ⟨230330405142625926535963319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153553603428417284357308879 230330405142625926535963319)
      ·
        refine ⟨345495607713938889803944979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230330405142625926535963319 345495607713938889803944979)
        ·
          refine ⟨518243411570908334705917469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345495607713938889803944979 518243411570908334705917469)
          ·
            refine ⟨194341279339090625514719051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 518243411570908334705917469 194341279339090625514719051)
            ·
              refine ⟨291511919008635938272078577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194341279339090625514719051 291511919008635938272078577)
              ·
                refine ⟨218633939256476953704058933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291511919008635938272078577 218633939256476953704058933)
                ·
                  refine ⟨20496931805294714409755525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218633939256476953704058933 20496931805294714409755525)
                  ·
                    refine ⟨3843174713492758951829161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20496931805294714409755525 3843174713492758951829161)
                    ·
                      refine ⟨2882381035119569213871871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843174713492758951829161 2882381035119569213871871)
                      ·
                        rfl

theorem cell23_5613417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 4, 2].length) (baseStart_5613417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613417 prefixEnd_5613417 := by exact prefixLift 5613417
  have htrace : WordTrace (prefixWord ++ tailWord_5613417) baseStart_5613417 baseEnd_5613417 := by
    simpa [prefixWord, tailWord_5613417, baseEnd_5613417] using wordTrace_append hprefix tailTrace_5613417
  have hstable : (prefixWord ++ tailWord_5613417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613417).length < 2 ^ (prefixWord ++ tailWord_5613417).sum := by decide
  have hdescent : baseEnd_5613417 < baseStart_5613417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613421 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 1, 3, 2]
def baseStart_5613421 : Nat := 118140960795 + 5613421 * 2 ^ 59
def prefixEnd_5613421 : Nat := 4983230072969 + 3 ^ 40 * 5613421 * 2
def baseEnd_5613421 : Nat := 2882383089042187198221853

theorem tailTrace_5613421 : CollatzResearch.WordTrace tailWord_5613421 prefixEnd_5613421 2882383089042187198221853 := by
  unfold tailWord_5613421
  simp only [CollatzResearch.WordTrace]
  refine ⟨204738283796541887826224117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136492189197694591884149411 204738283796541887826224117)
  ·
    refine ⟨19194214105925801983708511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204738283796541887826224117 19194214105925801983708511)
    ·
      refine ⟨28791321158888702975562767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19194214105925801983708511 28791321158888702975562767)
      ·
        refine ⟨43186981738333054463344151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28791321158888702975562767 43186981738333054463344151)
        ·
          refine ⟨64780472607499581695016227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43186981738333054463344151 64780472607499581695016227)
          ·
            refine ⟨97170708911249372542524341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64780472607499581695016227 97170708911249372542524341)
            ·
              refine ⟨9109753960429628675861657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 97170708911249372542524341 9109753960429628675861657)
              ·
                refine ⟨6832315470322221506896243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9109753960429628675861657 6832315470322221506896243)
                ·
                  refine ⟨10248473205483332260344365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6832315470322221506896243 10248473205483332260344365)
                  ·
                    refine ⟨3843177452056249597629137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10248473205483332260344365 3843177452056249597629137)
                    ·
                      refine ⟨2882383089042187198221853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843177452056249597629137 2882383089042187198221853)
                      ·
                        rfl

theorem cell23_5613421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_5613421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613421 prefixEnd_5613421 := by exact prefixLift 5613421
  have htrace : WordTrace (prefixWord ++ tailWord_5613421) baseStart_5613421 baseEnd_5613421 := by
    simpa [prefixWord, tailWord_5613421, baseEnd_5613421] using wordTrace_append hprefix tailTrace_5613421
  have hstable : (prefixWord ++ tailWord_5613421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613421).length < 2 ^ (prefixWord ++ tailWord_5613421).sum := by decide
  have hdescent : baseEnd_5613421 < baseStart_5613421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613434 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2]
def baseStart_5613434 : Nat := 118140960795 + 5613434 * 2 ^ 59
def prefixEnd_5613434 : Nat := 4983230072969 + 3 ^ 40 * 5613434 * 2
def baseEnd_5613434 : Nat := 2882389764290695647359293

theorem tailTrace_5613434 : CollatzResearch.WordTrace tailWord_5613434 prefixEnd_5613434 2882389764290695647359293 := by
  unfold tailWord_5613434
  simp only [CollatzResearch.WordTrace]
  refine ⟨51184689486373697761611839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136492505296996527364298237 51184689486373697761611839)
  ·
    refine ⟨76777034229560546642417759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51184689486373697761611839 76777034229560546642417759)
    ·
      refine ⟨115165551344340819963626639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76777034229560546642417759 115165551344340819963626639)
      ·
        refine ⟨172748327016511229945439959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115165551344340819963626639 172748327016511229945439959)
        ·
          refine ⟨259122490524766844918159939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172748327016511229945439959 259122490524766844918159939)
          ·
            refine ⟨388683735787150267377239909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259122490524766844918159939 388683735787150267377239909)
            ·
              refine ⟨72878200460090675133232483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 388683735787150267377239909 72878200460090675133232483)
              ·
                refine ⟨109317300690136012699848725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72878200460090675133232483 109317300690136012699848725)
                ·
                  refine ⟨5124248469850125595305409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 109317300690136012699848725 5124248469850125595305409)
                  ·
                    refine ⟨3843186352387594196479057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5124248469850125595305409 3843186352387594196479057)
                    ·
                      refine ⟨2882389764290695647359293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843186352387594196479057 2882389764290695647359293)
                      ·
                        rfl

theorem cell23_5613434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 2, 2].length) (baseStart_5613434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613434 prefixEnd_5613434 := by exact prefixLift 5613434
  have htrace : WordTrace (prefixWord ++ tailWord_5613434) baseStart_5613434 baseEnd_5613434 := by
    simpa [prefixWord, tailWord_5613434, baseEnd_5613434] using wordTrace_append hprefix tailTrace_5613434
  have hstable : (prefixWord ++ tailWord_5613434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613434).length < 2 ^ (prefixWord ++ tailWord_5613434).sum := by decide
  have hdescent : baseEnd_5613434 < baseStart_5613434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613468 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 2, 2, 2]
def baseStart_5613468 : Nat := 118140960795 + 5613468 * 2 ^ 59
def prefixEnd_5613468 : Nat := 4983230072969 + 3 ^ 40 * 5613468 * 2
def baseEnd_5613468 : Nat := 2882407222632948514334137

theorem tailTrace_5613468 : CollatzResearch.WordTrace tailWord_5613468 prefixEnd_5613468 2882407222632948514334137 := by
  unfold tailWord_5613468
  simp only [CollatzResearch.WordTrace]
  refine ⟨102369999013685807426592529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136493332018247743235456705 102369999013685807426592529)
  ·
    refine ⟨76777499260264355569944397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102369999013685807426592529 76777499260264355569944397)
    ·
      refine ⟨28791562222599133338729149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76777499260264355569944397 28791562222599133338729149)
      ·
        refine ⟨10796835833474675002023431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28791562222599133338729149 10796835833474675002023431)
        ·
          refine ⟨16195253750212012503035147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10796835833474675002023431 16195253750212012503035147)
          ·
            refine ⟨24292880625318018754552721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16195253750212012503035147 24292880625318018754552721)
            ·
              refine ⟨18219660468988514065914541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24292880625318018754552721 18219660468988514065914541)
              ·
                refine ⟨6832372675870692774717953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18219660468988514065914541 6832372675870692774717953)
                ·
                  refine ⟨5124279506903019581038465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6832372675870692774717953 5124279506903019581038465)
                  ·
                    refine ⟨3843209630177264685778849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5124279506903019581038465 3843209630177264685778849)
                    ·
                      refine ⟨2882407222632948514334137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843209630177264685778849 2882407222632948514334137)
                      ·
                        rfl

theorem cell23_5613468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_5613468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613468 prefixEnd_5613468 := by exact prefixLift 5613468
  have htrace : WordTrace (prefixWord ++ tailWord_5613468) baseStart_5613468 baseEnd_5613468 := by
    simpa [prefixWord, tailWord_5613468, baseEnd_5613468] using wordTrace_append hprefix tailTrace_5613468
  have hstable : (prefixWord ++ tailWord_5613468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613468).length < 2 ^ (prefixWord ++ tailWord_5613468).sum := by decide
  have hdescent : baseEnd_5613468 < baseStart_5613468 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613474 : List Nat := [3, 3, 1, 2, 3, 1, 1, 2, 7]
def baseStart_5613474 : Nat := 118140960795 + 5613474 * 2 ^ 59
def prefixEnd_5613474 : Nat := 4983230072969 + 3 ^ 40 * 5613474 * 2
def baseEnd_5613474 : Nat := 320267811501875054539901

theorem tailTrace_5613474 : CollatzResearch.WordTrace tailWord_5613474 prefixEnd_5613474 320267811501875054539901 := by
  unfold tailWord_5613474
  simp only [CollatzResearch.WordTrace]
  refine ⟨51185054216337469469475869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136493477910233251918602317 51185054216337469469475869)
  ·
    refine ⟨19194395331126551051053451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51185054216337469469475869 19194395331126551051053451)
    ·
      refine ⟨28791592996689826576580177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19194395331126551051053451 28791592996689826576580177)
      ·
        refine ⟨21593694747517369932435133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28791592996689826576580177 21593694747517369932435133)
        ·
          refine ⟨8097635530319013724663175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21593694747517369932435133 8097635530319013724663175)
          ·
            refine ⟨12146453295478520586994763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8097635530319013724663175 12146453295478520586994763)
            ·
              refine ⟨18219679943217780880492145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12146453295478520586994763 18219679943217780880492145)
              ·
                refine ⟨13664759957413335660369109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18219679943217780880492145 13664759957413335660369109)
                ·
                  refine ⟨320267811501875054539901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13664759957413335660369109 320267811501875054539901)
                  ·
                    rfl

theorem cell23_5613474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_5613474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613474 prefixEnd_5613474 := by exact prefixLift 5613474
  have htrace : WordTrace (prefixWord ++ tailWord_5613474) baseStart_5613474 baseEnd_5613474 := by
    simpa [prefixWord, tailWord_5613474, baseEnd_5613474] using wordTrace_append hprefix tailTrace_5613474
  have hstable : (prefixWord ++ tailWord_5613474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613474).length < 2 ^ (prefixWord ++ tailWord_5613474).sum := by decide
  have hdescent : baseEnd_5613474 < baseStart_5613474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613527 : List Nat := [1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_5613527 : Nat := 118140960795 + 5613527 * 2 ^ 59
def prefixEnd_5613527 : Nat := 4983230072969 + 3 ^ 40 * 5613527 * 2
def baseEnd_5613527 : Nat := 2882437517991563783496365

theorem tailTrace_5613527 : CollatzResearch.WordTrace tailWord_5613527 prefixEnd_5613527 2882437517991563783496365 := by
  unfold tailWord_5613527
  simp only [CollatzResearch.WordTrace]
  refine ⟨204742149934157867929582835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136494766622771911953055223 204742149934157867929582835)
  ·
    refine ⟨307113224901236801894374253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204742149934157867929582835 307113224901236801894374253)
    ·
      refine ⟨115167459337963800710390345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307113224901236801894374253 115167459337963800710390345)
      ·
        refine ⟨86375594503472850532792759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115167459337963800710390345 86375594503472850532792759)
        ·
          refine ⟨129563391755209275799189139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86375594503472850532792759 129563391755209275799189139)
          ·
            refine ⟨194345087632813913698783709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129563391755209275799189139 194345087632813913698783709)
            ·
              refine ⟨72879407862305217637043891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194345087632813913698783709 72879407862305217637043891)
              ·
                refine ⟨109319111793457826455565837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72879407862305217637043891 109319111793457826455565837)
                ·
                  refine ⟨40994666922546684920837189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109319111793457826455565837 40994666922546684920837189)
                  ·
                    refine ⟨7686500047977503422656973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40994666922546684920837189 7686500047977503422656973)
                    ·
                      refine ⟨2882437517991563783496365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7686500047977503422656973 2882437517991563783496365)
                      ·
                        rfl

theorem cell23_5613527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_5613527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613527 prefixEnd_5613527 := by exact prefixLift 5613527
  have htrace : WordTrace (prefixWord ++ tailWord_5613527) baseStart_5613527 baseEnd_5613527 := by
    simpa [prefixWord, tailWord_5613527, baseEnd_5613527] using wordTrace_append hprefix tailTrace_5613527
  have hstable : (prefixWord ++ tailWord_5613527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613527).length < 2 ^ (prefixWord ++ tailWord_5613527).sum := by decide
  have hdescent : baseEnd_5613527 < baseStart_5613527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613544 : List Nat := [2, 1, 4, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_5613544 : Nat := 118140960795 + 5613544 * 2 ^ 59
def prefixEnd_5613544 : Nat := 4983230072969 + 3 ^ 40 * 5613544 * 2
def baseEnd_5613544 : Nat := 2882446247162690216983787

theorem tailTrace_5613544 : CollatzResearch.WordTrace tailWord_5613544 prefixEnd_5613544 2882446247162690216983787 := by
  unfold tailWord_5613544
  simp only [CollatzResearch.WordTrace]
  refine ⟨102371384987548139916475843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136495179983397519888634457 102371384987548139916475843)
  ·
    refine ⟨153557077481322209874713765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102371384987548139916475843 153557077481322209874713765)
    ·
      refine ⟨28791952027747914351508831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 153557077481322209874713765 28791952027747914351508831)
      ·
        refine ⟨43187928041621871527263247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28791952027747914351508831 43187928041621871527263247)
        ·
          refine ⟨64781892062432807290894871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43187928041621871527263247 64781892062432807290894871)
          ·
            refine ⟨97172838093649210936342307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64781892062432807290894871 97172838093649210936342307)
            ·
              refine ⟨145759257140473816404513461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97172838093649210936342307 145759257140473816404513461)
              ·
                refine ⟨13664930356919420287923137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145759257140473816404513461 13664930356919420287923137)
                ·
                  refine ⟨10248697767689565215942353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13664930356919420287923137 10248697767689565215942353)
                  ·
                    refine ⟨7686523325767173911956765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10248697767689565215942353 7686523325767173911956765)
                    ·
                      refine ⟨2882446247162690216983787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7686523325767173911956765 2882446247162690216983787)
                      ·
                        rfl

theorem cell23_5613544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_5613544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613544 prefixEnd_5613544 := by exact prefixLift 5613544
  have htrace : WordTrace (prefixWord ++ tailWord_5613544) baseStart_5613544 baseEnd_5613544 := by
    simpa [prefixWord, tailWord_5613544, baseEnd_5613544] using wordTrace_append hprefix tailTrace_5613544
  have hstable : (prefixWord ++ tailWord_5613544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613544).length < 2 ^ (prefixWord ++ tailWord_5613544).sum := by decide
  have hdescent : baseEnd_5613544 < baseStart_5613544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613594 : List Nat := [3, 1, 1, 3, 1, 4, 1, 1, 3, 5]
def baseStart_5613594 : Nat := 118140960795 + 5613594 * 2 ^ 59
def prefixEnd_5613594 : Nat := 4983230072969 + 3 ^ 40 * 5613594 * 2
def baseEnd_5613594 : Nat := 960823973731805007119519

theorem tailTrace_5613594 : CollatzResearch.WordTrace tailWord_5613594 prefixEnd_5613594 960823973731805007119519 := by
  unfold tailWord_5613594
  simp only [CollatzResearch.WordTrace]
  refine ⟨51186148406228784593067959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136496395749943425581514557 51186148406228784593067959)
  ·
    refine ⟨76779222609343176889601939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51186148406228784593067959 76779222609343176889601939)
    ·
      refine ⟨115168833914014765334402909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76779222609343176889601939 115168833914014765334402909)
      ·
        refine ⟨43188312717755537000401091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115168833914014765334402909 43188312717755537000401091)
        ·
          refine ⟨64782469076633305500601637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43188312717755537000401091 64782469076633305500601637)
          ·
            refine ⟨12146712951868744781362807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64782469076633305500601637 12146712951868744781362807)
            ·
              refine ⟨18220069427803117172044211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12146712951868744781362807 18220069427803117172044211)
              ·
                refine ⟨27330104141704675758066317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18220069427803117172044211 27330104141704675758066317)
                ·
                  refine ⟨10248789053139253409274869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27330104141704675758066317 10248789053139253409274869)
                  ·
                    refine ⟨960823973731805007119519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10248789053139253409274869 960823973731805007119519)
                    ·
                      rfl

theorem cell23_5613594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 1, 3, 5].length) (baseStart_5613594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613594 prefixEnd_5613594 := by exact prefixLift 5613594
  have htrace : WordTrace (prefixWord ++ tailWord_5613594) baseStart_5613594 baseEnd_5613594 := by
    simpa [prefixWord, tailWord_5613594, baseEnd_5613594] using wordTrace_append hprefix tailTrace_5613594
  have hstable : (prefixWord ++ tailWord_5613594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613594).length < 2 ^ (prefixWord ++ tailWord_5613594).sum := by decide
  have hdescent : baseEnd_5613594 < baseStart_5613594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613625 : List Nat := [1, 2, 1, 5, 3, 1, 1, 4, 1, 1, 3]
def baseStart_5613625 : Nat := 118140960795 + 5613625 * 2 ^ 59
def prefixEnd_5613625 : Nat := 4983230072969 + 3 ^ 40 * 5613625 * 2
def baseEnd_5613625 : Nat := 2882487839095704400070915

theorem tailTrace_5613625 : CollatzResearch.WordTrace tailWord_5613625 prefixEnd_5613625 2882487839095704400070915 := by
  unfold tailWord_5613625
  simp only [CollatzResearch.WordTrace]
  refine ⟨204745724287802830666650329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136497149525201887111100219 204745724287802830666650329)
  ·
    refine ⟨153559293215852122999987747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204745724287802830666650329 153559293215852122999987747)
    ·
      refine ⟨230338939823778184499981621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153559293215852122999987747 230338939823778184499981621)
      ·
        refine ⟨21594275608479204796873277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 230338939823778184499981621 21594275608479204796873277)
        ·
          refine ⟨8097853353179701798827479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21594275608479204796873277 8097853353179701798827479)
          ·
            refine ⟨12146780029769552698241219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8097853353179701798827479 12146780029769552698241219)
            ·
              refine ⟨18220170044654329047361829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12146780029769552698241219 18220170044654329047361829)
              ·
                refine ⟨3416281883372686696380343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18220170044654329047361829 3416281883372686696380343)
                ·
                  refine ⟨5124422825059030044570515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3416281883372686696380343 5124422825059030044570515)
                  ·
                    refine ⟨7686634237588545066855773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5124422825059030044570515 7686634237588545066855773)
                    ·
                      refine ⟨2882487839095704400070915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7686634237588545066855773 2882487839095704400070915)
                      ·
                        rfl

theorem cell23_5613625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_5613625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613625 prefixEnd_5613625 := by exact prefixLift 5613625
  have htrace : WordTrace (prefixWord ++ tailWord_5613625) baseStart_5613625 baseEnd_5613625 := by
    simpa [prefixWord, tailWord_5613625, baseEnd_5613625] using wordTrace_append hprefix tailTrace_5613625
  have hstable : (prefixWord ++ tailWord_5613625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613625).length < 2 ^ (prefixWord ++ tailWord_5613625).sum := by decide
  have hdescent : baseEnd_5613625 < baseStart_5613625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613644 : List Nat := [2, 2, 1, 3, 1, 1, 3, 3, 1, 2, 4]
def baseStart_5613644 : Nat := 118140960795 + 5613644 * 2 ^ 59
def prefixEnd_5613644 : Nat := 4983230072969 + 3 ^ 40 * 5613644 * 2
def baseEnd_5613644 : Nat := 2882497595228139825733327

theorem tailTrace_5613644 : CollatzResearch.WordTrace tailWord_5613644 prefixEnd_5613644 2882497595228139825733327 := by
  unfold tailWord_5613644
  simp only [CollatzResearch.WordTrace]
  refine ⟨102373208637366998455795993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136497611516489331274394657 102373208637366998455795993)
  ·
    refine ⟨76779906478025248841846995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102373208637366998455795993 76779906478025248841846995)
    ·
      refine ⟨115169859717037873262770493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76779906478025248841846995 115169859717037873262770493)
      ·
        refine ⟨43188697393889202473538935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115169859717037873262770493 43188697393889202473538935)
        ·
          refine ⟨64783046090833803710308403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43188697393889202473538935 64783046090833803710308403)
          ·
            refine ⟨97174569136250705565462605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64783046090833803710308403 97174569136250705565462605)
            ·
              refine ⟨36440463426094014587048477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97174569136250705565462605 36440463426094014587048477)
              ·
                refine ⟨13665173784785255470143179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36440463426094014587048477 13665173784785255470143179)
                ·
                  refine ⟨20497760677177883205214769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13665173784785255470143179 20497760677177883205214769)
                  ·
                    refine ⟨15373320507883412403911077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20497760677177883205214769 15373320507883412403911077)
                    ·
                      refine ⟨2882497595228139825733327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15373320507883412403911077 2882497595228139825733327)
                      ·
                        rfl

theorem cell23_5613644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_5613644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613644 prefixEnd_5613644 := by exact prefixLift 5613644
  have htrace : WordTrace (prefixWord ++ tailWord_5613644) baseStart_5613644 baseEnd_5613644 := by
    simpa [prefixWord, tailWord_5613644, baseEnd_5613644] using wordTrace_append hprefix tailTrace_5613644
  have hstable : (prefixWord ++ tailWord_5613644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613644).length < 2 ^ (prefixWord ++ tailWord_5613644).sum := by decide
  have hdescent : baseEnd_5613644 < baseStart_5613644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613668 : List Nat := [2, 3, 1, 1, 2, 1, 6, 1, 1, 2, 3]
def baseStart_5613668 : Nat := 118140960795 + 5613668 * 2 ^ 59
def prefixEnd_5613668 : Nat := 4983230072969 + 3 ^ 40 * 5613668 * 2
def baseEnd_5613668 : Nat := 2882509918763847731833217

theorem tailTrace_5613668 : CollatzResearch.WordTrace tailWord_5613668 prefixEnd_5613668 2882509918763847731833217 := by
  unfold tailWord_5613668
  simp only [CollatzResearch.WordTrace]
  refine ⟨102373646313323524505232829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136498195084431366006977105 102373646313323524505232829)
  ·
    refine ⟨38390117367496321689462311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102373646313323524505232829 38390117367496321689462311)
    ·
      refine ⟨57585176051244482534193467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38390117367496321689462311 57585176051244482534193467)
      ·
        refine ⟨86377764076866723801290201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57585176051244482534193467 86377764076866723801290201)
        ·
          refine ⟨64783323057650042850967651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86377764076866723801290201 64783323057650042850967651)
          ·
            refine ⟨97174984586475064276451477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64783323057650042850967651 97174984586475064276451477)
            ·
              refine ⟨4555077402491018637958663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97174984586475064276451477 4555077402491018637958663)
              ·
                refine ⟨6832616103736527956937995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555077402491018637958663 6832616103736527956937995)
                ·
                  refine ⟨10248924155604791935406993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6832616103736527956937995 10248924155604791935406993)
                  ·
                    refine ⟨7686693116703593951555245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10248924155604791935406993 7686693116703593951555245)
                    ·
                      refine ⟨2882509918763847731833217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7686693116703593951555245 2882509918763847731833217)
                      ·
                        rfl

theorem cell23_5613668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_5613668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613668 prefixEnd_5613668 := by exact prefixLift 5613668
  have htrace : WordTrace (prefixWord ++ tailWord_5613668) baseStart_5613668 baseEnd_5613668 := by
    simpa [prefixWord, tailWord_5613668, baseEnd_5613668] using wordTrace_append hprefix tailTrace_5613668
  have hstable : (prefixWord ++ tailWord_5613668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613668).length < 2 ^ (prefixWord ++ tailWord_5613668).sum := by decide
  have hdescent : baseEnd_5613668 < baseStart_5613668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613681 : List Nat := [1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 3]
def baseStart_5613681 : Nat := 118140960795 + 5613681 * 2 ^ 59
def prefixEnd_5613681 : Nat := 4983230072969 + 3 ^ 40 * 5613681 * 2
def baseEnd_5613681 : Nat := 2882516594012356180970657

theorem tailTrace_5613681 : CollatzResearch.WordTrace tailWord_5613681 prefixEnd_5613681 2882516594012356180970657 := by
  unfold tailWord_5613681
  simp only [CollatzResearch.WordTrace]
  refine ⟨204747766775599952230688897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136498511183733301487125931 204747766775599952230688897)
  ·
    refine ⟨153560825081699964173016673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204747766775599952230688897 153560825081699964173016673)
    ·
      refine ⟨115170618811274973129762505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153560825081699964173016673 115170618811274973129762505)
      ·
        refine ⟨86377964108456229847321879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115170618811274973129762505 86377964108456229847321879)
        ·
          refine ⟨129566946162684344770982819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86377964108456229847321879 129566946162684344770982819)
          ·
            refine ⟨194350419244026517156474229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129566946162684344770982819 194350419244026517156474229)
            ·
              refine ⟨18220351804127485983419459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 194350419244026517156474229 18220351804127485983419459)
              ·
                refine ⟨27330527706191228975129189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18220351804127485983419459 27330527706191228975129189)
                ·
                  refine ⟨5124473944910855432836723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27330527706191228975129189 5124473944910855432836723)
                  ·
                    refine ⟨7686710917366283149255085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5124473944910855432836723 7686710917366283149255085)
                    ·
                      refine ⟨2882516594012356180970657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7686710917366283149255085 2882516594012356180970657)
                      ·
                        rfl

theorem cell23_5613681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 1, 3].length) (baseStart_5613681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613681 prefixEnd_5613681 := by exact prefixLift 5613681
  have htrace : WordTrace (prefixWord ++ tailWord_5613681) baseStart_5613681 baseEnd_5613681 := by
    simpa [prefixWord, tailWord_5613681, baseEnd_5613681] using wordTrace_append hprefix tailTrace_5613681
  have hstable : (prefixWord ++ tailWord_5613681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613681).length < 2 ^ (prefixWord ++ tailWord_5613681).sum := by decide
  have hdescent : baseEnd_5613681 < baseStart_5613681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613716 : List Nat := [2, 4, 2, 3, 1, 2, 1, 3, 1, 2, 2]
def baseStart_5613716 : Nat := 118140960795 + 5613716 * 2 ^ 59
def prefixEnd_5613716 : Nat := 4983230072969 + 3 ^ 40 * 5613716 * 2
def baseEnd_5613716 : Nat := 2882534565835263544032997

theorem tailTrace_5613716 : CollatzResearch.WordTrace tailWord_5613716 prefixEnd_5613716 2882534565835263544032997 := by
  unfold tailWord_5613716
  simp only [CollatzResearch.WordTrace]
  refine ⟨102374521665236576604106501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136499362220315435472142001 102374521665236576604106501)
  ·
    refine ⟨19195222812231858113269969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102374521665236576604106501 19195222812231858113269969)
    ·
      refine ⟨14396417109173893584952477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19195222812231858113269969 14396417109173893584952477)
      ·
        refine ⟨5398656415940210094357179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14396417109173893584952477 5398656415940210094357179)
        ·
          refine ⟨8097984623910315141535769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398656415940210094357179 8097984623910315141535769)
          ·
            refine ⟨6073488467932736356151827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8097984623910315141535769 6073488467932736356151827)
            ·
              refine ⟨9110232701899104534227741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073488467932736356151827 9110232701899104534227741)
              ·
                refine ⟨3416337263212164200335403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9110232701899104534227741 3416337263212164200335403)
                ·
                  refine ⟨5124505894818246300503105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3416337263212164200335403 5124505894818246300503105)
                  ·
                    refine ⟨3843379421113684725377329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5124505894818246300503105 3843379421113684725377329)
                    ·
                      refine ⟨2882534565835263544032997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843379421113684725377329 2882534565835263544032997)
                      ·
                        rfl

theorem cell23_5613716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_5613716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613716 prefixEnd_5613716 := by exact prefixLift 5613716
  have htrace : WordTrace (prefixWord ++ tailWord_5613716) baseStart_5613716 baseEnd_5613716 := by
    simpa [prefixWord, tailWord_5613716, baseEnd_5613716] using wordTrace_append hprefix tailTrace_5613716
  have hstable : (prefixWord ++ tailWord_5613716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613716).length < 2 ^ (prefixWord ++ tailWord_5613716).sum := by decide
  have hdescent : baseEnd_5613716 < baseStart_5613716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613721 : List Nat := [1, 2, 1, 2, 1, 2, 1, 6, 1, 4, 2]
def baseStart_5613721 : Nat := 118140960795 + 5613721 * 2 ^ 59
def prefixEnd_5613721 : Nat := 4983230072969 + 3 ^ 40 * 5613721 * 2
def baseEnd_5613721 : Nat := 2882537133238536024470473

theorem tailTrace_5613721 : CollatzResearch.WordTrace tailWord_5613721 prefixEnd_5613721 2882537133238536024470473 := by
  unfold tailWord_5613721
  simp only [CollatzResearch.WordTrace]
  refine ⟨204749225695455039062145017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136499483796970026041430011 204749225695455039062145017)
  ·
    refine ⟨153561919271591279296608763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204749225695455039062145017 153561919271591279296608763)
    ·
      refine ⟨230342878907386918944913145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153561919271591279296608763 230342878907386918944913145)
      ·
        refine ⟨172757159180540189208684859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230342878907386918944913145 172757159180540189208684859)
        ·
          refine ⟨259135738770810283813027289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172757159180540189208684859 259135738770810283813027289)
          ·
            refine ⟨194351804078107712859770467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259135738770810283813027289 194351804078107712859770467)
            ·
              refine ⟨291527706117161569289655701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194351804078107712859770467 291527706117161569289655701)
              ·
                refine ⟨13665361224241948560452611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291527706117161569289655701 13665361224241948560452611)
                ·
                  refine ⟨20498041836362922840678917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13665361224241948560452611 20498041836362922840678917)
                  ·
                    refine ⟨3843382844318048032627297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20498041836362922840678917 3843382844318048032627297)
                    ·
                      refine ⟨2882537133238536024470473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843382844318048032627297 2882537133238536024470473)
                      ·
                        rfl

theorem cell23_5613721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_5613721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613721 prefixEnd_5613721 := by exact prefixLift 5613721
  have htrace : WordTrace (prefixWord ++ tailWord_5613721) baseStart_5613721 baseEnd_5613721 := by
    simpa [prefixWord, tailWord_5613721, baseEnd_5613721] using wordTrace_append hprefix tailTrace_5613721
  have hstable : (prefixWord ++ tailWord_5613721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613721).length < 2 ^ (prefixWord ++ tailWord_5613721).sum := by decide
  have hdescent : baseEnd_5613721 < baseStart_5613721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613749 : List Nat := [1, 3, 3, 4, 1, 2, 2, 1, 2, 1, 3]
def baseStart_5613749 : Nat := 118140960795 + 5613749 * 2 ^ 59
def prefixEnd_5613749 : Nat := 4983230072969 + 3 ^ 40 * 5613749 * 2
def baseEnd_5613749 : Nat := 2882551510696861914920345

theorem tailTrace_5613749 : CollatzResearch.WordTrace tailWord_5613749 prefixEnd_5613749 2882551510696861914920345 := by
  unfold tailWord_5613749
  simp only [CollatzResearch.WordTrace]
  refine ⟨204750246939353599844164301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136500164626235733229442867 204750246939353599844164301)
  ·
    refine ⟨76781342602257599941561613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204750246939353599844164301 76781342602257599941561613)
    ·
      refine ⟨28793003475846599978085605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76781342602257599941561613 28793003475846599978085605)
      ·
        refine ⟨5398688151721237495891051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28793003475846599978085605 5398688151721237495891051)
        ·
          refine ⟨8098032227581856243836577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398688151721237495891051 8098032227581856243836577)
          ·
            refine ⟨6073524170686392182877433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8098032227581856243836577 6073524170686392182877433)
            ·
              refine ⟨4555143128014794137158075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6073524170686392182877433 4555143128014794137158075)
              ·
                refine ⟨6832714692022191205737113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555143128014794137158075 6832714692022191205737113)
                ·
                  refine ⟨5124536019016643404302835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6832714692022191205737113 5124536019016643404302835)
                  ·
                    refine ⟨7686804028524965106454253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5124536019016643404302835 7686804028524965106454253)
                    ·
                      refine ⟨2882551510696861914920345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7686804028524965106454253 2882551510696861914920345)
                      ·
                        rfl

theorem cell23_5613749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_5613749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613749 prefixEnd_5613749 := by exact prefixLift 5613749
  have htrace : WordTrace (prefixWord ++ tailWord_5613749) baseStart_5613749 baseEnd_5613749 := by
    simpa [prefixWord, tailWord_5613749, baseEnd_5613749] using wordTrace_append hprefix tailTrace_5613749
  have hstable : (prefixWord ++ tailWord_5613749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613749).length < 2 ^ (prefixWord ++ tailWord_5613749).sum := by decide
  have hdescent : baseEnd_5613749 < baseStart_5613749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613795 : List Nat := [1, 1, 1, 8, 1, 1, 1, 4, 5]
def baseStart_5613795 : Nat := 118140960795 + 5613795 * 2 ^ 59
def prefixEnd_5613795 : Nat := 4983230072969 + 3 ^ 40 * 5613795 * 2
def baseEnd_5613795 : Nat := 320286125645218748327237

theorem tailTrace_5613795 : CollatzResearch.WordTrace tailWord_5613795 prefixEnd_5613795 320286125645218748327237 := by
  unfold tailWord_5613795
  simp only [CollatzResearch.WordTrace]
  refine ⟨204751924697186949700338839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136501283131457966466892559 204751924697186949700338839)
  ·
    refine ⟨307127887045780424550508259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204751924697186949700338839 307127887045780424550508259)
    ·
      refine ⟨460691830568670636825762389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307127887045780424550508259 460691830568670636825762389)
      ·
        refine ⟨5398732389476609025301903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 460691830568670636825762389 5398732389476609025301903)
        ·
          refine ⟨8098098584214913537952855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5398732389476609025301903 8098098584214913537952855)
          ·
            refine ⟨12147147876322370306929283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8098098584214913537952855 12147147876322370306929283)
            ·
              refine ⟨18220721814483555460393925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12147147876322370306929283 18220721814483555460393925)
              ·
                refine ⟨3416385340215666648823861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18220721814483555460393925 3416385340215666648823861)
                ·
                  refine ⟨320286125645218748327237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3416385340215666648823861 320286125645218748327237)
                  ·
                    rfl

theorem cell23_5613795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 1, 4, 5].length) (baseStart_5613795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613795 prefixEnd_5613795 := by exact prefixLift 5613795
  have htrace : WordTrace (prefixWord ++ tailWord_5613795) baseStart_5613795 baseEnd_5613795 := by
    simpa [prefixWord, tailWord_5613795, baseEnd_5613795] using wordTrace_append hprefix tailTrace_5613795
  have hstable : (prefixWord ++ tailWord_5613795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613795).length < 2 ^ (prefixWord ++ tailWord_5613795).sum := by decide
  have hdescent : baseEnd_5613795 < baseStart_5613795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613828 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 1, 3, 4]
def baseStart_5613828 : Nat := 118140960795 + 5613828 * 2 ^ 59
def prefixEnd_5613828 : Nat := 4983230072969 + 3 ^ 40 * 5613828 * 2
def baseEnd_5613828 : Nat := 2882592075668567105832481

theorem tailTrace_5613828 : CollatzResearch.WordTrace tailWord_5613828 prefixEnd_5613828 2882592075668567105832481 := by
  unfold tailWord_5613828
  simp only [CollatzResearch.WordTrace]
  refine ⟨102376564153033698168145069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136502085537378264224193425 102376564153033698168145069)
  ·
    refine ⟨38391211557387636813054401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102376564153033698168145069 38391211557387636813054401)
    ·
      refine ⟨28793408668040727609790801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38391211557387636813054401 28793408668040727609790801)
      ·
        refine ⟨21595056501030545707343101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28793408668040727609790801 21595056501030545707343101)
        ·
          refine ⟨8098146187886454640253663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21595056501030545707343101 8098146187886454640253663)
          ·
            refine ⟨12147219281829681960380495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8098146187886454640253663 12147219281829681960380495)
            ·
              refine ⟨18220828922744522940570743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12147219281829681960380495 18220828922744522940570743)
              ·
                refine ⟨27331243384116784410856115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18220828922744522940570743 27331243384116784410856115)
                ·
                  refine ⟨40996865076175176616284173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27331243384116784410856115 40996865076175176616284173)
                  ·
                    refine ⟨15373824403565691231106565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40996865076175176616284173 15373824403565691231106565)
                    ·
                      refine ⟨2882592075668567105832481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15373824403565691231106565 2882592075668567105832481)
                      ·
                        rfl

theorem cell23_5613828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_5613828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613828 prefixEnd_5613828 := by exact prefixLift 5613828
  have htrace : WordTrace (prefixWord ++ tailWord_5613828) baseStart_5613828 baseEnd_5613828 := by
    simpa [prefixWord, tailWord_5613828, baseEnd_5613828] using wordTrace_append hprefix tailTrace_5613828
  have hstable : (prefixWord ++ tailWord_5613828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613828).length < 2 ^ (prefixWord ++ tailWord_5613828).sum := by decide
  have hdescent : baseEnd_5613828 < baseStart_5613828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613851 : List Nat := [1, 1, 1, 1, 1, 1, 9, 2, 6]
def baseStart_5613851 : Nat := 118140960795 + 5613851 * 2 ^ 59
def prefixEnd_5613851 : Nat := 4983230072969 + 3 ^ 40 * 5613851 * 2
def baseEnd_5613851 : Nat := 320289320635957835093875

theorem tailTrace_5613851 : CollatzResearch.WordTrace tailWord_5613851 prefixEnd_5613851 320289320635957835093875 := by
  unfold tailWord_5613851
  simp only [CollatzResearch.WordTrace]
  refine ⟨204753967184984071264377407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136502644789989380842918271 204753967184984071264377407)
  ·
    refine ⟨307130950777476106896566111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204753967184984071264377407 307130950777476106896566111)
    ·
      refine ⟨460696426166214160344849167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307130950777476106896566111 460696426166214160344849167)
      ·
        refine ⟨691044639249321240517273751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460696426166214160344849167 691044639249321240517273751)
        ·
          refine ⟨1036566958873981860775910627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691044639249321240517273751 1036566958873981860775910627)
          ·
            refine ⟨1554850438310972791163865941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1036566958873981860775910627 1554850438310972791163865941)
            ·
              refine ⟨9110451786978356198225777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1554850438310972791163865941 9110451786978356198225777)
              ·
                refine ⟨6832838840233767148669333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9110451786978356198225777 6832838840233767148669333)
                ·
                  refine ⟨320289320635957835093875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6832838840233767148669333 320289320635957835093875)
                  ·
                    rfl

theorem cell23_5613851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 6].length) (baseStart_5613851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613851 prefixEnd_5613851 := by exact prefixLift 5613851
  have htrace : WordTrace (prefixWord ++ tailWord_5613851) baseStart_5613851 baseEnd_5613851 := by
    simpa [prefixWord, tailWord_5613851, baseEnd_5613851] using wordTrace_append hprefix tailTrace_5613851
  have hstable : (prefixWord ++ tailWord_5613851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613851).length < 2 ^ (prefixWord ++ tailWord_5613851).sum := by decide
  have hdescent : baseEnd_5613851 < baseStart_5613851 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613855 : List Nat := [1, 1, 2, 4, 3, 1, 2, 4, 1, 4]
def baseStart_5613855 : Nat := 118140960795 + 5613855 * 2 ^ 59
def prefixEnd_5613855 : Nat := 4983230072969 + 3 ^ 40 * 5613855 * 2
def baseEnd_5613855 : Nat := 960868646548746166731619

theorem tailTrace_5613855 : CollatzResearch.WordTrace tailWord_5613855 prefixEnd_5613855 960868646548746166731619 := by
  unfold tailWord_5613855
  simp only [CollatzResearch.WordTrace]
  refine ⟨204754113076969579947523019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136502742051313053298348679 204754113076969579947523019)
  ·
    refine ⟨307131169615454369921284529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204754113076969579947523019 307131169615454369921284529)
    ·
      refine ⟨230348377211590777440963397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307131169615454369921284529 230348377211590777440963397)
      ·
        refine ⟨43190320727173270770180637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230348377211590777440963397 43190320727173270770180637)
        ·
          refine ⟨16196370272689976538817739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43190320727173270770180637 16196370272689976538817739)
          ·
            refine ⟨24294555409034964808226609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16196370272689976538817739 24294555409034964808226609)
            ·
              refine ⟨18220916556776223606169957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24294555409034964808226609 18220916556776223606169957)
              ·
                refine ⟨3416421854395541926156867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18220916556776223606169957 3416421854395541926156867)
                ·
                  refine ⟨5124632781593312889235301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3416421854395541926156867 5124632781593312889235301)
                  ·
                    refine ⟨960868646548746166731619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5124632781593312889235301 960868646548746166731619)
                    ·
                      rfl

theorem cell23_5613855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 1, 4].length) (baseStart_5613855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613855 prefixEnd_5613855 := by exact prefixLift 5613855
  have htrace : WordTrace (prefixWord ++ tailWord_5613855) baseStart_5613855 baseEnd_5613855 := by
    simpa [prefixWord, tailWord_5613855, baseEnd_5613855] using wordTrace_append hprefix tailTrace_5613855
  have hstable : (prefixWord ++ tailWord_5613855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613855).length < 2 ^ (prefixWord ++ tailWord_5613855).sum := by decide
  have hdescent : baseEnd_5613855 < baseStart_5613855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613889 : List Nat := [1, 2, 5, 2, 2, 2, 1, 3, 1, 4]
def baseStart_5613889 : Nat := 118140960795 + 5613889 * 2 ^ 59
def prefixEnd_5613889 : Nat := 4983230072969 + 3 ^ 40 * 5613889 * 2
def baseEnd_5613889 : Nat := 960874465996163789056567

theorem tailTrace_5613889 : CollatzResearch.WordTrace tailWord_5613889 prefixEnd_5613889 960874465996163789056567 := by
  unfold tailWord_5613889
  simp only [CollatzResearch.WordTrace]
  refine ⟨204755353158846403754260721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136503568772564269169507147 204755353158846403754260721)
  ·
    refine ⟨153566514869134802815695541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204755353158846403754260721 153566514869134802815695541)
    ·
      refine ⟨14396860768981387763971457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153566514869134802815695541 14396860768981387763971457)
      ·
        refine ⟨10797645576736040822978593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14396860768981387763971457 10797645576736040822978593)
        ·
          refine ⟨8098234182552030617233945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10797645576736040822978593 8098234182552030617233945)
          ·
            refine ⟨6073675636914022962925459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8098234182552030617233945 6073675636914022962925459)
            ·
              refine ⟨9110513455371034444388189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073675636914022962925459 9110513455371034444388189)
              ·
                refine ⟨3416442545764137916645571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9110513455371034444388189 3416442545764137916645571)
                ·
                  refine ⟨5124663818646206874968357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3416442545764137916645571 5124663818646206874968357)
                  ·
                    refine ⟨960874465996163789056567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5124663818646206874968357 960874465996163789056567)
                    ·
                      rfl

theorem cell23_5613889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_5613889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613889 prefixEnd_5613889 := by exact prefixLift 5613889
  have htrace : WordTrace (prefixWord ++ tailWord_5613889) baseStart_5613889 baseEnd_5613889 := by
    simpa [prefixWord, tailWord_5613889, baseEnd_5613889] using wordTrace_append hprefix tailTrace_5613889
  have hstable : (prefixWord ++ tailWord_5613889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613889).length < 2 ^ (prefixWord ++ tailWord_5613889).sum := by decide
  have hdescent : baseEnd_5613889 < baseStart_5613889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613905 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 2, 3, 2]
def baseStart_5613905 : Nat := 118140960795 + 5613905 * 2 ^ 59
def prefixEnd_5613905 : Nat := 4983230072969 + 3 ^ 40 * 5613905 * 2
def baseEnd_5613905 : Nat := 2882631613678963304569627

theorem tailTrace_5613905 : CollatzResearch.WordTrace tailWord_5613905 prefixEnd_5613905 2882631613678963304569627 := by
  unfold tailWord_5613905
  simp only [CollatzResearch.WordTrace]
  refine ⟨204755936726788438486843169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136503957817858958991228779 204755936726788438486843169)
  ·
    refine ⟨153566952545091328865132377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204755936726788438486843169 153566952545091328865132377)
    ·
      refine ⟨115175214408818496648849283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153566952545091328865132377 115175214408818496648849283)
      ·
        refine ⟨172762821613227744973273925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115175214408818496648849283 172762821613227744973273925)
        ·
          refine ⟨32393029052480202182488861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172762821613227744973273925 32393029052480202182488861)
          ·
            refine ⟨12147385894680075818433323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32393029052480202182488861 12147385894680075818433323)
            ·
              refine ⟨18221078842020113727649985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12147385894680075818433323 18221078842020113727649985)
              ·
                refine ⟨13665809131515085295737489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18221078842020113727649985 13665809131515085295737489)
                ·
                  refine ⟨10249356848636313971803117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13665809131515085295737489 10249356848636313971803117)
                  ·
                    refine ⟨3843508818238617739426169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10249356848636313971803117 3843508818238617739426169)
                    ·
                      refine ⟨2882631613678963304569627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843508818238617739426169 2882631613678963304569627)
                      ·
                        rfl

theorem cell23_5613905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 2, 3, 2].length) (baseStart_5613905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613905 prefixEnd_5613905 := by exact prefixLift 5613905
  have htrace : WordTrace (prefixWord ++ tailWord_5613905) baseStart_5613905 baseEnd_5613905 := by
    simpa [prefixWord, tailWord_5613905, baseEnd_5613905] using wordTrace_append hprefix tailTrace_5613905
  have hstable : (prefixWord ++ tailWord_5613905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613905).length < 2 ^ (prefixWord ++ tailWord_5613905).sum := by decide
  have hdescent : baseEnd_5613905 < baseStart_5613905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613921 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_5613921 : Nat := 118140960795 + 5613921 * 2 ^ 59
def prefixEnd_5613921 : Nat := 4983230072969 + 3 ^ 40 * 5613921 * 2
def baseEnd_5613921 : Nat := 2882639829369435241969553

theorem tailTrace_5613921 : CollatzResearch.WordTrace tailWord_5613921 prefixEnd_5613921 2882639829369435241969553 := by
  unfold tailWord_5613921
  simp only [CollatzResearch.WordTrace]
  refine ⟨204756520294730473219425617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136504346863153648812950411 204756520294730473219425617)
  ·
    refine ⟨153567390221047854914569213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204756520294730473219425617 153567390221047854914569213)
    ·
      refine ⟨57587771332892945592963455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153567390221047854914569213 57587771332892945592963455)
      ·
        refine ⟨86381656999339418389445183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57587771332892945592963455 86381656999339418389445183)
        ·
          refine ⟨129572485499009127584167775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86381656999339418389445183 129572485499009127584167775)
          ·
            refine ⟨194358728248513691376251663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129572485499009127584167775 194358728248513691376251663)
            ·
              refine ⟨291538092372770537064377495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194358728248513691376251663 291538092372770537064377495)
              ·
                refine ⟨437307138559155805596566243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291538092372770537064377495 437307138559155805596566243)
                ·
                  refine ⟨655960707838733708394849365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437307138559155805596566243 655960707838733708394849365)
                  ·
                    refine ⟨7687039544985160645252141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 655960707838733708394849365 7687039544985160645252141)
                    ·
                      refine ⟨2882639829369435241969553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7687039544985160645252141 2882639829369435241969553)
                      ·
                        rfl

theorem cell23_5613921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_5613921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613921 prefixEnd_5613921 := by exact prefixLift 5613921
  have htrace : WordTrace (prefixWord ++ tailWord_5613921) baseStart_5613921 baseEnd_5613921 := by
    simpa [prefixWord, tailWord_5613921, baseEnd_5613921] using wordTrace_append hprefix tailTrace_5613921
  have hstable : (prefixWord ++ tailWord_5613921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613921).length < 2 ^ (prefixWord ++ tailWord_5613921).sum := by decide
  have hdescent : baseEnd_5613921 < baseStart_5613921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613932 : List Nat := [2, 2, 1, 1, 7, 1, 1, 2, 1, 5]
def baseStart_5613932 : Nat := 118140960795 + 5613932 * 2 ^ 59
def prefixEnd_5613932 : Nat := 4983230072969 + 3 ^ 40 * 5613932 * 2
def baseEnd_5613932 : Nat := 960881825885544899644001

theorem tailTrace_5613932 : CollatzResearch.WordTrace tailWord_5613932 prefixEnd_5613932 960881825885544899644001 := by
  unfold tailWord_5613932
  simp only [CollatzResearch.WordTrace]
  refine ⟨102378460748845311049038025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136504614331793748065384033 102378460748845311049038025)
  ·
    refine ⟨76783845561633983286778519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102378460748845311049038025 76783845561633983286778519)
    ·
      refine ⟨115175768342450974930167779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76783845561633983286778519 115175768342450974930167779)
      ·
        refine ⟨172763652513676462395251669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115175768342450974930167779 172763652513676462395251669)
        ·
          refine ⟨4049148105789292087388711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 172763652513676462395251669 4049148105789292087388711)
          ·
            refine ⟨6073722158683938131083067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049148105789292087388711 6073722158683938131083067)
            ·
              refine ⟨9110583238025907196624601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073722158683938131083067 9110583238025907196624601)
              ·
                refine ⟨6832937428519430397468451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9110583238025907196624601 6832937428519430397468451)
                ·
                  refine ⟨10249406142779145596202677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6832937428519430397468451 10249406142779145596202677)
                  ·
                    refine ⟨960881825885544899644001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10249406142779145596202677 960881825885544899644001)
                    ·
                      rfl

theorem cell23_5613932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_5613932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613932 prefixEnd_5613932 := by exact prefixLift 5613932
  have htrace : WordTrace (prefixWord ++ tailWord_5613932) baseStart_5613932 baseEnd_5613932 := by
    simpa [prefixWord, tailWord_5613932, baseEnd_5613932] using wordTrace_append hprefix tailTrace_5613932
  have hstable : (prefixWord ++ tailWord_5613932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613932).length < 2 ^ (prefixWord ++ tailWord_5613932).sum := by decide
  have hdescent : baseEnd_5613932 < baseStart_5613932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613955 : List Nat := [1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 5]
def baseStart_5613955 : Nat := 118140960795 + 5613955 * 2 ^ 59
def prefixEnd_5613955 : Nat := 4983230072969 + 3 ^ 40 * 5613955 * 2
def baseEnd_5613955 : Nat := 2882657287711688108944397

theorem tailTrace_5613955 : CollatzResearch.WordTrace tailWord_5613955 prefixEnd_5613955 2882657287711688108944397 := by
  unfold tailWord_5613955
  simp only [CollatzResearch.WordTrace]
  refine ⟨204757760376607297026163319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136505173584404864684108879 204757760376607297026163319)
  ·
    refine ⟨307136640564910945539244979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204757760376607297026163319 307136640564910945539244979)
    ·
      refine ⟨460704960847366418308867469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307136640564910945539244979 460704960847366418308867469)
      ·
        refine ⟨172764360317762406865825301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460704960847366418308867469 172764360317762406865825301)
        ·
          refine ⟨8098329389895112821835561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 172764360317762406865825301 8098329389895112821835561)
          ·
            refine ⟨6073747042421334616376671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8098329389895112821835561 6073747042421334616376671)
            ·
              refine ⟨9110620563632001924565007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6073747042421334616376671 9110620563632001924565007)
              ·
                refine ⟨13665930845448002886847511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9110620563632001924565007 13665930845448002886847511)
                ·
                  refine ⟨20498896268172004330271267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13665930845448002886847511 20498896268172004330271267)
                  ·
                    refine ⟨30748344402258006495406901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20498896268172004330271267 30748344402258006495406901)
                    ·
                      refine ⟨2882657287711688108944397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30748344402258006495406901 2882657287711688108944397)
                      ·
                        rfl

theorem cell23_5613955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 1, 1, 1, 5].length) (baseStart_5613955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613955 prefixEnd_5613955 := by exact prefixLift 5613955
  have htrace : WordTrace (prefixWord ++ tailWord_5613955) baseStart_5613955 baseEnd_5613955 := by
    simpa [prefixWord, tailWord_5613955, baseEnd_5613955] using wordTrace_append hprefix tailTrace_5613955
  have hstable : (prefixWord ++ tailWord_5613955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613955).length < 2 ^ (prefixWord ++ tailWord_5613955).sum := by decide
  have hdescent : baseEnd_5613955 < baseStart_5613955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5613982 : List Nat := [4, 3, 1, 2, 1, 2, 2, 1, 1, 2, 4]
def baseStart_5613982 : Nat := 118140960795 + 5613982 * 2 ^ 59
def prefixEnd_5613982 : Nat := 4983230072969 + 3 ^ 40 * 5613982 * 2
def baseEnd_5613982 : Nat := 2882671151689359503306773

theorem tailTrace_5613982 : CollatzResearch.WordTrace tailWord_5613982 prefixEnd_5613982 2882671151689359503306773 := by
  unfold tailWord_5613982
  simp only [CollatzResearch.WordTrace]
  refine ⟨25594843143438685079674525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136505830098339653758264133 25594843143438685079674525)
  ·
    refine ⟨9598066178789506904877947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25594843143438685079674525 9598066178789506904877947)
    ·
      refine ⟨14397099268184260357316921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9598066178789506904877947 14397099268184260357316921)
      ·
        refine ⟨10797824451138195267987691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14397099268184260357316921 10797824451138195267987691)
        ·
          refine ⟨16196736676707292901981537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10797824451138195267987691 16196736676707292901981537)
          ·
            refine ⟨12147552507530469676486153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16196736676707292901981537 12147552507530469676486153)
            ·
              refine ⟨9110664380647852257364615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12147552507530469676486153 9110664380647852257364615)
              ·
                refine ⟨13665996570971778386046923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9110664380647852257364615 13665996570971778386046923)
                ·
                  refine ⟨20498994856457667579070385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13665996570971778386046923 20498994856457667579070385)
                  ·
                    refine ⟨15374246142343250684302789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20498994856457667579070385 15374246142343250684302789)
                    ·
                      refine ⟨2882671151689359503306773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15374246142343250684302789 2882671151689359503306773)
                      ·
                        rfl

theorem cell23_5613982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_5613982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5613982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5613982 prefixEnd_5613982 := by exact prefixLift 5613982
  have htrace : WordTrace (prefixWord ++ tailWord_5613982) baseStart_5613982 baseEnd_5613982 := by
    simpa [prefixWord, tailWord_5613982, baseEnd_5613982] using wordTrace_append hprefix tailTrace_5613982
  have hstable : (prefixWord ++ tailWord_5613982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5613982).length < 2 ^ (prefixWord ++ tailWord_5613982).sum := by decide
  have hdescent : baseEnd_5613982 < baseStart_5613982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5613982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614093 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_5614093 : Nat := 118140960795 + 5614093 * 2 ^ 59
def prefixEnd_5614093 : Nat := 4983230072969 + 3 ^ 40 * 5614093 * 2
def baseEnd_5614093 : Nat := 2882728148042008569018763

theorem tailTrace_5614093 : CollatzResearch.WordTrace tailWord_5614093 prefixEnd_5614093 2882728148042008569018763 := by
  unfold tailWord_5614093
  simp only [CollatzResearch.WordTrace]
  refine ⟨204762793650107346594686933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136508529100071564396457955 204762793650107346594686933)
  ·
    refine ⟨4799127976174390935812975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 204762793650107346594686933 4799127976174390935812975)
    ·
      refine ⟨7198691964261586403719463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4799127976174390935812975 7198691964261586403719463)
      ·
        refine ⟨10798037946392379605579195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7198691964261586403719463 10798037946392379605579195)
        ·
          refine ⟨16197056919588569408368793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10798037946392379605579195 16197056919588569408368793)
          ·
            refine ⟨12147792689691427056276595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16197056919588569408368793 12147792689691427056276595)
            ·
              refine ⟨18221689034537140584414893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12147792689691427056276595 18221689034537140584414893)
              ·
                refine ⟨6833133387951427719155585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18221689034537140584414893 6833133387951427719155585)
                ·
                  refine ⟨5124850040963570789366689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6833133387951427719155585 5124850040963570789366689)
                  ·
                    refine ⟨3843637530722678092025017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5124850040963570789366689 3843637530722678092025017)
                    ·
                      refine ⟨2882728148042008569018763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843637530722678092025017 2882728148042008569018763)
                      ·
                        rfl

theorem cell23_5614093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_5614093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614093 prefixEnd_5614093 := by exact prefixLift 5614093
  have htrace : WordTrace (prefixWord ++ tailWord_5614093) baseStart_5614093 baseEnd_5614093 := by
    simpa [prefixWord, tailWord_5614093, baseEnd_5614093] using wordTrace_append hprefix tailTrace_5614093
  have hstable : (prefixWord ++ tailWord_5614093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614093).length < 2 ^ (prefixWord ++ tailWord_5614093).sum := by decide
  have hdescent : baseEnd_5614093 < baseStart_5614093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614112 : List Nat := [2, 1, 1, 6, 2, 1, 2, 1, 2, 5]
def baseStart_5614112 : Nat := 118140960795 + 5614112 * 2 ^ 59
def prefixEnd_5614112 : Nat := 4983230072969 + 3 ^ 40 * 5614112 * 2
def baseEnd_5614112 : Nat := 960912634724814664893725

theorem tailTrace_5614112 : CollatzResearch.WordTrace tailWord_5614112 prefixEnd_5614112 960912634724814664893725 := by
  unfold tailWord_5614112
  simp only [CollatzResearch.WordTrace]
  refine ⟨102381743318519256419814295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136508991091359008559752393 102381743318519256419814295)
  ·
    refine ⟨153572614977778884629721443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102381743318519256419814295 153572614977778884629721443)
    ·
      refine ⟨230358922466668326944582165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153572614977778884629721443 230358922466668326944582165)
      ·
        refine ⟨10798074490625077825527289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 230358922466668326944582165 10798074490625077825527289)
        ·
          refine ⟨8098555867968808369145467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10798074490625077825527289 8098555867968808369145467)
          ·
            refine ⟨12147833801953212553718201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8098555867968808369145467 12147833801953212553718201)
            ·
              refine ⟨9110875351464909415288651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12147833801953212553718201 9110875351464909415288651)
              ·
                refine ⟨13666313027197364122932977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9110875351464909415288651 13666313027197364122932977)
                ·
                  refine ⟨10249734770398023092199733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13666313027197364122932977 10249734770398023092199733)
                  ·
                    refine ⟨960912634724814664893725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10249734770398023092199733 960912634724814664893725)
                    ·
                      rfl

theorem cell23_5614112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 2, 5].length) (baseStart_5614112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614112 prefixEnd_5614112 := by exact prefixLift 5614112
  have htrace : WordTrace (prefixWord ++ tailWord_5614112) baseStart_5614112 baseEnd_5614112 := by
    simpa [prefixWord, tailWord_5614112, baseEnd_5614112] using wordTrace_append hprefix tailTrace_5614112
  have hstable : (prefixWord ++ tailWord_5614112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614112).length < 2 ^ (prefixWord ++ tailWord_5614112).sum := by decide
  have hdescent : baseEnd_5614112 < baseStart_5614112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614115 : List Nat := [1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 4]
def baseStart_5614115 : Nat := 118140960795 + 5614115 * 2 ^ 59
def prefixEnd_5614115 : Nat := 4983230072969 + 3 ^ 40 * 5614115 * 2
def baseEnd_5614115 : Nat := 2882739444616407482943661

theorem tailTrace_5614115 : CollatzResearch.WordTrace tailWord_5614115 prefixEnd_5614115 2882739444616407482943661 := by
  unfold tailWord_5614115
  simp only [CollatzResearch.WordTrace]
  refine ⟨204763596056027644351987799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136509064037351762901325199 204763596056027644351987799)
  ·
    refine ⟨307145394084041466527981699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204763596056027644351987799 307145394084041466527981699)
    ·
      refine ⟨460718091126062199791972549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307145394084041466527981699 460718091126062199791972549)
      ·
        refine ⟨86384642086136662460994853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 460718091126062199791972549 86384642086136662460994853)
        ·
          refine ⟨16197120391150624211436535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86384642086136662460994853 16197120391150624211436535)
          ·
            refine ⟨24295680586725936317154803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16197120391150624211436535 24295680586725936317154803)
            ·
              refine ⟨36443520880088904475732205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24295680586725936317154803 36443520880088904475732205)
              ·
                refine ⟨13666320330033339178399577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36443520880088904475732205 13666320330033339178399577)
                ·
                  refine ⟨10249740247525004383799683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13666320330033339178399577 10249740247525004383799683)
                  ·
                    refine ⟨15374610371287506575699525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10249740247525004383799683 15374610371287506575699525)
                    ·
                      refine ⟨2882739444616407482943661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15374610371287506575699525 2882739444616407482943661)
                      ·
                        rfl

theorem cell23_5614115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_5614115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614115 prefixEnd_5614115 := by exact prefixLift 5614115
  have htrace : WordTrace (prefixWord ++ tailWord_5614115) baseStart_5614115 baseEnd_5614115 := by
    simpa [prefixWord, tailWord_5614115, baseEnd_5614115] using wordTrace_append hprefix tailTrace_5614115
  have hstable : (prefixWord ++ tailWord_5614115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614115).length < 2 ^ (prefixWord ++ tailWord_5614115).sum := by decide
  have hdescent : baseEnd_5614115 < baseStart_5614115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614135 : List Nat := [1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_5614135 : Nat := 118140960795 + 5614135 * 2 ^ 59
def prefixEnd_5614135 : Nat := 4983230072969 + 3 ^ 40 * 5614135 * 2
def baseEnd_5614135 : Nat := 2882749714229497404693569

theorem tailTrace_5614135 : CollatzResearch.WordTrace tailWord_5614135 prefixEnd_5614135 2882749714229497404693569 := by
  unfold tailWord_5614135
  simp only [CollatzResearch.WordTrace]
  refine ⟨204764325515955187767715859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136509550343970125178477239 204764325515955187767715859)
  ·
    refine ⟨307146488273932781651573789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204764325515955187767715859 307146488273932781651573789)
    ·
      refine ⟨115179933102724793119340171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307146488273932781651573789 115179933102724793119340171)
      ·
        refine ⟨172769899654087189679010257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115179933102724793119340171 172769899654087189679010257)
        ·
          refine ⟨129577424740565392259257693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172769899654087189679010257 129577424740565392259257693)
          ·
            refine ⟨48591534277712022097221635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129577424740565392259257693 48591534277712022097221635)
            ·
              refine ⟨72887301416568033145832453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48591534277712022097221635 72887301416568033145832453)
              ·
                refine ⟨13666369015606506214843585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72887301416568033145832453 13666369015606506214843585)
                ·
                  refine ⟨10249776761704879661132689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13666369015606506214843585 10249776761704879661132689)
                  ·
                    refine ⟨7687332571278659745849517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10249776761704879661132689 7687332571278659745849517)
                    ·
                      refine ⟨2882749714229497404693569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7687332571278659745849517 2882749714229497404693569)
                      ·
                        rfl

theorem cell23_5614135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_5614135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614135 prefixEnd_5614135 := by exact prefixLift 5614135
  have htrace : WordTrace (prefixWord ++ tailWord_5614135) baseStart_5614135 baseEnd_5614135 := by
    simpa [prefixWord, tailWord_5614135, baseEnd_5614135] using wordTrace_append hprefix tailTrace_5614135
  have hstable : (prefixWord ++ tailWord_5614135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614135).length < 2 ^ (prefixWord ++ tailWord_5614135).sum := by decide
  have hdescent : baseEnd_5614135 < baseStart_5614135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614199 : List Nat := [1, 1, 3, 1, 1, 3, 4, 4, 1, 1, 3]
def baseStart_5614199 : Nat := 118140960795 + 5614199 * 2 ^ 59
def prefixEnd_5614199 : Nat := 4983230072969 + 3 ^ 40 * 5614199 * 2
def baseEnd_5614199 : Nat := 2882782576991385154293275

theorem tailTrace_5614199 : CollatzResearch.WordTrace tailWord_5614199 prefixEnd_5614199 2882782576991385154293275 := by
  unfold tailWord_5614199
  simp only [CollatzResearch.WordTrace]
  refine ⟨204766659787723326698045651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136511106525148884465363767 204766659787723326698045651)
  ·
    refine ⟨307149989681584990047068477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204766659787723326698045651 307149989681584990047068477)
    ·
      refine ⟨115181246130594371267650679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307149989681584990047068477 115181246130594371267650679)
      ·
        refine ⟨172771869195891556901476019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115181246130594371267650679 172771869195891556901476019)
        ·
          refine ⟨259157803793837335352214029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172771869195891556901476019 259157803793837335352214029)
          ·
            refine ⟨97184176422689000757080261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 259157803793837335352214029 97184176422689000757080261)
            ·
              refine ⟨18222033079254187641952549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97184176422689000757080261 18222033079254187641952549)
              ·
                refine ⟨3416631202360160182866103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18222033079254187641952549 3416631202360160182866103)
                ·
                  refine ⟨5124946803540240274299155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3416631202360160182866103 5124946803540240274299155)
                  ·
                    refine ⟨7687420205310360411448733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5124946803540240274299155 7687420205310360411448733)
                    ·
                      refine ⟨2882782576991385154293275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7687420205310360411448733 2882782576991385154293275)
                      ·
                        rfl

theorem cell23_5614199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 4, 1, 1, 3].length) (baseStart_5614199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614199 prefixEnd_5614199 := by exact prefixLift 5614199
  have htrace : WordTrace (prefixWord ++ tailWord_5614199) baseStart_5614199 baseEnd_5614199 := by
    simpa [prefixWord, tailWord_5614199, baseEnd_5614199] using wordTrace_append hprefix tailTrace_5614199
  have hstable : (prefixWord ++ tailWord_5614199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614199).length < 2 ^ (prefixWord ++ tailWord_5614199).sum := by decide
  have hdescent : baseEnd_5614199 < baseStart_5614199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614222 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2]
def baseStart_5614222 : Nat := 118140960795 + 5614222 * 2 ^ 59
def prefixEnd_5614222 : Nat := 4983230072969 + 3 ^ 40 * 5614222 * 2
def baseEnd_5614222 : Nat := 2882794387046438564305669

theorem tailTrace_5614222 : CollatzResearch.WordTrace tailWord_5614222 prefixEnd_5614222 2882794387046438564305669 := by
  unfold tailWord_5614222
  simp only [CollatzResearch.WordTrace]
  refine ⟨25595937333330000203266615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136511665777760001084088613 25595937333330000203266615)
  ·
    refine ⟨38393905999995000304899923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25595937333330000203266615 38393905999995000304899923)
    ·
      refine ⟨57590858999992500457349885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38393905999995000304899923 57590858999992500457349885)
      ·
        refine ⟨21596572124997187671506207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57590858999992500457349885 21596572124997187671506207)
        ·
          refine ⟨32394858187495781507259311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21596572124997187671506207 32394858187495781507259311)
          ·
            refine ⟨48592287281243672260888967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32394858187495781507259311 48592287281243672260888967)
            ·
              refine ⟨72888430921865508391333451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48592287281243672260888967 72888430921865508391333451)
              ·
                refine ⟨109332646382798262587000177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72888430921865508391333451 109332646382798262587000177)
                ·
                  refine ⟨81999484787098696940250133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109332646382798262587000177 81999484787098696940250133)
                  ·
                    refine ⟨3843725849395251419074225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81999484787098696940250133 3843725849395251419074225)
                    ·
                      refine ⟨2882794387046438564305669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843725849395251419074225 2882794387046438564305669)
                      ·
                        rfl

theorem cell23_5614222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_5614222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614222 prefixEnd_5614222 := by exact prefixLift 5614222
  have htrace : WordTrace (prefixWord ++ tailWord_5614222) baseStart_5614222 baseEnd_5614222 := by
    simpa [prefixWord, tailWord_5614222, baseEnd_5614222] using wordTrace_append hprefix tailTrace_5614222
  have hstable : (prefixWord ++ tailWord_5614222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614222).length < 2 ^ (prefixWord ++ tailWord_5614222).sum := by decide
  have hdescent : baseEnd_5614222 < baseStart_5614222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614225 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 3]
def baseStart_5614225 : Nat := 118140960795 + 5614225 * 2 ^ 59
def prefixEnd_5614225 : Nat := 4983230072969 + 3 ^ 40 * 5614225 * 2
def baseEnd_5614225 : Nat := 2882795927488402052568155

theorem tailTrace_5614225 : CollatzResearch.WordTrace tailWord_5614225 prefixEnd_5614225 2882795927488402052568155 := by
  unfold tailWord_5614225
  simp only [CollatzResearch.WordTrace]
  refine ⟨204767608085629133138492129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136511738723752755425661419 204767608085629133138492129)
  ·
    refine ⟨153575706064221849853869097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204767608085629133138492129 153575706064221849853869097)
    ·
      refine ⟨115181779548166387390401823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153575706064221849853869097 115181779548166387390401823)
      ·
        refine ⟨172772669322249581085602735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115181779548166387390401823 172772669322249581085602735)
        ·
          refine ⟨259159003983374371628404103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172772669322249581085602735 259159003983374371628404103)
          ·
            refine ⟨388738505975061557442606155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259159003983374371628404103 388738505975061557442606155)
            ·
              refine ⟨583107758962592336163909233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388738505975061557442606155 583107758962592336163909233)
              ·
                refine ⟨437330819221944252122931925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583107758962592336163909233 437330819221944252122931925)
                ·
                  refine ⟨10249941075514318409131217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 437330819221944252122931925 10249941075514318409131217)
                  ·
                    refine ⟨7687455806635738806848413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10249941075514318409131217 7687455806635738806848413)
                    ·
                      refine ⟨2882795927488402052568155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7687455806635738806848413 2882795927488402052568155)
                      ·
                        rfl

theorem cell23_5614225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 3].length) (baseStart_5614225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614225 prefixEnd_5614225 := by exact prefixLift 5614225
  have htrace : WordTrace (prefixWord ++ tailWord_5614225) baseStart_5614225 baseEnd_5614225 := by
    simpa [prefixWord, tailWord_5614225, baseEnd_5614225] using wordTrace_append hprefix tailTrace_5614225
  have hstable : (prefixWord ++ tailWord_5614225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614225).length < 2 ^ (prefixWord ++ tailWord_5614225).sum := by decide
  have hdescent : baseEnd_5614225 < baseStart_5614225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614250 : List Nat := [3, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_5614250 : Nat := 118140960795 + 5614250 * 2 ^ 59
def prefixEnd_5614250 : Nat := 4983230072969 + 3 ^ 40 * 5614250 * 2
def baseEnd_5614250 : Nat := 2882808764504764454755541

theorem tailTrace_5614250 : CollatzResearch.WordTrace tailWord_5614250 prefixEnd_5614250 2882808764504764454755541 := by
  unfold tailWord_5614250
  simp only [CollatzResearch.WordTrace]
  refine ⟨51192129977634640602038051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136512346607025708272101469 51192129977634640602038051)
  ·
    refine ⟨76788194966451960903057077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51192129977634640602038051 76788194966451960903057077)
    ·
      refine ⟨7198893278104871334661601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 76788194966451960903057077 7198893278104871334661601)
      ·
        refine ⟨5399169958578653500996201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7198893278104871334661601 5399169958578653500996201)
        ·
          refine ⟨4049377468933990125747151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5399169958578653500996201 4049377468933990125747151)
          ·
            refine ⟨6074066203400985188620727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049377468933990125747151 6074066203400985188620727)
            ·
              refine ⟨9111099305101477782931091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6074066203400985188620727 9111099305101477782931091)
              ·
                refine ⟨13666648957652216674396637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9111099305101477782931091 13666648957652216674396637)
                ·
                  refine ⟨5124993359119581252898739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13666648957652216674396637 5124993359119581252898739)
                  ·
                    refine ⟨7687490038679371879348109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5124993359119581252898739 7687490038679371879348109)
                    ·
                      refine ⟨2882808764504764454755541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7687490038679371879348109 2882808764504764454755541)
                      ·
                        rfl

theorem cell23_5614250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_5614250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614250 prefixEnd_5614250 := by exact prefixLift 5614250
  have htrace : WordTrace (prefixWord ++ tailWord_5614250) baseStart_5614250 baseEnd_5614250 := by
    simpa [prefixWord, tailWord_5614250, baseEnd_5614250] using wordTrace_append hprefix tailTrace_5614250
  have hstable : (prefixWord ++ tailWord_5614250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614250).length < 2 ^ (prefixWord ++ tailWord_5614250).sum := by decide
  have hdescent : baseEnd_5614250 < baseStart_5614250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614273 : List Nat := [1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_5614273 : Nat := 118140960795 + 5614273 * 2 ^ 59
def prefixEnd_5614273 : Nat := 4983230072969 + 3 ^ 40 * 5614273 * 2
def baseEnd_5614273 : Nat := 2882820574559817864767935

theorem tailTrace_5614273 : CollatzResearch.WordTrace tailWord_5614273 prefixEnd_5614273 2882820574559817864767935 := by
  unfold tailWord_5614273
  simp only [CollatzResearch.WordTrace]
  refine ⟨204769358789455237336239473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136512905859636824890826315 204769358789455237336239473)
  ·
    refine ⟨153577019092091428002179605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204769358789455237336239473 153577019092091428002179605)
    ·
      refine ⟨7198922769941785687602169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153577019092091428002179605 7198922769941785687602169)
      ·
        refine ⟨5399192077456339265701627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7198922769941785687602169 5399192077456339265701627)
        ·
          refine ⟨8098788116184508898552441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399192077456339265701627 8098788116184508898552441)
          ·
            refine ⟨6074091087138381673914331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8098788116184508898552441 6074091087138381673914331)
            ·
              refine ⟨9111136630707572510871497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6074091087138381673914331 9111136630707572510871497)
              ·
                refine ⟨6833352473030679383153623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9111136630707572510871497 6833352473030679383153623)
                ·
                  refine ⟨10250028709546019074730435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6833352473030679383153623 10250028709546019074730435)
                  ·
                    refine ⟨15375043064319028612095653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10250028709546019074730435 15375043064319028612095653)
                    ·
                      refine ⟨2882820574559817864767935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15375043064319028612095653 2882820574559817864767935)
                      ·
                        rfl

theorem cell23_5614273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_5614273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614273 prefixEnd_5614273 := by exact prefixLift 5614273
  have htrace : WordTrace (prefixWord ++ tailWord_5614273) baseStart_5614273 baseEnd_5614273 := by
    simpa [prefixWord, tailWord_5614273, baseEnd_5614273] using wordTrace_append hprefix tailTrace_5614273
  have hstable : (prefixWord ++ tailWord_5614273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614273).length < 2 ^ (prefixWord ++ tailWord_5614273).sum := by decide
  have hdescent : baseEnd_5614273 < baseStart_5614273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614276 : List Nat := [2, 3, 3, 1, 1, 4, 1, 2, 1, 2, 3]
def baseStart_5614276 : Nat := 118140960795 + 5614276 * 2 ^ 59
def prefixEnd_5614276 : Nat := 4983230072969 + 3 ^ 40 * 5614276 * 2
def baseEnd_5614276 : Nat := 2882822115001781353030421

theorem tailTrace_5614276 : CollatzResearch.WordTrace tailWord_5614276 prefixEnd_5614276 2882822115001781353030421 := by
  unfold tailWord_5614276
  simp only [CollatzResearch.WordTrace]
  refine ⟨102384734104222184424299341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136512978805629579232399121 102384734104222184424299341)
  ·
    refine ⟨38394275289083319159112253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102384734104222184424299341 38394275289083319159112253)
    ·
      refine ⟨14397853233406244684667095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38394275289083319159112253 14397853233406244684667095)
      ·
        refine ⟨21596779850109367027000643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14397853233406244684667095 21596779850109367027000643)
        ·
          refine ⟨32395169775164050540500965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21596779850109367027000643 32395169775164050540500965)
          ·
            refine ⟨6074094332843259476343931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32395169775164050540500965 6074094332843259476343931)
            ·
              refine ⟨9111141499264889214515897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6074094332843259476343931 9111141499264889214515897)
              ·
                refine ⟨6833356124448666910886923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9111141499264889214515897 6833356124448666910886923)
                ·
                  refine ⟨10250034186673000366330385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6833356124448666910886923 10250034186673000366330385)
                  ·
                    refine ⟨7687525640004750274747789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10250034186673000366330385 7687525640004750274747789)
                    ·
                      refine ⟨2882822115001781353030421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7687525640004750274747789 2882822115001781353030421)
                      ·
                        rfl

theorem cell23_5614276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_5614276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614276 prefixEnd_5614276 := by exact prefixLift 5614276
  have htrace : WordTrace (prefixWord ++ tailWord_5614276) baseStart_5614276 baseEnd_5614276 := by
    simpa [prefixWord, tailWord_5614276, baseEnd_5614276] using wordTrace_append hprefix tailTrace_5614276
  have hstable : (prefixWord ++ tailWord_5614276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614276).length < 2 ^ (prefixWord ++ tailWord_5614276).sum := by decide
  have hdescent : baseEnd_5614276 < baseStart_5614276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614293 : List Nat := [1, 3, 2, 5, 1, 1, 3, 1, 1, 2, 3]
def baseStart_5614293 : Nat := 118140960795 + 5614293 * 2 ^ 59
def prefixEnd_5614293 : Nat := 4983230072969 + 3 ^ 40 * 5614293 * 2
def baseEnd_5614293 : Nat := 2882830844172907786517843

theorem tailTrace_5614293 : CollatzResearch.WordTrace tailWord_5614293 prefixEnd_5614293 2882830844172907786517843 := by
  unfold tailWord_5614293
  simp only [CollatzResearch.WordTrace]
  refine ⟨204770088249382780751967533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136513392166255187167978355 204770088249382780751967533)
  ·
    refine ⟨76788783093518542781987825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204770088249382780751967533 76788783093518542781987825)
    ·
      refine ⟨57591587320138907086490869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76788783093518542781987825 57591587320138907086490869)
      ·
        refine ⟨5399211311263022539358519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57591587320138907086490869 5399211311263022539358519)
        ·
          refine ⟨8098816966894533809037779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399211311263022539358519 8098816966894533809037779)
          ·
            refine ⟨12148225450341800713556669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8098816966894533809037779 12148225450341800713556669)
            ·
              refine ⟨4555584543878175267583751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12148225450341800713556669 4555584543878175267583751)
              ·
                refine ⟨6833376815817262901375627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555584543878175267583751 6833376815817262901375627)
                ·
                  refine ⟨10250065223725894352063441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6833376815817262901375627 10250065223725894352063441)
                  ·
                    refine ⟨7687548917794420764047581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10250065223725894352063441 7687548917794420764047581)
                    ·
                      refine ⟨2882830844172907786517843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7687548917794420764047581 2882830844172907786517843)
                      ·
                        rfl

theorem cell23_5614293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_5614293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614293 prefixEnd_5614293 := by exact prefixLift 5614293
  have htrace : WordTrace (prefixWord ++ tailWord_5614293) baseStart_5614293 baseEnd_5614293 := by
    simpa [prefixWord, tailWord_5614293, baseEnd_5614293] using wordTrace_append hprefix tailTrace_5614293
  have hstable : (prefixWord ++ tailWord_5614293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614293).length < 2 ^ (prefixWord ++ tailWord_5614293).sum := by decide
  have hdescent : baseEnd_5614293 < baseStart_5614293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614322 : List Nat := [3, 2, 1, 3, 1, 3, 1, 1, 2, 6]
def baseStart_5614322 : Nat := 118140960795 + 5614322 * 2 ^ 59
def prefixEnd_5614322 : Nat := 4983230072969 + 3 ^ 40 * 5614322 * 2
def baseEnd_5614322 : Nat := 960948578370629391018403

theorem tailTrace_5614322 : CollatzResearch.WordTrace tailWord_5614322 prefixEnd_5614322 960948578370629391018403 := by
  unfold tailWord_5614322
  simp only [CollatzResearch.WordTrace]
  refine ⟨51192786491569429676193305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136514097310851812469848813 51192786491569429676193305)
  ·
    refine ⟨38394589868677072257144979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51192786491569429676193305 38394589868677072257144979)
    ·
      refine ⟨57591884803015608385717469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38394589868677072257144979 57591884803015608385717469)
      ·
        refine ⟨21596956801130853144644051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57591884803015608385717469 21596956801130853144644051)
        ·
          refine ⟨32395435201696279716966077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21596956801130853144644051 32395435201696279716966077)
          ·
            refine ⟨12148288200636104893862279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32395435201696279716966077 12148288200636104893862279)
            ·
              refine ⟨18222432300954157340793419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12148288200636104893862279 18222432300954157340793419)
              ·
                refine ⟨27333648451431236011190129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18222432300954157340793419 27333648451431236011190129)
                ·
                  refine ⟨20500236338573427008392597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27333648451431236011190129 20500236338573427008392597)
                  ·
                    refine ⟨960948578370629391018403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20500236338573427008392597 960948578370629391018403)
                    ·
                      rfl

theorem cell23_5614322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_5614322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614322 prefixEnd_5614322 := by exact prefixLift 5614322
  have htrace : WordTrace (prefixWord ++ tailWord_5614322) baseStart_5614322 baseEnd_5614322 := by
    simpa [prefixWord, tailWord_5614322, baseEnd_5614322] using wordTrace_append hprefix tailTrace_5614322
  have hstable : (prefixWord ++ tailWord_5614322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614322).length < 2 ^ (prefixWord ++ tailWord_5614322).sum := by decide
  have hdescent : baseEnd_5614322 < baseStart_5614322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614362 : List Nat := [3, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3]
def baseStart_5614362 : Nat := 118140960795 + 5614362 * 2 ^ 59
def prefixEnd_5614362 : Nat := 4983230072969 + 3 ^ 40 * 5614362 * 2
def baseEnd_5614362 : Nat := 2882866274338068016555025

theorem tailTrace_5614362 : CollatzResearch.WordTrace tailWord_5614362 prefixEnd_5614362 2882866274338068016555025 := by
  unfold tailWord_5614362
  simp only [CollatzResearch.WordTrace]
  refine ⟨51193151221533201384057335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136515069924088537024152893 51193151221533201384057335)
  ·
    refine ⟨76789726832299802076086003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51193151221533201384057335 76789726832299802076086003)
    ·
      refine ⟨115184590248449703114129005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76789726832299802076086003 115184590248449703114129005)
      ·
        refine ⟨43194221343168638667798377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115184590248449703114129005 43194221343168638667798377)
        ·
          refine ⟨32395666007376479000848783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43194221343168638667798377 32395666007376479000848783)
          ·
            refine ⟨48593499011064718501273175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32395666007376479000848783 48593499011064718501273175)
            ·
              refine ⟨72890248516597077751909763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48593499011064718501273175 72890248516597077751909763)
              ·
                refine ⟨109335372774895616627864645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72890248516597077751909763 109335372774895616627864645)
                ·
                  refine ⟨20500382395292928117724621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109335372774895616627864645 20500382395292928117724621)
                  ·
                    refine ⟨7687643398234848044146733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20500382395292928117724621 7687643398234848044146733)
                    ·
                      refine ⟨2882866274338068016555025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7687643398234848044146733 2882866274338068016555025)
                      ·
                        rfl

theorem cell23_5614362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_5614362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614362 prefixEnd_5614362 := by exact prefixLift 5614362
  have htrace : WordTrace (prefixWord ++ tailWord_5614362) baseStart_5614362 baseEnd_5614362 := by
    simpa [prefixWord, tailWord_5614362, baseEnd_5614362] using wordTrace_append hprefix tailTrace_5614362
  have hstable : (prefixWord ++ tailWord_5614362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614362).length < 2 ^ (prefixWord ++ tailWord_5614362).sum := by decide
  have hdescent : baseEnd_5614362 < baseStart_5614362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614503 : List Nat := [1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_5614503 : Nat := 118140960795 + 5614503 * 2 ^ 59
def prefixEnd_5614503 : Nat := 4983230072969 + 3 ^ 40 * 5614503 * 2
def baseEnd_5614503 : Nat := 2882938675110351964891877

theorem tailTrace_5614503 : CollatzResearch.WordTrace tailWord_5614503 prefixEnd_5614503 2882938675110351964891877 := by
  unfold tailWord_5614503
  simp only [CollatzResearch.WordTrace]
  refine ⟨204777747578621986617112163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136518498385747991078074775 204777747578621986617112163)
  ·
    refine ⟨307166621367932979925668245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204777747578621986617112163 307166621367932979925668245)
    ·
      refine ⟨14398435376621858434015699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 307166621367932979925668245 14398435376621858434015699)
      ·
        refine ⟨21597653064932787651023549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14398435376621858434015699 21597653064932787651023549)
        ·
          refine ⟨8099119899349795369133831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21597653064932787651023549 8099119899349795369133831)
          ·
            refine ⟨12148679849024693053700747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8099119899349795369133831 12148679849024693053700747)
            ·
              refine ⟨18223019773537039580551121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12148679849024693053700747 18223019773537039580551121)
              ·
                refine ⟨13667264830152779685413341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18223019773537039580551121 13667264830152779685413341)
                ·
                  refine ⟨5125224311307292382030003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13667264830152779685413341 5125224311307292382030003)
                  ·
                    refine ⟨7687836466960938573045005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5125224311307292382030003 7687836466960938573045005)
                    ·
                      refine ⟨2882938675110351964891877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7687836466960938573045005 2882938675110351964891877)
                      ·
                        rfl

theorem cell23_5614503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_5614503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614503 prefixEnd_5614503 := by exact prefixLift 5614503
  have htrace : WordTrace (prefixWord ++ tailWord_5614503) baseStart_5614503 baseEnd_5614503 := by
    simpa [prefixWord, tailWord_5614503, baseEnd_5614503] using wordTrace_append hprefix tailTrace_5614503
  have hstable : (prefixWord ++ tailWord_5614503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614503).length < 2 ^ (prefixWord ++ tailWord_5614503).sum := by decide
  have hdescent : baseEnd_5614503 < baseStart_5614503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614526 : List Nat := [4, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4]
def baseStart_5614526 : Nat := 118140960795 + 5614526 * 2 ^ 59
def prefixEnd_5614526 : Nat := 4983230072969 + 3 ^ 40 * 5614526 * 2
def baseEnd_5614526 : Nat := 2882950485165405374904271

theorem tailTrace_5614526 : CollatzResearch.WordTrace tailWord_5614526 prefixEnd_5614526 2882950485165405374904271 := by
  unfold tailWord_5614526
  simp only [CollatzResearch.WordTrace]
  refine ⟨25597323307192332693149929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136519057638359107696799621 25597323307192332693149929)
  ·
    refine ⟨19197992480394249519862447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25597323307192332693149929 19197992480394249519862447)
    ·
      refine ⟨28796988720591374279793671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19197992480394249519862447 28796988720591374279793671)
      ·
        refine ⟨43195483080887061419690507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28796988720591374279793671 43195483080887061419690507)
        ·
          refine ⟨64793224621330592129535761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43195483080887061419690507 64793224621330592129535761)
          ·
            refine ⟨48594918465997944097151821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64793224621330592129535761 48594918465997944097151821)
            ·
              refine ⟨18223094424749229036431933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48594918465997944097151821 18223094424749229036431933)
              ·
                refine ⟨6833660409280960888661975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18223094424749229036431933 6833660409280960888661975)
                ·
                  refine ⟨10250490613921441332992963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6833660409280960888661975 10250490613921441332992963)
                  ·
                    refine ⟨15375735920882161999489445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10250490613921441332992963 15375735920882161999489445)
                    ·
                      refine ⟨2882950485165405374904271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15375735920882161999489445 2882950485165405374904271)
                      ·
                        rfl

theorem cell23_5614526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_5614526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614526 prefixEnd_5614526 := by exact prefixLift 5614526
  have htrace : WordTrace (prefixWord ++ tailWord_5614526) baseStart_5614526 baseEnd_5614526 := by
    simpa [prefixWord, tailWord_5614526, baseEnd_5614526] using wordTrace_append hprefix tailTrace_5614526
  have hstable : (prefixWord ++ tailWord_5614526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614526).length < 2 ^ (prefixWord ++ tailWord_5614526).sum := by decide
  have hdescent : baseEnd_5614526 < baseStart_5614526 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614536 : List Nat := [2, 1, 3, 1, 5, 1, 1, 1, 4, 4]
def baseStart_5614536 : Nat := 118140960795 + 5614536 * 2 ^ 59
def prefixEnd_5614536 : Nat := 4983230072969 + 3 ^ 40 * 5614536 * 2
def baseEnd_5614536 : Nat := 960985206657316778593075

theorem tailTrace_5614536 : CollatzResearch.WordTrace tailWord_5614536 prefixEnd_5614536 960985206657316778593075 := by
  unfold tailWord_5614536
  simp only [CollatzResearch.WordTrace]
  refine ⟨102389475593751216626531731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136519300791668288835375641 102389475593751216626531731)
  ·
    refine ⟨153584213390626824939797597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102389475593751216626531731 153584213390626824939797597)
    ·
      refine ⟨57594080021485059352424099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153584213390626824939797597 57594080021485059352424099)
      ·
        refine ⟨86391120032227589028636149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57594080021485059352424099 86391120032227589028636149)
        ·
          refine ⟨8099167503021336471434639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 86391120032227589028636149 8099167503021336471434639)
          ·
            refine ⟨12148751254532004707151959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8099167503021336471434639 12148751254532004707151959)
            ·
              refine ⟨18223126881798007060727939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12148751254532004707151959 18223126881798007060727939)
              ·
                refine ⟨27334690322697010591091909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18223126881798007060727939 27334690322697010591091909)
                ·
                  refine ⟨5125254435505689485829733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27334690322697010591091909 5125254435505689485829733)
                  ·
                    refine ⟨960985206657316778593075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5125254435505689485829733 960985206657316778593075)
                    ·
                      rfl

theorem cell23_5614536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_5614536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614536 prefixEnd_5614536 := by exact prefixLift 5614536
  have htrace : WordTrace (prefixWord ++ tailWord_5614536) baseStart_5614536 baseEnd_5614536 := by
    simpa [prefixWord, tailWord_5614536, baseEnd_5614536] using wordTrace_append hprefix tailTrace_5614536
  have hstable : (prefixWord ++ tailWord_5614536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614536).length < 2 ^ (prefixWord ++ tailWord_5614536).sum := by decide
  have hdescent : baseEnd_5614536 < baseStart_5614536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614543 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 3, 2, 2]
def baseStart_5614543 : Nat := 118140960795 + 5614543 * 2 ^ 59
def prefixEnd_5614543 : Nat := 4983230072969 + 3 ^ 40 * 5614543 * 2
def baseEnd_5614543 : Nat := 2882959214336531808391693

theorem tailTrace_5614543 : CollatzResearch.WordTrace tailWord_5614543 prefixEnd_5614543 2882959214336531808391693 := by
  unfold tailWord_5614543
  simp only [CollatzResearch.WordTrace]
  refine ⟨204779206498477073448568283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136519470998984715632378855 204779206498477073448568283)
  ·
    refine ⟨307168809747715610172852425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204779206498477073448568283 307168809747715610172852425)
    ·
      refine ⟨230376607310786707629639319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307168809747715610172852425 230376607310786707629639319)
      ·
        refine ⟨345564910966180061444458979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230376607310786707629639319 345564910966180061444458979)
        ·
          refine ⟨518347366449270092166688469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345564910966180061444458979 518347366449270092166688469)
          ·
            refine ⟨12148766401154767785156761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 518347366449270092166688469 12148766401154767785156761)
            ·
              refine ⟨9111574800866075838867571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12148766401154767785156761 9111574800866075838867571)
              ·
                refine ⟨13667362201299113758301357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9111574800866075838867571 13667362201299113758301357)
                ·
                  refine ⟨5125260825487167659363009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13667362201299113758301357 5125260825487167659363009)
                  ·
                    refine ⟨3843945619115375744522257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5125260825487167659363009 3843945619115375744522257)
                    ·
                      refine ⟨2882959214336531808391693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843945619115375744522257 2882959214336531808391693)
                      ·
                        rfl

theorem cell23_5614543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 3, 2, 2].length) (baseStart_5614543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614543 prefixEnd_5614543 := by exact prefixLift 5614543
  have htrace : WordTrace (prefixWord ++ tailWord_5614543) baseStart_5614543 baseEnd_5614543 := by
    simpa [prefixWord, tailWord_5614543, baseEnd_5614543] using wordTrace_append hprefix tailTrace_5614543
  have hstable : (prefixWord ++ tailWord_5614543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614543).length < 2 ^ (prefixWord ++ tailWord_5614543).sum := by decide
  have hdescent : baseEnd_5614543 < baseStart_5614543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614546 : List Nat := [3, 2, 2, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_5614546 : Nat := 118140960795 + 5614546 * 2 ^ 59
def prefixEnd_5614546 : Nat := 4983230072969 + 3 ^ 40 * 5614546 * 2
def baseEnd_5614546 : Nat := 2882960754778495296654179

theorem tailTrace_5614546 : CollatzResearch.WordTrace tailWord_5614546 prefixEnd_5614546 2882960754778495296654179 := by
  unfold tailWord_5614546
  simp only [CollatzResearch.WordTrace]
  refine ⟨51194828979366551240231873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136519543944977469973951661 51194828979366551240231873)
  ·
    refine ⟨38396121734524913430173905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51194828979366551240231873 38396121734524913430173905)
    ·
      refine ⟨28797091300893685072630429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38396121734524913430173905 28797091300893685072630429)
      ·
        refine ⟨10798909237835131902236411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28797091300893685072630429 10798909237835131902236411)
        ·
          refine ⟨16198363856752697853354617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10798909237835131902236411 16198363856752697853354617)
          ·
            refine ⟨12148772892564523390015963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16198363856752697853354617 12148772892564523390015963)
            ·
              refine ⟨18223159338846785085023945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12148772892564523390015963 18223159338846785085023945)
              ·
                refine ⟨13667369504135088813767959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18223159338846785085023945 13667369504135088813767959)
                ·
                  refine ⟨20501054256202633220651939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13667369504135088813767959 20501054256202633220651939)
                  ·
                    refine ⟨30751581384303949830977909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20501054256202633220651939 30751581384303949830977909)
                    ·
                      refine ⟨2882960754778495296654179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30751581384303949830977909 2882960754778495296654179)
                      ·
                        rfl

theorem cell23_5614546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_5614546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614546 prefixEnd_5614546 := by exact prefixLift 5614546
  have htrace : WordTrace (prefixWord ++ tailWord_5614546) baseStart_5614546 baseEnd_5614546 := by
    simpa [prefixWord, tailWord_5614546, baseEnd_5614546] using wordTrace_append hprefix tailTrace_5614546
  have hstable : (prefixWord ++ tailWord_5614546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614546).length < 2 ^ (prefixWord ++ tailWord_5614546).sum := by decide
  have hdescent : baseEnd_5614546 < baseStart_5614546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614553 : List Nat := [1, 2, 1, 2, 5, 2, 3, 1, 2, 4]
def baseStart_5614553 : Nat := 118140960795 + 5614553 * 2 ^ 59
def prefixEnd_5614553 : Nat := 4983230072969 + 3 ^ 40 * 5614553 * 2
def baseEnd_5614553 : Nat := 960988116381025589755549

theorem tailTrace_5614553 : CollatzResearch.WordTrace tailWord_5614553 prefixEnd_5614553 960988116381025589755549 := by
  unfold tailWord_5614553
  simp only [CollatzResearch.WordTrace]
  refine ⟨204779571228440845156432313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136519714152293896770954875 204779571228440845156432313)
  ·
    refine ⟨153584678421330633867324235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204779571228440845156432313 153584678421330633867324235)
    ·
      refine ⟨230377017631995950800986353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153584678421330633867324235 230377017631995950800986353)
      ·
        refine ⟨172782763223996963100739765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230377017631995950800986353 172782763223996963100739765)
        ·
          refine ⟨16198384052249715290694353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172782763223996963100739765 16198384052249715290694353)
          ·
            refine ⟨12148788039187286468020765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16198384052249715290694353 12148788039187286468020765)
            ·
              refine ⟨4555795514695232425507787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12148788039187286468020765 4555795514695232425507787)
              ·
                refine ⟨6833693272042848638261681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555795514695232425507787 6833693272042848638261681)
                ·
                  refine ⟨5125269954032136478696261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6833693272042848638261681 5125269954032136478696261)
                  ·
                    refine ⟨960988116381025589755549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5125269954032136478696261 960988116381025589755549)
                    ·
                      rfl

theorem cell23_5614553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 1, 2, 4].length) (baseStart_5614553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614553 prefixEnd_5614553 := by exact prefixLift 5614553
  have htrace : WordTrace (prefixWord ++ tailWord_5614553) baseStart_5614553 baseEnd_5614553 := by
    simpa [prefixWord, tailWord_5614553, baseEnd_5614553] using wordTrace_append hprefix tailTrace_5614553
  have hstable : (prefixWord ++ tailWord_5614553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614553).length < 2 ^ (prefixWord ++ tailWord_5614553).sum := by decide
  have hdescent : baseEnd_5614553 < baseStart_5614553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614569 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 4, 7, 2]
def baseStart_5614569 : Nat := 118140960795 + 5614569 * 2 ^ 59
def prefixEnd_5614569 : Nat := 4983230072969 + 3 ^ 40 * 5614569 * 2
def baseEnd_5614569 : Nat := 2882972564833548706666573

theorem tailTrace_5614569 : CollatzResearch.WordTrace tailWord_5614569 prefixEnd_5614569 2882972564833548706666573 := by
  unfold tailWord_5614569
  simp only [CollatzResearch.WordTrace]
  refine ⟨204780154796382879889014761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136520103197588586592676507 204780154796382879889014761)
  ·
    refine ⟨153585116097287159916761071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204780154796382879889014761 153585116097287159916761071)
    ·
      refine ⟨230377674145930739875141607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153585116097287159916761071 230377674145930739875141607)
      ·
        refine ⟨345566511218896109812712411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230377674145930739875141607 345566511218896109812712411)
        ·
          refine ⟨518349766828344164719068617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345566511218896109812712411 518349766828344164719068617)
          ·
            refine ⟨388762325121258123539301463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518349766828344164719068617 388762325121258123539301463)
            ·
              refine ⟨583143487681887185308952195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388762325121258123539301463 583143487681887185308952195)
              ·
                refine ⟨874715231522830777963428293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583143487681887185308952195 874715231522830777963428293)
                ·
                  refine ⟨164009105910530770868142805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 874715231522830777963428293 164009105910530770868142805)
                  ·
                    refine ⟨3843963419778064942222097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 164009105910530770868142805 3843963419778064942222097)
                    ·
                      refine ⟨2882972564833548706666573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843963419778064942222097 2882972564833548706666573)
                      ·
                        rfl

theorem cell23_5614569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 7, 2].length) (baseStart_5614569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614569 prefixEnd_5614569 := by exact prefixLift 5614569
  have htrace : WordTrace (prefixWord ++ tailWord_5614569) baseStart_5614569 baseEnd_5614569 := by
    simpa [prefixWord, tailWord_5614569, baseEnd_5614569] using wordTrace_append hprefix tailTrace_5614569
  have hstable : (prefixWord ++ tailWord_5614569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614569).length < 2 ^ (prefixWord ++ tailWord_5614569).sum := by decide
  have hdescent : baseEnd_5614569 < baseStart_5614569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614577 : List Nat := [1, 2, 2, 2, 4, 3, 1, 3, 1, 2, 2]
def baseStart_5614577 : Nat := 118140960795 + 5614577 * 2 ^ 59
def prefixEnd_5614577 : Nat := 4983230072969 + 3 ^ 40 * 5614577 * 2
def baseEnd_5614577 : Nat := 2882976672678784675366537

theorem tailTrace_5614577 : CollatzResearch.WordTrace tailWord_5614577 prefixEnd_5614577 2882976672678784675366537 := by
  unfold tailWord_5614577
  simp only [CollatzResearch.WordTrace]
  refine ⟨204780446580353897255305985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136520297720235931503537323 204780446580353897255305985)
  ·
    refine ⟨153585334935265422941479489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204780446580353897255305985 153585334935265422941479489)
    ·
      refine ⟨115189001201449067206109617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153585334935265422941479489 115189001201449067206109617)
      ·
        refine ⟨86391750901086800404582213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115189001201449067206109617 86391750901086800404582213)
        ·
          refine ⟨16198453293953775075859165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86391750901086800404582213 16198453293953775075859165)
          ·
            refine ⟨6074419985232665653447187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16198453293953775075859165 6074419985232665653447187)
            ·
              refine ⟨9111629977848998480170781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6074419985232665653447187 9111629977848998480170781)
              ·
                refine ⟨3416861241693374430064043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9111629977848998480170781 3416861241693374430064043)
                ·
                  refine ⟨5125291862540061645096065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3416861241693374430064043 5125291862540061645096065)
                  ·
                    refine ⟨3843968896905046233822049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5125291862540061645096065 3843968896905046233822049)
                    ·
                      refine ⟨2882976672678784675366537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843968896905046233822049 2882976672678784675366537)
                      ·
                        rfl

theorem cell23_5614577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 1, 2, 2].length) (baseStart_5614577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614577 prefixEnd_5614577 := by exact prefixLift 5614577
  have htrace : WordTrace (prefixWord ++ tailWord_5614577) baseStart_5614577 baseEnd_5614577 := by
    simpa [prefixWord, tailWord_5614577, baseEnd_5614577] using wordTrace_append hprefix tailTrace_5614577
  have hstable : (prefixWord ++ tailWord_5614577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614577).length < 2 ^ (prefixWord ++ tailWord_5614577).sum := by decide
  have hdescent : baseEnd_5614577 < baseStart_5614577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614594 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_5614594 : Nat := 118140960795 + 5614594 * 2 ^ 59
def prefixEnd_5614594 : Nat := 4983230072969 + 3 ^ 40 * 5614594 * 2
def baseEnd_5614594 : Nat := 2882985401849911108853959

theorem tailTrace_5614594 : CollatzResearch.WordTrace tailWord_5614594 prefixEnd_5614594 2882985401849911108853959 := by
  unfold tailWord_5614594
  simp only [CollatzResearch.WordTrace]
  refine ⟨51195266655323077289668709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136520711080861539439116557 51195266655323077289668709)
  ·
    refine ⟨9599112497873076991812883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 51195266655323077289668709 9599112497873076991812883)
    ·
      refine ⟨14398668746809615487719325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9599112497873076991812883 14398668746809615487719325)
      ·
        refine ⟨5399500780053605807894747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14398668746809615487719325 5399500780053605807894747)
        ·
          refine ⟨8099251170080408711842121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399500780053605807894747 8099251170080408711842121)
          ·
            refine ⟨6074438377560306533881591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8099251170080408711842121 6074438377560306533881591)
            ·
              refine ⟨9111657566340459800822387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6074438377560306533881591 9111657566340459800822387)
              ·
                refine ⟨13667486349510689701233581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9111657566340459800822387 13667486349510689701233581)
                ·
                  refine ⟨5125307381066508637962593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13667486349510689701233581 5125307381066508637962593)
                  ·
                    refine ⟨3843980535799881478471945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5125307381066508637962593 3843980535799881478471945)
                    ·
                      refine ⟨2882985401849911108853959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3843980535799881478471945 2882985401849911108853959)
                      ·
                        rfl

theorem cell23_5614594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_5614594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614594 prefixEnd_5614594 := by exact prefixLift 5614594
  have htrace : WordTrace (prefixWord ++ tailWord_5614594) baseStart_5614594 baseEnd_5614594 := by
    simpa [prefixWord, tailWord_5614594, baseEnd_5614594] using wordTrace_append hprefix tailTrace_5614594
  have hstable : (prefixWord ++ tailWord_5614594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614594).length < 2 ^ (prefixWord ++ tailWord_5614594).sum := by decide
  have hdescent : baseEnd_5614594 < baseStart_5614594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614599 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_5614599 : Nat := 118140960795 + 5614599 * 2 ^ 59
def prefixEnd_5614599 : Nat := 4983230072969 + 3 ^ 40 * 5614599 * 2
def baseEnd_5614599 : Nat := 2882987969253183589291435

theorem tailTrace_5614599 : CollatzResearch.WordTrace tailWord_5614599 prefixEnd_5614599 2882987969253183589291435 := by
  unfold tailWord_5614599
  simp only [CollatzResearch.WordTrace]
  refine ⟨204781248986274195012606851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136520832657516130008404567 204781248986274195012606851)
  ·
    refine ⟨307171873479411292518910277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204781248986274195012606851 307171873479411292518910277)
    ·
      refine ⟨57594726277389617347295677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307171873479411292518910277 57594726277389617347295677)
      ·
        refine ⟨21598022354021106505235879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57594726277389617347295677 21598022354021106505235879)
        ·
          refine ⟨32397033531031659757853819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21598022354021106505235879 32397033531031659757853819)
          ·
            refine ⟨48595550296547489636780729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32397033531031659757853819 48595550296547489636780729)
            ·
              refine ⟨36446662722410617227585547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48595550296547489636780729 36446662722410617227585547)
              ·
                refine ⟨54669994083615925841378321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36446662722410617227585547 54669994083615925841378321)
                ·
                  refine ⟨41002495562711944381033741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54669994083615925841378321 41002495562711944381033741)
                  ·
                    refine ⟨15375935836016979142887653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41002495562711944381033741 15375935836016979142887653)
                    ·
                      refine ⟨2882987969253183589291435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15375935836016979142887653 2882987969253183589291435)
                      ·
                        rfl

theorem cell23_5614599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_5614599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614599 prefixEnd_5614599 := by exact prefixLift 5614599
  have htrace : WordTrace (prefixWord ++ tailWord_5614599) baseStart_5614599 baseEnd_5614599 := by
    simpa [prefixWord, tailWord_5614599, baseEnd_5614599] using wordTrace_append hprefix tailTrace_5614599
  have hstable : (prefixWord ++ tailWord_5614599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614599).length < 2 ^ (prefixWord ++ tailWord_5614599).sum := by decide
  have hdescent : baseEnd_5614599 < baseStart_5614599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614656 : List Nat := [2, 1, 1, 2, 2, 3, 3, 4, 5]
def baseStart_5614656 : Nat := 118140960795 + 5614656 * 2 ^ 59
def prefixEnd_5614656 : Nat := 4983230072969 + 3 ^ 40 * 5614656 * 2
def baseEnd_5614656 : Nat := 320335248627832207364297

theorem tailTrace_5614656 : CollatzResearch.WordTrace tailWord_5614656 prefixEnd_5614656 320335248627832207364297 := by
  unfold tailWord_5614656
  simp only [CollatzResearch.WordTrace]
  refine ⟨102391663973533846873715911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136522218631378462498287881 102391663973533846873715911)
  ·
    refine ⟨153587495960300770310573867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102391663973533846873715911 153587495960300770310573867)
    ·
      refine ⟨230381243940451155465860801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153587495960300770310573867 230381243940451155465860801)
      ·
        refine ⟨172785932955338366599395601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230381243940451155465860801 172785932955338366599395601)
        ·
          refine ⟨129589449716503774949546701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172785932955338366599395601 129589449716503774949546701)
          ·
            refine ⟨48596043643688915606080013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129589449716503774949546701 48596043643688915606080013)
            ·
              refine ⟨18223516366383343352280005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48596043643688915606080013 18223516366383343352280005)
              ·
                refine ⟨3416909318696876878552501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18223516366383343352280005 3416909318696876878552501)
                ·
                  refine ⟨320335248627832207364297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3416909318696876878552501 320335248627832207364297)
                  ·
                    rfl

theorem cell23_5614656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 3, 4, 5].length) (baseStart_5614656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614656 prefixEnd_5614656 := by exact prefixLift 5614656
  have htrace : WordTrace (prefixWord ++ tailWord_5614656) baseStart_5614656 baseEnd_5614656 := by
    simpa [prefixWord, tailWord_5614656, baseEnd_5614656] using wordTrace_append hprefix tailTrace_5614656
  have hstable : (prefixWord ++ tailWord_5614656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614656).length < 2 ^ (prefixWord ++ tailWord_5614656).sum := by decide
  have hdescent : baseEnd_5614656 < baseStart_5614656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614690 : List Nat := [3, 3, 2, 2, 1, 2, 2, 3, 5]
def baseStart_5614690 : Nat := 118140960795 + 5614690 * 2 ^ 59
def prefixEnd_5614690 : Nat := 4983230072969 + 3 ^ 40 * 5614690 * 2
def baseEnd_5614690 : Nat := 320337188443638081472613

theorem tailTrace_5614690 : CollatzResearch.WordTrace tailWord_5614690 prefixEnd_5614690 320337188443638081472613 := by
  unfold tailWord_5614690
  simp only [CollatzResearch.WordTrace]
  refine ⟨51196142007236129388542381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136523045352629678369446349 51196142007236129388542381)
  ·
    refine ⟨19198553252713548520703393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51196142007236129388542381 19198553252713548520703393)
    ·
      refine ⟨14398914939535161390527545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19198553252713548520703393 14398914939535161390527545)
      ·
        refine ⟨10799186204651371042895659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14398914939535161390527545 10799186204651371042895659)
        ·
          refine ⟨16198779306977056564343489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10799186204651371042895659 16198779306977056564343489)
          ·
            refine ⟨12149084480232792423257617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16198779306977056564343489 12149084480232792423257617)
            ·
              refine ⟨9111813360174594317443213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12149084480232792423257617 9111813360174594317443213)
              ·
                refine ⟨3416930010065472869041205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9111813360174594317443213 3416930010065472869041205)
                ·
                  refine ⟨320337188443638081472613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3416930010065472869041205 320337188443638081472613)
                  ·
                    rfl

theorem cell23_5614690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_5614690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614690 prefixEnd_5614690 := by exact prefixLift 5614690
  have htrace : WordTrace (prefixWord ++ tailWord_5614690) baseStart_5614690 baseEnd_5614690 := by
    simpa [prefixWord, tailWord_5614690, baseEnd_5614690] using wordTrace_append hprefix tailTrace_5614690
  have hstable : (prefixWord ++ tailWord_5614690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614690).length < 2 ^ (prefixWord ++ tailWord_5614690).sum := by decide
  have hdescent : baseEnd_5614690 < baseStart_5614690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614706 : List Nat := [3, 2, 1, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_5614706 : Nat := 118140960795 + 5614706 * 2 ^ 59
def prefixEnd_5614706 : Nat := 4983230072969 + 3 ^ 40 * 5614706 * 2
def baseEnd_5614706 : Nat := 2883042911683214670653443

theorem tailTrace_5614706 : CollatzResearch.WordTrace tailWord_5614706 prefixEnd_5614706 2883042911683214670653443 := by
  unfold tailWord_5614706
  simp only [CollatzResearch.WordTrace]
  refine ⟨51196287899221638071687993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136523434397924368191167981 51196287899221638071687993)
  ·
    refine ⟨38397215924416228553765995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51196287899221638071687993 38397215924416228553765995)
    ·
      refine ⟨57595823886624342830648993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38397215924416228553765995 57595823886624342830648993)
      ·
        refine ⟨43196867914968257122986745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57595823886624342830648993 43196867914968257122986745)
        ·
          refine ⟨32397650936226192842240059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43196867914968257122986745 32397650936226192842240059)
          ·
            refine ⟨48596476404339289263360089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32397650936226192842240059 48596476404339289263360089)
            ·
              refine ⟨36447357303254466947520067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48596476404339289263360089 36447357303254466947520067)
              ·
                refine ⟨54671035954881700421280101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36447357303254466947520067 54671035954881700421280101)
                ·
                  refine ⟨10250819241540318828990019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54671035954881700421280101 10250819241540318828990019)
                  ·
                    refine ⟨15376228862310478243485029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10250819241540318828990019 15376228862310478243485029)
                    ·
                      refine ⟨2883042911683214670653443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15376228862310478243485029 2883042911683214670653443)
                      ·
                        rfl

theorem cell23_5614706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_5614706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614706 prefixEnd_5614706 := by exact prefixLift 5614706
  have htrace : WordTrace (prefixWord ++ tailWord_5614706) baseStart_5614706 baseEnd_5614706 := by
    simpa [prefixWord, tailWord_5614706, baseEnd_5614706] using wordTrace_append hprefix tailTrace_5614706
  have hstable : (prefixWord ++ tailWord_5614706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614706).length < 2 ^ (prefixWord ++ tailWord_5614706).sum := by decide
  have hdescent : baseEnd_5614706 < baseStart_5614706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614718 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 2, 2, 2]
def baseStart_5614718 : Nat := 118140960795 + 5614718 * 2 ^ 59
def prefixEnd_5614718 : Nat := 4983230072969 + 3 ^ 40 * 5614718 * 2
def baseEnd_5614718 : Nat := 2883049073451068623703389

theorem tailTrace_5614718 : CollatzResearch.WordTrace tailWord_5614718 prefixEnd_5614718 2883049073451068623703389 := by
  unfold tailWord_5614718
  simp only [CollatzResearch.WordTrace]
  refine ⟨25598198659105384792023601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136523726181895385557459205 25598198659105384792023601)
  ·
    refine ⟨19198648994329038594017701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25598198659105384792023601 19198648994329038594017701)
    ·
      refine ⟨3599746686436694736378319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19198648994329038594017701 3599746686436694736378319)
      ·
        refine ⟨5399620029655042104567479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3599746686436694736378319 5399620029655042104567479)
        ·
          refine ⟨8099430044482563156851219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399620029655042104567479 8099430044482563156851219)
          ·
            refine ⟨12149145066723844735276829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8099430044482563156851219 12149145066723844735276829)
            ·
              refine ⟨4555929400021441775728811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12149145066723844735276829 4555929400021441775728811)
              ·
                refine ⟨6833894100032162663593217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555929400021441775728811 6833894100032162663593217)
                ·
                  refine ⟨5125420575024121997694913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6833894100032162663593217 5125420575024121997694913)
                  ·
                    refine ⟨3844065431268091498271185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5125420575024121997694913 3844065431268091498271185)
                    ·
                      refine ⟨2883049073451068623703389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3844065431268091498271185 2883049073451068623703389)
                      ·
                        rfl

theorem cell23_5614718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_5614718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614718 prefixEnd_5614718 := by exact prefixLift 5614718
  have htrace : WordTrace (prefixWord ++ tailWord_5614718) baseStart_5614718 baseEnd_5614718 := by
    simpa [prefixWord, tailWord_5614718, baseEnd_5614718] using wordTrace_append hprefix tailTrace_5614718
  have hstable : (prefixWord ++ tailWord_5614718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614718).length < 2 ^ (prefixWord ++ tailWord_5614718).sum := by decide
  have hdescent : baseEnd_5614718 < baseStart_5614718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614746 : List Nat := [3, 1, 1, 5, 1, 1, 1, 2, 8]
def baseStart_5614746 : Nat := 118140960795 + 5614746 * 2 ^ 59
def prefixEnd_5614746 : Nat := 4983230072969 + 3 ^ 40 * 5614746 * 2
def baseEnd_5614746 : Nat := 320340383434377168239251

theorem tailTrace_5614746 : CollatzResearch.WordTrace tailWord_5614746 prefixEnd_5614746 320340383434377168239251 := by
  unfold tailWord_5614746
  simp only [CollatzResearch.WordTrace]
  refine ⟨51196652629185409779552023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136524407011161092745472061 51196652629185409779552023)
  ·
    refine ⟨76794978943778114669328035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51196652629185409779552023 76794978943778114669328035)
    ·
      refine ⟨115192468415667172003992053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76794978943778114669328035 115192468415667172003992053)
      ·
        refine ⟨10799293913968797375374255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115192468415667172003992053 10799293913968797375374255)
        ·
          refine ⟨16198940870953196063061383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10799293913968797375374255 16198940870953196063061383)
          ·
            refine ⟨24298411306429794094592075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16198940870953196063061383 24298411306429794094592075)
            ·
              refine ⟨36447616959644691141888113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24298411306429794094592075 36447616959644691141888113)
              ·
                refine ⟨27335712719733518356416085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36447616959644691141888113 27335712719733518356416085)
                ·
                  refine ⟨320340383434377168239251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27335712719733518356416085 320340383434377168239251)
                  ·
                    rfl

theorem cell23_5614746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 1, 2, 8].length) (baseStart_5614746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614746 prefixEnd_5614746 := by exact prefixLift 5614746
  have htrace : WordTrace (prefixWord ++ tailWord_5614746) baseStart_5614746 baseEnd_5614746 := by
    simpa [prefixWord, tailWord_5614746, baseEnd_5614746] using wordTrace_append hprefix tailTrace_5614746
  have hstable : (prefixWord ++ tailWord_5614746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614746).length < 2 ^ (prefixWord ++ tailWord_5614746).sum := by decide
  have hdescent : baseEnd_5614746 < baseStart_5614746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614780 : List Nat := [2, 2, 2, 3, 2, 3, 2, 1, 6]
def baseStart_5614780 : Nat := 118140960795 + 5614780 * 2 ^ 59
def prefixEnd_5614780 : Nat := 4983230072969 + 3 ^ 40 * 5614780 * 2
def baseEnd_5614780 : Nat := 320342323250183042347567

theorem tailTrace_5614780 : CollatzResearch.WordTrace tailWord_5614780 prefixEnd_5614780 320342323250183042347567 := by
  unfold tailWord_5614780
  simp only [CollatzResearch.WordTrace]
  refine ⟨102393925299309231462472897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136525233732412308616630529 102393925299309231462472897)
  ·
    refine ⟨76795443974481923596854673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102393925299309231462472897 76795443974481923596854673)
    ·
      refine ⟨57596582980861442697641005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76795443974481923596854673 57596582980861442697641005)
      ·
        refine ⟨21598718617823041011615377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57596582980861442697641005 21598718617823041011615377)
        ·
          refine ⟨16199038963367280758711533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21598718617823041011615377 16199038963367280758711533)
          ·
            refine ⟨6074639611262730284516825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16199038963367280758711533 6074639611262730284516825)
            ·
              refine ⟨4555979708447047713387619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6074639611262730284516825 4555979708447047713387619)
              ·
                refine ⟨6833969562670571570081429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4555979708447047713387619 6833969562670571570081429)
                ·
                  refine ⟨320342323250183042347567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6833969562670571570081429 320342323250183042347567)
                  ·
                    rfl

theorem cell23_5614780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_5614780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614780 prefixEnd_5614780 := by exact prefixLift 5614780
  have htrace : WordTrace (prefixWord ++ tailWord_5614780) baseStart_5614780 baseEnd_5614780 := by
    simpa [prefixWord, tailWord_5614780, baseEnd_5614780] using wordTrace_append hprefix tailTrace_5614780
  have hstable : (prefixWord ++ tailWord_5614780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614780).length < 2 ^ (prefixWord ++ tailWord_5614780).sum := by decide
  have hdescent : baseEnd_5614780 < baseStart_5614780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614819 : List Nat := [1, 1, 1, 20]
def baseStart_5614819 : Nat := 118140960795 + 5614819 * 2 ^ 59
def prefixEnd_5614819 : Nat := 4983230072969 + 3 ^ 40 * 5614819 * 2
def baseEnd_5614819 : Nat := 1318290322358103671029

theorem tailTrace_5614819 : CollatzResearch.WordTrace tailWord_5614819 prefixEnd_5614819 1318290322358103671029 := by
  unfold tailWord_5614819
  simp only [CollatzResearch.WordTrace]
  refine ⟨204789273045477172585615511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136526182030318115057077007 204789273045477172585615511)
  ·
    refine ⟨307183909568215758878423267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204789273045477172585615511 307183909568215758878423267)
    ·
      refine ⟨460775864352323638317634901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307183909568215758878423267 460775864352323638317634901)
      ·
        refine ⟨1318290322358103671029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 20 460775864352323638317634901 1318290322358103671029)
        ·
          rfl

theorem cell23_5614819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 20].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 20].length) (baseStart_5614819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614819 prefixEnd_5614819 := by exact prefixLift 5614819
  have htrace : WordTrace (prefixWord ++ tailWord_5614819) baseStart_5614819 baseEnd_5614819 := by
    simpa [prefixWord, tailWord_5614819, baseEnd_5614819] using wordTrace_append hprefix tailTrace_5614819
  have hstable : (prefixWord ++ tailWord_5614819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614819).length < 2 ^ (prefixWord ++ tailWord_5614819).sum := by decide
  have hdescent : baseEnd_5614819 < baseStart_5614819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614896 : List Nat := [2, 1, 1, 1, 2, 2, 3, 3, 2, 6]
def baseStart_5614896 : Nat := 118140960795 + 5614896 * 2 ^ 59
def prefixEnd_5614896 : Nat := 4983230072969 + 3 ^ 40 * 5614896 * 2
def baseEnd_5614896 : Nat := 961046824335856309092523

theorem tailTrace_5614896 : CollatzResearch.WordTrace tailWord_5614896 prefixEnd_5614896 961046824335856309092523 := by
  unfold tailWord_5614896
  simp only [CollatzResearch.WordTrace]
  refine ⟨102396040733099107368084271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136528054310798809824112361 102396040733099107368084271)
  ·
    refine ⟨153594061099648661052126407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102396040733099107368084271 153594061099648661052126407)
    ·
      refine ⟨230391091649472991578189611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153594061099648661052126407 230391091649472991578189611)
      ·
        refine ⟨345586637474209487367284417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230391091649472991578189611 345586637474209487367284417)
        ·
          refine ⟨259189978105657115525463313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345586637474209487367284417 259189978105657115525463313)
          ·
            refine ⟨194392483579242836644097485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259189978105657115525463313 194392483579242836644097485)
            ·
              refine ⟨72897181342216063741536557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194392483579242836644097485 72897181342216063741536557)
              ·
                refine ⟨27336443003331023903076209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72897181342216063741536557 27336443003331023903076209)
                ·
                  refine ⟨20502332252498267927307157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27336443003331023903076209 20502332252498267927307157)
                  ·
                    refine ⟨961046824335856309092523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20502332252498267927307157 961046824335856309092523)
                    ·
                      rfl

theorem cell23_5614896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 3, 2, 6].length) (baseStart_5614896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614896 prefixEnd_5614896 := by exact prefixLift 5614896
  have htrace : WordTrace (prefixWord ++ tailWord_5614896) baseStart_5614896 baseEnd_5614896 := by
    simpa [prefixWord, tailWord_5614896, baseEnd_5614896] using wordTrace_append hprefix tailTrace_5614896
  have hstable : (prefixWord ++ tailWord_5614896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614896).length < 2 ^ (prefixWord ++ tailWord_5614896).sum := by decide
  have hdescent : baseEnd_5614896 < baseStart_5614896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614936 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_5614936 : Nat := 118140960795 + 5614936 * 2 ^ 59
def prefixEnd_5614936 : Nat := 4983230072969 + 3 ^ 40 * 5614936 * 2
def baseEnd_5614936 : Nat := 2883161012233748770777385

theorem tailTrace_5614936 : CollatzResearch.WordTrace tailWord_5614936 prefixEnd_5614936 2883161012233748770777385 := by
  unfold tailWord_5614936
  simp only [CollatzResearch.WordTrace]
  refine ⟨102396770193026650783812331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136529026924035534378416441 102396770193026650783812331)
  ·
    refine ⟨153595155289539976175718497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102396770193026650783812331 153595155289539976175718497)
    ·
      refine ⟨115196366467154982131788873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153595155289539976175718497 115196366467154982131788873)
      ·
        refine ⟨86397274850366236598841655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115196366467154982131788873 86397274850366236598841655)
        ·
          refine ⟨129595912275549354898262483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86397274850366236598841655 129595912275549354898262483)
          ·
            refine ⟨194393868413324032347393725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129595912275549354898262483 194393868413324032347393725)
            ·
              refine ⟨72897700654996512130272647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194393868413324032347393725 72897700654996512130272647)
              ·
                refine ⟨109346550982494768195408971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72897700654996512130272647 109346550982494768195408971)
                ·
                  refine ⟨164019826473742152293113457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109346550982494768195408971 164019826473742152293113457)
                  ·
                    refine ⟨123014869855306614219835093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 164019826473742152293113457 123014869855306614219835093)
                    ·
                      refine ⟨2883161012233748770777385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123014869855306614219835093 2883161012233748770777385)
                      ·
                        rfl

theorem cell23_5614936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_5614936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614936 prefixEnd_5614936 := by exact prefixLift 5614936
  have htrace : WordTrace (prefixWord ++ tailWord_5614936) baseStart_5614936 baseEnd_5614936 := by
    simpa [prefixWord, tailWord_5614936, baseEnd_5614936] using wordTrace_append hprefix tailTrace_5614936
  have hstable : (prefixWord ++ tailWord_5614936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614936).length < 2 ^ (prefixWord ++ tailWord_5614936).sum := by decide
  have hdescent : baseEnd_5614936 < baseStart_5614936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614958 : List Nat := [4, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2]
def baseStart_5614958 : Nat := 118140960795 + 5614958 * 2 ^ 59
def prefixEnd_5614958 : Nat := 4983230072969 + 3 ^ 40 * 5614958 * 2
def baseEnd_5614958 : Nat := 2883172308808147684702285

theorem tailTrace_5614958 : CollatzResearch.WordTrace tailWord_5614958 prefixEnd_5614958 2883172308808147684702285 := by
  unfold tailWord_5614958
  simp only [CollatzResearch.WordTrace]
  refine ⟨25599292848996699915615691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136529561861315732883283685 25599292848996699915615691)
  ·
    refine ⟨38398939273495049873423537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25599292848996699915615691 38398939273495049873423537)
    ·
      refine ⟨28799204455121287405067653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38398939273495049873423537 28799204455121287405067653)
      ·
        refine ⟨5399850835335241388450185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28799204455121287405067653 5399850835335241388450185)
        ·
          refine ⟨4049888126501431041337639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5399850835335241388450185 4049888126501431041337639)
          ·
            refine ⟨6074832189752146562006459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4049888126501431041337639 6074832189752146562006459)
            ·
              refine ⟨9112248284628219843009689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6074832189752146562006459 9112248284628219843009689)
              ·
                refine ⟨6834186213471164882257267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9112248284628219843009689 6834186213471164882257267)
                ·
                  refine ⟨10251279320206747323385901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6834186213471164882257267 10251279320206747323385901)
                  ·
                    refine ⟨3844229745077530246269713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10251279320206747323385901 3844229745077530246269713)
                    ·
                      refine ⟨2883172308808147684702285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3844229745077530246269713 2883172308808147684702285)
                      ·
                        rfl

theorem cell23_5614958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_5614958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614958 prefixEnd_5614958 := by exact prefixLift 5614958
  have htrace : WordTrace (prefixWord ++ tailWord_5614958) baseStart_5614958 baseEnd_5614958 := by
    simpa [prefixWord, tailWord_5614958, baseEnd_5614958] using wordTrace_append hprefix tailTrace_5614958
  have hstable : (prefixWord ++ tailWord_5614958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614958).length < 2 ^ (prefixWord ++ tailWord_5614958).sum := by decide
  have hdescent : baseEnd_5614958 < baseStart_5614958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614983 : List Nat := [1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_5614983 : Nat := 118140960795 + 5614983 * 2 ^ 59
def prefixEnd_5614983 : Nat := 4983230072969 + 3 ^ 40 * 5614983 * 2
def baseEnd_5614983 : Nat := 2883185145824510086889669

theorem tailTrace_5614983 : CollatzResearch.WordTrace tailWord_5614983 prefixEnd_5614983 2883185145824510086889669 := by
  unfold tailWord_5614983
  simp only [CollatzResearch.WordTrace]
  refine ⟨204795254616883028594585603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136530169744588685729723735 204795254616883028594585603)
  ·
    refine ⟨307192881925324542891878405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204795254616883028594585603 307192881925324542891878405)
    ·
      refine ⟨57598665360998351792227201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307192881925324542891878405 57598665360998351792227201)
      ·
        refine ⟨43198999020748763844170401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57598665360998351792227201 43198999020748763844170401)
        ·
          refine ⟨32399249265561572883127801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43198999020748763844170401 32399249265561572883127801)
          ·
            refine ⟨24299436949171179662345851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32399249265561572883127801 24299436949171179662345851)
            ·
              refine ⟨36449155423756769493518777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24299436949171179662345851 36449155423756769493518777)
              ·
                refine ⟨27336866567817577120139083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36449155423756769493518777 27336866567817577120139083)
                ·
                  refine ⟨41005299851726365680208625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27336866567817577120139083 41005299851726365680208625)
                  ·
                    refine ⟨30753974888794774260156469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41005299851726365680208625 30753974888794774260156469)
                    ·
                      refine ⟨2883185145824510086889669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30753974888794774260156469 2883185145824510086889669)
                      ·
                        rfl

theorem cell23_5614983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_5614983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614983 prefixEnd_5614983 := by exact prefixLift 5614983
  have htrace : WordTrace (prefixWord ++ tailWord_5614983) baseStart_5614983 baseEnd_5614983 := by
    simpa [prefixWord, tailWord_5614983, baseEnd_5614983] using wordTrace_append hprefix tailTrace_5614983
  have hstable : (prefixWord ++ tailWord_5614983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614983).length < 2 ^ (prefixWord ++ tailWord_5614983).sum := by decide
  have hdescent : baseEnd_5614983 < baseStart_5614983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5614994 : List Nat := [3, 2, 3, 3, 1, 1, 1, 4, 5]
def baseStart_5614994 : Nat := 118140960795 + 5614994 * 2 ^ 59
def prefixEnd_5614994 : Nat := 4983230072969 + 3 ^ 40 * 5614994 * 2
def baseEnd_5614994 : Nat := 320354532679078838205791

theorem tailTrace_5614994 : CollatzResearch.WordTrace tailWord_5614994 prefixEnd_5614994 320354532679078838205791 := by
  unfold tailWord_5614994
  simp only [CollatzResearch.WordTrace]
  refine ⟨51198913954960794368309009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136530437213228784982157357 51198913954960794368309009)
  ·
    refine ⟨38399185466220595776231757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51198913954960794368309009 38399185466220595776231757)
    ·
      refine ⟨14399694549832723416086909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38399185466220595776231757 14399694549832723416086909)
      ·
        refine ⟨5399885456187271281032591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14399694549832723416086909 5399885456187271281032591)
        ·
          refine ⟨8099828184280906921548887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5399885456187271281032591 8099828184280906921548887)
          ·
            refine ⟨12149742276421360382323331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8099828184280906921548887 12149742276421360382323331)
            ·
              refine ⟨18224613414632040573484997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12149742276421360382323331 18224613414632040573484997)
              ·
                refine ⟨3417115015243507607528437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18224613414632040573484997 3417115015243507607528437)
                ·
                  refine ⟨320354532679078838205791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3417115015243507607528437 320354532679078838205791)
                  ·
                    rfl

theorem cell23_5614994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_5614994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5614994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5614994 prefixEnd_5614994 := by exact prefixLift 5614994
  have htrace : WordTrace (prefixWord ++ tailWord_5614994) baseStart_5614994 baseEnd_5614994 := by
    simpa [prefixWord, tailWord_5614994, baseEnd_5614994] using wordTrace_append hprefix tailTrace_5614994
  have hstable : (prefixWord ++ tailWord_5614994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5614994).length < 2 ^ (prefixWord ++ tailWord_5614994).sum := by decide
  have hdescent : baseEnd_5614994 < baseStart_5614994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5614994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615050 : List Nat := [3, 1, 2, 1, 2, 3, 3, 2, 6]
def baseStart_5615050 : Nat := 118140960795 + 5615050 * 2 ^ 59
def prefixEnd_5615050 : Nat := 4983230072969 + 3 ^ 40 * 5615050 * 2
def baseEnd_5615050 : Nat := 320357727669817924972429

theorem tailTrace_5615050 : CollatzResearch.WordTrace tailWord_5615050 prefixEnd_5615050 320357727669817924972429 := by
  unfold tailWord_5615050
  simp only [CollatzResearch.WordTrace]
  refine ⟨51199424576910074759318651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136531798871760199358183069 51199424576910074759318651)
  ·
    refine ⟨76799136865365112138977977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51199424576910074759318651 76799136865365112138977977)
    ·
      refine ⟨57599352649023834104233483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76799136865365112138977977 57599352649023834104233483)
      ·
        refine ⟨86399028973535751156350225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57599352649023834104233483 86399028973535751156350225)
        ·
          refine ⟨64799271730151813367262669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86399028973535751156350225 64799271730151813367262669)
          ·
            refine ⟨24299726898806930012723501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64799271730151813367262669 24299726898806930012723501)
            ·
              refine ⟨9112397587052598754771313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24299726898806930012723501 9112397587052598754771313)
              ·
                refine ⟨6834298190289449066078485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9112397587052598754771313 6834298190289449066078485)
                ·
                  refine ⟨320357727669817924972429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6834298190289449066078485 320357727669817924972429)
                  ·
                    rfl

theorem cell23_5615050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_5615050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615050 prefixEnd_5615050 := by exact prefixLift 5615050
  have htrace : WordTrace (prefixWord ++ tailWord_5615050) baseStart_5615050 baseEnd_5615050 := by
    simpa [prefixWord, tailWord_5615050, baseEnd_5615050] using wordTrace_append hprefix tailTrace_5615050
  have hstable : (prefixWord ++ tailWord_5615050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615050).length < 2 ^ (prefixWord ++ tailWord_5615050).sum := by decide
  have hdescent : baseEnd_5615050 < baseStart_5615050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615063 : List Nat := [1, 1, 3, 2, 1, 1, 1, 3, 5, 5]
def baseStart_5615063 : Nat := 118140960795 + 5615063 * 2 ^ 59
def prefixEnd_5615063 : Nat := 4983230072969 + 3 ^ 40 * 5615063 * 2
def baseEnd_5615063 : Nat := 961075408092289924629767

theorem tailTrace_5615063 : CollatzResearch.WordTrace tailWord_5615063 prefixEnd_5615063 961075408092289924629767 := by
  unfold tailWord_5615063
  simp only [CollatzResearch.WordTrace]
  refine ⟨204798172456593202257497843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136532114971062134838331895 204798172456593202257497843)
  ·
    refine ⟨307197258684889803386246765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204798172456593202257497843 307197258684889803386246765)
    ·
      refine ⟨115198972006833676269842537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307197258684889803386246765 115198972006833676269842537)
      ·
        refine ⟨86399229005125257202381903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115198972006833676269842537 86399229005125257202381903)
        ·
          refine ⟨129598843507687885803572855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86399229005125257202381903 129598843507687885803572855)
          ·
            refine ⟨194398265261531828705359283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129598843507687885803572855 194398265261531828705359283)
            ·
              refine ⟨291597397892297743058038925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194398265261531828705359283 291597397892297743058038925)
              ·
                refine ⟨109349024209611653646764597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291597397892297743058038925 109349024209611653646764597)
                ·
                  refine ⟨10251471019651092529384181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 109349024209611653646764597 10251471019651092529384181)
                  ·
                    refine ⟨961075408092289924629767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10251471019651092529384181 961075408092289924629767)
                    ·
                      rfl

theorem cell23_5615063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_5615063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615063 prefixEnd_5615063 := by exact prefixLift 5615063
  have htrace : WordTrace (prefixWord ++ tailWord_5615063) baseStart_5615063 baseEnd_5615063 := by
    simpa [prefixWord, tailWord_5615063, baseEnd_5615063] using wordTrace_append hprefix tailTrace_5615063
  have hstable : (prefixWord ++ tailWord_5615063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615063).length < 2 ^ (prefixWord ++ tailWord_5615063).sum := by decide
  have hdescent : baseEnd_5615063 < baseStart_5615063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615113 : List Nat := [1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 6]
def baseStart_5615113 : Nat := 118140960795 + 5615113 * 2 ^ 59
def prefixEnd_5615113 : Nat := 4983230072969 + 3 ^ 40 * 5615113 * 2
def baseEnd_5615113 : Nat := 2883251898309594578264071

theorem tailTrace_5615113 : CollatzResearch.WordTrace tailWord_5615113 prefixEnd_5615113 2883251898309594578264071 := by
  unfold tailWord_5615113
  simp only [CollatzResearch.WordTrace]
  refine ⟨204799996106412060796817993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136533330737608040531211995 204799996106412060796817993)
  ·
    refine ⟨153599997079809045597613495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204799996106412060796817993 153599997079809045597613495)
    ·
      refine ⟨230399995619713568396420243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153599997079809045597613495 230399995619713568396420243)
      ·
        refine ⟨345599993429570352594630365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230399995619713568396420243 345599993429570352594630365)
        ·
          refine ⟨129599997536088882222986387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345599993429570352594630365 129599997536088882222986387)
          ·
            refine ⟨194399996304133323334479581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129599997536088882222986387 194399996304133323334479581)
            ·
              refine ⟨72899998614049996250429843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194399996304133323334479581 72899998614049996250429843)
              ·
                refine ⟨109349997921074994375644765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72899998614049996250429843 109349997921074994375644765)
                ·
                  refine ⟨41006249220403122890866787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109349997921074994375644765 41006249220403122890866787)
                  ·
                    refine ⟨61509373830604684336300181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41006249220403122890866787 61509373830604684336300181)
                    ·
                      refine ⟨2883251898309594578264071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61509373830604684336300181 2883251898309594578264071)
                      ·
                        rfl

theorem cell23_5615113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_5615113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615113 prefixEnd_5615113 := by exact prefixLift 5615113
  have htrace : WordTrace (prefixWord ++ tailWord_5615113) baseStart_5615113 baseEnd_5615113 := by
    simpa [prefixWord, tailWord_5615113, baseEnd_5615113] using wordTrace_append hprefix tailTrace_5615113
  have hstable : (prefixWord ++ tailWord_5615113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615113).length < 2 ^ (prefixWord ++ tailWord_5615113).sum := by decide
  have hdescent : baseEnd_5615113 < baseStart_5615113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615123 : List Nat := [1, 1, 1, 2, 1, 6, 1, 10]
def baseStart_5615123 : Nat := 118140960795 + 5615123 * 2 ^ 59
def prefixEnd_5615123 : Nat := 4983230072969 + 3 ^ 40 * 5615123 * 2
def baseEnd_5615123 : Nat := 106787297522819982931075

theorem tailTrace_5615123 : CollatzResearch.WordTrace tailWord_5615123 prefixEnd_5615123 106787297522819982931075 := by
  unfold tailWord_5615123
  simp only [CollatzResearch.WordTrace]
  refine ⟨204800360836375832504682023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136533573890917221669788015 204800360836375832504682023)
  ·
    refine ⟨307200541254563748757023035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204800360836375832504682023 307200541254563748757023035)
    ·
      refine ⟨460800811881845623135534553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307200541254563748757023035 460800811881845623135534553)
      ·
        refine ⟨345600608911384217351650915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460800811881845623135534553 345600608911384217351650915)
        ·
          refine ⟨518400913367076326027476373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345600608911384217351650915 518400913367076326027476373)
          ·
            refine ⟨24300042814081702782537955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 518400913367076326027476373 24300042814081702782537955)
            ·
              refine ⟨36450064221122554173806933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24300042814081702782537955 36450064221122554173806933)
              ·
                refine ⟨106787297522819982931075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 36450064221122554173806933 106787297522819982931075)
                ·
                  rfl

theorem cell23_5615123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 1, 10].length) (baseStart_5615123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615123 prefixEnd_5615123 := by exact prefixLift 5615123
  have htrace : WordTrace (prefixWord ++ tailWord_5615123) baseStart_5615123 baseEnd_5615123 := by
    simpa [prefixWord, tailWord_5615123, baseEnd_5615123] using wordTrace_append hprefix tailTrace_5615123
  have hstable : (prefixWord ++ tailWord_5615123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615123).length < 2 ^ (prefixWord ++ tailWord_5615123).sum := by decide
  have hdescent : baseEnd_5615123 < baseStart_5615123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615130 : List Nat := [3, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4]
def baseStart_5615130 : Nat := 118140960795 + 5615130 * 2 ^ 59
def prefixEnd_5615130 : Nat := 4983230072969 + 3 ^ 40 * 5615130 * 2
def baseEnd_5615130 : Nat := 2883260627480721011751493

theorem tailTrace_5615130 : CollatzResearch.WordTrace tailWord_5615130 prefixEnd_5615130 2883260627480721011751493 := by
  unfold tailWord_5615130
  simp only [CollatzResearch.WordTrace]
  refine ⟨51200154036837618175046711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136533744098233648466791229 51200154036837618175046711)
  ·
    refine ⟨76800231055256427262570067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51200154036837618175046711 76800231055256427262570067)
    ·
      refine ⟨115200346582884640893855101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76800231055256427262570067 115200346582884640893855101)
      ·
        refine ⟨43200129968581740335195663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115200346582884640893855101 43200129968581740335195663)
        ·
          refine ⟨64800194952872610502793495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43200129968581740335195663 64800194952872610502793495)
          ·
            refine ⟨97200292429308915754190243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64800194952872610502793495 97200292429308915754190243)
            ·
              refine ⟨145800438643963373631285365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97200292429308915754190243 145800438643963373631285365)
              ·
                refine ⟨13668791122871566277933003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145800438643963373631285365 13668791122871566277933003)
                ·
                  refine ⟨20503186684307349416899505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13668791122871566277933003 20503186684307349416899505)
                  ·
                    refine ⟨15377390013230512062674629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20503186684307349416899505 15377390013230512062674629)
                    ·
                      refine ⟨2883260627480721011751493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15377390013230512062674629 2883260627480721011751493)
                      ·
                        rfl

theorem cell23_5615130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_5615130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615130 prefixEnd_5615130 := by exact prefixLift 5615130
  have htrace : WordTrace (prefixWord ++ tailWord_5615130) baseStart_5615130 baseEnd_5615130 := by
    simpa [prefixWord, tailWord_5615130, baseEnd_5615130] using wordTrace_append hprefix tailTrace_5615130
  have hstable : (prefixWord ++ tailWord_5615130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615130).length < 2 ^ (prefixWord ++ tailWord_5615130).sum := by decide
  have hdescent : baseEnd_5615130 < baseStart_5615130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615137 : List Nat := [1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_5615137 : Nat := 118140960795 + 5615137 * 2 ^ 59
def prefixEnd_5615137 : Nat := 4983230072969 + 3 ^ 40 * 5615137 * 2
def baseEnd_5615137 : Nat := 2883264221845302484363961

theorem tailTrace_5615137 : CollatzResearch.WordTrace tailWord_5615137 prefixEnd_5615137 2883264221845302484363961 := by
  unfold tailWord_5615137
  simp only [CollatzResearch.WordTrace]
  refine ⟨204800871458325112895691665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136533914305550075263794443 204800871458325112895691665)
  ·
    refine ⟨153600653593743834671768749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204800871458325112895691665 153600653593743834671768749)
    ·
      refine ⟨57600245097653938001913281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153600653593743834671768749 57600245097653938001913281)
      ·
        refine ⟨43200183823240453501434961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57600245097653938001913281 43200183823240453501434961)
        ·
          refine ⟨32400137867430340126076221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43200183823240453501434961 32400137867430340126076221)
          ·
            refine ⟨12150051700286377547278583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32400137867430340126076221 12150051700286377547278583)
            ·
              refine ⟨18225077550429566320917875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12150051700286377547278583 18225077550429566320917875)
              ·
                refine ⟨27337616325644349481376813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18225077550429566320917875 27337616325644349481376813)
                ·
                  refine ⟨10251606122116631055516305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27337616325644349481376813 10251606122116631055516305)
                  ·
                    refine ⟨7688704591587473291637229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10251606122116631055516305 7688704591587473291637229)
                    ·
                      refine ⟨2883264221845302484363961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7688704591587473291637229 2883264221845302484363961)
                      ·
                        rfl

theorem cell23_5615137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_5615137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615137 prefixEnd_5615137 := by exact prefixLift 5615137
  have htrace : WordTrace (prefixWord ++ tailWord_5615137) baseStart_5615137 baseEnd_5615137 := by
    simpa [prefixWord, tailWord_5615137, baseEnd_5615137] using wordTrace_append hprefix tailTrace_5615137
  have hstable : (prefixWord ++ tailWord_5615137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615137).length < 2 ^ (prefixWord ++ tailWord_5615137).sum := by decide
  have hdescent : baseEnd_5615137 < baseStart_5615137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615264 : List Nat := [2, 1, 1, 4, 3, 1, 3, 3, 5]
def baseStart_5615264 : Nat := 118140960795 + 5615264 * 2 ^ 59
def prefixEnd_5615264 : Nat := 4983230072969 + 3 ^ 40 * 5615264 * 2
def baseEnd_5615264 : Nat := 320369937098713720830653

theorem tailTrace_5615264 : CollatzResearch.WordTrace tailWord_5615264 prefixEnd_5615264 320369937098713720830653 := by
  unfold tailWord_5615264
  simp only [CollatzResearch.WordTrace]
  refine ⟨102402751764432506792782423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136537002352576675723709897 102402751764432506792782423)
  ·
    refine ⟨153604127646648760189173635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102402751764432506792782423 153604127646648760189173635)
    ·
      refine ⟨230406191469973140283760453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153604127646648760189173635 230406191469973140283760453)
      ·
        refine ⟨43201160900619963803205085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230406191469973140283760453 43201160900619963803205085)
        ·
          refine ⟨16200435337732486426201907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43201160900619963803205085 16200435337732486426201907)
          ·
            refine ⟨24300653006598729639302861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16200435337732486426201907 24300653006598729639302861)
            ·
              refine ⟨9112744877474523614738573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24300653006598729639302861 9112744877474523614738573)
              ·
                refine ⟨3417279329052946355526965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9112744877474523614738573 3417279329052946355526965)
                ·
                  refine ⟨320369937098713720830653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3417279329052946355526965 320369937098713720830653)
                  ·
                    rfl

theorem cell23_5615264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 5].length) (baseStart_5615264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615264 prefixEnd_5615264 := by exact prefixLift 5615264
  have htrace : WordTrace (prefixWord ++ tailWord_5615264) baseStart_5615264 baseEnd_5615264 := by
    simpa [prefixWord, tailWord_5615264, baseEnd_5615264] using wordTrace_append hprefix tailTrace_5615264
  have hstable : (prefixWord ++ tailWord_5615264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615264).length < 2 ^ (prefixWord ++ tailWord_5615264).sum := by decide
  have hdescent : baseEnd_5615264 < baseStart_5615264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615287 : List Nat := [1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_5615287 : Nat := 118140960795 + 5615287 * 2 ^ 59
def prefixEnd_5615287 : Nat := 4983230072969 + 3 ^ 40 * 5615287 * 2
def baseEnd_5615287 : Nat := 2883341243943476897488271

theorem tailTrace_5615287 : CollatzResearch.WordTrace tailWord_5615287 prefixEnd_5615287 2883341243943476897488271 := by
  unfold tailWord_5615287
  simp only [CollatzResearch.WordTrace]
  refine ⟨204806342407781688513652115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136537561605187792342434743 204806342407781688513652115)
  ·
    refine ⟨307209513611672532770478173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204806342407781688513652115 307209513611672532770478173)
    ·
      refine ⟨115203567604377199788929315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307209513611672532770478173 115203567604377199788929315)
      ·
        refine ⟨172805351406565799683393973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115203567604377199788929315 172805351406565799683393973)
        ·
          refine ⟨16200501694365543720318185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172805351406565799683393973 16200501694365543720318185)
          ·
            refine ⟨12150376270774157790238639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16200501694365543720318185 12150376270774157790238639)
            ·
              refine ⟨18225564406161236685357959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12150376270774157790238639 18225564406161236685357959)
              ·
                refine ⟨27338346609241855028036939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18225564406161236685357959 27338346609241855028036939)
                ·
                  refine ⟨41007519913862782542055409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27338346609241855028036939 41007519913862782542055409)
                  ·
                    refine ⟨30755639935397086906541557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41007519913862782542055409 30755639935397086906541557)
                    ·
                      refine ⟨2883341243943476897488271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30755639935397086906541557 2883341243943476897488271)
                      ·
                        rfl

theorem cell23_5615287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_5615287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615287 prefixEnd_5615287 := by exact prefixLift 5615287
  have htrace : WordTrace (prefixWord ++ tailWord_5615287) baseStart_5615287 baseEnd_5615287 := by
    simpa [prefixWord, tailWord_5615287, baseEnd_5615287] using wordTrace_append hprefix tailTrace_5615287
  have hstable : (prefixWord ++ tailWord_5615287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615287).length < 2 ^ (prefixWord ++ tailWord_5615287).sum := by decide
  have hdescent : baseEnd_5615287 < baseStart_5615287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615307 : List Nat := [1, 1, 1, 1, 3, 2, 1, 6, 3, 4]
def baseStart_5615307 : Nat := 118140960795 + 5615307 * 2 ^ 59
def prefixEnd_5615307 : Nat := 4983230072969 + 3 ^ 40 * 5615307 * 2
def baseEnd_5615307 : Nat := 961117171185522273079393

theorem tailTrace_5615307 : CollatzResearch.WordTrace tailWord_5615307 prefixEnd_5615307 961117171185522273079393 := by
  unfold tailWord_5615307
  simp only [CollatzResearch.WordTrace]
  refine ⟨204807071867709231929380175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136538047911806154619586783 204807071867709231929380175)
  ·
    refine ⟨307210607801563847894070263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204807071867709231929380175 307210607801563847894070263)
    ·
      refine ⟨460815911702345771841105395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307210607801563847894070263 460815911702345771841105395)
      ·
        refine ⟨691223867553518657761658093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460815911702345771841105395 691223867553518657761658093)
        ·
          refine ⟨259208950332569496660621785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 691223867553518657761658093 259208950332569496660621785)
          ·
            refine ⟨194406712749427122495466339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259208950332569496660621785 194406712749427122495466339)
            ·
              refine ⟨291610069124140683743199509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194406712749427122495466339 291610069124140683743199509)
              ·
                refine ⟨13669221990194094550462477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291610069124140683743199509 13669221990194094550462477)
                ·
                  refine ⟨5125958246322785456423429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13669221990194094550462477 5125958246322785456423429)
                  ·
                    refine ⟨961117171185522273079393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5125958246322785456423429 961117171185522273079393)
                    ·
                      rfl

theorem cell23_5615307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 3, 4].length) (baseStart_5615307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615307 prefixEnd_5615307 := by exact prefixLift 5615307
  have htrace : WordTrace (prefixWord ++ tailWord_5615307) baseStart_5615307 baseEnd_5615307 := by
    simpa [prefixWord, tailWord_5615307, baseEnd_5615307] using wordTrace_append hprefix tailTrace_5615307
  have hstable : (prefixWord ++ tailWord_5615307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615307).length < 2 ^ (prefixWord ++ tailWord_5615307).sum := by decide
  have hdescent : baseEnd_5615307 < baseStart_5615307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615314 : List Nat := [3, 2, 2, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_5615314 : Nat := 118140960795 + 5615314 * 2 ^ 59
def prefixEnd_5615314 : Nat := 4983230072969 + 3 ^ 40 * 5615314 * 2
def baseEnd_5615314 : Nat := 2883355107921148291850647

theorem tailTrace_5615314 : CollatzResearch.WordTrace tailWord_5615314 prefixEnd_5615314 2883355107921148291850647 := by
  unfold tailWord_5615314
  simp only [CollatzResearch.WordTrace]
  refine ⟨51201831794670968031221249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136538218119122581416589997 51201831794670968031221249)
  ·
    refine ⟨38401373846003226023415937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51201831794670968031221249 38401373846003226023415937)
    ·
      refine ⟨28801030384502419517561953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38401373846003226023415937 28801030384502419517561953)
      ·
        refine ⟨21600772788376814638171465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28801030384502419517561953 21600772788376814638171465)
        ·
          refine ⟨16200579591282610978628599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21600772788376814638171465 16200579591282610978628599)
          ·
            refine ⟨24300869386923916467942899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16200579591282610978628599 24300869386923916467942899)
            ·
              refine ⟨36451304080385874701914349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24300869386923916467942899 36451304080385874701914349)
              ·
                refine ⟨13669239030144703013217881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36451304080385874701914349 13669239030144703013217881)
                ·
                  refine ⟨10251929272608527259913411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13669239030144703013217881 10251929272608527259913411)
                  ·
                    refine ⟨15377893908912790889870117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10251929272608527259913411 15377893908912790889870117)
                    ·
                      refine ⟨2883355107921148291850647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15377893908912790889870117 2883355107921148291850647)
                      ·
                        rfl

theorem cell23_5615314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_5615314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615314 prefixEnd_5615314 := by exact prefixLift 5615314
  have htrace : WordTrace (prefixWord ++ tailWord_5615314) baseStart_5615314 baseEnd_5615314 := by
    simpa [prefixWord, tailWord_5615314, baseEnd_5615314] using wordTrace_append hprefix tailTrace_5615314
  have hstable : (prefixWord ++ tailWord_5615314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615314).length < 2 ^ (prefixWord ++ tailWord_5615314).sum := by decide
  have hdescent : baseEnd_5615314 < baseStart_5615314 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615348 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 1, 6, 2]
def baseStart_5615348 : Nat := 118140960795 + 5615348 * 2 ^ 59
def prefixEnd_5615348 : Nat := 4983230072969 + 3 ^ 40 * 5615348 * 2
def baseEnd_5615348 : Nat := 2883372566263401158825491

theorem tailTrace_5615348 : CollatzResearch.WordTrace tailWord_5615348 prefixEnd_5615348 2883372566263401158825491 := by
  unfold tailWord_5615348
  simp only [CollatzResearch.WordTrace]
  refine ⟨102404283630280347965811349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136539044840373797287748465 102404283630280347965811349)
  ·
    refine ⟨4800200795169391310897407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 102404283630280347965811349 4800200795169391310897407)
    ·
      refine ⟨7200301192754086966346111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4800200795169391310897407 7200301192754086966346111)
      ·
        refine ⟨10800451789131130449519167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7200301192754086966346111 10800451789131130449519167)
        ·
          refine ⟨16200677683696695674278751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10800451789131130449519167 16200677683696695674278751)
          ·
            refine ⟨24301016525545043511418127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16200677683696695674278751 24301016525545043511418127)
            ·
              refine ⟨36451524788317565267127191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24301016525545043511418127 36451524788317565267127191)
              ·
                refine ⟨54677287182476347900690787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36451524788317565267127191 54677287182476347900690787)
                ·
                  refine ⟨82015930773714521851036181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54677287182476347900690787 82015930773714521851036181)
                  ·
                    refine ⟨3844496755017868211767321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82015930773714521851036181 3844496755017868211767321)
                    ·
                      refine ⟨2883372566263401158825491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3844496755017868211767321 2883372566263401158825491)
                      ·
                        rfl

theorem cell23_5615348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 1, 6, 2].length) (baseStart_5615348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615348 prefixEnd_5615348 := by exact prefixLift 5615348
  have htrace : WordTrace (prefixWord ++ tailWord_5615348) baseStart_5615348 baseEnd_5615348 := by
    simpa [prefixWord, tailWord_5615348, baseEnd_5615348] using wordTrace_append hprefix tailTrace_5615348
  have hstable : (prefixWord ++ tailWord_5615348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615348).length < 2 ^ (prefixWord ++ tailWord_5615348).sum := by decide
  have hdescent : baseEnd_5615348 < baseStart_5615348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615407 : List Nat := [1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 5]
def baseStart_5615407 : Nat := 118140960795 + 5615407 * 2 ^ 59
def prefixEnd_5615407 : Nat := 4983230072969 + 3 ^ 40 * 5615407 * 2
def baseEnd_5615407 : Nat := 2883402861622016427987719

theorem tailTrace_5615407 : CollatzResearch.WordTrace tailWord_5615407 prefixEnd_5615407 2883402861622016427987719 := by
  unfold tailWord_5615407
  simp only [CollatzResearch.WordTrace]
  refine ⟨204810719167346949008020475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136540479444897966005346983 204810719167346949008020475)
  ·
    refine ⟨307216078751020423512030713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204810719167346949008020475 307216078751020423512030713)
    ·
      refine ⟨230412059063265317634023035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307216078751020423512030713 230412059063265317634023035)
      ·
        refine ⟨345618088594897976451034553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230412059063265317634023035 345618088594897976451034553)
        ·
          refine ⟨259213566446173482338275915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345618088594897976451034553 259213566446173482338275915)
          ·
            refine ⟨388820349669260223507413873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259213566446173482338275915 388820349669260223507413873)
            ·
              refine ⟨291615262251945167630560405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388820349669260223507413873 291615262251945167630560405)
              ·
                refine ⟨13669465418059929732682519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291615262251945167630560405 13669465418059929732682519)
                ·
                  refine ⟨20504198127089894599023779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13669465418059929732682519 20504198127089894599023779)
                  ·
                    refine ⟨30756297190634841898535669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20504198127089894599023779 30756297190634841898535669)
                    ·
                      refine ⟨2883402861622016427987719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30756297190634841898535669 2883402861622016427987719)
                      ·
                        rfl

theorem cell23_5615407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_5615407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615407 prefixEnd_5615407 := by exact prefixLift 5615407
  have htrace : WordTrace (prefixWord ++ tailWord_5615407) baseStart_5615407 baseEnd_5615407 := by
    simpa [prefixWord, tailWord_5615407, baseEnd_5615407] using wordTrace_append hprefix tailTrace_5615407
  have hstable : (prefixWord ++ tailWord_5615407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615407).length < 2 ^ (prefixWord ++ tailWord_5615407).sum := by decide
  have hdescent : baseEnd_5615407 < baseStart_5615407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615421 : List Nat := [1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 4]
def baseStart_5615421 : Nat := 118140960795 + 5615421 * 2 ^ 59
def prefixEnd_5615421 : Nat := 4983230072969 + 3 ^ 40 * 5615421 * 2
def baseEnd_5615421 : Nat := 2883410050351179373212655

theorem tailTrace_5615421 : CollatzResearch.WordTrace tailWord_5615421 prefixEnd_5615421 2883410050351179373212655 := by
  unfold tailWord_5615421
  simp only [CollatzResearch.WordTrace]
  refine ⟨204811229789296229399030117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136540819859530819599353411 204811229789296229399030117)
  ·
    refine ⟨38402105585493043012318147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204811229789296229399030117 38402105585493043012318147)
    ·
      refine ⟨57603158378239564518477221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38402105585493043012318147 57603158378239564518477221)
      ·
        refine ⟨10800592195919918347214479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57603158378239564518477221 10800592195919918347214479)
        ·
          refine ⟨16200888293879877520821719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10800592195919918347214479 16200888293879877520821719)
          ·
            refine ⟨24301332440819816281232579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16200888293879877520821719 24301332440819816281232579)
            ·
              refine ⟨36451998661229724421848869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24301332440819816281232579 36451998661229724421848869)
              ·
                refine ⟨6834749748980573329096663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36451998661229724421848869 6834749748980573329096663)
                ·
                  refine ⟨10252124623470859993644995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6834749748980573329096663 10252124623470859993644995)
                  ·
                    refine ⟨15378186935206289990467493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10252124623470859993644995 15378186935206289990467493)
                    ·
                      refine ⟨2883410050351179373212655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15378186935206289990467493 2883410050351179373212655)
                      ·
                        rfl

theorem cell23_5615421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_5615421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615421 prefixEnd_5615421 := by exact prefixLift 5615421
  have htrace : WordTrace (prefixWord ++ tailWord_5615421) baseStart_5615421 baseEnd_5615421 := by
    simpa [prefixWord, tailWord_5615421, baseEnd_5615421] using wordTrace_append hprefix tailTrace_5615421
  have hstable : (prefixWord ++ tailWord_5615421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615421).length < 2 ^ (prefixWord ++ tailWord_5615421).sum := by decide
  have hdescent : baseEnd_5615421 < baseStart_5615421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615427 : List Nat := [1, 1, 1, 3, 1, 6, 1, 9]
def baseStart_5615427 : Nat := 118140960795 + 5615427 * 2 ^ 59
def prefixEnd_5615427 : Nat := 4983230072969 + 3 ^ 40 * 5615427 * 2
def baseEnd_5615427 : Nat := 106793078934633568508801

theorem tailTrace_5615427 : CollatzResearch.WordTrace tailWord_5615427 prefixEnd_5615427 106793078934633568508801 := by
  unfold tailWord_5615427
  simp only [CollatzResearch.WordTrace]
  refine ⟨204811448627274492423748535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136540965751516328282499023 204811448627274492423748535)
  ·
    refine ⟨307217172940911738635622803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204811448627274492423748535 307217172940911738635622803)
    ·
      refine ⟨460825759411367607953434205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307217172940911738635622803 460825759411367607953434205)
      ·
        refine ⟨172809659779262852982537827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460825759411367607953434205 172809659779262852982537827)
        ·
          refine ⟨259214489668894279473806741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172809659779262852982537827 259214489668894279473806741)
          ·
            refine ⟨12150679203229419350334691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 259214489668894279473806741 12150679203229419350334691)
            ·
              refine ⟨18226018804844129025502037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12150679203229419350334691 18226018804844129025502037)
              ·
                refine ⟨106793078934633568508801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18226018804844129025502037 106793078934633568508801)
                ·
                  rfl

theorem cell23_5615427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 1, 9].length) (baseStart_5615427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615427 prefixEnd_5615427 := by exact prefixLift 5615427
  have htrace : WordTrace (prefixWord ++ tailWord_5615427) baseStart_5615427 baseEnd_5615427 := by
    simpa [prefixWord, tailWord_5615427, baseEnd_5615427] using wordTrace_append hprefix tailTrace_5615427
  have hstable : (prefixWord ++ tailWord_5615427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615427).length < 2 ^ (prefixWord ++ tailWord_5615427).sum := by decide
  have hdescent : baseEnd_5615427 < baseStart_5615427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615441 : List Nat := [1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 3]
def baseStart_5615441 : Nat := 118140960795 + 5615441 * 2 ^ 59
def prefixEnd_5615441 : Nat := 4983230072969 + 3 ^ 40 * 5615441 * 2
def baseEnd_5615441 : Nat := 2883420319964269294962563

theorem tailTrace_5615441 : CollatzResearch.WordTrace tailWord_5615441 prefixEnd_5615441 2883420319964269294962563 := by
  unfold tailWord_5615441
  simp only [CollatzResearch.WordTrace]
  refine ⟨204811959249223772814758177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136541306166149181876505451 204811959249223772814758177)
  ·
    refine ⟨153608969436917829611068633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204811959249223772814758177 153608969436917829611068633)
    ·
      refine ⟨115206727077688372208301475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153608969436917829611068633 115206727077688372208301475)
      ·
        refine ⟨172810090616532558312452213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115206727077688372208301475 172810090616532558312452213)
        ·
          refine ⟨16200945995299927341792395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 172810090616532558312452213 16200945995299927341792395)
          ·
            refine ⟨24301418992949891012688593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16200945995299927341792395 24301418992949891012688593)
            ·
              refine ⟨18226064244712418259516445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24301418992949891012688593 18226064244712418259516445)
              ·
                refine ⟨6834774091767156847318667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18226064244712418259516445 6834774091767156847318667)
                ·
                  refine ⟨10252161137650735270978001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6834774091767156847318667 10252161137650735270978001)
                  ·
                    refine ⟨7689120853238051453233501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10252161137650735270978001 7689120853238051453233501)
                    ·
                      refine ⟨2883420319964269294962563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7689120853238051453233501 2883420319964269294962563)
                      ·
                        rfl

theorem cell23_5615441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 3, 1, 2, 3].length) (baseStart_5615441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615441 prefixEnd_5615441 := by exact prefixLift 5615441
  have htrace : WordTrace (prefixWord ++ tailWord_5615441) baseStart_5615441 baseEnd_5615441 := by
    simpa [prefixWord, tailWord_5615441, baseEnd_5615441] using wordTrace_append hprefix tailTrace_5615441
  have hstable : (prefixWord ++ tailWord_5615441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615441).length < 2 ^ (prefixWord ++ tailWord_5615441).sum := by decide
  have hdescent : baseEnd_5615441 < baseStart_5615441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615444 : List Nat := [2, 4, 1, 1, 3, 3, 9]
def baseStart_5615444 : Nat := 118140960795 + 5615444 * 2 ^ 59
def prefixEnd_5615444 : Nat := 4983230072969 + 3 ^ 40 * 5615444 * 2
def baseEnd_5615444 : Nat := 35597800745755960286729

theorem tailTrace_5615444 : CollatzResearch.WordTrace tailWord_5615444 prefixEnd_5615444 35597800745755960286729 := by
  unfold tailWord_5615444
  simp only [CollatzResearch.WordTrace]
  refine ⟨102406034334106452163558693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136541379112141936218078257 102406034334106452163558693)
  ·
    refine ⟨19201131437644959780667255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102406034334106452163558693 19201131437644959780667255)
    ·
      refine ⟨28801697156467439671000883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19201131437644959780667255 28801697156467439671000883)
      ·
        refine ⟨43202545734701159506501325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28801697156467439671000883 43202545734701159506501325)
        ·
          refine ⟨16200954650512934814937997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43202545734701159506501325 16200954650512934814937997)
          ·
            refine ⟨6075357993942350555601749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16200954650512934814937997 6075357993942350555601749)
            ·
              refine ⟨35597800745755960286729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6075357993942350555601749 35597800745755960286729)
              ·
                rfl

theorem cell23_5615444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 9].length) (baseStart_5615444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615444 prefixEnd_5615444 := by exact prefixLift 5615444
  have htrace : WordTrace (prefixWord ++ tailWord_5615444) baseStart_5615444 baseEnd_5615444 := by
    simpa [prefixWord, tailWord_5615444, baseEnd_5615444] using wordTrace_append hprefix tailTrace_5615444
  have hstable : (prefixWord ++ tailWord_5615444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615444).length < 2 ^ (prefixWord ++ tailWord_5615444).sum := by decide
  have hdescent : baseEnd_5615444 < baseStart_5615444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615457 : List Nat := [1, 2, 3, 1, 1, 1, 4, 1, 2, 7]
def baseStart_5615457 : Nat := 118140960795 + 5615457 * 2 ^ 59
def prefixEnd_5615457 : Nat := 4983230072969 + 3 ^ 40 * 5615457 * 2
def baseEnd_5615457 : Nat := 961142845218247077454163

theorem tailTrace_5615457 : CollatzResearch.WordTrace tailWord_5615457 prefixEnd_5615457 961142845218247077454163 := by
  unfold tailWord_5615457
  simp only [CollatzResearch.WordTrace]
  refine ⟨204812542817165807547340625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136541695211443871698227083 204812542817165807547340625)
  ·
    refine ⟨153609407112874355660505469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204812542817165807547340625 153609407112874355660505469)
    ·
      refine ⟨57603527667327883372689551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153609407112874355660505469 57603527667327883372689551)
      ·
        refine ⟨86405291500991825059034327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57603527667327883372689551 86405291500991825059034327)
        ·
          refine ⟨129607937251487737588551491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86405291500991825059034327 129607937251487737588551491)
          ·
            refine ⟨194411905877231606382827237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129607937251487737588551491 194411905877231606382827237)
            ·
              refine ⟨36452232351980926196780107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 194411905877231606382827237 36452232351980926196780107)
              ·
                refine ⟨54678348527971389295170161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36452232351980926196780107 54678348527971389295170161)
                ·
                  refine ⟨41008761395978541971377621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54678348527971389295170161 41008761395978541971377621)
                  ·
                    refine ⟨961142845218247077454163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 41008761395978541971377621 961142845218247077454163)
                    ·
                      rfl

theorem cell23_5615457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_5615457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615457 prefixEnd_5615457 := by exact prefixLift 5615457
  have htrace : WordTrace (prefixWord ++ tailWord_5615457) baseStart_5615457 baseEnd_5615457 := by
    simpa [prefixWord, tailWord_5615457, baseEnd_5615457] using wordTrace_append hprefix tailTrace_5615457
  have hstable : (prefixWord ++ tailWord_5615457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615457).length < 2 ^ (prefixWord ++ tailWord_5615457).sum := by decide
  have hdescent : baseEnd_5615457 < baseStart_5615457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615481 : List Nat := [1, 2, 1, 3, 2, 2, 3, 1, 3, 3, 2]
def baseStart_5615481 : Nat := 118140960795 + 5615481 * 2 ^ 59
def prefixEnd_5615481 : Nat := 4983230072969 + 3 ^ 40 * 5615481 * 2
def baseEnd_5615481 : Nat := 2883440859190449138462379

theorem tailTrace_5615481 : CollatzResearch.WordTrace tailWord_5615481 prefixEnd_5615481 2883440859190449138462379 := by
  unfold tailWord_5615481
  simp only [CollatzResearch.WordTrace]
  refine ⟨204813418169078859646214297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136542278779385906430809531 204813418169078859646214297)
  ·
    refine ⟨153610063626809144734660723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204813418169078859646214297 153610063626809144734660723)
    ·
      refine ⟨230415095440213717101991085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153610063626809144734660723 230415095440213717101991085)
      ·
        refine ⟨86405660790080143913246657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230415095440213717101991085 86405660790080143913246657)
        ·
          refine ⟨64804245592560107934934993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86405660790080143913246657 64804245592560107934934993)
          ·
            refine ⟨48603184194420080951201245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64804245592560107934934993 48603184194420080951201245)
            ·
              refine ⟨18226194072907530356700467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48603184194420080951201245 18226194072907530356700467)
              ·
                refine ⟨27339291109361295535050701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18226194072907530356700467 27339291109361295535050701)
                ·
                  refine ⟨10252234166010485825644013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27339291109361295535050701 10252234166010485825644013)
                  ·
                    refine ⟨3844587812253932184616505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10252234166010485825644013 3844587812253932184616505)
                    ·
                      refine ⟨2883440859190449138462379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3844587812253932184616505 2883440859190449138462379)
                      ·
                        rfl

theorem cell23_5615481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_5615481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615481 prefixEnd_5615481 := by exact prefixLift 5615481
  have htrace : WordTrace (prefixWord ++ tailWord_5615481) baseStart_5615481 baseEnd_5615481 := by
    simpa [prefixWord, tailWord_5615481, baseEnd_5615481] using wordTrace_append hprefix tailTrace_5615481
  have hstable : (prefixWord ++ tailWord_5615481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615481).length < 2 ^ (prefixWord ++ tailWord_5615481).sum := by decide
  have hdescent : baseEnd_5615481 < baseStart_5615481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615487 : List Nat := [1, 1, 2, 2, 1, 1, 3, 2, 4, 6]
def baseStart_5615487 : Nat := 118140960795 + 5615487 * 2 ^ 59
def prefixEnd_5615487 : Nat := 4983230072969 + 3 ^ 40 * 5615487 * 2
def baseEnd_5615487 : Nat := 961147980024792038329117

theorem tailTrace_5615487 : CollatzResearch.WordTrace tailWord_5615487 prefixEnd_5615487 961147980024792038329117 := by
  unfold tailWord_5615487
  simp only [CollatzResearch.WordTrace]
  refine ⟨204813637007057122670932715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136542424671371415113955143 204813637007057122670932715)
  ·
    refine ⟨307220455510585684006399073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204813637007057122670932715 307220455510585684006399073)
    ·
      refine ⟨230415341632939263004799305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307220455510585684006399073 230415341632939263004799305)
      ·
        refine ⟨172811506224704447253599479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230415341632939263004799305 172811506224704447253599479)
        ·
          refine ⟨259217259337056670880399219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172811506224704447253599479 259217259337056670880399219)
          ·
            refine ⟨388825889005585006320598829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259217259337056670880399219 388825889005585006320598829)
            ·
              refine ⟨145809708377094377370224561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388825889005585006320598829 145809708377094377370224561)
              ·
                refine ⟨109357281282820783027668421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145809708377094377370224561 109357281282820783027668421)
                ·
                  refine ⟨20504490240528896817687829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 109357281282820783027668421 20504490240528896817687829)
                  ·
                    refine ⟨961147980024792038329117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20504490240528896817687829 961147980024792038329117)
                    ·
                      rfl

theorem cell23_5615487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 6].length) (baseStart_5615487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615487 prefixEnd_5615487 := by exact prefixLift 5615487
  have htrace : WordTrace (prefixWord ++ tailWord_5615487) baseStart_5615487 baseEnd_5615487 := by
    simpa [prefixWord, tailWord_5615487, baseEnd_5615487] using wordTrace_append hprefix tailTrace_5615487
  have hstable : (prefixWord ++ tailWord_5615487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615487).length < 2 ^ (prefixWord ++ tailWord_5615487).sum := by decide
  have hdescent : baseEnd_5615487 < baseStart_5615487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615521 : List Nat := [1, 2, 3, 4, 2, 1, 1, 1, 2, 6]
def baseStart_5615521 : Nat := 118140960795 + 5615521 * 2 ^ 59
def prefixEnd_5615521 : Nat := 4983230072969 + 3 ^ 40 * 5615521 * 2
def baseEnd_5615521 : Nat := 961153799472209660654065

theorem tailTrace_5615521 : CollatzResearch.WordTrace tailWord_5615521 prefixEnd_5615521 961153799472209660654065 := by
  unfold tailWord_5615521
  simp only [CollatzResearch.WordTrace]
  refine ⟨204814877088933946477670417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136543251392622630985113611 204814877088933946477670417)
  ·
    refine ⟨153611157816700459858252813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204814877088933946477670417 153611157816700459858252813)
    ·
      refine ⟨57604184181262672446844805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153611157816700459858252813 57604184181262672446844805)
      ·
        refine ⟨10800784533986751083783401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57604184181262672446844805 10800784533986751083783401)
        ·
          refine ⟨8100588400490063312837551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10800784533986751083783401 8100588400490063312837551)
          ·
            refine ⟨12150882600735094969256327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8100588400490063312837551 12150882600735094969256327)
            ·
              refine ⟨18226323901102642453884491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12150882600735094969256327 18226323901102642453884491)
              ·
                refine ⟨27339485851653963680826737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18226323901102642453884491 27339485851653963680826737)
                ·
                  refine ⟨20504614388740472760620053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27339485851653963680826737 20504614388740472760620053)
                  ·
                    refine ⟨961153799472209660654065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20504614388740472760620053 961153799472209660654065)
                    ·
                      rfl

theorem cell23_5615521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_5615521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615521 prefixEnd_5615521 := by exact prefixLift 5615521
  have htrace : WordTrace (prefixWord ++ tailWord_5615521) baseStart_5615521 baseEnd_5615521 := by
    simpa [prefixWord, tailWord_5615521, baseEnd_5615521] using wordTrace_append hprefix tailTrace_5615521
  have hstable : (prefixWord ++ tailWord_5615521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615521).length < 2 ^ (prefixWord ++ tailWord_5615521).sum := by decide
  have hdescent : baseEnd_5615521 < baseStart_5615521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615524 : List Nat := [2, 3, 1, 2, 1, 3, 1, 1, 1, 4, 4]
def baseStart_5615524 : Nat := 118140960795 + 5615524 * 2 ^ 59
def prefixEnd_5615524 : Nat := 4983230072969 + 3 ^ 40 * 5615524 * 2
def baseEnd_5615524 : Nat := 2883462938858592470224681

theorem tailTrace_5615524 : CollatzResearch.WordTrace tailWord_5615524 prefixEnd_5615524 2883462938858592470224681 := by
  unfold tailWord_5615524
  simp only [CollatzResearch.WordTrace]
  refine ⟨102407493253961538995014813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136543324338615385326686417 102407493253961538995014813)
  ·
    refine ⟨38402809970235577123130555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102407493253961538995014813 38402809970235577123130555)
    ·
      refine ⟨57604214955353365684695833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38402809970235577123130555 57604214955353365684695833)
      ·
        refine ⟨43203161216515024263521875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57604214955353365684695833 43203161216515024263521875)
        ·
          refine ⟨64804741824772536395282813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43203161216515024263521875 64804741824772536395282813)
          ·
            refine ⟨24301778184289701148231055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64804741824772536395282813 24301778184289701148231055)
            ·
              refine ⟨36452667276434551722346583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24301778184289701148231055 36452667276434551722346583)
              ·
                refine ⟨54679000914651827583519875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36452667276434551722346583 54679000914651827583519875)
                ·
                  refine ⟨82018501371977741375279813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54679000914651827583519875 82018501371977741375279813)
                  ·
                    refine ⟨15378469007245826507864965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82018501371977741375279813 15378469007245826507864965)
                    ·
                      refine ⟨2883462938858592470224681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15378469007245826507864965 2883462938858592470224681)
                      ·
                        rfl

theorem cell23_5615524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_5615524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615524 prefixEnd_5615524 := by exact prefixLift 5615524
  have htrace : WordTrace (prefixWord ++ tailWord_5615524) baseStart_5615524 baseEnd_5615524 := by
    simpa [prefixWord, tailWord_5615524, baseEnd_5615524] using wordTrace_append hprefix tailTrace_5615524
  have hstable : (prefixWord ++ tailWord_5615524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615524).length < 2 ^ (prefixWord ++ tailWord_5615524).sum := by decide
  have hdescent : baseEnd_5615524 < baseStart_5615524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615544 : List Nat := [2, 1, 2, 1, 2, 3, 1, 2, 1, 5, 3]
def baseStart_5615544 : Nat := 118140960795 + 5615544 * 2 ^ 59
def prefixEnd_5615544 : Nat := 4983230072969 + 3 ^ 40 * 5615544 * 2
def baseEnd_5615544 : Nat := 2883473208471682391974589

theorem tailTrace_5615544 : CollatzResearch.WordTrace tailWord_5615544 prefixEnd_5615544 2883473208471682391974589 := by
  unfold tailWord_5615544
  simp only [CollatzResearch.WordTrace]
  refine ⟨102407857983925310702878843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136543810645233747603838457 102407857983925310702878843)
  ·
    refine ⟨153611786975887966054318265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102407857983925310702878843 153611786975887966054318265)
    ·
      refine ⟨115208840231915974540738699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153611786975887966054318265 115208840231915974540738699)
      ·
        refine ⟨172813260347873961811108049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115208840231915974540738699 172813260347873961811108049)
        ·
          refine ⟨129609945260905471358331037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172813260347873961811108049 129609945260905471358331037)
          ·
            refine ⟨48603729472839551759374139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 129609945260905471358331037 48603729472839551759374139)
            ·
              refine ⟨72905594209259327639061209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48603729472839551759374139 72905594209259327639061209)
              ·
                refine ⟨54679195656944495729295907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72905594209259327639061209 54679195656944495729295907)
                ·
                  refine ⟨82018793485416743593943861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54679195656944495729295907 82018793485416743593943861)
                  ·
                    refine ⟨7689261889257819711932237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 82018793485416743593943861 7689261889257819711932237)
                    ·
                      refine ⟨2883473208471682391974589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7689261889257819711932237 2883473208471682391974589)
                      ·
                        rfl

theorem cell23_5615544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 5, 3].length) (baseStart_5615544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615544 prefixEnd_5615544 := by exact prefixLift 5615544
  have htrace : WordTrace (prefixWord ++ tailWord_5615544) baseStart_5615544 baseEnd_5615544 := by
    simpa [prefixWord, tailWord_5615544, baseEnd_5615544] using wordTrace_append hprefix tailTrace_5615544
  have hstable : (prefixWord ++ tailWord_5615544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615544).length < 2 ^ (prefixWord ++ tailWord_5615544).sum := by decide
  have hdescent : baseEnd_5615544 < baseStart_5615544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615551 : List Nat := [1, 1, 2, 2, 2, 1, 6, 3, 5]
def baseStart_5615551 : Nat := 118140960795 + 5615551 * 2 ^ 59
def prefixEnd_5615551 : Nat := 4983230072969 + 3 ^ 40 * 5615551 * 2
def baseEnd_5615551 : Nat := 320386311426251540509673

theorem tailTrace_5615551 : CollatzResearch.WordTrace tailWord_5615551 prefixEnd_5615551 320386311426251540509673 := by
  unfold tailWord_5615551
  simp only [CollatzResearch.WordTrace]
  refine ⟨204815971278825261601262507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136543980852550174400841671 204815971278825261601262507)
  ·
    refine ⟨307223956918237892401893761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204815971278825261601262507 307223956918237892401893761)
    ·
      refine ⟨230417967688678419301420321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307223956918237892401893761 230417967688678419301420321)
      ·
        refine ⟨172813475766508814476065241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230417967688678419301420321 172813475766508814476065241)
        ·
          refine ⟨129610106824881610857048931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172813475766508814476065241 129610106824881610857048931)
          ·
            refine ⟨194415160237322416285573397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129610106824881610857048931 194415160237322416285573397)
            ·
              refine ⟨9113210636124488263386253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 194415160237322416285573397 9113210636124488263386253)
              ·
                refine ⟨3417453988546683098769845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9113210636124488263386253 3417453988546683098769845)
                ·
                  refine ⟨320386311426251540509673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3417453988546683098769845 320386311426251540509673)
                  ·
                    rfl

theorem cell23_5615551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 6, 3, 5].length) (baseStart_5615551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615551 prefixEnd_5615551 := by exact prefixLift 5615551
  have htrace : WordTrace (prefixWord ++ tailWord_5615551) baseStart_5615551 baseEnd_5615551 := by
    simpa [prefixWord, tailWord_5615551, baseEnd_5615551] using wordTrace_append hprefix tailTrace_5615551
  have hstable : (prefixWord ++ tailWord_5615551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615551).length < 2 ^ (prefixWord ++ tailWord_5615551).sum := by decide
  have hdescent : baseEnd_5615551 < baseStart_5615551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615594 : List Nat := [3, 1, 3, 1, 2, 1, 1, 1, 2, 8]
def baseStart_5615594 : Nat := 118140960795 + 5615594 * 2 ^ 59
def prefixEnd_5615594 : Nat := 4983230072969 + 3 ^ 40 * 5615594 * 2
def baseEnd_5615594 : Nat := 961166294168135732116453

theorem tailTrace_5615594 : CollatzResearch.WordTrace tailWord_5615594 prefixEnd_5615594 961166294168135732116453 := by
  unfold tailWord_5615594
  simp only [CollatzResearch.WordTrace]
  refine ⟨51204384904417369986269459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136545026411779653296718557 51204384904417369986269459)
  ·
    refine ⟨76806577356626054979404189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51204384904417369986269459 76806577356626054979404189)
    ·
      refine ⟨28802466508734770617276571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76806577356626054979404189 28802466508734770617276571)
      ·
        refine ⟨43203699763102155925914857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28802466508734770617276571 43203699763102155925914857)
        ·
          refine ⟨32402774822326616944436143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43203699763102155925914857 32402774822326616944436143)
          ·
            refine ⟨48604162233489925416654215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32402774822326616944436143 48604162233489925416654215)
            ·
              refine ⟨72906243350234888124981323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48604162233489925416654215 72906243350234888124981323)
              ·
                refine ⟨109359365025352332187471985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72906243350234888124981323 109359365025352332187471985)
                ·
                  refine ⟨82019523769014249140603989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109359365025352332187471985 82019523769014249140603989)
                  ·
                    refine ⟨961166294168135732116453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 82019523769014249140603989 961166294168135732116453)
                    ·
                      rfl

theorem cell23_5615594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_5615594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615594 prefixEnd_5615594 := by exact prefixLift 5615594
  have htrace : WordTrace (prefixWord ++ tailWord_5615594) baseStart_5615594 baseEnd_5615594 := by
    simpa [prefixWord, tailWord_5615594, baseEnd_5615594] using wordTrace_append hprefix tailTrace_5615594
  have hstable : (prefixWord ++ tailWord_5615594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615594).length < 2 ^ (prefixWord ++ tailWord_5615594).sum := by decide
  have hdescent : baseEnd_5615594 < baseStart_5615594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615621 : List Nat := [1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 3]
def baseStart_5615621 : Nat := 118140960795 + 5615621 * 2 ^ 59
def prefixEnd_5615621 : Nat := 4983230072969 + 3 ^ 40 * 5615621 * 2
def baseEnd_5615621 : Nat := 2883512746482078590711735

theorem tailTrace_5615621 : CollatzResearch.WordTrace tailWord_5615621 prefixEnd_5615621 2883512746482078590711735 := by
  unfold tailWord_5615621
  simp only [CollatzResearch.WordTrace]
  refine ⟨204818524388571663556310717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136545682925714442370873811 204818524388571663556310717)
  ·
    refine ⟨76806946645714373833616519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204818524388571663556310717 76806946645714373833616519)
    ·
      refine ⟨115210419968571560750424779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76806946645714373833616519 115210419968571560750424779)
      ·
        refine ⟨172815629952857341125637169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115210419968571560750424779 172815629952857341125637169)
        ·
          refine ⟨129611722464643005844227877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172815629952857341125637169 129611722464643005844227877)
          ·
            refine ⟨24302197962120563595792727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129611722464643005844227877 24302197962120563595792727)
            ·
              refine ⟨36453296943180845393689091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24302197962120563595792727 36453296943180845393689091)
              ·
                refine ⟨54679945414771268090533637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36453296943180845393689091 54679945414771268090533637)
                ·
                  refine ⟨10252489765269612766975057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54679945414771268090533637 10252489765269612766975057)
                  ·
                    refine ⟨7689367323952209575231293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10252489765269612766975057 7689367323952209575231293)
                    ·
                      refine ⟨2883512746482078590711735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7689367323952209575231293 2883512746482078590711735)
                      ·
                        rfl

theorem cell23_5615621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 1, 4, 2, 3].length) (baseStart_5615621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615621 prefixEnd_5615621 := by exact prefixLift 5615621
  have htrace : WordTrace (prefixWord ++ tailWord_5615621) baseStart_5615621 baseEnd_5615621 := by
    simpa [prefixWord, tailWord_5615621, baseEnd_5615621] using wordTrace_append hprefix tailTrace_5615621
  have hstable : (prefixWord ++ tailWord_5615621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615621).length < 2 ^ (prefixWord ++ tailWord_5615621).sum := by decide
  have hdescent : baseEnd_5615621 < baseStart_5615621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615624 : List Nat := [2, 1, 3, 2, 1, 2, 1, 3, 8]
def baseStart_5615624 : Nat := 118140960795 + 5615624 * 2 ^ 59
def prefixEnd_5615624 : Nat := 4983230072969 + 3 ^ 40 * 5615624 * 2
def baseEnd_5615624 : Nat := 320390476324893564330469

theorem tailTrace_5615624 : CollatzResearch.WordTrace tailWord_5615624 prefixEnd_5615624 320390476324893564330469 := by
  unfold tailWord_5615624
  simp only [CollatzResearch.WordTrace]
  refine ⟨102409316903780397534334963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136545755871707196712446617 102409316903780397534334963)
  ·
    refine ⟨153613975355670596301502445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102409316903780397534334963 153613975355670596301502445)
    ·
      refine ⟨57605240758376473613063417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153613975355670596301502445 57605240758376473613063417)
      ·
        refine ⟨43203930568782355209797563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57605240758376473613063417 43203930568782355209797563)
        ·
          refine ⟨64805895853173532814696345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43203930568782355209797563 64805895853173532814696345)
          ·
            refine ⟨48604421889880149611022259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64805895853173532814696345 48604421889880149611022259)
            ·
              refine ⟨72906632834820224416533389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48604421889880149611022259 72906632834820224416533389)
              ·
                refine ⟨27339987313057584156200021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72906632834820224416533389 27339987313057584156200021)
                ·
                  refine ⟨320390476324893564330469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 27339987313057584156200021 320390476324893564330469)
                  ·
                    rfl

theorem cell23_5615624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 8].length) (baseStart_5615624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615624 prefixEnd_5615624 := by exact prefixLift 5615624
  have htrace : WordTrace (prefixWord ++ tailWord_5615624) baseStart_5615624 baseEnd_5615624 := by
    simpa [prefixWord, tailWord_5615624, baseEnd_5615624] using wordTrace_append hprefix tailTrace_5615624
  have hstable : (prefixWord ++ tailWord_5615624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615624).length < 2 ^ (prefixWord ++ tailWord_5615624).sum := by decide
  have hdescent : baseEnd_5615624 < baseStart_5615624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615671 : List Nat := [1, 1, 3, 1, 2, 2, 2, 5, 1, 5]
def baseStart_5615671 : Nat := 118140960795 + 5615671 * 2 ^ 59
def prefixEnd_5615671 : Nat := 4983230072969 + 3 ^ 40 * 5615671 * 2
def baseEnd_5615671 : Nat := 961179473504934465028835

theorem tailTrace_5615671 : CollatzResearch.WordTrace tailWord_5615671 prefixEnd_5615671 961179473504934465028835 := by
  unfold tailWord_5615671
  simp only [CollatzResearch.WordTrace]
  refine ⟨204820348038390522095630867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136546898692260348063753911 204820348038390522095630867)
  ·
    refine ⟨307230522057585783143446301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204820348038390522095630867 307230522057585783143446301)
    ·
      refine ⟨115211445771594668678792363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307230522057585783143446301 115211445771594668678792363)
      ·
        refine ⟨172817168657392003018188545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115211445771594668678792363 172817168657392003018188545)
        ·
          refine ⟨129612876493044002263641409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172817168657392003018188545 129612876493044002263641409)
          ·
            refine ⟨97209657369783001697731057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129612876493044002263641409 97209657369783001697731057)
            ·
              refine ⟨72907243027337251273298293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97209657369783001697731057 72907243027337251273298293)
              ·
                refine ⟨6835054033812867306871715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72907243027337251273298293 6835054033812867306871715)
                ·
                  refine ⟨10252581050719300960307573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6835054033812867306871715 10252581050719300960307573)
                  ·
                    refine ⟨961179473504934465028835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10252581050719300960307573 961179473504934465028835)
                    ·
                      rfl

theorem cell23_5615671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_5615671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615671 prefixEnd_5615671 := by exact prefixLift 5615671
  have htrace : WordTrace (prefixWord ++ tailWord_5615671) baseStart_5615671 baseEnd_5615671 := by
    simpa [prefixWord, tailWord_5615671, baseEnd_5615671] using wordTrace_append hprefix tailTrace_5615671
  have hstable : (prefixWord ++ tailWord_5615671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615671).length < 2 ^ (prefixWord ++ tailWord_5615671).sum := by decide
  have hdescent : baseEnd_5615671 < baseStart_5615671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615701 : List Nat := [1, 3, 2, 2, 1, 3, 1, 3, 1, 6]
def baseStart_5615701 : Nat := 118140960795 + 5615701 * 2 ^ 59
def prefixEnd_5615701 : Nat := 4983230072969 + 3 ^ 40 * 5615701 * 2
def baseEnd_5615701 : Nat := 961184608311479425903789

theorem tailTrace_5615701 : CollatzResearch.WordTrace tailWord_5615701 prefixEnd_5615701 961184608311479425903789 := by
  unfold tailWord_5615701
  simp only [CollatzResearch.WordTrace]
  refine ⟨204821442228281837219222957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136547628152187891479481971 204821442228281837219222957)
  ·
    refine ⟨76808040835605688957208609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204821442228281837219222957 76808040835605688957208609)
    ·
      refine ⟨57606030626704266717906457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76808040835605688957208609 57606030626704266717906457)
      ·
        refine ⟨43204522970028200038429843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57606030626704266717906457 43204522970028200038429843)
        ·
          refine ⟨64806784455042300057644765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43204522970028200038429843 64806784455042300057644765)
          ·
            refine ⟨24302544170640862521616787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64806784455042300057644765 24302544170640862521616787)
            ·
              refine ⟨36453816255961293782425181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24302544170640862521616787 36453816255961293782425181)
              ·
                refine ⟨13670181095985485168409443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36453816255961293782425181 13670181095985485168409443)
                ·
                  refine ⟨20505271643978227752614165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13670181095985485168409443 20505271643978227752614165)
                  ·
                    refine ⟨961184608311479425903789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20505271643978227752614165 961184608311479425903789)
                    ·
                      rfl

theorem cell23_5615701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_5615701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615701 prefixEnd_5615701 := by exact prefixLift 5615701
  have htrace : WordTrace (prefixWord ++ tailWord_5615701) baseStart_5615701 baseEnd_5615701 := by
    simpa [prefixWord, tailWord_5615701, baseEnd_5615701] using wordTrace_append hprefix tailTrace_5615701
  have hstable : (prefixWord ++ tailWord_5615701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615701).length < 2 ^ (prefixWord ++ tailWord_5615701).sum := by decide
  have hdescent : baseEnd_5615701 < baseStart_5615701 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615702 : List Nat := [5, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_5615702 : Nat := 118140960795 + 5615702 * 2 ^ 59
def prefixEnd_5615702 : Nat := 4983230072969 + 3 ^ 40 * 5615702 * 2
def baseEnd_5615702 : Nat := 2883554338415092773798863

theorem tailTrace_5615702 : CollatzResearch.WordTrace tailWord_5615702 prefixEnd_5615702 2883554338415092773798863 := by
  unfold tailWord_5615702
  simp only [CollatzResearch.WordTrace]
  refine ⟨12801342418829888399375585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136547652467518809593339573 12801342418829888399375585)
  ·
    refine ⟨9601006814122416299531689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12801342418829888399375585 9601006814122416299531689)
    ·
      refine ⟨7200755110591812224648767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9601006814122416299531689 7200755110591812224648767)
      ·
        refine ⟨10801132665887718336973151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7200755110591812224648767 10801132665887718336973151)
        ·
          refine ⟨16201698998831577505459727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10801132665887718336973151 16201698998831577505459727)
          ·
            refine ⟨24302548498247366258189591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16201698998831577505459727 24302548498247366258189591)
            ·
              refine ⟨36453822747371049387284387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24302548498247366258189591 36453822747371049387284387)
              ·
                refine ⟨54680734121056574080926581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36453822747371049387284387 54680734121056574080926581)
                ·
                  refine ⟨5126318823849053820086867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54680734121056574080926581 5126318823849053820086867)
                  ·
                    refine ⟨7689478235773580730130301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5126318823849053820086867 7689478235773580730130301)
                    ·
                      refine ⟨2883554338415092773798863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7689478235773580730130301 2883554338415092773798863)
                      ·
                        rfl

theorem cell23_5615702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_5615702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615702 prefixEnd_5615702 := by exact prefixLift 5615702
  have htrace : WordTrace (prefixWord ++ tailWord_5615702) baseStart_5615702 baseEnd_5615702 := by
    simpa [prefixWord, tailWord_5615702, baseEnd_5615702] using wordTrace_append hprefix tailTrace_5615702
  have hstable : (prefixWord ++ tailWord_5615702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615702).length < 2 ^ (prefixWord ++ tailWord_5615702).sum := by decide
  have hdescent : baseEnd_5615702 < baseStart_5615702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615708 : List Nat := [2, 2, 4, 1, 1, 2, 2, 1, 3, 1, 4]
def baseStart_5615708 : Nat := 118140960795 + 5615708 * 2 ^ 59
def prefixEnd_5615708 : Nat := 4983230072969 + 3 ^ 40 * 5615708 * 2
def baseEnd_5615708 : Nat := 2883557419299019750323835

theorem tailTrace_5615708 : CollatzResearch.WordTrace tailWord_5615708 prefixEnd_5615708 2883557419299019750323835 := by
  unfold tailWord_5615708
  simp only [CollatzResearch.WordTrace]
  refine ⟨102410848769628238707363889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136547798359504318276485185 102410848769628238707363889)
  ·
    refine ⟨76808136577221179030522917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102410848769628238707363889 76808136577221179030522917)
    ·
      refine ⟨14401525608228971068223047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76808136577221179030522917 14401525608228971068223047)
      ·
        refine ⟨21602288412343456602334571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14401525608228971068223047 21602288412343456602334571)
        ·
          refine ⟨32403432618515184903501857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21602288412343456602334571 32403432618515184903501857)
          ·
            refine ⟨24302574463886388677626393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32403432618515184903501857 24302574463886388677626393)
            ·
              refine ⟨18226930847914791508219795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24302574463886388677626393 18226930847914791508219795)
              ·
                refine ⟨27340396271872187262329693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18226930847914791508219795 27340396271872187262329693)
                ·
                  refine ⟨10252648601952070223373635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27340396271872187262329693 10252648601952070223373635)
                  ·
                    refine ⟨15378972902928105335060453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10252648601952070223373635 15378972902928105335060453)
                    ·
                      refine ⟨2883557419299019750323835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15378972902928105335060453 2883557419299019750323835)
                      ·
                        rfl

theorem cell23_5615708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_5615708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615708 prefixEnd_5615708 := by exact prefixLift 5615708
  have htrace : WordTrace (prefixWord ++ tailWord_5615708) baseStart_5615708 baseEnd_5615708 := by
    simpa [prefixWord, tailWord_5615708, baseEnd_5615708] using wordTrace_append hprefix tailTrace_5615708
  have hstable : (prefixWord ++ tailWord_5615708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615708).length < 2 ^ (prefixWord ++ tailWord_5615708).sum := by decide
  have hdescent : baseEnd_5615708 < baseStart_5615708 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615721 : List Nat := [1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 4]
def baseStart_5615721 : Nat := 118140960795 + 5615721 * 2 ^ 59
def prefixEnd_5615721 : Nat := 4983230072969 + 3 ^ 40 * 5615721 * 2
def baseEnd_5615721 : Nat := 2883564094547528199461275

theorem tailTrace_5615721 : CollatzResearch.WordTrace tailWord_5615721 prefixEnd_5615721 2883564094547528199461275 := by
  unfold tailWord_5615721
  simp only [CollatzResearch.WordTrace]
  refine ⟨204822171688209380634951017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136548114458806253756634011 204822171688209380634951017)
  ·
    refine ⟨153616628766157035476213263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204822171688209380634951017 153616628766157035476213263)
    ·
      refine ⟨230424943149235553214319895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153616628766157035476213263 230424943149235553214319895)
      ·
        refine ⟨345637414723853329821479843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230424943149235553214319895 345637414723853329821479843)
        ·
          refine ⟨518456122085779994732219765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345637414723853329821479843 518456122085779994732219765)
          ·
            refine ⟨48605261445541874506145603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 518456122085779994732219765 48605261445541874506145603)
            ·
              refine ⟨72907892168312811759218405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48605261445541874506145603 72907892168312811759218405)
              ·
                refine ⟨13670229781558652204853451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72907892168312811759218405 13670229781558652204853451)
                ·
                  refine ⟨20505344672337978307280177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13670229781558652204853451 20505344672337978307280177)
                  ·
                    refine ⟨15379008504253483730460133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20505344672337978307280177 15379008504253483730460133)
                    ·
                      refine ⟨2883564094547528199461275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15379008504253483730460133 2883564094547528199461275)
                      ·
                        rfl

theorem cell23_5615721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_5615721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615721 prefixEnd_5615721 := by exact prefixLift 5615721
  have htrace : WordTrace (prefixWord ++ tailWord_5615721) baseStart_5615721 baseEnd_5615721 := by
    simpa [prefixWord, tailWord_5615721, baseEnd_5615721] using wordTrace_append hprefix tailTrace_5615721
  have hstable : (prefixWord ++ tailWord_5615721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615721).length < 2 ^ (prefixWord ++ tailWord_5615721).sum := by decide
  have hdescent : baseEnd_5615721 < baseStart_5615721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615722 : List Nat := [3, 1, 3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_5615722 : Nat := 118140960795 + 5615722 * 2 ^ 59
def prefixEnd_5615722 : Nat := 4983230072969 + 3 ^ 40 * 5615722 * 2
def baseEnd_5615722 : Nat := 961188202676060898516257

theorem tailTrace_5615722 : CollatzResearch.WordTrace tailWord_5615722 prefixEnd_5615722 961188202676060898516257 := by
  unfold tailWord_5615722
  simp only [CollatzResearch.WordTrace]
  refine ⟨51205552040301439451434355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136548138774137171870491613 51205552040301439451434355)
  ·
    refine ⟨76808328060452159177151533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51205552040301439451434355 76808328060452159177151533)
    ·
      refine ⟨28803123022669559691431825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76808328060452159177151533 28803123022669559691431825)
      ·
        refine ⟨21602342267002169768573869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28803123022669559691431825 21602342267002169768573869)
        ·
          refine ⟨8100878350125813663215201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21602342267002169768573869 8100878350125813663215201)
          ·
            refine ⟨6075658762594360247411401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8100878350125813663215201 6075658762594360247411401)
            ·
              refine ⟨4556744071945770185558551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6075658762594360247411401 4556744071945770185558551)
              ·
                refine ⟨6835116107918655278337827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4556744071945770185558551 6835116107918655278337827)
                ·
                  refine ⟨10252674161877982917506741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6835116107918655278337827 10252674161877982917506741)
                  ·
                    refine ⟨961188202676060898516257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10252674161877982917506741 961188202676060898516257)
                    ·
                      rfl

theorem cell23_5615722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_5615722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615722 prefixEnd_5615722 := by exact prefixLift 5615722
  have htrace : WordTrace (prefixWord ++ tailWord_5615722) baseStart_5615722 baseEnd_5615722 := by
    simpa [prefixWord, tailWord_5615722, baseEnd_5615722] using wordTrace_append hprefix tailTrace_5615722
  have hstable : (prefixWord ++ tailWord_5615722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615722).length < 2 ^ (prefixWord ++ tailWord_5615722).sum := by decide
  have hdescent : baseEnd_5615722 < baseStart_5615722 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615725 : List Nat := [1, 5, 1, 1, 2, 1, 1, 2, 5, 2, 2]
def baseStart_5615725 : Nat := 118140960795 + 5615725 * 2 ^ 59
def prefixEnd_5615725 : Nat := 4983230072969 + 3 ^ 40 * 5615725 * 2
def baseEnd_5615725 : Nat := 2883566148470146183811257

theorem tailTrace_5615725 : CollatzResearch.WordTrace tailWord_5615725 prefixEnd_5615725 2883566148470146183811257 := by
  unfold tailWord_5615725
  simp only [CollatzResearch.WordTrace]
  refine ⟨204822317580194889318096629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136548211720129926212064419 204822317580194889318096629)
  ·
    refine ⟨19202092273143270873571559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204822317580194889318096629 19202092273143270873571559)
    ·
      refine ⟨28803138409714906310357339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19202092273143270873571559 28803138409714906310357339)
      ·
        refine ⟨43204707614572359465536009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28803138409714906310357339 43204707614572359465536009)
        ·
          refine ⟨32403530710929269599152007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43204707614572359465536009 32403530710929269599152007)
          ·
            refine ⟨48605296066393904398728011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32403530710929269599152007 48605296066393904398728011)
            ·
              refine ⟨72907944099590856598092017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48605296066393904398728011 72907944099590856598092017)
              ·
                refine ⟨54680958074693142448569013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72907944099590856598092017 54680958074693142448569013)
                ·
                  refine ⟨5126339819502482104553345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54680958074693142448569013 5126339819502482104553345)
                  ·
                    refine ⟨3844754864626861578415009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5126339819502482104553345 3844754864626861578415009)
                    ·
                      refine ⟨2883566148470146183811257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3844754864626861578415009 2883566148470146183811257)
                      ·
                        rfl

theorem cell23_5615725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_5615725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615725 prefixEnd_5615725 := by exact prefixLift 5615725
  have htrace : WordTrace (prefixWord ++ tailWord_5615725) baseStart_5615725 baseEnd_5615725 := by
    simpa [prefixWord, tailWord_5615725, baseEnd_5615725] using wordTrace_append hprefix tailTrace_5615725
  have hstable : (prefixWord ++ tailWord_5615725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615725).length < 2 ^ (prefixWord ++ tailWord_5615725).sum := by decide
  have hdescent : baseEnd_5615725 < baseStart_5615725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615735 : List Nat := [1, 1, 3, 1, 1, 7, 1, 2, 2, 4]
def baseStart_5615735 : Nat := 118140960795 + 5615735 * 2 ^ 59
def prefixEnd_5615735 : Nat := 4983230072969 + 3 ^ 40 * 5615735 * 2
def baseEnd_5615735 : Nat := 961190427758897048228737

theorem tailTrace_5615735 : CollatzResearch.WordTrace tailWord_5615735 prefixEnd_5615735 961190427758897048228737 := by
  unfold tailWord_5615735
  simp only [CollatzResearch.WordTrace]
  refine ⟨204822682310158661025960659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136548454873439107350640439 204822682310158661025960659)
  ·
    refine ⟨307234023465237991538940989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204822682310158661025960659 307234023465237991538940989)
    ·
      refine ⟨115212758799464246827102871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307234023465237991538940989 115212758799464246827102871)
      ·
        refine ⟨172819138199196370240654307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115212758799464246827102871 172819138199196370240654307)
        ·
          refine ⟨259228707298794555360981461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172819138199196370240654307 259228707298794555360981461)
          ·
            refine ⟨6075672827315497391273003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 259228707298794555360981461 6075672827315497391273003)
            ·
              refine ⟨9113509240973246086909505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6075672827315497391273003 9113509240973246086909505)
              ·
                refine ⟨6835131930729934565182129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9113509240973246086909505 6835131930729934565182129)
                ·
                  refine ⟨5126348948047450923886597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6835131930729934565182129 5126348948047450923886597)
                  ·
                    refine ⟨961190427758897048228737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5126348948047450923886597 961190427758897048228737)
                    ·
                      rfl

theorem cell23_5615735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_5615735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615735 prefixEnd_5615735 := by exact prefixLift 5615735
  have htrace : WordTrace (prefixWord ++ tailWord_5615735) baseStart_5615735 baseEnd_5615735 := by
    simpa [prefixWord, tailWord_5615735, baseEnd_5615735] using wordTrace_append hprefix tailTrace_5615735
  have hstable : (prefixWord ++ tailWord_5615735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615735).length < 2 ^ (prefixWord ++ tailWord_5615735).sum := by decide
  have hdescent : baseEnd_5615735 < baseStart_5615735 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615752 : List Nat := [2, 1, 3, 4, 1, 2, 3, 1, 2, 4]
def baseStart_5615752 : Nat := 118140960795 + 5615752 * 2 ^ 59
def prefixEnd_5615752 : Nat := 4983230072969 + 3 ^ 40 * 5615752 * 2
def baseEnd_5615752 : Nat := 961193337482605859391211

theorem tailTrace_5615752 : CollatzResearch.WordTrace tailWord_5615752 prefixEnd_5615752 961193337482605859391211 := by
  unfold tailWord_5615752
  simp only [CollatzResearch.WordTrace]
  refine ⟨102411651175548536464664755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136548868234064715286219673 102411651175548536464664755)
  ·
    refine ⟨153617476763322804696997133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102411651175548536464664755 153617476763322804696997133)
    ·
      refine ⟨57606553786246051761373925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153617476763322804696997133 57606553786246051761373925)
      ·
        refine ⟨10801228834921134705257611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57606553786246051761373925 10801228834921134705257611)
        ·
          refine ⟨16201843252381702057886417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10801228834921134705257611 16201843252381702057886417)
          ·
            refine ⟨12151382439286276543414813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16201843252381702057886417 12151382439286276543414813)
            ·
              refine ⟨4556768414732353703780555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12151382439286276543414813 4556768414732353703780555)
              ·
                refine ⟨6835152622098530555670833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4556768414732353703780555 6835152622098530555670833)
                ·
                  refine ⟨5126364466573897916753125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6835152622098530555670833 5126364466573897916753125)
                  ·
                    refine ⟨961193337482605859391211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5126364466573897916753125 961193337482605859391211)
                    ·
                      rfl

theorem cell23_5615752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_5615752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615752 prefixEnd_5615752 := by exact prefixLift 5615752
  have htrace : WordTrace (prefixWord ++ tailWord_5615752) baseStart_5615752 baseEnd_5615752 := by
    simpa [prefixWord, tailWord_5615752, baseEnd_5615752] using wordTrace_append hprefix tailTrace_5615752
  have hstable : (prefixWord ++ tailWord_5615752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615752).length < 2 ^ (prefixWord ++ tailWord_5615752).sum := by decide
  have hdescent : baseEnd_5615752 < baseStart_5615752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615775 : List Nat := [1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 3]
def baseStart_5615775 : Nat := 118140960795 + 5615775 * 2 ^ 59
def prefixEnd_5615775 : Nat := 4983230072969 + 3 ^ 40 * 5615775 * 2
def baseEnd_5615775 : Nat := 2883591822502870988186027

theorem tailTrace_5615775 : CollatzResearch.WordTrace tailWord_5615775 prefixEnd_5615775 2883591822502870988186027 := by
  unfold tailWord_5615775
  simp only [CollatzResearch.WordTrace]
  refine ⟨204824141230013747857416779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136549427486675831904944519 204824141230013747857416779)
  ·
    refine ⟨307236211845020621786125169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204824141230013747857416779 307236211845020621786125169)
    ·
      refine ⟨230427158883765466339593877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307236211845020621786125169 230427158883765466339593877)
      ·
        refine ⟨10801273072676506234668463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 230427158883765466339593877 10801273072676506234668463)
        ·
          refine ⟨16201909609014759352002695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10801273072676506234668463 16201909609014759352002695)
          ·
            refine ⟨24302864413522139028004043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16201909609014759352002695 24302864413522139028004043)
            ·
              refine ⟨36454296620283208542006065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24302864413522139028004043 36454296620283208542006065)
              ·
                refine ⟨27340722465212406406504549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36454296620283208542006065 27340722465212406406504549)
                ·
                  refine ⟨5126385462227326201219603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27340722465212406406504549 5126385462227326201219603)
                  ·
                    refine ⟨7689578193340989301829405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5126385462227326201219603 7689578193340989301829405)
                    ·
                      refine ⟨2883591822502870988186027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7689578193340989301829405 2883591822502870988186027)
                      ·
                        rfl

theorem cell23_5615775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_5615775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615775 prefixEnd_5615775 := by exact prefixLift 5615775
  have htrace : WordTrace (prefixWord ++ tailWord_5615775) baseStart_5615775 baseEnd_5615775 := by
    simpa [prefixWord, tailWord_5615775, baseEnd_5615775] using wordTrace_append hprefix tailTrace_5615775
  have hstable : (prefixWord ++ tailWord_5615775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615775).length < 2 ^ (prefixWord ++ tailWord_5615775).sum := by decide
  have hdescent : baseEnd_5615775 < baseStart_5615775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615801 : List Nat := [1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 5]
def baseStart_5615801 : Nat := 118140960795 + 5615801 * 2 ^ 59
def prefixEnd_5615801 : Nat := 4983230072969 + 3 ^ 40 * 5615801 * 2
def baseEnd_5615801 : Nat := 2883605172999887886460907

theorem tailTrace_5615801 : CollatzResearch.WordTrace tailWord_5615801 prefixEnd_5615801 2883605172999887886460907 := by
  unfold tailWord_5615801
  simp only [CollatzResearch.WordTrace]
  refine ⟨204825089527919554297863257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136550059685279702865242171 204825089527919554297863257)
  ·
    refine ⟨153618817145939665723397443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204825089527919554297863257 153618817145939665723397443)
    ·
      refine ⟨230428225718909498585096165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153618817145939665723397443 230428225718909498585096165)
      ·
        refine ⟨43205292322295530984705531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 230428225718909498585096165 43205292322295530984705531)
        ·
          refine ⟨64807938483443296477058297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43205292322295530984705531 64807938483443296477058297)
          ·
            refine ⟨48605953862582472357793723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64807938483443296477058297 48605953862582472357793723)
            ·
              refine ⟨72908930793873708536690585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48605953862582472357793723 72908930793873708536690585)
              ·
                refine ⟨54681698095405281402517939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72908930793873708536690585 54681698095405281402517939)
                ·
                  refine ⟨82022547143107922103776909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54681698095405281402517939 82022547143107922103776909)
                  ·
                    refine ⟨30758455178665470788916341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82022547143107922103776909 30758455178665470788916341)
                    ·
                      refine ⟨2883605172999887886460907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30758455178665470788916341 2883605172999887886460907)
                      ·
                        rfl

theorem cell23_5615801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_5615801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615801 prefixEnd_5615801 := by exact prefixLift 5615801
  have htrace : WordTrace (prefixWord ++ tailWord_5615801) baseStart_5615801 baseEnd_5615801 := by
    simpa [prefixWord, tailWord_5615801, baseEnd_5615801] using wordTrace_append hprefix tailTrace_5615801
  have hstable : (prefixWord ++ tailWord_5615801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615801).length < 2 ^ (prefixWord ++ tailWord_5615801).sum := by decide
  have hdescent : baseEnd_5615801 < baseStart_5615801 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615809 : List Nat := [1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_5615809 : Nat := 118140960795 + 5615809 * 2 ^ 59
def prefixEnd_5615809 : Nat := 4983230072969 + 3 ^ 40 * 5615809 * 2
def baseEnd_5615809 : Nat := 2883609280845123855160871

theorem tailTrace_5615809 : CollatzResearch.WordTrace tailWord_5615809 prefixEnd_5615809 2883609280845123855160871 := by
  unfold tailWord_5615809
  simp only [CollatzResearch.WordTrace]
  refine ⟨204825381311890571664154481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136550254207927047776102987 204825381311890571664154481)
  ·
    refine ⟨153619035983917928748115861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204825381311890571664154481 153619035983917928748115861)
    ·
      refine ⟨7200892311746152910067931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 153619035983917928748115861 7200892311746152910067931)
      ·
        refine ⟨10801338467619229365101897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7200892311746152910067931 10801338467619229365101897)
        ·
          refine ⟨8101003850714422023826423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10801338467619229365101897 8101003850714422023826423)
          ·
            refine ⟨12151505776071633035739635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8101003850714422023826423 12151505776071633035739635)
            ·
              refine ⟨18227258664107449553609453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12151505776071633035739635 18227258664107449553609453)
              ·
                refine ⟨6835221999040293582603545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18227258664107449553609453 6835221999040293582603545)
                ·
                  refine ⟨5126416499280220186952659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6835221999040293582603545 5126416499280220186952659)
                  ·
                    refine ⟨7689624748920330280428989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5126416499280220186952659 7689624748920330280428989)
                    ·
                      refine ⟨2883609280845123855160871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7689624748920330280428989 2883609280845123855160871)
                      ·
                        rfl

theorem cell23_5615809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_5615809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615809 prefixEnd_5615809 := by exact prefixLift 5615809
  have htrace : WordTrace (prefixWord ++ tailWord_5615809) baseStart_5615809 baseEnd_5615809 := by
    simpa [prefixWord, tailWord_5615809, baseEnd_5615809] using wordTrace_append hprefix tailTrace_5615809
  have hstable : (prefixWord ++ tailWord_5615809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615809).length < 2 ^ (prefixWord ++ tailWord_5615809).sum := by decide
  have hdescent : baseEnd_5615809 < baseStart_5615809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615811 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 4]
def baseStart_5615811 : Nat := 118140960795 + 5615811 * 2 ^ 59
def prefixEnd_5615811 : Nat := 4983230072969 + 3 ^ 40 * 5615811 * 2
def baseEnd_5615811 : Nat := 2883610307806432847335861

theorem tailTrace_5615811 : CollatzResearch.WordTrace tailWord_5615811 prefixEnd_5615811 2883610307806432847335861 := by
  unfold tailWord_5615811
  simp only [CollatzResearch.WordTrace]
  refine ⟨204825454257883326005727287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136550302838588884003818191 204825454257883326005727287)
  ·
    refine ⟨307238181386824989008590931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204825454257883326005727287 307238181386824989008590931)
    ·
      refine ⟨460857272080237483512886397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307238181386824989008590931 460857272080237483512886397)
      ·
        refine ⟨172821477030089056317332399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460857272080237483512886397 172821477030089056317332399)
        ·
          refine ⟨259232215545133584475998599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172821477030089056317332399 259232215545133584475998599)
          ·
            refine ⟨388848323317700376713997899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259232215545133584475998599 388848323317700376713997899)
            ·
              refine ⟨583272484976550565070996849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388848323317700376713997899 583272484976550565070996849)
              ·
                refine ⟨437454363732412923803247637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583272484976550565070996849 437454363732412923803247637)
                ·
                  refine ⟨20505673299956855803277233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 437454363732412923803247637 20505673299956855803277233)
                  ·
                    refine ⟨15379254974967641852457925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20505673299956855803277233 15379254974967641852457925)
                    ·
                      refine ⟨2883610307806432847335861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15379254974967641852457925 2883610307806432847335861)
                      ·
                        rfl

theorem cell23_5615811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 2, 4].length) (baseStart_5615811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615811 prefixEnd_5615811 := by exact prefixLift 5615811
  have htrace : WordTrace (prefixWord ++ tailWord_5615811) baseStart_5615811 baseEnd_5615811 := by
    simpa [prefixWord, tailWord_5615811, baseEnd_5615811] using wordTrace_append hprefix tailTrace_5615811
  have hstable : (prefixWord ++ tailWord_5615811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615811).length < 2 ^ (prefixWord ++ tailWord_5615811).sum := by decide
  have hdescent : baseEnd_5615811 < baseStart_5615811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615855 : List Nat := [1, 1, 2, 1, 6, 2, 1, 4, 5]
def baseStart_5615855 : Nat := 118140960795 + 5615855 * 2 ^ 59
def prefixEnd_5615855 : Nat := 4983230072969 + 3 ^ 40 * 5615855 * 2
def baseEnd_5615855 : Nat := 320403655661692297242851

theorem tailTrace_5615855 : CollatzResearch.WordTrace tailWord_5615855 prefixEnd_5615855 320403655661692297242851 := by
  unfold tailWord_5615855
  simp only [CollatzResearch.WordTrace]
  refine ⟨204827059069723921520329019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136551372713149281013552679 204827059069723921520329019)
  ·
    refine ⟨307240588604585882280493529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204827059069723921520329019 307240588604585882280493529)
    ·
      refine ⟨230430441453439411710370147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307240588604585882280493529 230430441453439411710370147)
      ·
        refine ⟨345645662180159117565555221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230430441453439411710370147 345645662180159117565555221)
        ·
          refine ⟨16202140414694958635885401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 345645662180159117565555221 16202140414694958635885401)
          ·
            refine ⟨12151605311021218976914051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16202140414694958635885401 12151605311021218976914051)
            ·
              refine ⟨18227407966531828465371077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12151605311021218976914051 18227407966531828465371077)
              ·
                refine ⟨3417638993724717837257077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18227407966531828465371077 3417638993724717837257077)
                ·
                  refine ⟨320403655661692297242851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3417638993724717837257077 320403655661692297242851)
                  ·
                    rfl

theorem cell23_5615855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 5].length) (baseStart_5615855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615855 prefixEnd_5615855 := by exact prefixLift 5615855
  have htrace : WordTrace (prefixWord ++ tailWord_5615855) baseStart_5615855 baseEnd_5615855 := by
    simpa [prefixWord, tailWord_5615855, baseEnd_5615855] using wordTrace_append hprefix tailTrace_5615855
  have hstable : (prefixWord ++ tailWord_5615855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615855).length < 2 ^ (prefixWord ++ tailWord_5615855).sum := by decide
  have hdescent : baseEnd_5615855 < baseStart_5615855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615905 : List Nat := [1, 2, 3, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_5615905 : Nat := 118140960795 + 5615905 * 2 ^ 59
def prefixEnd_5615905 : Nat := 4983230072969 + 3 ^ 40 * 5615905 * 2
def baseEnd_5615905 : Nat := 2883658574987955479560429

theorem tailTrace_5615905 : CollatzResearch.WordTrace tailWord_5615905 prefixEnd_5615905 2883658574987955479560429 := by
  unfold tailWord_5615905
  simp only [CollatzResearch.WordTrace]
  refine ⟨204828882719542780059649169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136552588479695186706432779 204828882719542780059649169)
  ·
    refine ⟨153621662039657085044736877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204828882719542780059649169 153621662039657085044736877)
    ·
      refine ⟨57608123264871406891776329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153621662039657085044736877 57608123264871406891776329)
      ·
        refine ⟨43206092448653555168832247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57608123264871406891776329 43206092448653555168832247)
        ·
          refine ⟨64809138672980332753248371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43206092448653555168832247 64809138672980332753248371)
          ·
            refine ⟨97213708009470499129872557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64809138672980332753248371 97213708009470499129872557)
            ·
              refine ⟨36455140503551437173702209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97213708009470499129872557 36455140503551437173702209)
              ·
                refine ⟨27341355377663577880276657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36455140503551437173702209 27341355377663577880276657)
                ·
                  refine ⟨20506016533247683410207493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27341355377663577880276657 20506016533247683410207493)
                  ·
                    refine ⟨3844878099983940639413905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20506016533247683410207493 3844878099983940639413905)
                    ·
                      refine ⟨2883658574987955479560429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3844878099983940639413905 2883658574987955479560429)
                      ·
                        rfl

theorem cell23_5615905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_5615905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615905 prefixEnd_5615905 := by exact prefixLift 5615905
  have htrace : WordTrace (prefixWord ++ tailWord_5615905) baseStart_5615905 baseEnd_5615905 := by
    simpa [prefixWord, tailWord_5615905, baseEnd_5615905] using wordTrace_append hprefix tailTrace_5615905
  have hstable : (prefixWord ++ tailWord_5615905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615905).length < 2 ^ (prefixWord ++ tailWord_5615905).sum := by decide
  have hdescent : baseEnd_5615905 < baseStart_5615905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615928 : List Nat := [2, 1, 2, 1, 3, 1, 2, 5, 6]
def baseStart_5615928 : Nat := 118140960795 + 5615928 * 2 ^ 59
def prefixEnd_5615928 : Nat := 4983230072969 + 3 ^ 40 * 5615928 * 2
def baseEnd_5615928 : Nat := 320407820560334321063647

theorem tailTrace_5615928 : CollatzResearch.WordTrace tailWord_5615928 prefixEnd_5615928 320407820560334321063647 := by
  unfold tailWord_5615928
  simp only [CollatzResearch.WordTrace]
  refine ⟨102414860799229727493868219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136553147732306303325157625 102414860799229727493868219)
  ·
    refine ⟨153622291198844591240802329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102414860799229727493868219 153622291198844591240802329)
    ·
      refine ⟨115216718399133443430601747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153622291198844591240802329 115216718399133443430601747)
      ·
        refine ⟨172825077598700165145902621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115216718399133443430601747 172825077598700165145902621)
        ·
          refine ⟨64809404099512561929713483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172825077598700165145902621 64809404099512561929713483)
          ·
            refine ⟨97214106149268842894570225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64809404099512561929713483 97214106149268842894570225)
            ·
              refine ⟨72910579611951632170927669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97214106149268842894570225 72910579611951632170927669)
              ·
                refine ⟨6835366838620465516024469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72910579611951632170927669 6835366838620465516024469)
                ·
                  refine ⟨320407820560334321063647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6835366838620465516024469 320407820560334321063647)
                  ·
                    rfl

theorem cell23_5615928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 5, 6].length) (baseStart_5615928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615928 prefixEnd_5615928 := by exact prefixLift 5615928
  have htrace : WordTrace (prefixWord ++ tailWord_5615928) baseStart_5615928 baseEnd_5615928 := by
    simpa [prefixWord, tailWord_5615928, baseEnd_5615928] using wordTrace_append hprefix tailTrace_5615928
  have hstable : (prefixWord ++ tailWord_5615928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615928).length < 2 ^ (prefixWord ++ tailWord_5615928).sum := by decide
  have hdescent : baseEnd_5615928 < baseStart_5615928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5615995 : List Nat := [1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 4]
def baseStart_5615995 : Nat := 118140960795 + 5615995 * 2 ^ 59
def prefixEnd_5615995 : Nat := 4983230072969 + 3 ^ 40 * 5615995 * 2
def baseEnd_5615995 : Nat := 2883704788246860127435015

theorem tailTrace_5615995 : CollatzResearch.WordTrace tailWord_5615995 prefixEnd_5615995 2883704788246860127435015 := by
  unfold tailWord_5615995
  simp only [CollatzResearch.WordTrace]
  refine ⟨204832165289216725430425439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136554776859477816953616959 204832165289216725430425439)
  ·
    refine ⟨307248247933825088145638159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204832165289216725430425439 307248247933825088145638159)
    ·
      refine ⟨460872371900737632218457239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307248247933825088145638159 460872371900737632218457239)
      ·
        refine ⟨691308557851106448327685859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460872371900737632218457239 691308557851106448327685859)
        ·
          refine ⟨1036962836776659672491528789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691308557851106448327685859 1036962836776659672491528789)
          ·
            refine ⟨12151908243476480537010103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1036962836776659672491528789 12151908243476480537010103)
            ·
              refine ⟨18227862365214720805515155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12151908243476480537010103 18227862365214720805515155)
              ·
                refine ⟨27341793547822081208272733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18227862365214720805515155 27341793547822081208272733)
                ·
                  refine ⟨10253172580433280453102275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27341793547822081208272733 10253172580433280453102275)
                  ·
                    refine ⟨15379758870649920679653413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10253172580433280453102275 15379758870649920679653413)
                    ·
                      refine ⟨2883704788246860127435015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15379758870649920679653413 2883704788246860127435015)
                      ·
                        rfl

theorem cell23_5615995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 4].length) (baseStart_5615995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5615995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5615995 prefixEnd_5615995 := by exact prefixLift 5615995
  have htrace : WordTrace (prefixWord ++ tailWord_5615995) baseStart_5615995 baseEnd_5615995 := by
    simpa [prefixWord, tailWord_5615995, baseEnd_5615995] using wordTrace_append hprefix tailTrace_5615995
  have hstable : (prefixWord ++ tailWord_5615995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5615995).length < 2 ^ (prefixWord ++ tailWord_5615995).sum := by decide
  have hdescent : baseEnd_5615995 < baseStart_5615995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5615995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616018 : List Nat := [3, 2, 3, 15]
def baseStart_5616018 : Nat := 118140960795 + 5616018 * 2 ^ 59
def prefixEnd_5616018 : Nat := 4983230072969 + 3 ^ 40 * 5616018 * 2
def baseEnd_5616018 : Nat := 1318571832785511448307

theorem tailTrace_5616018 : CollatzResearch.WordTrace tailWord_5616018 prefixEnd_5616018 1318571832785511448307 := by
  unfold tailWord_5616018
  simp only [CollatzResearch.WordTrace]
  refine ⟨51208251042033350089628177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136555336112088933572341805 51208251042033350089628177)
  ·
    refine ⟨38406188281525012567221133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51208251042033350089628177 38406188281525012567221133)
    ·
      refine ⟨14402320605571879712707925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38406188281525012567221133 14402320605571879712707925)
      ·
        refine ⟨1318571832785511448307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 14402320605571879712707925 1318571832785511448307)
        ·
          rfl

theorem cell23_5616018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 15].length) (baseStart_5616018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616018 prefixEnd_5616018 := by exact prefixLift 5616018
  have htrace : WordTrace (prefixWord ++ tailWord_5616018) baseStart_5616018 baseEnd_5616018 := by
    simpa [prefixWord, tailWord_5616018, baseEnd_5616018] using wordTrace_append hprefix tailTrace_5616018
  have hstable : (prefixWord ++ tailWord_5616018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616018).length < 2 ^ (prefixWord ++ tailWord_5616018).sum := by decide
  have hdescent : baseEnd_5616018 < baseStart_5616018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616035 : List Nat := [1, 1, 1, 4, 1, 6, 1, 8]
def baseStart_5616035 : Nat := 118140960795 + 5616035 * 2 ^ 59
def prefixEnd_5616035 : Nat := 4983230072969 + 3 ^ 40 * 5616035 * 2
def baseEnd_5616035 : Nat := 106804641758260739664253

theorem tailTrace_5616035 : CollatzResearch.WordTrace tailWord_5616035 prefixEnd_5616035 106804641758260739664253 := by
  unfold tailWord_5616035
  simp only [CollatzResearch.WordTrace]
  refine ⟨204833624209071812261881559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136555749472714541507921039 204833624209071812261881559)
  ·
    refine ⟨307250436313607718392822339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204833624209071812261881559 307250436313607718392822339)
    ·
      refine ⟨460875654470411577589233509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307250436313607718392822339 460875654470411577589233509)
      ·
        refine ⟨86414185213202170797981283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 460875654470411577589233509 86414185213202170797981283)
        ·
          refine ⟨129621277819803256196971925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86414185213202170797981283 129621277819803256196971925)
          ·
            refine ⟨6075997397803277634233059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 129621277819803256196971925 6075997397803277634233059)
            ·
              refine ⟨9113996096704916451349589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6075997397803277634233059 9113996096704916451349589)
              ·
                refine ⟨106804641758260739664253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9113996096704916451349589 106804641758260739664253)
                ·
                  rfl

theorem cell23_5616035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 6, 1, 8].length) (baseStart_5616035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616035 prefixEnd_5616035 := by exact prefixLift 5616035
  have htrace : WordTrace (prefixWord ++ tailWord_5616035) baseStart_5616035 baseEnd_5616035 := by
    simpa [prefixWord, tailWord_5616035, baseEnd_5616035] using wordTrace_append hprefix tailTrace_5616035
  have hstable : (prefixWord ++ tailWord_5616035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616035).length < 2 ^ (prefixWord ++ tailWord_5616035).sum := by decide
  have hdescent : baseEnd_5616035 < baseStart_5616035 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616062 : List Nat := [4, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3]
def baseStart_5616062 : Nat := 118140960795 + 5616062 * 2 ^ 59
def prefixEnd_5616062 : Nat := 4983230072969 + 3 ^ 40 * 5616062 * 2
def baseEnd_5616062 : Nat := 2883739191450711365297207

theorem tailTrace_5616062 : CollatzResearch.WordTrace tailWord_5616062 prefixEnd_5616062 2883739191450711365297207 := by
  unfold tailWord_5616062
  simp only [CollatzResearch.WordTrace]
  refine ⟨25604326122496749484139305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136556405986649330582076293 25604326122496749484139305)
  ·
    refine ⟨19203244591872562113104479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25604326122496749484139305 19203244591872562113104479)
    ·
      refine ⟨28804866887808843169656719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19203244591872562113104479 28804866887808843169656719)
      ·
        refine ⟨43207300331713264754485079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28804866887808843169656719 43207300331713264754485079)
        ·
          refine ⟨64810950497569897131727619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43207300331713264754485079 64810950497569897131727619)
          ·
            refine ⟨97216425746354845697591429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64810950497569897131727619 97216425746354845697591429)
            ·
              refine ⟨18228079827441533568298393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97216425746354845697591429 18228079827441533568298393)
              ·
                refine ⟨13671059870581150176223795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18228079827441533568298393 13671059870581150176223795)
                ·
                  refine ⟨20506589805871725264335693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13671059870581150176223795 20506589805871725264335693)
                  ·
                    refine ⟨7689971177201896974125885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20506589805871725264335693 7689971177201896974125885)
                    ·
                      refine ⟨2883739191450711365297207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7689971177201896974125885 2883739191450711365297207)
                      ·
                        rfl

theorem cell23_5616062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_5616062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616062 prefixEnd_5616062 := by exact prefixLift 5616062
  have htrace : WordTrace (prefixWord ++ tailWord_5616062) baseStart_5616062 baseEnd_5616062 := by
    simpa [prefixWord, tailWord_5616062, baseEnd_5616062] using wordTrace_append hprefix tailTrace_5616062
  have hstable : (prefixWord ++ tailWord_5616062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616062).length < 2 ^ (prefixWord ++ tailWord_5616062).sum := by decide
  have hdescent : baseEnd_5616062 < baseStart_5616062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616095 : List Nat := [1, 1, 2, 3, 3, 2, 2, 1, 2, 6]
def baseStart_5616095 : Nat := 118140960795 + 5616095 * 2 ^ 59
def prefixEnd_5616095 : Nat := 4983230072969 + 3 ^ 40 * 5616095 * 2
def baseEnd_5616095 : Nat := 961252045437436578728185

theorem tailTrace_5616095 : CollatzResearch.WordTrace tailWord_5616095 prefixEnd_5616095 961252045437436578728185 := by
  unfold tailWord_5616095
  simp only [CollatzResearch.WordTrace]
  refine ⟨204835812588854442509065739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136557208392569628339377159 204835812588854442509065739)
  ·
    refine ⟨307253718883281663763598609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204835812588854442509065739 307253718883281663763598609)
    ·
      refine ⟨230440289162461247822698957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307253718883281663763598609 230440289162461247822698957)
      ·
        refine ⟨86415108435922967933512109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230440289162461247822698957 86415108435922967933512109)
        ·
          refine ⟨32405665663471112975067041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86415108435922967933512109 32405665663471112975067041)
          ·
            refine ⟨24304249247603334731300281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32405665663471112975067041 24304249247603334731300281)
            ·
              refine ⟨18228186935702501048475211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24304249247603334731300281 18228186935702501048475211)
              ·
                refine ⟨27342280403553751572712817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18228186935702501048475211 27342280403553751572712817)
                ·
                  refine ⟨20506710302665313679534613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27342280403553751572712817 20506710302665313679534613)
                  ·
                    refine ⟨961252045437436578728185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20506710302665313679534613 961252045437436578728185)
                    ·
                      rfl

theorem cell23_5616095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 6].length) (baseStart_5616095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616095 prefixEnd_5616095 := by exact prefixLift 5616095
  have htrace : WordTrace (prefixWord ++ tailWord_5616095) baseStart_5616095 baseEnd_5616095 := by
    simpa [prefixWord, tailWord_5616095, baseEnd_5616095] using wordTrace_append hprefix tailTrace_5616095
  have hstable : (prefixWord ++ tailWord_5616095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616095).length < 2 ^ (prefixWord ++ tailWord_5616095).sum := by decide
  have hdescent : baseEnd_5616095 < baseStart_5616095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616106 : List Nat := [3, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_5616106 : Nat := 118140960795 + 5616106 * 2 ^ 59
def prefixEnd_5616106 : Nat := 4983230072969 + 3 ^ 40 * 5616106 * 2
def baseEnd_5616106 : Nat := 2883761784599509193147005

theorem tailTrace_5616106 : CollatzResearch.WordTrace tailWord_5616106 prefixEnd_5616106 2883761784599509193147005 := by
  unfold tailWord_5616106
  simp only [CollatzResearch.WordTrace]
  refine ⟨51209053447953647846929043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136557475861209727591810781 51209053447953647846929043)
  ·
    refine ⟨76813580171930471770393565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51209053447953647846929043 76813580171930471770393565)
    ·
      refine ⟨28805092564473926913897587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76813580171930471770393565 28805092564473926913897587)
      ·
        refine ⟨43207638846710890370846381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28805092564473926913897587 43207638846710890370846381)
        ·
          refine ⟨16202864567516583889067393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43207638846710890370846381 16202864567516583889067393)
          ·
            refine ⟨12152148425637437916800545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16202864567516583889067393 12152148425637437916800545)
            ·
              refine ⟨9114111319228078437600409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12152148425637437916800545 9114111319228078437600409)
              ·
                refine ⟨6835583489421058828200307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9114111319228078437600409 6835583489421058828200307)
                ·
                  refine ⟨10253375234131588242300461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6835583489421058828200307 10253375234131588242300461)
                  ·
                    refine ⟨3845015712799345590862673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10253375234131588242300461 3845015712799345590862673)
                    ·
                      refine ⟨2883761784599509193147005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845015712799345590862673 2883761784599509193147005)
                      ·
                        rfl

theorem cell23_5616106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_5616106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616106 prefixEnd_5616106 := by exact prefixLift 5616106
  have htrace : WordTrace (prefixWord ++ tailWord_5616106) baseStart_5616106 baseEnd_5616106 := by
    simpa [prefixWord, tailWord_5616106, baseEnd_5616106] using wordTrace_append hprefix tailTrace_5616106
  have hstable : (prefixWord ++ tailWord_5616106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616106).length < 2 ^ (prefixWord ++ tailWord_5616106).sum := by decide
  have hdescent : baseEnd_5616106 < baseStart_5616106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616142 : List Nat := [4, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_5616142 : Nat := 118140960795 + 5616142 * 2 ^ 59
def prefixEnd_5616142 : Nat := 4983230072969 + 3 ^ 40 * 5616142 * 2
def baseEnd_5616142 : Nat := 320420029989230116921871

theorem tailTrace_5616142 : CollatzResearch.WordTrace tailWord_5616142 prefixEnd_5616142 320420029989230116921871 := by
  unfold tailWord_5616142
  simp only [CollatzResearch.WordTrace]
  refine ⟨25604690852460521192003335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136558351213122779690684453 25604690852460521192003335)
  ·
    refine ⟨38407036278690781788005003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25604690852460521192003335 38407036278690781788005003)
    ·
      refine ⟨57610554418036172682007505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38407036278690781788005003 57610554418036172682007505)
      ·
        refine ⟨43207915813527129511505629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57610554418036172682007505 43207915813527129511505629)
        ·
          refine ⟨16202968430072673566814611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43207915813527129511505629 16202968430072673566814611)
          ·
            refine ⟨24304452645109010350221917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16202968430072673566814611 24304452645109010350221917)
            ·
              refine ⟨9114169741915878881333219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24304452645109010350221917 9114169741915878881333219)
              ·
                refine ⟨13671254612873818321999829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9114169741915878881333219 13671254612873818321999829)
                ·
                  refine ⟨320420029989230116921871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13671254612873818321999829 320420029989230116921871)
                  ·
                    rfl

theorem cell23_5616142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_5616142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616142 prefixEnd_5616142 := by exact prefixLift 5616142
  have htrace : WordTrace (prefixWord ++ tailWord_5616142) baseStart_5616142 baseEnd_5616142 := by
    simpa [prefixWord, tailWord_5616142, baseEnd_5616142] using wordTrace_append hprefix tailTrace_5616142
  have hstable : (prefixWord ++ tailWord_5616142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616142).length < 2 ^ (prefixWord ++ tailWord_5616142).sum := by decide
  have hdescent : baseEnd_5616142 < baseStart_5616142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616192 : List Nat := [2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 4]
def baseStart_5616192 : Nat := 118140960795 + 5616192 * 2 ^ 59
def prefixEnd_5616192 : Nat := 4983230072969 + 3 ^ 40 * 5616192 * 2
def baseEnd_5616192 : Nat := 2883805943935795856671609

theorem tailTrace_5616192 : CollatzResearch.WordTrace tailWord_5616192 prefixEnd_5616192 2883805943935795856671609 := by
  unfold tailWord_5616192
  simp only [CollatzResearch.WordTrace]
  refine ⟨102419675234751514037673415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136559566979668685383564553 102419675234751514037673415)
  ·
    refine ⟨153629512852127271056510123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102419675234751514037673415 153629512852127271056510123)
    ·
      refine ⟨230444269278190906584765185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153629512852127271056510123 230444269278190906584765185)
      ·
        refine ⟨172833201958643179938573889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230444269278190906584765185 172833201958643179938573889)
        ·
          refine ⟨129624901468982384953930417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172833201958643179938573889 129624901468982384953930417)
          ·
            refine ⟨97218676101736788715447813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129624901468982384953930417 97218676101736788715447813)
            ·
              refine ⟨18228501769075647884146465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 97218676101736788715447813 18228501769075647884146465)
              ·
                refine ⟨13671376326806735913109849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18228501769075647884146465 13671376326806735913109849)
                ·
                  refine ⟨10253532245105051934832387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13671376326806735913109849 10253532245105051934832387)
                  ·
                    refine ⟨15380298367657577902248581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10253532245105051934832387 15380298367657577902248581)
                    ·
                      refine ⟨2883805943935795856671609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15380298367657577902248581 2883805943935795856671609)
                      ·
                        rfl

theorem cell23_5616192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 4].length) (baseStart_5616192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616192 prefixEnd_5616192 := by exact prefixLift 5616192
  have htrace : WordTrace (prefixWord ++ tailWord_5616192) baseStart_5616192 baseEnd_5616192 := by
    simpa [prefixWord, tailWord_5616192, baseEnd_5616192] using wordTrace_append hprefix tailTrace_5616192
  have hstable : (prefixWord ++ tailWord_5616192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616192).length < 2 ^ (prefixWord ++ tailWord_5616192).sum := by decide
  have hdescent : baseEnd_5616192 < baseStart_5616192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616209 : List Nat := [1, 2, 2, 1, 3, 4, 1, 1, 2, 4, 2]
def baseStart_5616209 : Nat := 118140960795 + 5616209 * 2 ^ 59
def prefixEnd_5616209 : Nat := 4983230072969 + 3 ^ 40 * 5616209 * 2
def baseEnd_5616209 : Nat := 2883814673106922290159031

theorem tailTrace_5616209 : CollatzResearch.WordTrace tailWord_5616209 prefixEnd_5616209 2883814673106922290159031 := by
  unfold tailWord_5616209
  simp only [CollatzResearch.WordTrace]
  refine ⟨204839970510441439978715681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136559980340294293319143787 204839970510441439978715681)
  ·
    refine ⟨153629977882831079984036761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204839970510441439978715681 153629977882831079984036761)
    ·
      refine ⟨115222483412123309988027571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153629977882831079984036761 115222483412123309988027571)
      ·
        refine ⟨172833725118184964982041357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115222483412123309988027571 172833725118184964982041357)
        ·
          refine ⟨64812646919319361868265509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172833725118184964982041357 64812646919319361868265509)
          ·
            refine ⟨12152371297372380350299783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64812646919319361868265509 12152371297372380350299783)
            ·
              refine ⟨18228556946058570525449675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12152371297372380350299783 18228556946058570525449675)
              ·
                refine ⟨27342835419087855788174513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18228556946058570525449675 27342835419087855788174513)
                ·
                  refine ⟨20507126564315891841130885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27342835419087855788174513 20507126564315891841130885)
                  ·
                    refine ⟨3845086230809229720212041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20507126564315891841130885 3845086230809229720212041)
                    ·
                      refine ⟨2883814673106922290159031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845086230809229720212041 2883814673106922290159031)
                      ·
                        rfl

theorem cell23_5616209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 1, 2, 4, 2].length) (baseStart_5616209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616209 prefixEnd_5616209 := by exact prefixLift 5616209
  have htrace : WordTrace (prefixWord ++ tailWord_5616209) baseStart_5616209 baseEnd_5616209 := by
    simpa [prefixWord, tailWord_5616209, baseEnd_5616209] using wordTrace_append hprefix tailTrace_5616209
  have hstable : (prefixWord ++ tailWord_5616209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616209).length < 2 ^ (prefixWord ++ tailWord_5616209).sum := by decide
  have hdescent : baseEnd_5616209 < baseStart_5616209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616226 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 1, 3, 4]
def baseStart_5616226 : Nat := 118140960795 + 5616226 * 2 ^ 59
def prefixEnd_5616226 : Nat := 4983230072969 + 3 ^ 40 * 5616226 * 2
def baseEnd_5616226 : Nat := 2883823402278048723646453

theorem tailTrace_5616226 : CollatzResearch.WordTrace tailWord_5616226 prefixEnd_5616226 2883823402278048723646453 := by
  unfold tailWord_5616226
  simp only [CollatzResearch.WordTrace]
  refine ⟨51210147637844962970521133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136560393700919901254723021 51210147637844962970521133)
  ·
    refine ⟨19203805364191861113945425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51210147637844962970521133 19203805364191861113945425)
    ·
      refine ⟨14402854023143895835459069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19203805364191861113945425 14402854023143895835459069)
      ·
        refine ⟨5401070258678960938297151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14402854023143895835459069 5401070258678960938297151)
        ·
          refine ⟨8101605388018441407445727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5401070258678960938297151 8101605388018441407445727)
          ·
            refine ⟨12152408082027662111168591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8101605388018441407445727 12152408082027662111168591)
            ·
              refine ⟨18228612123041493166752887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12152408082027662111168591 18228612123041493166752887)
              ·
                refine ⟨27342918184562239750129331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18228612123041493166752887 27342918184562239750129331)
                ·
                  refine ⟨41014377276843359625193997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27342918184562239750129331 41014377276843359625193997)
                  ·
                    refine ⟨15380391478816259859447749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41014377276843359625193997 15380391478816259859447749)
                    ·
                      refine ⟨2883823402278048723646453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15380391478816259859447749 2883823402278048723646453)
                      ·
                        rfl

theorem cell23_5616226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_5616226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616226 prefixEnd_5616226 := by exact prefixLift 5616226
  have htrace : WordTrace (prefixWord ++ tailWord_5616226) baseStart_5616226 baseEnd_5616226 := by
    simpa [prefixWord, tailWord_5616226, baseEnd_5616226] using wordTrace_append hprefix tailTrace_5616226
  have hstable : (prefixWord ++ tailWord_5616226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616226).length < 2 ^ (prefixWord ++ tailWord_5616226).sum := by decide
  have hdescent : baseEnd_5616226 < baseStart_5616226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616229 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 3]
def baseStart_5616229 : Nat := 118140960795 + 5616229 * 2 ^ 59
def prefixEnd_5616229 : Nat := 4983230072969 + 3 ^ 40 * 5616229 * 2
def baseEnd_5616229 : Nat := 2883824942720012211908939

theorem tailTrace_5616229 : CollatzResearch.WordTrace tailWord_5616229 prefixEnd_5616229 2883824942720012211908939 := by
  unfold tailWord_5616229
  simp only [CollatzResearch.WordTrace]
  refine ⟨204840699970368983394443741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136560466646912655596295827 204840699970368983394443741)
  ·
    refine ⟨76815262488888368772916403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204840699970368983394443741 76815262488888368772916403)
    ·
      refine ⟨115222893733332553159374605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76815262488888368772916403 115222893733332553159374605)
      ·
        refine ⟨43208585149999707434765477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115222893733332553159374605 43208585149999707434765477)
        ·
          refine ⟨8101609715624945144018527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43208585149999707434765477 8101609715624945144018527)
          ·
            refine ⟨12152414573437417716027791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8101609715624945144018527 12152414573437417716027791)
            ·
              refine ⟨18228621860156126574041687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12152414573437417716027791 18228621860156126574041687)
              ·
                refine ⟨27342932790234189861062531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18228621860156126574041687 27342932790234189861062531)
                ·
                  refine ⟨41014399185351284791593797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27342932790234189861062531 41014399185351284791593797)
                  ·
                    refine ⟨7690199847253365898423837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41014399185351284791593797 7690199847253365898423837)
                    ·
                      refine ⟨2883824942720012211908939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7690199847253365898423837 2883824942720012211908939)
                      ·
                        rfl

theorem cell23_5616229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_5616229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616229 prefixEnd_5616229 := by exact prefixLift 5616229
  have htrace : WordTrace (prefixWord ++ tailWord_5616229) baseStart_5616229 baseEnd_5616229 := by
    simpa [prefixWord, tailWord_5616229, baseEnd_5616229] using wordTrace_append hprefix tailTrace_5616229
  have hstable : (prefixWord ++ tailWord_5616229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616229).length < 2 ^ (prefixWord ++ tailWord_5616229).sum := by decide
  have hdescent : baseEnd_5616229 < baseStart_5616229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616249 : List Nat := [1, 2, 1, 3, 3, 4, 1, 2, 6]
def baseStart_5616249 : Nat := 118140960795 + 5616249 * 2 ^ 59
def prefixEnd_5616249 : Nat := 4983230072969 + 3 ^ 40 * 5616249 * 2
def baseEnd_5616249 : Nat := 320426134703678014850983

theorem tailTrace_5616249 : CollatzResearch.WordTrace tailWord_5616249 prefixEnd_5616249 320426134703678014850983 := by
  unfold tailWord_5616249
  simp only [CollatzResearch.WordTrace]
  refine ⟨204841429430296526810171801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136560952953531017873447867 204841429430296526810171801)
  ·
    refine ⟨153631072072722395107628851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204841429430296526810171801 153631072072722395107628851)
    ·
      refine ⟨230446608109083592661443277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153631072072722395107628851 230446608109083592661443277)
      ·
        refine ⟨86417478040906347248041229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230446608109083592661443277 86417478040906347248041229)
        ·
          refine ⟨32406554265339880218015461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86417478040906347248041229 32406554265339880218015461)
          ·
            refine ⟨6076228924751227540877899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32406554265339880218015461 6076228924751227540877899)
            ·
              refine ⟨9114343387126841311316849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6076228924751227540877899 9114343387126841311316849)
              ·
                refine ⟨6835757540345130983487637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9114343387126841311316849 6835757540345130983487637)
                ·
                  refine ⟨320426134703678014850983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6835757540345130983487637 320426134703678014850983)
                  ·
                    rfl

theorem cell23_5616249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 4, 1, 2, 6].length) (baseStart_5616249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616249 prefixEnd_5616249 := by exact prefixLift 5616249
  have htrace : WordTrace (prefixWord ++ tailWord_5616249) baseStart_5616249 baseEnd_5616249 := by
    simpa [prefixWord, tailWord_5616249, baseEnd_5616249] using wordTrace_append hprefix tailTrace_5616249
  have hstable : (prefixWord ++ tailWord_5616249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616249).length < 2 ^ (prefixWord ++ tailWord_5616249).sum := by decide
  have hdescent : baseEnd_5616249 < baseStart_5616249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616255 : List Nat := [1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 7]
def baseStart_5616255 : Nat := 118140960795 + 5616255 * 2 ^ 59
def prefixEnd_5616255 : Nat := 4983230072969 + 3 ^ 40 * 5616255 * 2
def baseEnd_5616255 : Nat := 2883838293217029110183819

theorem tailTrace_5616255 : CollatzResearch.WordTrace tailWord_5616255 prefixEnd_5616255 2883838293217029110183819 := by
  unfold tailWord_5616255
  simp only [CollatzResearch.WordTrace]
  refine ⟨204841648268274789834890219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136561098845516526556593479 204841648268274789834890219)
  ·
    refine ⟨307262472402412184752335329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204841648268274789834890219 307262472402412184752335329)
    ·
      refine ⟨230446854301809138564251497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307262472402412184752335329 230446854301809138564251497)
      ·
        refine ⟨172835140726356853923188623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230446854301809138564251497 172835140726356853923188623)
        ·
          refine ⟨259252711089535280884782935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172835140726356853923188623 259252711089535280884782935)
          ·
            refine ⟨388879066634302921327174403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259252711089535280884782935 388879066634302921327174403)
            ·
              refine ⟨583318599951454381990761605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388879066634302921327174403 583318599951454381990761605)
              ·
                refine ⟨109372237490897696623267801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583318599951454381990761605 109372237490897696623267801)
                ·
                  refine ⟨82029178118173272467450851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109372237490897696623267801 82029178118173272467450851)
                  ·
                    refine ⟨123043767177259908701176277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 82029178118173272467450851 123043767177259908701176277)
                    ·
                      refine ⟨2883838293217029110183819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 123043767177259908701176277 2883838293217029110183819)
                      ·
                        rfl

theorem cell23_5616255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 7].length) (baseStart_5616255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616255 prefixEnd_5616255 := by exact prefixLift 5616255
  have htrace : WordTrace (prefixWord ++ tailWord_5616255) baseStart_5616255 baseEnd_5616255 := by
    simpa [prefixWord, tailWord_5616255, baseEnd_5616255] using wordTrace_append hprefix tailTrace_5616255
  have hstable : (prefixWord ++ tailWord_5616255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616255).length < 2 ^ (prefixWord ++ tailWord_5616255).sum := by decide
  have hdescent : baseEnd_5616255 < baseStart_5616255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616259 : List Nat := [1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 3]
def baseStart_5616259 : Nat := 118140960795 + 5616259 * 2 ^ 59
def prefixEnd_5616259 : Nat := 4983230072969 + 3 ^ 40 * 5616259 * 2
def baseEnd_5616259 : Nat := 2883840347139647094533801

theorem tailTrace_5616259 : CollatzResearch.WordTrace tailWord_5616259 prefixEnd_5616259 2883840347139647094533801 := by
  unfold tailWord_5616259
  simp only [CollatzResearch.WordTrace]
  refine ⟨204841794160260298518035831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136561196106840199012023887 204841794160260298518035831)
  ·
    refine ⟨307262691240390447777053747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204841794160260298518035831 307262691240390447777053747)
    ·
      refine ⟨460894036860585671665580621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307262691240390447777053747 460894036860585671665580621)
      ·
        refine ⟨172835263822719626874592733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 460894036860585671665580621 172835263822719626874592733)
        ·
          refine ⟨64813223933519860077972275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172835263822719626874592733 64813223933519860077972275)
          ·
            refine ⟨97219835900279790116958413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64813223933519860077972275 97219835900279790116958413)
            ·
              refine ⟨36457438462604921293859405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 97219835900279790116958413 36457438462604921293859405)
              ·
                refine ⟨13671539423476845485197277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36457438462604921293859405 13671539423476845485197277)
                ·
                  refine ⟨5126827283803817056948979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13671539423476845485197277 5126827283803817056948979)
                  ·
                    refine ⟨7690240925705725585423469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5126827283803817056948979 7690240925705725585423469)
                    ·
                      refine ⟨2883840347139647094533801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7690240925705725585423469 2883840347139647094533801)
                      ·
                        rfl

theorem cell23_5616259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 3, 3, 1, 3].length) (baseStart_5616259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616259 prefixEnd_5616259 := by exact prefixLift 5616259
  have htrace : WordTrace (prefixWord ++ tailWord_5616259) baseStart_5616259 baseEnd_5616259 := by
    simpa [prefixWord, tailWord_5616259, baseEnd_5616259] using wordTrace_append hprefix tailTrace_5616259
  have hstable : (prefixWord ++ tailWord_5616259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616259).length < 2 ^ (prefixWord ++ tailWord_5616259).sum := by decide
  have hdescent : baseEnd_5616259 < baseStart_5616259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616266 : List Nat := [3, 1, 2, 3, 3, 1, 3, 1, 6]
def baseStart_5616266 : Nat := 118140960795 + 5616266 * 2 ^ 59
def prefixEnd_5616266 : Nat := 4983230072969 + 3 ^ 40 * 5616266 * 2
def baseEnd_5616266 : Nat := 320427104611580951905141

theorem tailTrace_5616266 : CollatzResearch.WordTrace tailWord_5616266 prefixEnd_5616266 320427104611580951905141 := by
  unfold tailWord_5616266
  simp only [CollatzResearch.WordTrace]
  refine ⟨51210512367808734678385163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136561366314156625809027101 51210512367808734678385163)
  ·
    refine ⟨76815768551713102017577745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51210512367808734678385163 76815768551713102017577745)
    ·
      refine ⟨57611826413784826513183309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76815768551713102017577745 57611826413784826513183309)
      ·
        refine ⟨21604434905169309942443741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57611826413784826513183309 21604434905169309942443741)
        ·
          refine ⟨8101663089438491228416403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21604434905169309942443741 8101663089438491228416403)
          ·
            refine ⟨12152494634157736842624605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8101663089438491228416403 12152494634157736842624605)
            ·
              refine ⟨4557185487809151315984227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12152494634157736842624605 4557185487809151315984227)
              ·
                refine ⟨6835778231713726973976341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557185487809151315984227 6835778231713726973976341)
                ·
                  refine ⟨320427104611580951905141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6835778231713726973976341 320427104611580951905141)
                  ·
                    rfl

theorem cell23_5616266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 6].length) (baseStart_5616266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616266 prefixEnd_5616266 := by exact prefixLift 5616266
  have htrace : WordTrace (prefixWord ++ tailWord_5616266) baseStart_5616266 baseEnd_5616266 := by
    simpa [prefixWord, tailWord_5616266, baseEnd_5616266] using wordTrace_append hprefix tailTrace_5616266
  have hstable : (prefixWord ++ tailWord_5616266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616266).length < 2 ^ (prefixWord ++ tailWord_5616266).sum := by decide
  have hdescent : baseEnd_5616266 < baseStart_5616266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616279 : List Nat := [1, 1, 3, 3, 2, 1, 4, 2, 1, 5]
def baseStart_5616279 : Nat := 118140960795 + 5616279 * 2 ^ 59
def prefixEnd_5616279 : Nat := 4983230072969 + 3 ^ 40 * 5616279 * 2
def baseEnd_5616279 : Nat := 961283538917579005427903

theorem tailTrace_5616279 : CollatzResearch.WordTrace tailWord_5616279 prefixEnd_5616279 961283538917579005427903 := by
  unfold tailWord_5616279
  simp only [CollatzResearch.WordTrace]
  refine ⟨204842523620187841933763891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136561682413458561289175927 204842523620187841933763891)
  ·
    refine ⟨307263785430281762900645837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204842523620187841933763891 307263785430281762900645837)
    ·
      refine ⟨115223919536355661087742189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307263785430281762900645837 115223919536355661087742189)
      ·
        refine ⟨43208969826133372907903321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115223919536355661087742189 43208969826133372907903321)
        ·
          refine ⟨32406727369600029680927491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43208969826133372907903321 32406727369600029680927491)
          ·
            refine ⟨48610091054400044521391237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32406727369600029680927491 48610091054400044521391237)
            ·
              refine ⟨9114392072700008347760857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48610091054400044521391237 9114392072700008347760857)
              ·
                refine ⟨6835794054525006260820643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9114392072700008347760857 6835794054525006260820643)
                ·
                  refine ⟨10253691081787509391230965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6835794054525006260820643 10253691081787509391230965)
                  ·
                    refine ⟨961283538917579005427903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10253691081787509391230965 961283538917579005427903)
                    ·
                      rfl

theorem cell23_5616279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_5616279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616279 prefixEnd_5616279 := by exact prefixLift 5616279
  have htrace : WordTrace (prefixWord ++ tailWord_5616279) baseStart_5616279 baseEnd_5616279 := by
    simpa [prefixWord, tailWord_5616279, baseEnd_5616279] using wordTrace_append hprefix tailTrace_5616279
  have hstable : (prefixWord ++ tailWord_5616279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616279).length < 2 ^ (prefixWord ++ tailWord_5616279).sum := by decide
  have hdescent : baseEnd_5616279 < baseStart_5616279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616286 : List Nat := [4, 3, 1, 1, 1, 1, 1, 3, 1, 5, 2]
def baseStart_5616286 : Nat := 118140960795 + 5616286 * 2 ^ 59
def prefixEnd_5616286 : Nat := 4983230072969 + 3 ^ 40 * 5616286 * 2
def baseEnd_5616286 : Nat := 2883854211117318488896177

theorem tailTrace_5616286 : CollatzResearch.WordTrace tailWord_5616286 prefixEnd_5616286 2883854211117318488896177 := by
  unfold tailWord_5616286
  simp only [CollatzResearch.WordTrace]
  refine ⟨25605347366395310266158589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136561852620774988086179141 25605347366395310266158589)
  ·
    refine ⟨9602005262398241349809471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25605347366395310266158589 9602005262398241349809471)
    ·
      refine ⟨14403007893597362024714207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9602005262398241349809471 14403007893597362024714207)
      ·
        refine ⟨21604511840396043037071311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14403007893597362024714207 21604511840396043037071311)
        ·
          refine ⟨32406767760594064555606967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21604511840396043037071311 32406767760594064555606967)
          ·
            refine ⟨48610151640891096833410451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32406767760594064555606967 48610151640891096833410451)
            ·
              refine ⟨72915227461336645250115677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48610151640891096833410451 72915227461336645250115677)
              ·
                refine ⟨27343210298001241968793379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72915227461336645250115677 27343210298001241968793379)
                ·
                  refine ⟨41014815447001862953190069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27343210298001241968793379 41014815447001862953190069)
                  ·
                    refine ⟨3845138948156424651861569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41014815447001862953190069 3845138948156424651861569)
                    ·
                      refine ⟨2883854211117318488896177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845138948156424651861569 2883854211117318488896177)
                      ·
                        rfl

theorem cell23_5616286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_5616286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616286 prefixEnd_5616286 := by exact prefixLift 5616286
  have htrace : WordTrace (prefixWord ++ tailWord_5616286) baseStart_5616286 baseEnd_5616286 := by
    simpa [prefixWord, tailWord_5616286, baseEnd_5616286] using wordTrace_append hprefix tailTrace_5616286
  have hstable : (prefixWord ++ tailWord_5616286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616286).length < 2 ^ (prefixWord ++ tailWord_5616286).sum := by decide
  have hdescent : baseEnd_5616286 < baseStart_5616286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616292 : List Nat := [2, 3, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_5616292 : Nat := 118140960795 + 5616292 * 2 ^ 59
def prefixEnd_5616292 : Nat := 4983230072969 + 3 ^ 40 * 5616292 * 2
def baseEnd_5616292 : Nat := 961285764000415155140383

theorem tailTrace_5616292 : CollatzResearch.WordTrace tailWord_5616292 prefixEnd_5616292 961285764000415155140383 := by
  unfold tailWord_5616292
  simp only [CollatzResearch.WordTrace]
  refine ⟨102421498884570372576993565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136561998512760496769324753 102421498884570372576993565)
  ·
    refine ⟨38408062081713889716372587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102421498884570372576993565 38408062081713889716372587)
    ·
      refine ⟨57612093122570834574558881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38408062081713889716372587 57612093122570834574558881)
      ·
        refine ⟨43209069841928125930919161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57612093122570834574558881 43209069841928125930919161)
        ·
          refine ⟨32406802381446094448189371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43209069841928125930919161 32406802381446094448189371)
          ·
            refine ⟨48610203572169141672284057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32406802381446094448189371 48610203572169141672284057)
            ·
              refine ⟨36457652679126856254213043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48610203572169141672284057 36457652679126856254213043)
              ·
                refine ⟨54686479018690284381319565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36457652679126856254213043 54686479018690284381319565)
                ·
                  refine ⟨20507429632008856642994837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54686479018690284381319565 20507429632008856642994837)
                  ·
                    refine ⟨961285764000415155140383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20507429632008856642994837 961285764000415155140383)
                    ·
                      rfl

theorem cell23_5616292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_5616292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616292 prefixEnd_5616292 := by exact prefixLift 5616292
  have htrace : WordTrace (prefixWord ++ tailWord_5616292) baseStart_5616292 baseEnd_5616292 := by
    simpa [prefixWord, tailWord_5616292, baseEnd_5616292] using wordTrace_append hprefix tailTrace_5616292
  have hstable : (prefixWord ++ tailWord_5616292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616292).length < 2 ^ (prefixWord ++ tailWord_5616292).sum := by decide
  have hdescent : baseEnd_5616292 < baseStart_5616292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616333 : List Nat := [1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_5616333 : Nat := 118140960795 + 5616333 * 2 ^ 59
def prefixEnd_5616333 : Nat := 4983230072969 + 3 ^ 40 * 5616333 * 2
def baseEnd_5616333 : Nat := 2883878344708079805008461

theorem tailTrace_5616333 : CollatzResearch.WordTrace tailWord_5616333 prefixEnd_5616333 2883878344708079805008461 := by
  unfold tailWord_5616333
  simp only [CollatzResearch.WordTrace]
  refine ⟨204844493161992209156229653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136562995441328139437486435 204844493161992209156229653)
  ·
    refine ⟨9602085616968384804198265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204844493161992209156229653 9602085616968384804198265)
    ·
      refine ⟨7201564212726288603148699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9602085616968384804198265 7201564212726288603148699)
      ·
        refine ⟨10802346319089432904723049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7201564212726288603148699 10802346319089432904723049)
        ·
          refine ⟨8101759739317074678542287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10802346319089432904723049 8101759739317074678542287)
          ·
            refine ⟨12152639608975612017813431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8101759739317074678542287 12152639608975612017813431)
            ·
              refine ⟨18228959413463418026720147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12152639608975612017813431 18228959413463418026720147)
              ·
                refine ⟨27343439120195127040080221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18228959413463418026720147 27343439120195127040080221)
                ·
                  refine ⟨10253789670073172640030083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27343439120195127040080221 10253789670073172640030083)
                  ·
                    refine ⟨15380684505109758960045125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10253789670073172640030083 15380684505109758960045125)
                    ·
                      refine ⟨2883878344708079805008461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15380684505109758960045125 2883878344708079805008461)
                      ·
                        rfl

theorem cell23_5616333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_5616333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616333 prefixEnd_5616333 := by exact prefixLift 5616333
  have htrace : WordTrace (prefixWord ++ tailWord_5616333) baseStart_5616333 baseEnd_5616333 := by
    simpa [prefixWord, tailWord_5616333, baseEnd_5616333] using wordTrace_append hprefix tailTrace_5616333
  have hstable : (prefixWord ++ tailWord_5616333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616333).length < 2 ^ (prefixWord ++ tailWord_5616333).sum := by decide
  have hdescent : baseEnd_5616333 < baseStart_5616333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616353 : List Nat := [1, 2, 3, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_5616353 : Nat := 118140960795 + 5616353 * 2 ^ 59
def prefixEnd_5616353 : Nat := 4983230072969 + 3 ^ 40 * 5616353 * 2
def baseEnd_5616353 : Nat := 2883888614321169726758369

theorem tailTrace_5616353 : CollatzResearch.WordTrace tailWord_5616353 prefixEnd_5616353 2883888614321169726758369 := by
  unfold tailWord_5616353
  simp only [CollatzResearch.WordTrace]
  refine ⟨204845222621919752571957713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136563481747946501714638475 204845222621919752571957713)
  ·
    refine ⟨153633916966439814428968285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204845222621919752571957713 153633916966439814428968285)
    ·
      refine ⟨57612718862414930410863107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153633916966439814428968285 57612718862414930410863107)
      ·
        refine ⟨86419078293622395616294661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57612718862414930410863107 86419078293622395616294661)
        ·
          refine ⟨16203577180054199178055249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 86419078293622395616294661 16203577180054199178055249)
          ·
            refine ⟨12152682885040649383541437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16203577180054199178055249 12152682885040649383541437)
            ·
              refine ⟨4557256081890243518828039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12152682885040649383541437 4557256081890243518828039)
              ·
                refine ⟨6835884122835365278242059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557256081890243518828039 6835884122835365278242059)
                ·
                  refine ⟨10253826184253047917363089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6835884122835365278242059 10253826184253047917363089)
                  ·
                    refine ⟨7690369638189785938022317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10253826184253047917363089 7690369638189785938022317)
                    ·
                      refine ⟨2883888614321169726758369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7690369638189785938022317 2883888614321169726758369)
                      ·
                        rfl

theorem cell23_5616353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_5616353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616353 prefixEnd_5616353 := by exact prefixLift 5616353
  have htrace : WordTrace (prefixWord ++ tailWord_5616353) baseStart_5616353 baseEnd_5616353 := by
    simpa [prefixWord, tailWord_5616353, baseEnd_5616353] using wordTrace_append hprefix tailTrace_5616353
  have hstable : (prefixWord ++ tailWord_5616353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616353).length < 2 ^ (prefixWord ++ tailWord_5616353).sum := by decide
  have hdescent : baseEnd_5616353 < baseStart_5616353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616367 : List Nat := [1, 1, 2, 1, 5, 4, 2, 2, 1, 2, 2]
def baseStart_5616367 : Nat := 118140960795 + 5616367 * 2 ^ 59
def prefixEnd_5616367 : Nat := 4983230072969 + 3 ^ 40 * 5616367 * 2
def baseEnd_5616367 : Nat := 2883895803050332671983305

theorem tailTrace_5616367 : CollatzResearch.WordTrace tailWord_5616367 prefixEnd_5616367 2883895803050332671983305 := by
  unfold tailWord_5616367
  simp only [CollatzResearch.WordTrace]
  refine ⟨204845733243869032962967355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136563822162579355308644903 204845733243869032962967355)
  ·
    refine ⟨307268599865803549444451033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204845733243869032962967355 307268599865803549444451033)
    ·
      refine ⟨230451449899352662083338275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307268599865803549444451033 230451449899352662083338275)
      ·
        refine ⟨345677174849028993125007413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230451449899352662083338275 345677174849028993125007413)
        ·
          refine ⟨32407235142096468105469445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 345677174849028993125007413 32407235142096468105469445)
          ·
            refine ⟨6076356589143087769775521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32407235142096468105469445 6076356589143087769775521)
            ·
              refine ⟨4557267441857315827331641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6076356589143087769775521 4557267441857315827331641)
              ·
                refine ⟨3417950581392986870498731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4557267441857315827331641 3417950581392986870498731)
                ·
                  refine ⟨5126925872089480305748097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3417950581392986870498731 5126925872089480305748097)
                  ·
                    refine ⟨3845194404067110229311073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5126925872089480305748097 3845194404067110229311073)
                    ·
                      refine ⟨2883895803050332671983305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845194404067110229311073 2883895803050332671983305)
                      ·
                        rfl

theorem cell23_5616367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 2, 2, 1, 2, 2].length) (baseStart_5616367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616367 prefixEnd_5616367 := by exact prefixLift 5616367
  have htrace : WordTrace (prefixWord ++ tailWord_5616367) baseStart_5616367 baseEnd_5616367 := by
    simpa [prefixWord, tailWord_5616367, baseEnd_5616367] using wordTrace_append hprefix tailTrace_5616367
  have hstable : (prefixWord ++ tailWord_5616367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616367).length < 2 ^ (prefixWord ++ tailWord_5616367).sum := by decide
  have hdescent : baseEnd_5616367 < baseStart_5616367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616439 : List Nat := [1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_5616439 : Nat := 118140960795 + 5616439 * 2 ^ 59
def prefixEnd_5616439 : Nat := 4983230072969 + 3 ^ 40 * 5616439 * 2
def baseEnd_5616439 : Nat := 2883932773657456390282973

theorem tailTrace_5616439 : CollatzResearch.WordTrace tailWord_5616439 prefixEnd_5616439 2883932773657456390282973 := by
  unfold tailWord_5616439
  simp only [CollatzResearch.WordTrace]
  refine ⟨204848359299608189259588371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136565572866405459506392247 204848359299608189259588371)
  ·
    refine ⟨307272538949412283889382557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204848359299608189259588371 307272538949412283889382557)
    ·
      refine ⟨115227202106029606458518459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307272538949412283889382557 115227202106029606458518459)
      ·
        refine ⟨172840803159044409687777689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115227202106029606458518459 172840803159044409687777689)
        ·
          refine ⟨129630602369283307265833267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172840803159044409687777689 129630602369283307265833267)
          ·
            refine ⟨194445903553924960898749901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129630602369283307265833267 194445903553924960898749901)
            ·
              refine ⟨72917213832721860337031213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 194445903553924960898749901 72917213832721860337031213)
              ·
                refine ⟨27343955187270697626386705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72917213832721860337031213 27343955187270697626386705)
                ·
                  refine ⟨20507966390453023219790029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27343955187270697626386705 20507966390453023219790029)
                  ·
                    refine ⟨7690487396419883707421261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20507966390453023219790029 7690487396419883707421261)
                    ·
                      refine ⟨2883932773657456390282973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7690487396419883707421261 2883932773657456390282973)
                      ·
                        rfl

theorem cell23_5616439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_5616439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616439 prefixEnd_5616439 := by exact prefixLift 5616439
  have htrace : WordTrace (prefixWord ++ tailWord_5616439) baseStart_5616439 baseEnd_5616439 := by
    simpa [prefixWord, tailWord_5616439, baseEnd_5616439] using wordTrace_append hprefix tailTrace_5616439
  have hstable : (prefixWord ++ tailWord_5616439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616439).length < 2 ^ (prefixWord ++ tailWord_5616439).sum := by decide
  have hdescent : baseEnd_5616439 < baseStart_5616439 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616440 : List Nat := [2, 1, 2, 1, 3, 2, 5, 1, 2, 2, 2]
def baseStart_5616440 : Nat := 118140960795 + 5616440 * 2 ^ 59
def prefixEnd_5616440 : Nat := 4983230072969 + 3 ^ 40 * 5616440 * 2
def baseEnd_5616440 : Nat := 2883933287138110886370469

theorem tailTrace_5616440 : CollatzResearch.WordTrace tailWord_5616440 prefixEnd_5616440 2883933287138110886370469 := by
  unfold tailWord_5616440
  simp only [CollatzResearch.WordTrace]
  refine ⟨102424197886302283215187387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136565597181736377620249849 102424197886302283215187387)
  ·
    refine ⟨153636296829453424822781081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102424197886302283215187387 153636296829453424822781081)
    ·
      refine ⟨115227222622090068617085811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153636296829453424822781081 115227222622090068617085811)
      ·
        refine ⟨172840833933135102925628717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115227222622090068617085811 172840833933135102925628717)
        ·
          refine ⟨64815312724925663597110769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172840833933135102925628717 64815312724925663597110769)
          ·
            refine ⟨48611484543694247697833077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64815312724925663597110769 48611484543694247697833077)
            ·
              refine ⟨4557326675971335721671851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48611484543694247697833077 4557326675971335721671851)
              ·
                refine ⟨6835990013957003582507777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557326675971335721671851 6835990013957003582507777)
                ·
                  refine ⟨5126992510467752686880833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6835990013957003582507777 5126992510467752686880833)
                  ·
                    refine ⟨3845244382850814515160625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5126992510467752686880833 3845244382850814515160625)
                    ·
                      refine ⟨2883933287138110886370469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845244382850814515160625 2883933287138110886370469)
                      ·
                        rfl

theorem cell23_5616440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 5, 1, 2, 2, 2].length) (baseStart_5616440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616440 prefixEnd_5616440 := by exact prefixLift 5616440
  have htrace : WordTrace (prefixWord ++ tailWord_5616440) baseStart_5616440 baseEnd_5616440 := by
    simpa [prefixWord, tailWord_5616440, baseEnd_5616440] using wordTrace_append hprefix tailTrace_5616440
  have hstable : (prefixWord ++ tailWord_5616440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616440).length < 2 ^ (prefixWord ++ tailWord_5616440).sum := by decide
  have hdescent : baseEnd_5616440 < baseStart_5616440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616469 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_5616469 : Nat := 118140960795 + 5616469 * 2 ^ 59
def prefixEnd_5616469 : Nat := 4983230072969 + 3 ^ 40 * 5616469 * 2
def baseEnd_5616469 : Nat := 2883948178077091272907835

theorem tailTrace_5616469 : CollatzResearch.WordTrace tailWord_5616469 prefixEnd_5616469 2883948178077091272907835 := by
  unfold tailWord_5616469
  simp only [CollatzResearch.WordTrace]
  refine ⟨204849453489499504383180461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136566302326333002922120307 204849453489499504383180461)
  ·
    refine ⟨76818545058562314143692673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 204849453489499504383180461 76818545058562314143692673)
    ·
      refine ⟨57613908793921735607769505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76818545058562314143692673 57613908793921735607769505)
      ·
        refine ⟨43210431595441301705827129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57613908793921735607769505 43210431595441301705827129)
        ·
          refine ⟨32407823696580976279370347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43210431595441301705827129 32407823696580976279370347)
          ·
            refine ⟨48611735544871464419055521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32407823696580976279370347 48611735544871464419055521)
            ·
              refine ⟨36458801658653598314291641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48611735544871464419055521 36458801658653598314291641)
              ·
                refine ⟨27344101243990198735718731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36458801658653598314291641 27344101243990198735718731)
                ·
                  refine ⟨41016151865985298103578097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27344101243990198735718731 41016151865985298103578097)
                  ·
                    refine ⟨30762113899488973577683573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 41016151865985298103578097 30762113899488973577683573)
                    ·
                      refine ⟨2883948178077091272907835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30762113899488973577683573 2883948178077091272907835)
                      ·
                        rfl

theorem cell23_5616469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_5616469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616469 prefixEnd_5616469 := by exact prefixLift 5616469
  have htrace : WordTrace (prefixWord ++ tailWord_5616469) baseStart_5616469 baseEnd_5616469 := by
    simpa [prefixWord, tailWord_5616469, baseEnd_5616469] using wordTrace_append hprefix tailTrace_5616469
  have hstable : (prefixWord ++ tailWord_5616469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616469).length < 2 ^ (prefixWord ++ tailWord_5616469).sum := by decide
  have hdescent : baseEnd_5616469 < baseStart_5616469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616476 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 4, 5]
def baseStart_5616476 : Nat := 118140960795 + 5616476 * 2 ^ 59
def prefixEnd_5616476 : Nat := 4983230072969 + 3 ^ 40 * 5616476 * 2
def baseEnd_5616476 : Nat := 961317257480557581840101

theorem tailTrace_5616476 : CollatzResearch.WordTrace tailWord_5616476 prefixEnd_5616476 961317257480557581840101 := by
  unfold tailWord_5616476
  simp only [CollatzResearch.WordTrace]
  refine ⟨102424854400237072289342641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136566472533649429719123521 102424854400237072289342641)
  ·
    refine ⟨76818640800177804217006981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102424854400237072289342641 76818640800177804217006981)
    ·
      refine ⟨14403495150033338290688809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76818640800177804217006981 14403495150033338290688809)
      ·
        refine ⟨10802621362525003718016607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14403495150033338290688809 10802621362525003718016607)
        ·
          refine ⟨16203932043787505577024911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10802621362525003718016607 16203932043787505577024911)
          ·
            refine ⟨24305898065681258365537367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16203932043787505577024911 24305898065681258365537367)
            ·
              refine ⟨36458847098521887548306051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24305898065681258365537367 36458847098521887548306051)
              ·
                refine ⟨54688270647782831322459077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36458847098521887548306051 54688270647782831322459077)
                ·
                  refine ⟨10254050746459280872961077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54688270647782831322459077 10254050746459280872961077)
                  ·
                    refine ⟨961317257480557581840101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10254050746459280872961077 961317257480557581840101)
                    ·
                      rfl

theorem cell23_5616476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_5616476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616476 prefixEnd_5616476 := by exact prefixLift 5616476
  have htrace : WordTrace (prefixWord ++ tailWord_5616476) baseStart_5616476 baseEnd_5616476 := by
    simpa [prefixWord, tailWord_5616476, baseEnd_5616476] using wordTrace_append hprefix tailTrace_5616476
  have hstable : (prefixWord ++ tailWord_5616476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616476).length < 2 ^ (prefixWord ++ tailWord_5616476).sum := by decide
  have hdescent : baseEnd_5616476 < baseStart_5616476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616496 : List Nat := [2, 1, 1, 1, 4, 1, 2, 3, 2, 4, 2]
def baseStart_5616496 : Nat := 118140960795 + 5616496 * 2 ^ 59
def prefixEnd_5616496 : Nat := 4983230072969 + 3 ^ 40 * 5616496 * 2
def baseEnd_5616496 : Nat := 2883962042054762667270211

theorem tailTrace_5616496 : CollatzResearch.WordTrace tailWord_5616496 prefixEnd_5616496 2883962042054762667270211 := by
  unfold tailWord_5616496
  simp only [CollatzResearch.WordTrace]
  refine ⟨102425219130200843997206671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136566958840267791996275561 102425219130200843997206671)
  ·
    refine ⟨153637828695301265995810007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102425219130200843997206671 153637828695301265995810007)
    ·
      refine ⟨230456743042951898993715011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153637828695301265995810007 230456743042951898993715011)
      ·
        refine ⟨345685114564427848490572517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230456743042951898993715011 345685114564427848490572517)
        ·
          refine ⟨64815958980830221591982347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345685114564427848490572517 64815958980830221591982347)
          ·
            refine ⟨97223938471245332387973521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64815958980830221591982347 97223938471245332387973521)
            ·
              refine ⟨72917953853433999290980141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97223938471245332387973521 72917953853433999290980141)
              ·
                refine ⟨27344232695037749734117553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72917953853433999290980141 27344232695037749734117553)
                ·
                  refine ⟨20508174521278312300588165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27344232695037749734117553 20508174521278312300588165)
                  ·
                    refine ⟨3845282722739683556360281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20508174521278312300588165 3845282722739683556360281)
                    ·
                      refine ⟨2883962042054762667270211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845282722739683556360281 2883962042054762667270211)
                      ·
                        rfl

theorem cell23_5616496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 3, 2, 4, 2].length) (baseStart_5616496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616496 prefixEnd_5616496 := by exact prefixLift 5616496
  have htrace : WordTrace (prefixWord ++ tailWord_5616496) baseStart_5616496 baseEnd_5616496 := by
    simpa [prefixWord, tailWord_5616496, baseEnd_5616496] using wordTrace_append hprefix tailTrace_5616496
  have hstable : (prefixWord ++ tailWord_5616496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616496).length < 2 ^ (prefixWord ++ tailWord_5616496).sum := by decide
  have hdescent : baseEnd_5616496 < baseStart_5616496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616499 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 3]
def baseStart_5616499 : Nat := 118140960795 + 5616499 * 2 ^ 59
def prefixEnd_5616499 : Nat := 4983230072969 + 3 ^ 40 * 5616499 * 2
def baseEnd_5616499 : Nat := 2883963582496726155532697

theorem tailTrace_5616499 : CollatzResearch.WordTrace tailWord_5616499 prefixEnd_5616499 2883963582496726155532697 := by
  unfold tailWord_5616499
  simp only [CollatzResearch.WordTrace]
  refine ⟨204850547679390819506772551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136567031786260546337848367 204850547679390819506772551)
  ·
    refine ⟨307275821519086229260158827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204850547679390819506772551 307275821519086229260158827)
    ·
      refine ⟨460913732278629343890238241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307275821519086229260158827 460913732278629343890238241)
      ·
        refine ⟨345685299208972007917678681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460913732278629343890238241 345685299208972007917678681)
        ·
          refine ⟨259263974406729005938259011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345685299208972007917678681 259263974406729005938259011)
          ·
            refine ⟨388895961610093508907388517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259263974406729005938259011 388895961610093508907388517)
            ·
              refine ⟨72917992801892532920135347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 388895961610093508907388517 72917992801892532920135347)
              ·
                refine ⟨109376989202838799380203021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72917992801892532920135347 109376989202838799380203021)
                ·
                  refine ⟨41016370951064549767576133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109376989202838799380203021 41016370951064549767576133)
                  ·
                    refine ⟨7690569553324603081420525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41016370951064549767576133 7690569553324603081420525)
                    ·
                      refine ⟨2883963582496726155532697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7690569553324603081420525 2883963582496726155532697)
                      ·
                        rfl

theorem cell23_5616499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 3, 4, 3].length) (baseStart_5616499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616499 prefixEnd_5616499 := by exact prefixLift 5616499
  have htrace : WordTrace (prefixWord ++ tailWord_5616499) baseStart_5616499 baseEnd_5616499 := by
    simpa [prefixWord, tailWord_5616499, baseEnd_5616499] using wordTrace_append hprefix tailTrace_5616499
  have hstable : (prefixWord ++ tailWord_5616499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616499).length < 2 ^ (prefixWord ++ tailWord_5616499).sum := by decide
  have hdescent : baseEnd_5616499 < baseStart_5616499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616509 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 4]
def baseStart_5616509 : Nat := 118140960795 + 5616509 * 2 ^ 59
def prefixEnd_5616509 : Nat := 4983230072969 + 3 ^ 40 * 5616509 * 2
def baseEnd_5616509 : Nat := 2883968717303271116407651

theorem tailTrace_5616509 : CollatzResearch.WordTrace tailWord_5616509 prefixEnd_5616509 2883968717303271116407651 := by
  unfold tailWord_5616509
  simp only [CollatzResearch.WordTrace]
  refine ⟨204850912409354591214636581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136567274939569727476424387 204850912409354591214636581)
  ·
    refine ⟨38409546076753985852744359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204850912409354591214636581 38409546076753985852744359)
    ·
      refine ⟨57614319115130978779116539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38409546076753985852744359 57614319115130978779116539)
      ·
        refine ⟨86421478672696468168674809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57614319115130978779116539 86421478672696468168674809)
        ·
          refine ⟨64816109004522351126506107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86421478672696468168674809 64816109004522351126506107)
          ·
            refine ⟨97224163506783526689759161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64816109004522351126506107 97224163506783526689759161)
            ·
              refine ⟨72918122630087645017319371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97224163506783526689759161 72918122630087645017319371)
              ·
                refine ⟨109377183945131467525979057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72918122630087645017319371 109377183945131467525979057)
                ·
                  refine ⟨82032887958848600644484293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109377183945131467525979057 82032887958848600644484293)
                  ·
                    refine ⟨15381166492284112620840805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82032887958848600644484293 15381166492284112620840805)
                    ·
                      refine ⟨2883968717303271116407651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15381166492284112620840805 2883968717303271116407651)
                      ·
                        rfl

theorem cell23_5616509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_5616509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616509 prefixEnd_5616509 := by exact prefixLift 5616509
  have htrace : WordTrace (prefixWord ++ tailWord_5616509) baseStart_5616509 baseEnd_5616509 := by
    simpa [prefixWord, tailWord_5616509, baseEnd_5616509] using wordTrace_append hprefix tailTrace_5616509
  have hstable : (prefixWord ++ tailWord_5616509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616509).length < 2 ^ (prefixWord ++ tailWord_5616509).sum := by decide
  have hdescent : baseEnd_5616509 < baseStart_5616509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616510 : List Nat := [4, 2, 3, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5616510 : Nat := 118140960795 + 5616510 * 2 ^ 59
def prefixEnd_5616510 : Nat := 4983230072969 + 3 ^ 40 * 5616510 * 2
def baseEnd_5616510 : Nat := 961323076927975204165049

theorem tailTrace_5616510 : CollatzResearch.WordTrace tailWord_5616510 prefixEnd_5616510 961323076927975204165049 := by
  unfold tailWord_5616510
  simp only [CollatzResearch.WordTrace]
  refine ⟨25606368610293871048177873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136567299254900645590281989 25606368610293871048177873)
  ·
    refine ⟨19204776457720403286133405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25606368610293871048177873 19204776457720403286133405)
    ·
      refine ⟨7201791171645151232300027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19204776457720403286133405 7201791171645151232300027)
      ·
        refine ⟨10802686757467726848450041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7201791171645151232300027 10802686757467726848450041)
        ·
          refine ⟨8102015068100795136337531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10802686757467726848450041 8102015068100795136337531)
          ·
            refine ⟨12153022602151192704506297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8102015068100795136337531 12153022602151192704506297)
            ·
              refine ⟨9114766951613394528379723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12153022602151192704506297 9114766951613394528379723)
              ·
                refine ⟨13672150427420091792569585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9114766951613394528379723 13672150427420091792569585)
                ·
                  refine ⟨10254112820565068844427189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13672150427420091792569585 10254112820565068844427189)
                  ·
                    refine ⟨961323076927975204165049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10254112820565068844427189 961323076927975204165049)
                    ·
                      rfl

theorem cell23_5616510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5616510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616510 prefixEnd_5616510 := by exact prefixLift 5616510
  have htrace : WordTrace (prefixWord ++ tailWord_5616510) baseStart_5616510 baseEnd_5616510 := by
    simpa [prefixWord, tailWord_5616510, baseEnd_5616510] using wordTrace_append hprefix tailTrace_5616510
  have hstable : (prefixWord ++ tailWord_5616510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616510).length < 2 ^ (prefixWord ++ tailWord_5616510).sum := by decide
  have hdescent : baseEnd_5616510 < baseStart_5616510 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616556 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 3, 5, 2]
def baseStart_5616556 : Nat := 118140960795 + 5616556 * 2 ^ 59
def prefixEnd_5616556 : Nat := 4983230072969 + 3 ^ 40 * 5616556 * 2
def baseEnd_5616556 : Nat := 2883992850894032432519935

theorem tailTrace_5616556 : CollatzResearch.WordTrace tailWord_5616556 prefixEnd_5616556 2883992850894032432519935 := by
  unfold tailWord_5616556
  simp only [CollatzResearch.WordTrace]
  refine ⟨102426313320092159120798761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136568417760122878827731681 102426313320092159120798761)
  ·
    refine ⟨76819734990069119340599071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102426313320092159120798761 76819734990069119340599071)
    ·
      refine ⟨115229602485103679010898607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76819734990069119340599071 115229602485103679010898607)
      ·
        refine ⟨172844403727655518516347911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115229602485103679010898607 172844403727655518516347911)
        ·
          refine ⟨259266605591483277774521867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172844403727655518516347911 259266605591483277774521867)
          ·
            refine ⟨388899908387224916661782801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259266605591483277774521867 388899908387224916661782801)
            ·
              refine ⟨291674931290418687496337101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388899908387224916661782801 291674931290418687496337101)
              ·
                refine ⟨109378099233907007811126413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 291674931290418687496337101 109378099233907007811126413)
                ·
                  refine ⟨41016787212715127929172405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 109378099233907007811126413 41016787212715127929172405)
                  ·
                    refine ⟨3845323801192043243359913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41016787212715127929172405 3845323801192043243359913)
                    ·
                      refine ⟨2883992850894032432519935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845323801192043243359913 2883992850894032432519935)
                      ·
                        rfl

theorem cell23_5616556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 5, 2].length) (baseStart_5616556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616556 prefixEnd_5616556 := by exact prefixLift 5616556
  have htrace : WordTrace (prefixWord ++ tailWord_5616556) baseStart_5616556 baseEnd_5616556 := by
    simpa [prefixWord, tailWord_5616556, baseEnd_5616556] using wordTrace_append hprefix tailTrace_5616556
  have hstable : (prefixWord ++ tailWord_5616556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616556).length < 2 ^ (prefixWord ++ tailWord_5616556).sum := by decide
  have hdescent : baseEnd_5616556 < baseStart_5616556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616583 : List Nat := [1, 1, 4, 1, 1, 2, 6, 1, 1, 5]
def baseStart_5616583 : Nat := 118140960795 + 5616583 * 2 ^ 59
def prefixEnd_5616583 : Nat := 4983230072969 + 3 ^ 40 * 5616583 * 2
def baseEnd_5616583 : Nat := 961335571623901275627437

theorem tailTrace_5616583 : CollatzResearch.WordTrace tailWord_5616583 prefixEnd_5616583 961335571623901275627437 := by
  unfold tailWord_5616583
  simp only [CollatzResearch.WordTrace]
  refine ⟨204853611411086501852830403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136569074274057667901886935 204853611411086501852830403)
  ·
    refine ⟨307280417116629752779245605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204853611411086501852830403 307280417116629752779245605)
    ·
      refine ⟨57615078209368078646108551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 307280417116629752779245605 57615078209368078646108551)
      ·
        refine ⟨86422617314052117969162827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57615078209368078646108551 86422617314052117969162827)
        ·
          refine ⟨129633925971078176953744241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86422617314052117969162827 129633925971078176953744241)
          ·
            refine ⟨97225444478308632715308181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129633925971078176953744241 97225444478308632715308181)
            ·
              refine ⟨4557442709920717158530071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97225444478308632715308181 4557442709920717158530071)
              ·
                refine ⟨6836164064881075737795107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557442709920717158530071 6836164064881075737795107)
                ·
                  refine ⟨10254246097321613606692661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6836164064881075737795107 10254246097321613606692661)
                  ·
                    refine ⟨961335571623901275627437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10254246097321613606692661 961335571623901275627437)
                    ·
                      rfl

theorem cell23_5616583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_5616583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616583 prefixEnd_5616583 := by exact prefixLift 5616583
  have htrace : WordTrace (prefixWord ++ tailWord_5616583) baseStart_5616583 baseEnd_5616583 := by
    simpa [prefixWord, tailWord_5616583, baseEnd_5616583] using wordTrace_append hprefix tailTrace_5616583
  have hstable : (prefixWord ++ tailWord_5616583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616583).length < 2 ^ (prefixWord ++ tailWord_5616583).sum := by decide
  have hdescent : baseEnd_5616583 < baseStart_5616583 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616609 : List Nat := [1, 2, 3, 1, 2, 1, 1, 12]
def baseStart_5616609 : Nat := 118140960795 + 5616609 * 2 ^ 59
def prefixEnd_5616609 : Nat := 4983230072969 + 3 ^ 40 * 5616609 * 2
def baseEnd_5616609 : Nat := 106815557976619286116933

theorem tailTrace_5616609 : CollatzResearch.WordTrace tailWord_5616609 prefixEnd_5616609 106815557976619286116933 := by
  unfold tailWord_5616609
  simp only [CollatzResearch.WordTrace]
  refine ⟨204854559708992308293276881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136569706472661538862184587 204854559708992308293276881)
  ·
    refine ⟨153640919781744231219957661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204854559708992308293276881 153640919781744231219957661)
    ·
      refine ⟨57615344918154086707484123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153640919781744231219957661 57615344918154086707484123)
      ·
        refine ⟨86423017377231130061226185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57615344918154086707484123 86423017377231130061226185)
        ·
          refine ⟨64817263032923347545919639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86423017377231130061226185 64817263032923347545919639)
          ·
            refine ⟨97225894549385021318879459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64817263032923347545919639 97225894549385021318879459)
            ·
              refine ⟨145838841824077531978319189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97225894549385021318879459 145838841824077531978319189)
              ·
                refine ⟨106815557976619286116933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 145838841824077531978319189 106815557976619286116933)
                ·
                  rfl

theorem cell23_5616609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 12].length) (baseStart_5616609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616609 prefixEnd_5616609 := by exact prefixLift 5616609
  have htrace : WordTrace (prefixWord ++ tailWord_5616609) baseStart_5616609 baseEnd_5616609 := by
    simpa [prefixWord, tailWord_5616609, baseEnd_5616609] using wordTrace_append hprefix tailTrace_5616609
  have hstable : (prefixWord ++ tailWord_5616609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616609).length < 2 ^ (prefixWord ++ tailWord_5616609).sum := by decide
  have hdescent : baseEnd_5616609 < baseStart_5616609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616623 : List Nat := [1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 3]
def baseStart_5616623 : Nat := 118140960795 + 5616623 * 2 ^ 59
def prefixEnd_5616623 : Nat := 4983230072969 + 3 ^ 40 * 5616623 * 2
def baseEnd_5616623 : Nat := 2884027254097883670382127

theorem tailTrace_5616623 : CollatzResearch.WordTrace tailWord_5616623 prefixEnd_5616623 2884027254097883670382127 := by
  unfold tailWord_5616623
  simp only [CollatzResearch.WordTrace]
  refine ⟨204855070330941588684286523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136570046887294392456191015 204855070330941588684286523)
  ·
    refine ⟨307282605496412383026429785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204855070330941588684286523 307282605496412383026429785)
    ·
      refine ⟨230461954122309287269822339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307282605496412383026429785 230461954122309287269822339)
      ·
        refine ⟨345692931183463930904733509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230461954122309287269822339 345692931183463930904733509)
        ·
          refine ⟨64817424596899487044637533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 345692931183463930904733509 64817424596899487044637533)
          ·
            refine ⟨24306534223837307641739075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64817424596899487044637533 24306534223837307641739075)
            ·
              refine ⟨36459801335755961462608613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24306534223837307641739075 36459801335755961462608613)
              ·
                refine ⟨6836212750454242774239115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36459801335755961462608613 6836212750454242774239115)
                ·
                  refine ⟨10254319125681364161358673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6836212750454242774239115 10254319125681364161358673)
                  ·
                    refine ⟨7690739344261023121019005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10254319125681364161358673 7690739344261023121019005)
                    ·
                      refine ⟨2884027254097883670382127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7690739344261023121019005 2884027254097883670382127)
                      ·
                        rfl

theorem cell23_5616623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 4, 1, 2, 3].length) (baseStart_5616623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616623 prefixEnd_5616623 := by exact prefixLift 5616623
  have htrace : WordTrace (prefixWord ++ tailWord_5616623) baseStart_5616623 baseEnd_5616623 := by
    simpa [prefixWord, tailWord_5616623, baseEnd_5616623] using wordTrace_append hprefix tailTrace_5616623
  have hstable : (prefixWord ++ tailWord_5616623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616623).length < 2 ^ (prefixWord ++ tailWord_5616623).sum := by decide
  have hdescent : baseEnd_5616623 < baseStart_5616623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616639 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 3, 9]
def baseStart_5616639 : Nat := 118140960795 + 5616639 * 2 ^ 59
def prefixEnd_5616639 : Nat := 4983230072969 + 3 ^ 40 * 5616639 * 2
def baseEnd_5616639 : Nat := 961345156596118535927351

theorem tailTrace_5616639 : CollatzResearch.WordTrace tailWord_5616639 prefixEnd_5616639 961345156596118535927351 := by
  unfold tailWord_5616639
  simp only [CollatzResearch.WordTrace]
  refine ⟨204855653898883623416868971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136570435932589082277912647 204855653898883623416868971)
  ·
    refine ⟨307283480848325435125303457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204855653898883623416868971 307283480848325435125303457)
    ·
      refine ⟨230462610636244076343977593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307283480848325435125303457 230462610636244076343977593)
      ·
        refine ⟨172846957977183057257983195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 230462610636244076343977593 172846957977183057257983195)
        ·
          refine ⟨259270436965774585886974793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172846957977183057257983195 259270436965774585886974793)
          ·
            refine ⟨194452827724330939415231095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 259270436965774585886974793 194452827724330939415231095)
            ·
              refine ⟨291679241586496409122846643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194452827724330939415231095 291679241586496409122846643)
              ·
                refine ⟨437518862379744613684269965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291679241586496409122846643 437518862379744613684269965)
                ·
                  refine ⟨164069573392404230131601237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 437518862379744613684269965 164069573392404230131601237)
                  ·
                    refine ⟨961345156596118535927351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 164069573392404230131601237 961345156596118535927351)
                    ·
                      rfl

theorem cell23_5616639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 3, 9].length) (baseStart_5616639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616639 prefixEnd_5616639 := by exact prefixLift 5616639
  have htrace : WordTrace (prefixWord ++ tailWord_5616639) baseStart_5616639 baseEnd_5616639 := by
    simpa [prefixWord, tailWord_5616639, baseEnd_5616639] using wordTrace_append hprefix tailTrace_5616639
  have hstable : (prefixWord ++ tailWord_5616639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616639).length < 2 ^ (prefixWord ++ tailWord_5616639).sum := by decide
  have hdescent : baseEnd_5616639 < baseStart_5616639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616710 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_5616710 : Nat := 118140960795 + 5616710 * 2 ^ 59
def prefixEnd_5616710 : Nat := 4983230072969 + 3 ^ 40 * 5616710 * 2
def baseEnd_5616710 : Nat := 2884071926914824829994227

theorem tailTrace_5616710 : CollatzResearch.WordTrace tailWord_5616710 prefixEnd_5616710 2884071926914824829994227 := by
  unfold tailWord_5616710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6401820108800825079459487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136572162321084268361802389 6401820108800825079459487)
  ·
    refine ⟨9602730163201237619189231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6401820108800825079459487 9602730163201237619189231)
    ·
      refine ⟨14404095244801856428783847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9602730163201237619189231 14404095244801856428783847)
      ·
        refine ⟨21606142867202784643175771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14404095244801856428783847 21606142867202784643175771)
        ·
          refine ⟨32409214300804176964763657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21606142867202784643175771 32409214300804176964763657)
          ·
            refine ⟨24306910725603132723572743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32409214300804176964763657 24306910725603132723572743)
            ·
              refine ⟨36460366088404699085359115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24306910725603132723572743 36460366088404699085359115)
              ·
                refine ⟨54690549132607048628038673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36460366088404699085359115 54690549132607048628038673)
                ·
                  refine ⟨41017911849455286471029005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54690549132607048628038673 41017911849455286471029005)
                  ·
                    refine ⟨15381716943545732426635877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 41017911849455286471029005 15381716943545732426635877)
                    ·
                      refine ⟨2884071926914824829994227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15381716943545732426635877 2884071926914824829994227)
                      ·
                        rfl

theorem cell23_5616710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_5616710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616710 prefixEnd_5616710 := by exact prefixLift 5616710
  have htrace : WordTrace (prefixWord ++ tailWord_5616710) baseStart_5616710 baseEnd_5616710 := by
    simpa [prefixWord, tailWord_5616710, baseEnd_5616710] using wordTrace_append hprefix tailTrace_5616710
  have hstable : (prefixWord ++ tailWord_5616710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616710).length < 2 ^ (prefixWord ++ tailWord_5616710).sum := by decide
  have hdescent : baseEnd_5616710 < baseStart_5616710 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616716 : List Nat := [2, 2, 1, 3, 1, 1, 1, 5, 7]
def baseStart_5616716 : Nat := 118140960795 + 5616716 * 2 ^ 59
def prefixEnd_5616716 : Nat := 4983230072969 + 3 ^ 40 * 5616716 * 2
def baseEnd_5616716 : Nat := 320452778644305756279911

theorem tailTrace_5616716 : CollatzResearch.WordTrace tailWord_5616716 prefixEnd_5616716 320452778644305756279911 := by
  unfold tailWord_5616716
  simp only [CollatzResearch.WordTrace]
  refine ⟨102429231159802332783711001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136572308213069777044948001 102429231159802332783711001)
  ·
    refine ⟨76821923369851749587783251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102429231159802332783711001 76821923369851749587783251)
    ·
      refine ⟨115232885054777624381674877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76821923369851749587783251 115232885054777624381674877)
      ·
        refine ⟨43212331895541609143128079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115232885054777624381674877 43212331895541609143128079)
        ·
          refine ⟨64818497843312413714692119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43212331895541609143128079 64818497843312413714692119)
          ·
            refine ⟨97227746764968620572038179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64818497843312413714692119 97227746764968620572038179)
            ·
              refine ⟨145841620147452930858057269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97227746764968620572038179 145841620147452930858057269)
              ·
                refine ⟨13672651888823712267942869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145841620147452930858057269 13672651888823712267942869)
                ·
                  refine ⟨320452778644305756279911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13672651888823712267942869 320452778644305756279911)
                  ·
                    rfl

theorem cell23_5616716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 7].length) (baseStart_5616716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616716 prefixEnd_5616716 := by exact prefixLift 5616716
  have htrace : WordTrace (prefixWord ++ tailWord_5616716) baseStart_5616716 baseEnd_5616716 := by
    simpa [prefixWord, tailWord_5616716, baseEnd_5616716] using wordTrace_append hprefix tailTrace_5616716
  have hstable : (prefixWord ++ tailWord_5616716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616716).length < 2 ^ (prefixWord ++ tailWord_5616716).sum := by decide
  have hdescent : baseEnd_5616716 < baseStart_5616716 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616750 : List Nat := [4, 1, 2, 2, 1, 2, 1, 5, 5]
def baseStart_5616750 : Nat := 118140960795 + 5616750 * 2 ^ 59
def prefixEnd_5616750 : Nat := 4983230072969 + 3 ^ 40 * 5616750 * 2
def baseEnd_5616750 : Nat := 320454718460111630388227

theorem tailTrace_5616750 : CollatzResearch.WordTrace tailWord_5616750 prefixEnd_5616750 320454718460111630388227 := by
  unfold tailWord_5616750
  simp only [CollatzResearch.WordTrace]
  refine ⟨25607462800185186171769963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136573134934320992916106469 25607462800185186171769963)
  ·
    refine ⟨38411194200277779257654945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25607462800185186171769963 38411194200277779257654945)
    ·
      refine ⟨28808395650208334443241209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38411194200277779257654945 28808395650208334443241209)
      ·
        refine ⟨21606296737656250832430907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28808395650208334443241209 21606296737656250832430907)
        ·
          refine ⟨32409445106484376248646361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21606296737656250832430907 32409445106484376248646361)
          ·
            refine ⟨24307083829863282186484771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32409445106484376248646361 24307083829863282186484771)
            ·
              refine ⟨36460625744794923279727157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24307083829863282186484771 36460625744794923279727157)
              ·
                refine ⟨3418183663574524057474421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36460625744794923279727157 3418183663574524057474421)
                ·
                  refine ⟨320454718460111630388227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3418183663574524057474421 320454718460111630388227)
                  ·
                    rfl

theorem cell23_5616750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 5, 5].length) (baseStart_5616750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616750 prefixEnd_5616750 := by exact prefixLift 5616750
  have htrace : WordTrace (prefixWord ++ tailWord_5616750) baseStart_5616750 baseEnd_5616750 := by
    simpa [prefixWord, tailWord_5616750, baseEnd_5616750] using wordTrace_append hprefix tailTrace_5616750
  have hstable : (prefixWord ++ tailWord_5616750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616750).length < 2 ^ (prefixWord ++ tailWord_5616750).sum := by decide
  have hdescent : baseEnd_5616750 < baseStart_5616750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616753 : List Nat := [1, 2, 2, 2, 1, 1, 2, 2, 1, 7, 2]
def baseStart_5616753 : Nat := 118140960795 + 5616753 * 2 ^ 59
def prefixEnd_5616753 : Nat := 4983230072969 + 3 ^ 40 * 5616753 * 2
def baseEnd_5616753 : Nat := 2884094006582968161756529

theorem tailTrace_5616753 : CollatzResearch.WordTrace tailWord_5616753 prefixEnd_5616753 2884094006582968161756529 := by
  unfold tailWord_5616753
  simp only [CollatzResearch.WordTrace]
  refine ⟨204859811820470620886518913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136573207880313747257679275 204859811820470620886518913)
  ·
    refine ⟨153644858865352965664889185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204859811820470620886518913 153644858865352965664889185)
    ·
      refine ⟨115233644149014724248666889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153644858865352965664889185 115233644149014724248666889)
      ·
        refine ⟨86425233111761043186500167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115233644149014724248666889 86425233111761043186500167)
        ·
          refine ⟨129637849667641564779750251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86425233111761043186500167 129637849667641564779750251)
          ·
            refine ⟨194456774501462347169625377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129637849667641564779750251 194456774501462347169625377)
            ·
              refine ⟨145842580876096760377219033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 194456774501462347169625377 145842580876096760377219033)
              ·
                refine ⟨109381935657072570282914275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 145842580876096760377219033 109381935657072570282914275)
                ·
                  refine ⟨164072903485608855424371413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 109381935657072570282914275 164072903485608855424371413)
                  ·
                    refine ⟨3845458675443957549008705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 164072903485608855424371413 3845458675443957549008705)
                    ·
                      refine ⟨2884094006582968161756529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845458675443957549008705 2884094006582968161756529)
                      ·
                        rfl

theorem cell23_5616753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_5616753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616753 prefixEnd_5616753 := by exact prefixLift 5616753
  have htrace : WordTrace (prefixWord ++ tailWord_5616753) baseStart_5616753 baseEnd_5616753 := by
    simpa [prefixWord, tailWord_5616753, baseEnd_5616753] using wordTrace_append hprefix tailTrace_5616753
  have hstable : (prefixWord ++ tailWord_5616753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616753).length < 2 ^ (prefixWord ++ tailWord_5616753).sum := by decide
  have hdescent : baseEnd_5616753 < baseStart_5616753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616761 : List Nat := [1, 2, 1, 3, 6, 1, 1, 2, 2, 2, 2]
def baseStart_5616761 : Nat := 118140960795 + 5616761 * 2 ^ 59
def prefixEnd_5616761 : Nat := 4983230072969 + 3 ^ 40 * 5616761 * 2
def baseEnd_5616761 : Nat := 2884098114428204130456493

theorem tailTrace_5616761 : CollatzResearch.WordTrace tailWord_5616761 prefixEnd_5616761 2884098114428204130456493 := by
  unfold tailWord_5616761
  simp only [CollatzResearch.WordTrace]
  refine ⟨204860103604441638252810137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136573402402961092168540091 204860103604441638252810137)
  ·
    refine ⟨153645077703331228689607603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204860103604441638252810137 153645077703331228689607603)
    ·
      refine ⟨230467616554996843034411405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153645077703331228689607603 230467616554996843034411405)
      ·
        refine ⟨86425356208123816137904277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230467616554996843034411405 86425356208123816137904277)
        ·
          refine ⟨4051188572255803881464263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 86425356208123816137904277 4051188572255803881464263)
          ·
            refine ⟨6076782858383705822196395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051188572255803881464263 6076782858383705822196395)
            ·
              refine ⟨9115174287575558733294593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6076782858383705822196395 9115174287575558733294593)
              ·
                refine ⟨6836380715681669049970945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9115174287575558733294593 6836380715681669049970945)
                ·
                  refine ⟨5127285536761251787478209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6836380715681669049970945 5127285536761251787478209)
                  ·
                    refine ⟨3845464152570938840608657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5127285536761251787478209 3845464152570938840608657)
                    ·
                      refine ⟨2884098114428204130456493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845464152570938840608657 2884098114428204130456493)
                      ·
                        rfl

theorem cell23_5616761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_5616761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616761 prefixEnd_5616761 := by exact prefixLift 5616761
  have htrace : WordTrace (prefixWord ++ tailWord_5616761) baseStart_5616761 baseEnd_5616761 := by
    simpa [prefixWord, tailWord_5616761, baseEnd_5616761] using wordTrace_append hprefix tailTrace_5616761
  have hstable : (prefixWord ++ tailWord_5616761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616761).length < 2 ^ (prefixWord ++ tailWord_5616761).sum := by decide
  have hdescent : baseEnd_5616761 < baseStart_5616761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616783 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 5, 6, 2]
def baseStart_5616783 : Nat := 118140960795 + 5616783 * 2 ^ 59
def prefixEnd_5616783 : Nat := 4983230072969 + 3 ^ 40 * 5616783 * 2
def baseEnd_5616783 : Nat := 2884109411002603044381391

theorem tailTrace_5616783 : CollatzResearch.WordTrace tailWord_5616783 prefixEnd_5616783 2884109411002603044381391 := by
  unfold tailWord_5616783
  simp only [CollatzResearch.WordTrace]
  refine ⟨204860906010361936010111003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136573937340241290673407335 204860906010361936010111003)
  ·
    refine ⟨307291359015542904015166505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204860906010361936010111003 307291359015542904015166505)
    ·
      refine ⟨230468519261657178011374879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307291359015542904015166505 230468519261657178011374879)
      ·
        refine ⟨345702778892485767017062319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230468519261657178011374879 345702778892485767017062319)
        ·
          refine ⟨518554168338728650525593479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345702778892485767017062319 518554168338728650525593479)
          ·
            refine ⟨777831252508092975788390219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518554168338728650525593479 777831252508092975788390219)
            ·
              refine ⟨1166746878762139463682585329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777831252508092975788390219 1166746878762139463682585329)
              ·
                refine ⟨875060159071604597761938997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1166746878762139463682585329 875060159071604597761938997)
                ·
                  refine ⟨82036889912962931040181781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 875060159071604597761938997 82036889912962931040181781)
                  ·
                    refine ⟨3845479214670137392508521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82036889912962931040181781 3845479214670137392508521)
                    ·
                      refine ⟨2884109411002603044381391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845479214670137392508521 2884109411002603044381391)
                      ·
                        rfl

theorem cell23_5616783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 6, 2].length) (baseStart_5616783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616783 prefixEnd_5616783 := by exact prefixLift 5616783
  have htrace : WordTrace (prefixWord ++ tailWord_5616783) baseStart_5616783 baseEnd_5616783 := by
    simpa [prefixWord, tailWord_5616783, baseEnd_5616783] using wordTrace_append hprefix tailTrace_5616783
  have hstable : (prefixWord ++ tailWord_5616783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616783).length < 2 ^ (prefixWord ++ tailWord_5616783).sum := by decide
  have hdescent : baseEnd_5616783 < baseStart_5616783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616803 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 3]
def baseStart_5616803 : Nat := 118140960795 + 5616803 * 2 ^ 59
def prefixEnd_5616803 : Nat := 4983230072969 + 3 ^ 40 * 5616803 * 2
def baseEnd_5616803 : Nat := 2884119680615692966131299

theorem tailTrace_5616803 : CollatzResearch.WordTrace tailWord_5616803 prefixEnd_5616803 2884119680615692966131299 := by
  unfold tailWord_5616803
  simp only [CollatzResearch.WordTrace]
  refine ⟨204861635470289479425839063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136574423646859652950559375 204861635470289479425839063)
  ·
    refine ⟨307292453205434219138758595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204861635470289479425839063 307292453205434219138758595)
    ·
      refine ⟨460938679808151328708137893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307292453205434219138758595 460938679808151328708137893)
      ·
        refine ⟨86426002464028374132775855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 460938679808151328708137893 86426002464028374132775855)
        ·
          refine ⟨129639003696042561199163783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 86426002464028374132775855 129639003696042561199163783)
          ·
            refine ⟨194458505544063841798745675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 129639003696042561199163783 194458505544063841798745675)
            ·
              refine ⟨291687758316095762698118513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 194458505544063841798745675 291687758316095762698118513)
              ·
                refine ⟨218765818737071822023588885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291687758316095762698118513 218765818737071822023588885)
                ·
                  refine ⟨10254647753300241657355729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 218765818737071822023588885 10254647753300241657355729)
                  ·
                    refine ⟨7690985814975181243016797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10254647753300241657355729 7690985814975181243016797)
                    ·
                      refine ⟨2884119680615692966131299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7690985814975181243016797 2884119680615692966131299)
                      ·
                        rfl

theorem cell23_5616803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_5616803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616803 prefixEnd_5616803 := by exact prefixLift 5616803
  have htrace : WordTrace (prefixWord ++ tailWord_5616803) baseStart_5616803 baseEnd_5616803 := by
    simpa [prefixWord, tailWord_5616803, baseEnd_5616803] using wordTrace_append hprefix tailTrace_5616803
  have hstable : (prefixWord ++ tailWord_5616803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616803).length < 2 ^ (prefixWord ++ tailWord_5616803).sum := by decide
  have hdescent : baseEnd_5616803 < baseStart_5616803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616823 : List Nat := [1, 1, 3, 1, 4, 1, 2, 4, 6]
def baseStart_5616823 : Nat := 118140960795 + 5616823 * 2 ^ 59
def prefixEnd_5616823 : Nat := 4983230072969 + 3 ^ 40 * 5616823 * 2
def baseEnd_5616823 : Nat := 320458883358753654209023

theorem tailTrace_5616823 : CollatzResearch.WordTrace tailWord_5616823 prefixEnd_5616823 320458883358753654209023 := by
  unfold tailWord_5616823
  simp only [CollatzResearch.WordTrace]
  refine ⟨204862364930217022841567123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136574909953478015227711415 204862364930217022841567123)
  ·
    refine ⟨307293547395325534262350685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204862364930217022841567123 307293547395325534262350685)
    ·
      refine ⟨115235080273247075348381507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307293547395325534262350685 115235080273247075348381507)
      ·
        refine ⟨172852620409870613022572261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115235080273247075348381507 172852620409870613022572261)
        ·
          refine ⟨32409866326850739941732299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 172852620409870613022572261 32409866326850739941732299)
          ·
            refine ⟨48614799490276109912598449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32409866326850739941732299 48614799490276109912598449)
            ·
              refine ⟨36461099617707082434448837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48614799490276109912598449 36461099617707082434448837)
              ·
                refine ⟨6836456178320077956459157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36461099617707082434448837 6836456178320077956459157)
                ·
                  refine ⟨320458883358753654209023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6836456178320077956459157 320458883358753654209023)
                  ·
                    rfl

theorem cell23_5616823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 4, 6].length) (baseStart_5616823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616823 prefixEnd_5616823 := by exact prefixLift 5616823
  have htrace : WordTrace (prefixWord ++ tailWord_5616823) baseStart_5616823 baseEnd_5616823 := by
    simpa [prefixWord, tailWord_5616823, baseEnd_5616823] using wordTrace_append hprefix tailTrace_5616823
  have hstable : (prefixWord ++ tailWord_5616823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616823).length < 2 ^ (prefixWord ++ tailWord_5616823).sum := by decide
  have hdescent : baseEnd_5616823 < baseStart_5616823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616840 : List Nat := [2, 1, 3, 1, 2, 1, 6, 1, 6]
def baseStart_5616840 : Nat := 118140960795 + 5616840 * 2 ^ 59
def prefixEnd_5616840 : Nat := 4983230072969 + 3 ^ 40 * 5616840 * 2
def baseEnd_5616840 : Nat := 320459853266656591263181

theorem tailTrace_5616840 : CollatzResearch.WordTrace tailWord_5616840 prefixEnd_5616840 320459853266656591263181 := by
  unfold tailWord_5616840
  simp only [CollatzResearch.WordTrace]
  refine ⟨102431492485577717372467987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136575323314103623163290649 102431492485577717372467987)
  ·
    refine ⟨153647238728366576058701981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102431492485577717372467987 153647238728366576058701981)
    ·
      refine ⟨57617714523137466022013243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153647238728366576058701981 57617714523137466022013243)
      ·
        refine ⟨86426571784706199033019865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57617714523137466022013243 86426571784706199033019865)
        ·
          refine ⟨64819928838529649274764899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 86426571784706199033019865 64819928838529649274764899)
          ·
            refine ⟨97229893257794473912147349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64819928838529649274764899 97229893257794473912147349)
            ·
              refine ⟨4557651246459115964631907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 97229893257794473912147349 4557651246459115964631907)
              ·
                refine ⟨6836476869688673946947861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4557651246459115964631907 6836476869688673946947861)
                ·
                  refine ⟨320459853266656591263181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6836476869688673946947861 320459853266656591263181)
                  ·
                    rfl

theorem cell23_5616840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 6, 1, 6].length) (baseStart_5616840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616840 prefixEnd_5616840 := by exact prefixLift 5616840
  have htrace : WordTrace (prefixWord ++ tailWord_5616840) baseStart_5616840 baseEnd_5616840 := by
    simpa [prefixWord, tailWord_5616840, baseEnd_5616840] using wordTrace_append hprefix tailTrace_5616840
  have hstable : (prefixWord ++ tailWord_5616840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616840).length < 2 ^ (prefixWord ++ tailWord_5616840).sum := by decide
  have hdescent : baseEnd_5616840 < baseStart_5616840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616873 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_5616873 : Nat := 118140960795 + 5616873 * 2 ^ 59
def prefixEnd_5616873 : Nat := 4983230072969 + 3 ^ 40 * 5616873 * 2
def baseEnd_5616873 : Nat := 2884155624261507692255977

theorem tailTrace_5616873 : CollatzResearch.WordTrace tailWord_5616873 prefixEnd_5616873 2884155624261507692255977 := by
  unfold tailWord_5616873
  simp only [CollatzResearch.WordTrace]
  refine ⟨204864188580035881380887273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136576125720023920920591515 204864188580035881380887273)
  ·
    refine ⟨153648141435026911035665455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204864188580035881380887273 153648141435026911035665455)
    ·
      refine ⟨230472212152540366553498183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153648141435026911035665455 230472212152540366553498183)
      ·
        refine ⟨345708318228810549830247275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230472212152540366553498183 345708318228810549830247275)
        ·
          refine ⟨518562477343215824745370913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345708318228810549830247275 518562477343215824745370913)
          ·
            refine ⟨388921858007411868559028185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 518562477343215824745370913 388921858007411868559028185)
            ·
              refine ⟨291691393505558901419271139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388921858007411868559028185 291691393505558901419271139)
              ·
                refine ⟨437537090258338352128906709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291691393505558901419271139 437537090258338352128906709)
                ·
                  refine ⟨10254775552929805128021251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 437537090258338352128906709 10254775552929805128021251)
                  ·
                    refine ⟨15382163329394707692031877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10254775552929805128021251 15382163329394707692031877)
                    ·
                      refine ⟨2884155624261507692255977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15382163329394707692031877 2884155624261507692255977)
                      ·
                        rfl

theorem cell23_5616873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_5616873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616873 prefixEnd_5616873 := by exact prefixLift 5616873
  have htrace : WordTrace (prefixWord ++ tailWord_5616873) baseStart_5616873 baseEnd_5616873 := by
    simpa [prefixWord, tailWord_5616873, baseEnd_5616873] using wordTrace_append hprefix tailTrace_5616873
  have hstable : (prefixWord ++ tailWord_5616873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616873).length < 2 ^ (prefixWord ++ tailWord_5616873).sum := by decide
  have hdescent : baseEnd_5616873 < baseStart_5616873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616900 : List Nat := [2, 3, 2, 2, 2, 1, 1, 3, 1, 6]
def baseStart_5616900 : Nat := 118140960795 + 5616900 * 2 ^ 59
def prefixEnd_5616900 : Nat := 4983230072969 + 3 ^ 40 * 5616900 * 2
def baseEnd_5616900 : Nat := 961389829413059695539451

theorem tailTrace_5616900 : CollatzResearch.WordTrace tailWord_5616900 prefixEnd_5616900 961389829413059695539451 := by
  unfold tailWord_5616900
  simp only [CollatzResearch.WordTrace]
  refine ⟨102432586675469032496060077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136576782233958709994746769 102432586675469032496060077)
  ·
    refine ⟨38412220003300887186022529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102432586675469032496060077 38412220003300887186022529)
    ·
      refine ⟨28809165002475665389516897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38412220003300887186022529 28809165002475665389516897)
      ·
        refine ⟨21606873751856749042137673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28809165002475665389516897 21606873751856749042137673)
        ·
          refine ⟨16205155313892561781603255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21606873751856749042137673 16205155313892561781603255)
          ·
            refine ⟨24307732970838842672404883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16205155313892561781603255 24307732970838842672404883)
            ·
              refine ⟨36461599456258264008607325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24307732970838842672404883 36461599456258264008607325)
              ·
                refine ⟨13673099796096849003227747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36461599456258264008607325 13673099796096849003227747)
                ·
                  refine ⟨20509649694145273504841621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13673099796096849003227747 20509649694145273504841621)
                  ·
                    refine ⟨961389829413059695539451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20509649694145273504841621 961389829413059695539451)
                    ·
                      rfl

theorem cell23_5616900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_5616900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616900 prefixEnd_5616900 := by exact prefixLift 5616900
  have htrace : WordTrace (prefixWord ++ tailWord_5616900) baseStart_5616900 baseEnd_5616900 := by
    simpa [prefixWord, tailWord_5616900, baseEnd_5616900] using wordTrace_append hprefix tailTrace_5616900
  have hstable : (prefixWord ++ tailWord_5616900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616900).length < 2 ^ (prefixWord ++ tailWord_5616900).sum := by decide
  have hdescent : baseEnd_5616900 < baseStart_5616900 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616907 : List Nat := [1, 1, 1, 1, 5, 3, 1, 1, 5, 2, 2]
def baseStart_5616907 : Nat := 118140960795 + 5616907 * 2 ^ 59
def prefixEnd_5616907 : Nat := 4983230072969 + 3 ^ 40 * 5616907 * 2
def baseEnd_5616907 : Nat := 2884173082603760559230821

theorem tailTrace_5616907 : CollatzResearch.WordTrace tailWord_5616907 prefixEnd_5616907 2884173082603760559230821 := by
  unfold tailWord_5616907
  simp only [CollatzResearch.WordTrace]
  refine ⟨204865428661912705187624975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136576952441275136791749983 204865428661912705187624975)
  ·
    refine ⟨307298142992869057781437463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204865428661912705187624975 307298142992869057781437463)
    ·
      refine ⟨460947214489303586672156195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307298142992869057781437463 460947214489303586672156195)
      ·
        refine ⟨691420821733955380008234293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460947214489303586672156195 691420821733955380008234293)
        ·
          refine ⟨64820702037558316875771965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 691420821733955380008234293 64820702037558316875771965)
          ·
            refine ⟨24307763264084368828414487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64820702037558316875771965 24307763264084368828414487)
            ·
              refine ⟨36461644896126553242621731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24307763264084368828414487 36461644896126553242621731)
              ·
                refine ⟨54692467344189829863932597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36461644896126553242621731 54692467344189829863932597)
                ·
                  refine ⟨5127418813517796549743681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54692467344189829863932597 5127418813517796549743681)
                  ·
                    refine ⟨3845564110138347412307761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5127418813517796549743681 3845564110138347412307761)
                    ·
                      refine ⟨2884173082603760559230821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845564110138347412307761 2884173082603760559230821)
                      ·
                        rfl

theorem cell23_5616907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 5, 2, 2].length) (baseStart_5616907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616907 prefixEnd_5616907 := by exact prefixLift 5616907
  have htrace : WordTrace (prefixWord ++ tailWord_5616907) baseStart_5616907 baseEnd_5616907 := by
    simpa [prefixWord, tailWord_5616907, baseEnd_5616907] using wordTrace_append hprefix tailTrace_5616907
  have hstable : (prefixWord ++ tailWord_5616907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616907).length < 2 ^ (prefixWord ++ tailWord_5616907).sum := by decide
  have hdescent : baseEnd_5616907 < baseStart_5616907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616920 : List Nat := [2, 1, 2, 3, 1, 3, 2, 2, 1, 2, 4]
def baseStart_5616920 : Nat := 118140960795 + 5616920 * 2 ^ 59
def prefixEnd_5616920 : Nat := 4983230072969 + 3 ^ 40 * 5616920 * 2
def baseEnd_5616920 : Nat := 2884179757852269008368261

theorem tailTrace_5616920 : CollatzResearch.WordTrace tailWord_5616920 prefixEnd_5616920 2884179757852269008368261 := by
  unfold tailWord_5616920
  simp only [CollatzResearch.WordTrace]
  refine ⟨102432951405432804203924107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136577268540577072271898809 102432951405432804203924107)
  ·
    refine ⟨153649427108149206305886161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102432951405432804203924107 153649427108149206305886161)
    ·
      refine ⟨115237070331111904729414621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153649427108149206305886161 115237070331111904729414621)
      ·
        refine ⟨43213901374166964273530483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115237070331111904729414621 43213901374166964273530483)
        ·
          refine ⟨64820852061250446410295725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43213901374166964273530483 64820852061250446410295725)
          ·
            refine ⟨24307819522968917403860897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64820852061250446410295725 24307819522968917403860897)
            ·
              refine ⟨18230864642226688052895673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24307819522968917403860897 18230864642226688052895673)
              ·
                refine ⟨13673148481670016039671755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18230864642226688052895673 13673148481670016039671755)
                ·
                  refine ⟨20509722722505024059507633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13673148481670016039671755 20509722722505024059507633)
                  ·
                    refine ⟨15382292041878768044630725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20509722722505024059507633 15382292041878768044630725)
                    ·
                      refine ⟨2884179757852269008368261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15382292041878768044630725 2884179757852269008368261)
                      ·
                        rfl

theorem cell23_5616920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_5616920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616920 prefixEnd_5616920 := by exact prefixLift 5616920
  have htrace : WordTrace (prefixWord ++ tailWord_5616920) baseStart_5616920 baseEnd_5616920 := by
    simpa [prefixWord, tailWord_5616920, baseEnd_5616920] using wordTrace_append hprefix tailTrace_5616920
  have hstable : (prefixWord ++ tailWord_5616920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616920).length < 2 ^ (prefixWord ++ tailWord_5616920).sum := by decide
  have hdescent : baseEnd_5616920 < baseStart_5616920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616930 : List Nat := [3, 3, 1, 1, 4, 1, 10]
def baseStart_5616930 : Nat := 118140960795 + 5616930 * 2 ^ 59
def prefixEnd_5616930 : Nat := 4983230072969 + 3 ^ 40 * 5616930 * 2
def baseEnd_5616930 : Nat := 35607220897022394682015

theorem tailTrace_5616930 : CollatzResearch.WordTrace tailWord_5616930 prefixEnd_5616930 35607220897022394682015 := by
  unfold tailWord_5616930
  simp only [CollatzResearch.WordTrace]
  refine ⟨51216566885207345028928061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136577511693886253410474829 51216566885207345028928061)
  ·
    refine ⟨19206212581952754385848023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 51216566885207345028928061 19206212581952754385848023)
    ·
      refine ⟨28809318872929131578772035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19206212581952754385848023 28809318872929131578772035)
      ·
        refine ⟨43213978309393697368158053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28809318872929131578772035 43213978309393697368158053)
        ·
          refine ⟨8102620933011318256529635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43213978309393697368158053 8102620933011318256529635)
          ·
            refine ⟨12153931399516977384794453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8102620933011318256529635 12153931399516977384794453)
            ·
              refine ⟨35607220897022394682015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12153931399516977384794453 35607220897022394682015)
              ·
                rfl

theorem cell23_5616930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 10].length) (baseStart_5616930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616930 prefixEnd_5616930 := by exact prefixLift 5616930
  have htrace : WordTrace (prefixWord ++ tailWord_5616930) baseStart_5616930 baseEnd_5616930 := by
    simpa [prefixWord, tailWord_5616930, baseEnd_5616930] using wordTrace_append hprefix tailTrace_5616930
  have hstable : (prefixWord ++ tailWord_5616930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616930).length < 2 ^ (prefixWord ++ tailWord_5616930).sum := by decide
  have hdescent : baseEnd_5616930 < baseStart_5616930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616941 : List Nat := [1, 5, 3, 1, 1, 1, 1, 3, 3, 2, 2]
def baseStart_5616941 : Nat := 118140960795 + 5616941 * 2 ^ 59
def prefixEnd_5616941 : Nat := 4983230072969 + 3 ^ 40 * 5616941 * 2
def baseEnd_5616941 : Nat := 2884190540946013426205665

theorem tailTrace_5616941 : CollatzResearch.WordTrace tailWord_5616941 prefixEnd_5616941 2884190540946013426205665 := by
  unfold tailWord_5616941
  simp only [CollatzResearch.WordTrace]
  refine ⟨204866668743789528994362677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136577779162526352662908451 204866668743789528994362677)
  ·
    refine ⟨19206250194730268343221501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 204866668743789528994362677 19206250194730268343221501)
    ·
      refine ⟨7202343823023850628708063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19206250194730268343221501 7202343823023850628708063)
      ·
        refine ⟨10803515734535775943062095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7202343823023850628708063 10803515734535775943062095)
        ·
          refine ⟨16205273601803663914593143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10803515734535775943062095 16205273601803663914593143)
          ·
            refine ⟨24307910402705495871889715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16205273601803663914593143 24307910402705495871889715)
            ·
              refine ⟨36461865604058243807834573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24307910402705495871889715 36461865604058243807834573)
              ·
                refine ⟨13673199601521841427937965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36461865604058243807834573 13673199601521841427937965)
                ·
                  refine ⟨5127449850570690535476737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13673199601521841427937965 5127449850570690535476737)
                  ·
                    refine ⟨3845587387928017901607553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5127449850570690535476737 3845587387928017901607553)
                    ·
                      refine ⟨2884190540946013426205665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845587387928017901607553 2884190540946013426205665)
                      ·
                        rfl

theorem cell23_5616941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_5616941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616941 prefixEnd_5616941 := by exact prefixLift 5616941
  have htrace : WordTrace (prefixWord ++ tailWord_5616941) baseStart_5616941 baseEnd_5616941 := by
    simpa [prefixWord, tailWord_5616941, baseEnd_5616941] using wordTrace_append hprefix tailTrace_5616941
  have hstable : (prefixWord ++ tailWord_5616941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616941).length < 2 ^ (prefixWord ++ tailWord_5616941).sum := by decide
  have hdescent : baseEnd_5616941 < baseStart_5616941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5616964 : List Nat := [2, 3, 4, 1, 1, 3, 2, 7]
def baseStart_5616964 : Nat := 118140960795 + 5616964 * 2 ^ 59
def prefixEnd_5616964 : Nat := 4983230072969 + 3 ^ 40 * 5616964 * 2
def baseEnd_5616964 : Nat := 106822309296335808748817

theorem tailTrace_5616964 : CollatzResearch.WordTrace tailWord_5616964 prefixEnd_5616964 106822309296335808748817 := by
  unfold tailWord_5616964
  simp only [CollatzResearch.WordTrace]
  refine ⟨102433753811353101961224973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136578338415137469281633297 102433753811353101961224973)
  ·
    refine ⟨38412657679257413235459365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 102433753811353101961224973 38412657679257413235459365)
    ·
      refine ⟨7202373314860764981648631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38412657679257413235459365 7202373314860764981648631)
      ·
        refine ⟨10803559972291147472472947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7202373314860764981648631 10803559972291147472472947)
        ·
          refine ⟨16205339958436721208709421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10803559972291147472472947 16205339958436721208709421)
          ·
            refine ⟨6077002484413770453266033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16205339958436721208709421 6077002484413770453266033)
            ·
              refine ⟨4557751863310327839949525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6077002484413770453266033 4557751863310327839949525)
              ·
                refine ⟨106822309296335808748817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4557751863310327839949525 106822309296335808748817)
                ·
                  rfl

theorem cell23_5616964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 3, 2, 7].length) (baseStart_5616964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5616964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5616964 prefixEnd_5616964 := by exact prefixLift 5616964
  have htrace : WordTrace (prefixWord ++ tailWord_5616964) baseStart_5616964 baseEnd_5616964 := by
    simpa [prefixWord, tailWord_5616964, baseEnd_5616964] using wordTrace_append hprefix tailTrace_5616964
  have hstable : (prefixWord ++ tailWord_5616964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5616964).length < 2 ^ (prefixWord ++ tailWord_5616964).sum := by decide
  have hdescent : baseEnd_5616964 < baseStart_5616964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5616964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617010 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_5617010 : Nat := 118140960795 + 5617010 * 2 ^ 59
def prefixEnd_5617010 : Nat := 4983230072969 + 3 ^ 40 * 5617010 * 2
def baseEnd_5617010 : Nat := 2884225971111173656242847

theorem tailTrace_5617010 : CollatzResearch.WordTrace tailWord_5617010 prefixEnd_5617010 2884225971111173656242847 := by
  unfold tailWord_5617010
  simp only [CollatzResearch.WordTrace]
  refine ⟨51217296345134888444656121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136579456920359702519082989 51217296345134888444656121)
  ·
    refine ⟨38412972258851166333492091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51217296345134888444656121 38412972258851166333492091)
    ·
      refine ⟨57619458388276749500238137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38412972258851166333492091 57619458388276749500238137)
      ·
        refine ⟨43214593791207562125178603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57619458388276749500238137 43214593791207562125178603)
        ·
          refine ⟨64821890686811343187767905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 43214593791207562125178603 64821890686811343187767905)
          ·
            refine ⟨48616418015108507390825929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64821890686811343187767905 48616418015108507390825929)
            ·
              refine ⟨36462313511331380543119447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48616418015108507390825929 36462313511331380543119447)
              ·
                refine ⟨54693470266997070814679171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36462313511331380543119447 54693470266997070814679171)
                ·
                  refine ⟨82040205400495606222018757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54693470266997070814679171 82040205400495606222018757)
                  ·
                    refine ⟨15382538512592926166628517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82040205400495606222018757 15382538512592926166628517)
                    ·
                      refine ⟨2884225971111173656242847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15382538512592926166628517 2884225971111173656242847)
                      ·
                        rfl

theorem cell23_5617010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_5617010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617010 prefixEnd_5617010 := by exact prefixLift 5617010
  have htrace : WordTrace (prefixWord ++ tailWord_5617010) baseStart_5617010 baseEnd_5617010 := by
    simpa [prefixWord, tailWord_5617010, baseEnd_5617010] using wordTrace_append hprefix tailTrace_5617010
  have hstable : (prefixWord ++ tailWord_5617010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617010).length < 2 ^ (prefixWord ++ tailWord_5617010).sum := by decide
  have hdescent : baseEnd_5617010 < baseStart_5617010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617048 : List Nat := [2, 1, 2, 5, 2, 1, 2, 2, 2, 2, 2]
def baseStart_5617048 : Nat := 118140960795 + 5617048 * 2 ^ 59
def prefixEnd_5617048 : Nat := 4983230072969 + 3 ^ 40 * 5617048 * 2
def baseEnd_5617048 : Nat := 2884245483376044507567673

theorem tailTrace_5617048 : CollatzResearch.WordTrace tailWord_5617048 prefixEnd_5617048 2884245483376044507567673 := by
  unfold tailWord_5617048
  simp only [CollatzResearch.WordTrace]
  refine ⟨102435285677200943134253899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136580380902934590845671865 102435285677200943134253899)
  ·
    refine ⟨153652928515801414701380849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102435285677200943134253899 153652928515801414701380849)
    ·
      refine ⟨115239696386851061026035637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153652928515801414701380849 115239696386851061026035637)
      ·
        refine ⟨10803721536267286971190841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 115239696386851061026035637 10803721536267286971190841)
        ·
          refine ⟨8102791152200465228393131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10803721536267286971190841 8102791152200465228393131)
          ·
            refine ⟨12154186728300697842589697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8102791152200465228393131 12154186728300697842589697)
            ·
              refine ⟨9115640046225523381942273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12154186728300697842589697 9115640046225523381942273)
              ·
                refine ⟨6836730034669142536456705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9115640046225523381942273 6836730034669142536456705)
                ·
                  refine ⟨5127547526001856902342529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6836730034669142536456705 5127547526001856902342529)
                  ·
                    refine ⟨3845660644501392676756897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5127547526001856902342529 3845660644501392676756897)
                    ·
                      refine ⟨2884245483376044507567673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845660644501392676756897 2884245483376044507567673)
                      ·
                        rfl

theorem cell23_5617048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_5617048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617048 prefixEnd_5617048 := by exact prefixLift 5617048
  have htrace : WordTrace (prefixWord ++ tailWord_5617048) baseStart_5617048 baseEnd_5617048 := by
    simpa [prefixWord, tailWord_5617048, baseEnd_5617048] using wordTrace_append hprefix tailTrace_5617048
  have hstable : (prefixWord ++ tailWord_5617048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617048).length < 2 ^ (prefixWord ++ tailWord_5617048).sum := by decide
  have hdescent : baseEnd_5617048 < baseStart_5617048 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617114 : List Nat := [3, 1, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_5617114 : Nat := 118140960795 + 5617114 * 2 ^ 59
def prefixEnd_5617114 : Nat := 4983230072969 + 3 ^ 40 * 5617114 * 2
def baseEnd_5617114 : Nat := 961426457699747083114123

theorem tailTrace_5617114 : CollatzResearch.WordTrace tailWord_5617114 prefixEnd_5617114 961426457699747083114123 := by
  unfold tailWord_5617114
  simp only [CollatzResearch.WordTrace]
  refine ⟨51218244643040694885102599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136581985714775186360273597 51218244643040694885102599)
  ·
    refine ⟨76827366964561042327653899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51218244643040694885102599 76827366964561042327653899)
    ·
      refine ⟨115241050446841563491480849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76827366964561042327653899 115241050446841563491480849)
      ·
        refine ⟨86430787835131172618610637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 115241050446841563491480849 86430787835131172618610637)
        ·
          refine ⟨32411545438174189731978989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86430787835131172618610637 32411545438174189731978989)
          ·
            refine ⟨12154329539315321149492121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32411545438174189731978989 12154329539315321149492121)
            ·
              refine ⟨9115747154486490862119091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12154329539315321149492121 9115747154486490862119091)
              ·
                refine ⟨13673620731729736293178637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9115747154486490862119091 13673620731729736293178637)
                ·
                  refine ⟨5127607774398651109941989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13673620731729736293178637 5127607774398651109941989)
                  ·
                    refine ⟨961426457699747083114123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5127607774398651109941989 961426457699747083114123)
                    ·
                      rfl

theorem cell23_5617114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_5617114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617114 prefixEnd_5617114 := by exact prefixLift 5617114
  have htrace : WordTrace (prefixWord ++ tailWord_5617114) baseStart_5617114 baseEnd_5617114 := by
    simpa [prefixWord, tailWord_5617114, baseEnd_5617114] using wordTrace_append hprefix tailTrace_5617114
  have hstable : (prefixWord ++ tailWord_5617114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617114).length < 2 ^ (prefixWord ++ tailWord_5617114).sum := by decide
  have hdescent : baseEnd_5617114 < baseStart_5617114 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617165 : List Nat := [1, 7, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_5617165 : Nat := 118140960795 + 5617165 * 2 ^ 59
def prefixEnd_5617165 : Nat := 4983230072969 + 3 ^ 40 * 5617165 * 2
def baseEnd_5617165 : Nat := 961435186870873516601545

theorem tailTrace_5617165 : CollatzResearch.WordTrace tailWord_5617165 prefixEnd_5617165 961435186870873516601545 := by
  unfold tailWord_5617165
  simp only [CollatzResearch.WordTrace]
  refine ⟨204874838694978015250516949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136583225796652010167011299 204874838694978015250516949)
  ·
    refine ⟨4801754031913547232433991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 204874838694978015250516949 4801754031913547232433991)
    ·
      refine ⟨7202631047870320848650987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4801754031913547232433991 7202631047870320848650987)
      ·
        refine ⟨10803946571805481272976481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7202631047870320848650987 10803946571805481272976481)
        ·
          refine ⟨8102959928854110954732361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10803946571805481272976481 8102959928854110954732361)
          ·
            refine ⟨6077219946640583216049271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8102959928854110954732361 6077219946640583216049271)
            ·
              refine ⟨9115829919960874824073907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077219946640583216049271 9115829919960874824073907)
              ·
                refine ⟨13673744879941312236110861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9115829919960874824073907 13673744879941312236110861)
                ·
                  refine ⟨5127654329977992088541573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13673744879941312236110861 5127654329977992088541573)
                  ·
                    refine ⟨961435186870873516601545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5127654329977992088541573 961435186870873516601545)
                    ·
                      rfl

theorem cell23_5617165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_5617165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617165 prefixEnd_5617165 := by exact prefixLift 5617165
  have htrace : WordTrace (prefixWord ++ tailWord_5617165) baseStart_5617165 baseEnd_5617165 := by
    simpa [prefixWord, tailWord_5617165, baseEnd_5617165] using wordTrace_append hprefix tailTrace_5617165
  have hstable : (prefixWord ++ tailWord_5617165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617165).length < 2 ^ (prefixWord ++ tailWord_5617165).sum := by decide
  have hdescent : baseEnd_5617165 < baseStart_5617165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617171 : List Nat := [1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 3]
def baseStart_5617171 : Nat := 118140960795 + 5617171 * 2 ^ 59
def prefixEnd_5617171 : Nat := 4983230072969 + 3 ^ 40 * 5617171 * 2
def baseEnd_5617171 : Nat := 2884308641496547526329607

theorem tailTrace_5617171 : CollatzResearch.WordTrace tailWord_5617171 prefixEnd_5617171 2884308641496547526329607 := by
  unfold tailWord_5617171
  simp only [CollatzResearch.WordTrace]
  refine ⟨204875057532956278275235367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136583371688637518850156911 204875057532956278275235367)
  ·
    refine ⟨307312586299434417412853051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204875057532956278275235367 307312586299434417412853051)
    ·
      refine ⟨460968879449151626119279577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307312586299434417412853051 460968879449151626119279577)
      ·
        refine ⟨345726659586863719589459683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 460968879449151626119279577 345726659586863719589459683)
        ·
          refine ⟨518589989380295579384189525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 345726659586863719589459683 518589989380295579384189525)
          ·
            refine ⟨6077226438050338820908471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 518589989380295579384189525 6077226438050338820908471)
            ·
              refine ⟨9115839657075508231362707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077226438050338820908471 9115839657075508231362707)
              ·
                refine ⟨13673759485613262347044061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9115839657075508231362707 13673759485613262347044061)
                ·
                  refine ⟨5127659807104973380141523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13673759485613262347044061 5127659807104973380141523)
                  ·
                    refine ⟨7691489710657460070212285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5127659807104973380141523 7691489710657460070212285)
                    ·
                      refine ⟨2884308641496547526329607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7691489710657460070212285 2884308641496547526329607)
                      ·
                        rfl

theorem cell23_5617171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 1, 3].length) (baseStart_5617171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617171 prefixEnd_5617171 := by exact prefixLift 5617171
  have htrace : WordTrace (prefixWord ++ tailWord_5617171) baseStart_5617171 baseEnd_5617171 := by
    simpa [prefixWord, tailWord_5617171, baseEnd_5617171] using wordTrace_append hprefix tailTrace_5617171
  have hstable : (prefixWord ++ tailWord_5617171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617171).length < 2 ^ (prefixWord ++ tailWord_5617171).sum := by decide
  have hdescent : baseEnd_5617171 < baseStart_5617171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617194 : List Nat := [3, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_5617194 : Nat := 118140960795 + 5617194 * 2 ^ 59
def prefixEnd_5617194 : Nat := 4983230072969 + 3 ^ 40 * 5617194 * 2
def baseEnd_5617194 : Nat := 2884320451551600936342001

theorem tailTrace_5617194 : CollatzResearch.WordTrace tailWord_5617194 prefixEnd_5617194 2884320451551600936342001 := by
  unfold tailWord_5617194
  simp only [CollatzResearch.WordTrace]
  refine ⟨51218974102968238300830659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136583930941248635468881757 51218974102968238300830659)
  ·
    refine ⟨76828461154452357451245989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 51218974102968238300830659 76828461154452357451245989)
    ·
      refine ⟨14405336466459817022108623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76828461154452357451245989 14405336466459817022108623)
      ·
        refine ⟨21608004699689725533162935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14405336466459817022108623 21608004699689725533162935)
        ·
          refine ⟨32412007049534588299744403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21608004699689725533162935 32412007049534588299744403)
          ·
            refine ⟨48618010574301882449616605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32412007049534588299744403 48618010574301882449616605)
            ·
              refine ⟨18231753965363205918606227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48618010574301882449616605 18231753965363205918606227)
              ·
                refine ⟨27347630948044808877909341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18231753965363205918606227 27347630948044808877909341)
                ·
                  refine ⟨10255361605516803329216003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27347630948044808877909341 10255361605516803329216003)
                  ·
                    refine ⟨15383042408275204993824005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10255361605516803329216003 15383042408275204993824005)
                    ·
                      refine ⟨2884320451551600936342001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15383042408275204993824005 2884320451551600936342001)
                      ·
                        rfl

theorem cell23_5617194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_5617194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617194 prefixEnd_5617194 := by exact prefixLift 5617194
  have htrace : WordTrace (prefixWord ++ tailWord_5617194) baseStart_5617194 baseEnd_5617194 := by
    simpa [prefixWord, tailWord_5617194, baseEnd_5617194] using wordTrace_append hprefix tailTrace_5617194
  have hstable : (prefixWord ++ tailWord_5617194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617194).length < 2 ^ (prefixWord ++ tailWord_5617194).sum := by decide
  have hdescent : baseEnd_5617194 < baseStart_5617194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617198 : List Nat := [4, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_5617198 : Nat := 118140960795 + 5617198 * 2 ^ 59
def prefixEnd_5617198 : Nat := 4983230072969 + 3 ^ 40 * 5617198 * 2
def baseEnd_5617198 : Nat := 2884322505474218920691983

theorem tailTrace_5617198 : CollatzResearch.WordTrace tailWord_5617198 prefixEnd_5617198 2884322505474218920691983 := by
  unfold tailWord_5617198
  simp only [CollatzResearch.WordTrace]
  refine ⟨25609505287982307735808531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136584028202572307924312165 25609505287982307735808531)
  ·
    refine ⟨38414257931973461603712797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25609505287982307735808531 38414257931973461603712797)
    ·
      refine ⟨14405346724490048101392299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38414257931973461603712797 14405346724490048101392299)
      ·
        refine ⟨21608020086735072152088449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14405346724490048101392299 21608020086735072152088449)
        ·
          refine ⟨16206015065051304114066337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21608020086735072152088449 16206015065051304114066337)
          ·
            refine ⟨12154511298788478085549753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16206015065051304114066337 12154511298788478085549753)
            ·
              refine ⟨9115883474091358564162315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12154511298788478085549753 9115883474091358564162315)
              ·
                refine ⟨13673825211137037846243473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9115883474091358564162315 13673825211137037846243473)
                ·
                  refine ⟨10255368908352778384682605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13673825211137037846243473 10255368908352778384682605)
                  ·
                    refine ⟨3845763340632291894255977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10255368908352778384682605 3845763340632291894255977)
                    ·
                      refine ⟨2884322505474218920691983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845763340632291894255977 2884322505474218920691983)
                      ·
                        rfl

theorem cell23_5617198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_5617198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617198 prefixEnd_5617198 := by exact prefixLift 5617198
  have htrace : WordTrace (prefixWord ++ tailWord_5617198) baseStart_5617198 baseEnd_5617198 := by
    simpa [prefixWord, tailWord_5617198, baseEnd_5617198] using wordTrace_append hprefix tailTrace_5617198
  have hstable : (prefixWord ++ tailWord_5617198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617198).length < 2 ^ (prefixWord ++ tailWord_5617198).sum := by decide
  have hdescent : baseEnd_5617198 < baseStart_5617198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617207 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_5617207 : Nat := 118140960795 + 5617207 * 2 ^ 59
def prefixEnd_5617207 : Nat := 4983230072969 + 3 ^ 40 * 5617207 * 2
def baseEnd_5617207 : Nat := 2884327126800109385479441

theorem tailTrace_5617207 : CollatzResearch.WordTrace tailWord_5617207 prefixEnd_5617207 2884327126800109385479441 := by
  unfold tailWord_5617207
  simp only [CollatzResearch.WordTrace]
  refine ⟨204876370560825856423545875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136584247040550570949030583 204876370560825856423545875)
  ·
    refine ⟨307314555841238784635318813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204876370560825856423545875 307314555841238784635318813)
    ·
      refine ⟨115242958440464544238244555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307314555841238784635318813 115242958440464544238244555)
      ·
        refine ⟨172864437660696816357366833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115242958440464544238244555 172864437660696816357366833)
        ·
          refine ⟨129648328245522612268025125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 172864437660696816357366833 129648328245522612268025125)
          ·
            refine ⟨24309061546035489800254711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 129648328245522612268025125 24309061546035489800254711)
            ·
              refine ⟨36463592319053234700382067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24309061546035489800254711 36463592319053234700382067)
              ·
                refine ⟨54695388478579852050573101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36463592319053234700382067 54695388478579852050573101)
                ·
                  refine ⟨20510770679467444518964913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54695388478579852050573101 20510770679467444518964913)
                  ·
                    refine ⟨15383078009600583389223685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20510770679467444518964913 15383078009600583389223685)
                    ·
                      refine ⟨2884327126800109385479441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15383078009600583389223685 2884327126800109385479441)
                      ·
                        rfl

theorem cell23_5617207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_5617207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617207 prefixEnd_5617207 := by exact prefixLift 5617207
  have htrace : WordTrace (prefixWord ++ tailWord_5617207) baseStart_5617207 baseEnd_5617207 := by
    simpa [prefixWord, tailWord_5617207, baseEnd_5617207] using wordTrace_append hprefix tailTrace_5617207
  have hstable : (prefixWord ++ tailWord_5617207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617207).length < 2 ^ (prefixWord ++ tailWord_5617207).sum := by decide
  have hdescent : baseEnd_5617207 < baseStart_5617207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617222 : List Nat := [6, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_5617222 : Nat := 118140960795 + 5617222 * 2 ^ 59
def prefixEnd_5617222 : Nat := 4983230072969 + 3 ^ 40 * 5617222 * 2
def baseEnd_5617222 : Nat := 2884334829009926826791873

theorem tailTrace_5617222 : CollatzResearch.WordTrace tailWord_5617222 prefixEnd_5617222 2884334829009926826791873 := by
  unfold tailWord_5617222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6402403676742859812041935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 136584611770514342656894613 6402403676742859812041935)
  ·
    refine ⟨9603605515114289718062903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6402403676742859812041935 9603605515114289718062903)
    ·
      refine ⟨14405408272671434577094355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9603605515114289718062903 14405408272671434577094355)
      ·
        refine ⟨21608112409007151865641533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14405408272671434577094355 21608112409007151865641533)
        ·
          refine ⟨8103042153377681949615575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21608112409007151865641533 8103042153377681949615575)
          ·
            refine ⟨12154563230066522924423363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103042153377681949615575 12154563230066522924423363)
            ·
              refine ⟨18231844845099784386635045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12154563230066522924423363 18231844845099784386635045)
              ·
                refine ⟨3418470908456209572494071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18231844845099784386635045 3418470908456209572494071)
                ·
                  refine ⟨5127706362684314358741107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418470908456209572494071 5127706362684314358741107)
                  ·
                    refine ⟨7691559544026471538111661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5127706362684314358741107 7691559544026471538111661)
                    ·
                      refine ⟨2884334829009926826791873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7691559544026471538111661 2884334829009926826791873)
                      ·
                        rfl

theorem cell23_5617222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_5617222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617222 prefixEnd_5617222 := by exact prefixLift 5617222
  have htrace : WordTrace (prefixWord ++ tailWord_5617222) baseStart_5617222 baseEnd_5617222 := by
    simpa [prefixWord, tailWord_5617222, baseEnd_5617222] using wordTrace_append hprefix tailTrace_5617222
  have hstable : (prefixWord ++ tailWord_5617222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617222).length < 2 ^ (prefixWord ++ tailWord_5617222).sum := by decide
  have hdescent : baseEnd_5617222 < baseStart_5617222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617227 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 3]
def baseStart_5617227 : Nat := 118140960795 + 5617227 * 2 ^ 59
def prefixEnd_5617227 : Nat := 4983230072969 + 3 ^ 40 * 5617227 * 2
def baseEnd_5617227 : Nat := 2884337396413199307229349

theorem tailTrace_5617227 : CollatzResearch.WordTrace tailWord_5617227 prefixEnd_5617227 2884337396413199307229349 := by
  unfold tailWord_5617227
  simp only [CollatzResearch.WordTrace]
  refine ⟨204877100020753399839273935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136584733347168933226182623 204877100020753399839273935)
  ·
    refine ⟨307315650031130099758910903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204877100020753399839273935 307315650031130099758910903)
    ·
      refine ⟨460973475046695149638366355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307315650031130099758910903 460973475046695149638366355)
      ·
        refine ⟨691460212570042724457549533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460973475046695149638366355 691460212570042724457549533)
        ·
          refine ⟨259297579713766021671581075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 691460212570042724457549533 259297579713766021671581075)
          ·
            refine ⟨388946369570649032507371613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259297579713766021671581075 388946369570649032507371613)
            ·
              refine ⟨145854888588993387190264355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 388946369570649032507371613 145854888588993387190264355)
              ·
                refine ⟨218782332883490080785396533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145854888588993387190264355 218782332883490080785396533)
                ·
                  refine ⟨20510843707827195073630925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 218782332883490080785396533 20510843707827195073630925)
                  ·
                    refine ⟨7691566390435198152611597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20510843707827195073630925 7691566390435198152611597)
                    ·
                      refine ⟨2884337396413199307229349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7691566390435198152611597 2884337396413199307229349)
                      ·
                        rfl

theorem cell23_5617227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 3, 3].length) (baseStart_5617227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617227 prefixEnd_5617227 := by exact prefixLift 5617227
  have htrace : WordTrace (prefixWord ++ tailWord_5617227) baseStart_5617227 baseEnd_5617227 := by
    simpa [prefixWord, tailWord_5617227, baseEnd_5617227] using wordTrace_append hprefix tailTrace_5617227
  have hstable : (prefixWord ++ tailWord_5617227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617227).length < 2 ^ (prefixWord ++ tailWord_5617227).sum := by decide
  have hdescent : baseEnd_5617227 < baseStart_5617227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617234 : List Nat := [3, 2, 2, 1, 2, 4, 1, 8]
def baseStart_5617234 : Nat := 118140960795 + 5617234 * 2 ^ 59
def prefixEnd_5617234 : Nat := 4983230072969 + 3 ^ 40 * 5617234 * 2
def baseEnd_5617234 : Nat := 106827444102880769623771

theorem tailTrace_5617234 : CollatzResearch.WordTrace tailWord_5617234 prefixEnd_5617234 106827444102880769623771 := by
  unfold tailWord_5617234
  simp only [CollatzResearch.WordTrace]
  refine ⟨51219338832932010008694689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136584903554485360023185837 51219338832932010008694689)
  ·
    refine ⟨38414504124699007506521017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51219338832932010008694689 38414504124699007506521017)
    ·
      refine ⟨28810878093524255629890763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38414504124699007506521017 28810878093524255629890763)
      ·
        refine ⟨43216317140286383444836145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28810878093524255629890763 43216317140286383444836145)
        ·
          refine ⟨32412237855214787583627109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43216317140286383444836145 32412237855214787583627109)
          ·
            refine ⟨6077294597852772671930083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32412237855214787583627109 6077294597852772671930083)
            ·
              refine ⟨9115941896779159007895125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077294597852772671930083 9115941896779159007895125)
              ·
                refine ⟨106827444102880769623771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9115941896779159007895125 106827444102880769623771)
                ·
                  rfl

theorem cell23_5617234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 8].length) (baseStart_5617234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617234 prefixEnd_5617234 := by exact prefixLift 5617234
  have htrace : WordTrace (prefixWord ++ tailWord_5617234) baseStart_5617234 baseEnd_5617234 := by
    simpa [prefixWord, tailWord_5617234, baseEnd_5617234] using wordTrace_append hprefix tailTrace_5617234
  have hstable : (prefixWord ++ tailWord_5617234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617234).length < 2 ^ (prefixWord ++ tailWord_5617234).sum := by decide
  have hdescent : baseEnd_5617234 < baseStart_5617234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617262 : List Nat := [4, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_5617262 : Nat := 118140960795 + 5617262 * 2 ^ 59
def prefixEnd_5617262 : Nat := 4983230072969 + 3 ^ 40 * 5617262 * 2
def baseEnd_5617262 : Nat := 2884355368236106670291689

theorem tailTrace_5617262 : CollatzResearch.WordTrace tailWord_5617262 prefixEnd_5617262 2884355368236106670291689 := by
  unfold tailWord_5617262
  simp only [CollatzResearch.WordTrace]
  refine ⟨25609797071953325102099755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136585584383751067211198693 25609797071953325102099755)
  ·
    refine ⟨38414695607929987653149633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25609797071953325102099755 38414695607929987653149633)
    ·
      refine ⟨28811021705947490739862225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38414695607929987653149633 28811021705947490739862225)
      ·
        refine ⟨21608266279460618054896669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28811021705947490739862225 21608266279460618054896669)
        ·
          refine ⟨8103099854797731770586251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21608266279460618054896669 8103099854797731770586251)
          ·
            refine ⟨12154649782196597655879377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103099854797731770586251 12154649782196597655879377)
            ·
              refine ⟨9115987336647448241909533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12154649782196597655879377 9115987336647448241909533)
              ·
                refine ⟨3418495251242793090716075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9115987336647448241909533 3418495251242793090716075)
                ·
                  refine ⟨5127742876864189636074113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418495251242793090716075 5127742876864189636074113)
                  ·
                    refine ⟨3845807157648142227055585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5127742876864189636074113 3845807157648142227055585)
                    ·
                      refine ⟨2884355368236106670291689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845807157648142227055585 2884355368236106670291689)
                      ·
                        rfl

theorem cell23_5617262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_5617262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617262 prefixEnd_5617262 := by exact prefixLift 5617262
  have htrace : WordTrace (prefixWord ++ tailWord_5617262) baseStart_5617262 baseEnd_5617262 := by
    simpa [prefixWord, tailWord_5617262, baseEnd_5617262] using wordTrace_append hprefix tailTrace_5617262
  have hstable : (prefixWord ++ tailWord_5617262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617262).length < 2 ^ (prefixWord ++ tailWord_5617262).sum := by decide
  have hdescent : baseEnd_5617262 < baseStart_5617262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617294 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_5617294 : Nat := 118140960795 + 5617294 * 2 ^ 59
def prefixEnd_5617294 : Nat := 4983230072969 + 3 ^ 40 * 5617294 * 2
def baseEnd_5617294 : Nat := 961457266539016848363847

theorem tailTrace_5617294 : CollatzResearch.WordTrace tailWord_5617294 prefixEnd_5617294 961457266539016848363847 := by
  unfold tailWord_5617294
  simp only [CollatzResearch.WordTrace]
  refine ⟨25609942963938833785245367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136586362474340446854641957 25609942963938833785245367)
  ·
    refine ⟨38414914445908250677868051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25609942963938833785245367 38414914445908250677868051)
    ·
      refine ⟨57622371668862376016802077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38414914445908250677868051 57622371668862376016802077)
      ·
        refine ⟨21608389375823391006300779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57622371668862376016802077 21608389375823391006300779)
        ·
          refine ⟨32412584063735086509451169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21608389375823391006300779 32412584063735086509451169)
          ·
            refine ⟨24309438047801314882088377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32412584063735086509451169 24309438047801314882088377)
            ·
              refine ⟨18232078535850986161566283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24309438047801314882088377 18232078535850986161566283)
              ·
                refine ⟨27348117803776479242349425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18232078535850986161566283 27348117803776479242349425)
                ·
                  refine ⟨20511088352832359431762069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27348117803776479242349425 20511088352832359431762069)
                  ·
                    refine ⟨961457266539016848363847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20511088352832359431762069 961457266539016848363847)
                    ·
                      rfl

theorem cell23_5617294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_5617294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617294 prefixEnd_5617294 := by exact prefixLift 5617294
  have htrace : WordTrace (prefixWord ++ tailWord_5617294) baseStart_5617294 baseEnd_5617294 := by
    simpa [prefixWord, tailWord_5617294, baseEnd_5617294] using wordTrace_append hprefix tailTrace_5617294
  have hstable : (prefixWord ++ tailWord_5617294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617294).length < 2 ^ (prefixWord ++ tailWord_5617294).sum := by decide
  have hdescent : baseEnd_5617294 < baseStart_5617294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617297 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_5617297 : Nat := 118140960795 + 5617297 * 2 ^ 59
def prefixEnd_5617297 : Nat := 4983230072969 + 3 ^ 40 * 5617297 * 2
def baseEnd_5617297 : Nat := 2884373340059014033354027

theorem tailTrace_5617297 : CollatzResearch.WordTrace tailWord_5617297 prefixEnd_5617297 2884373340059014033354027 := by
  unfold tailWord_5617297
  simp only [CollatzResearch.WordTrace]
  refine ⟨204879653130499801794322145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136586435420333201196214763 204879653130499801794322145)
  ·
    refine ⟨153659739847874851345741609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204879653130499801794322145 153659739847874851345741609)
    ·
      refine ⟨115244804885906138509306207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153659739847874851345741609 115244804885906138509306207)
      ·
        refine ⟨172867207328859207763959311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115244804885906138509306207 172867207328859207763959311)
        ·
          refine ⟨259300810993288811645938967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 172867207328859207763959311 259300810993288811645938967)
          ·
            refine ⟨388951216489933217468908451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259300810993288811645938967 388951216489933217468908451)
            ·
              refine ⟨583426824734899826203362677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388951216489933217468908451 583426824734899826203362677)
              ·
                refine ⟨54696264818896858706565251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 583426824734899826203362677 54696264818896858706565251)
                ·
                  refine ⟨82044397228345288059847877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54696264818896858706565251 82044397228345288059847877)
                  ·
                    refine ⟨15383324480314741511221477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82044397228345288059847877 15383324480314741511221477)
                    ·
                      refine ⟨2884373340059014033354027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15383324480314741511221477 2884373340059014033354027)
                      ·
                        rfl

theorem cell23_5617297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_5617297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617297 prefixEnd_5617297 := by exact prefixLift 5617297
  have htrace : WordTrace (prefixWord ++ tailWord_5617297) baseStart_5617297 baseEnd_5617297 := by
    simpa [prefixWord, tailWord_5617297, baseEnd_5617297] using wordTrace_append hprefix tailTrace_5617297
  have hstable : (prefixWord ++ tailWord_5617297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617297).length < 2 ^ (prefixWord ++ tailWord_5617297).sum := by decide
  have hdescent : baseEnd_5617297 < baseStart_5617297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617346 : List Nat := [3, 5, 1, 2, 1, 2, 2, 1, 2, 1, 3]
def baseStart_5617346 : Nat := 118140960795 + 5617346 * 2 ^ 59
def prefixEnd_5617346 : Nat := 4983230072969 + 3 ^ 40 * 5617346 * 2
def baseEnd_5617346 : Nat := 2884398500611084341641303

theorem tailTrace_5617346 : CollatzResearch.WordTrace tailWord_5617346 prefixEnd_5617346 2884398500611084341641303 := by
  unfold tailWord_5617346
  simp only [CollatzResearch.WordTrace]
  refine ⟨51220360076830570790713973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136587626871548188775237261 51220360076830570790713973)
  ·
    refine ⟨4801908757202866011629435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 51220360076830570790713973 4801908757202866011629435)
    ·
      refine ⟨7202863135804299017444153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4801908757202866011629435 7202863135804299017444153)
      ·
        refine ⟨5402147351853224263083115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7202863135804299017444153 5402147351853224263083115)
        ·
          refine ⟨8103221027779836394624673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402147351853224263083115 8103221027779836394624673)
          ·
            refine ⟨6077415770834877295968505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8103221027779836394624673 6077415770834877295968505)
            ·
              refine ⟨4558061828126157971976379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6077415770834877295968505 4558061828126157971976379)
              ·
                refine ⟨6837092742189236957964569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4558061828126157971976379 6837092742189236957964569)
                ·
                  refine ⟨5127819556641927718473427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6837092742189236957964569 5127819556641927718473427)
                  ·
                    refine ⟨7691729334962891577710141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5127819556641927718473427 7691729334962891577710141)
                    ·
                      refine ⟨2884398500611084341641303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7691729334962891577710141 2884398500611084341641303)
                      ·
                        rfl

theorem cell23_5617346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_5617346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617346 prefixEnd_5617346 := by exact prefixLift 5617346
  have htrace : WordTrace (prefixWord ++ tailWord_5617346) baseStart_5617346 baseEnd_5617346 := by
    simpa [prefixWord, tailWord_5617346, baseEnd_5617346] using wordTrace_append hprefix tailTrace_5617346
  have hstable : (prefixWord ++ tailWord_5617346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617346).length < 2 ^ (prefixWord ++ tailWord_5617346).sum := by decide
  have hdescent : baseEnd_5617346 < baseStart_5617346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617391 : List Nat := [1, 1, 2, 1, 5, 1, 2, 2, 2, 4, 2]
def baseStart_5617391 : Nat := 118140960795 + 5617391 * 2 ^ 59
def prefixEnd_5617391 : Nat := 4983230072969 + 3 ^ 40 * 5617391 * 2
def baseEnd_5617391 : Nat := 2884421607240536665578595

theorem tailTrace_5617391 : CollatzResearch.WordTrace tailWord_5617391 prefixEnd_5617391 2884421607240536665578595 := by
  unfold tailWord_5617391
  simp only [CollatzResearch.WordTrace]
  refine ⟨204883081592159255848244027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136588721061439503898829351 204883081592159255848244027)
  ·
    refine ⟨307324622388238883772366041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204883081592159255848244027 307324622388238883772366041)
    ·
      refine ⟨230493466791179162829274531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 307324622388238883772366041 230493466791179162829274531)
      ·
        refine ⟨345740200186768744243911797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230493466791179162829274531 345740200186768744243911797)
        ·
          refine ⟨32413143767509569772866731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 345740200186768744243911797 32413143767509569772866731)
          ·
            refine ⟨48619715651264354659300097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32413143767509569772866731 48619715651264354659300097)
            ·
              refine ⟨36464786738448265994475073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48619715651264354659300097 36464786738448265994475073)
              ·
                refine ⟨27348590053836199495856305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36464786738448265994475073 27348590053836199495856305)
                ·
                  refine ⟨20511442540377149621892229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27348590053836199495856305 20511442540377149621892229)
                  ·
                    refine ⟨3845895476320715554104793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20511442540377149621892229 3845895476320715554104793)
                    ·
                      refine ⟨2884421607240536665578595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845895476320715554104793 2884421607240536665578595)
                      ·
                        rfl

theorem cell23_5617391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 2, 2, 4, 2].length) (baseStart_5617391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617391 prefixEnd_5617391 := by exact prefixLift 5617391
  have htrace : WordTrace (prefixWord ++ tailWord_5617391) baseStart_5617391 baseEnd_5617391 := by
    simpa [prefixWord, tailWord_5617391, baseEnd_5617391] using wordTrace_append hprefix tailTrace_5617391
  have hstable : (prefixWord ++ tailWord_5617391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617391).length < 2 ^ (prefixWord ++ tailWord_5617391).sum := by decide
  have hdescent : baseEnd_5617391 < baseStart_5617391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617394 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_5617394 : Nat := 118140960795 + 5617394 * 2 ^ 59
def prefixEnd_5617394 : Nat := 4983230072969 + 3 ^ 40 * 5617394 * 2
def baseEnd_5617394 : Nat := 2884423147682500153841081

theorem tailTrace_5617394 : CollatzResearch.WordTrace tailWord_5617394 prefixEnd_5617394 2884423147682500153841081 := by
  unfold tailWord_5617394
  simp only [CollatzResearch.WordTrace]
  refine ⟨51220797752787096840150809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136588794007432258240402157 51220797752787096840150809)
  ·
    refine ⟨38415598314590322630113107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51220797752787096840150809 38415598314590322630113107)
    ·
      refine ⟨57623397471885483945169661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38415598314590322630113107 57623397471885483945169661)
      ·
        refine ⟨21608774051957056479438623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57623397471885483945169661 21608774051957056479438623)
        ·
          refine ⟨32413161077935584719157935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21608774051957056479438623 32413161077935584719157935)
          ·
            refine ⟨48619741616903377078736903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32413161077935584719157935 48619741616903377078736903)
            ·
              refine ⟨72929612425355065618105355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48619741616903377078736903 72929612425355065618105355)
              ·
                refine ⟨109394418638032598427158033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72929612425355065618105355 109394418638032598427158033)
                ·
                  refine ⟨82045813978524448820368525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109394418638032598427158033 82045813978524448820368525)
                  ·
                    refine ⟨30767180241946668307638197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 82045813978524448820368525 30767180241946668307638197)
                    ·
                      refine ⟨2884423147682500153841081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30767180241946668307638197 2884423147682500153841081)
                      ·
                        rfl

theorem cell23_5617394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_5617394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617394 prefixEnd_5617394 := by exact prefixLift 5617394
  have htrace : WordTrace (prefixWord ++ tailWord_5617394) baseStart_5617394 baseEnd_5617394 := by
    simpa [prefixWord, tailWord_5617394, baseEnd_5617394] using wordTrace_append hprefix tailTrace_5617394
  have hstable : (prefixWord ++ tailWord_5617394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617394).length < 2 ^ (prefixWord ++ tailWord_5617394).sum := by decide
  have hdescent : baseEnd_5617394 < baseStart_5617394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617448 : List Nat := [2, 1, 5, 1, 1, 4, 1, 2, 6]
def baseStart_5617448 : Nat := 118140960795 + 5617448 * 2 ^ 59
def prefixEnd_5617448 : Nat := 4983230072969 + 3 ^ 40 * 5617448 * 2
def baseEnd_5617448 : Nat := 320494541737538104729537

theorem tailTrace_5617448 : CollatzResearch.WordTrace tailWord_5617448 prefixEnd_5617448 320494541737538104729537 := by
  unfold tailWord_5617448
  simp only [CollatzResearch.WordTrace]
  refine ⟨102442580276476377291534499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136590107035301836388712665 102442580276476377291534499)
  ·
    refine ⟨153663870414714565937301749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102442580276476377291534499 153663870414714565937301749)
    ·
      refine ⟨14405987851379490556622039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 153663870414714565937301749 14405987851379490556622039)
      ·
        refine ⟨21608981777069235834933059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14405987851379490556622039 21608981777069235834933059)
        ·
          refine ⟨32413472665603853752399589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21608981777069235834933059 32413472665603853752399589)
          ·
            refine ⟨6077526124800722578574923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32413472665603853752399589 6077526124800722578574923)
            ·
              refine ⟨9116289187201083867862385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077526124800722578574923 9116289187201083867862385)
              ·
                refine ⟨6837216890400812900896789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9116289187201083867862385 6837216890400812900896789)
                ·
                  refine ⟨320494541737538104729537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6837216890400812900896789 320494541737538104729537)
                  ·
                    rfl

theorem cell23_5617448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 6].length) (baseStart_5617448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617448 prefixEnd_5617448 := by exact prefixLift 5617448
  have htrace : WordTrace (prefixWord ++ tailWord_5617448) baseStart_5617448 baseEnd_5617448 := by
    simpa [prefixWord, tailWord_5617448, baseEnd_5617448] using wordTrace_append hprefix tailTrace_5617448
  have hstable : (prefixWord ++ tailWord_5617448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617448).length < 2 ^ (prefixWord ++ tailWord_5617448).sum := by decide
  have hdescent : baseEnd_5617448 < baseStart_5617448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617458 : List Nat := [3, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_5617458 : Nat := 118140960795 + 5617458 * 2 ^ 59
def prefixEnd_5617458 : Nat := 4983230072969 + 3 ^ 40 * 5617458 * 2
def baseEnd_5617458 : Nat := 2884456010444387903440787

theorem tailTrace_5617458 : CollatzResearch.WordTrace tailWord_5617458 prefixEnd_5617458 2884456010444387903440787 := by
  unfold tailWord_5617458
  simp only [CollatzResearch.WordTrace]
  refine ⟨51221381320729131572733257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 136590350188611017527288685 51221381320729131572733257)
  ·
    refine ⟨38416035990546848679549943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 51221381320729131572733257 38416035990546848679549943)
    ·
      refine ⟨57624053985820273019324915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38416035990546848679549943 57624053985820273019324915)
      ·
        refine ⟨86436080978730409528987373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57624053985820273019324915 86436080978730409528987373)
        ·
          refine ⟨32413530367023903573370265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86436080978730409528987373 32413530367023903573370265)
          ·
            refine ⟨24310147775267927680027699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32413530367023903573370265 24310147775267927680027699)
            ·
              refine ⟨36465221662901891520041549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24310147775267927680027699 36465221662901891520041549)
              ·
                refine ⟨13674458123588209320015581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36465221662901891520041549 13674458123588209320015581)
                ·
                  refine ⟨5127921796345578495005843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13674458123588209320015581 5127921796345578495005843)
                  ·
                    refine ⟨7691882694518367742508765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5127921796345578495005843 7691882694518367742508765)
                    ·
                      refine ⟨2884456010444387903440787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7691882694518367742508765 2884456010444387903440787)
                      ·
                        rfl

theorem cell23_5617458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_5617458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617458 prefixEnd_5617458 := by exact prefixLift 5617458
  have htrace : WordTrace (prefixWord ++ tailWord_5617458) baseStart_5617458 baseEnd_5617458 := by
    simpa [prefixWord, tailWord_5617458, baseEnd_5617458] using wordTrace_append hprefix tailTrace_5617458
  have hstable : (prefixWord ++ tailWord_5617458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617458).length < 2 ^ (prefixWord ++ tailWord_5617458).sum := by decide
  have hdescent : baseEnd_5617458 < baseStart_5617458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617465 : List Nat := [1, 2, 1, 7, 1, 1, 3, 1, 6]
def baseStart_5617465 : Nat := 118140960795 + 5617465 * 2 ^ 59
def prefixEnd_5617465 : Nat := 4983230072969 + 3 ^ 40 * 5617465 * 2
def baseEnd_5617465 : Nat := 320495511645441041783695

theorem tailTrace_5617465 : CollatzResearch.WordTrace tailWord_5617465 prefixEnd_5617465 320495511645441041783695 := by
  unfold tailWord_5617465
  simp only [CollatzResearch.WordTrace]
  refine ⟨204885780593891166486437849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136590520395927444324291899 204885780593891166486437849)
  ·
    refine ⟨153664335445418374864828387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204885780593891166486437849 153664335445418374864828387)
    ·
      refine ⟨230496503168127562297242581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153664335445418374864828387 230496503168127562297242581)
      ·
        refine ⟨5402261793002989741341623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 230496503168127562297242581 5402261793002989741341623)
        ·
          refine ⟨8103392689504484612012435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5402261793002989741341623 8103392689504484612012435)
          ·
            refine ⟨12155089034256726918018653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103392689504484612012435 12155089034256726918018653)
            ·
              refine ⟨4558158387846272594256995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12155089034256726918018653 4558158387846272594256995)
              ·
                refine ⟨6837237581769408891385493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4558158387846272594256995 6837237581769408891385493)
                ·
                  refine ⟨320495511645441041783695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6837237581769408891385493 320495511645441041783695)
                  ·
                    rfl

theorem cell23_5617465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 3, 1, 6].length) (baseStart_5617465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617465 prefixEnd_5617465 := by exact prefixLift 5617465
  have htrace : WordTrace (prefixWord ++ tailWord_5617465) baseStart_5617465 baseEnd_5617465 := by
    simpa [prefixWord, tailWord_5617465, baseEnd_5617465] using wordTrace_append hprefix tailTrace_5617465
  have hstable : (prefixWord ++ tailWord_5617465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617465).length < 2 ^ (prefixWord ++ tailWord_5617465).sum := by decide
  have hdescent : baseEnd_5617465 < baseStart_5617465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617481 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 2, 6, 2]
def baseStart_5617481 : Nat := 118140960795 + 5617481 * 2 ^ 59
def prefixEnd_5617481 : Nat := 4983230072969 + 3 ^ 40 * 5617481 * 2
def baseEnd_5617481 : Nat := 2884467820499441313453181

theorem tailTrace_5617481 : CollatzResearch.WordTrace tailWord_5617481 prefixEnd_5617481 2884467820499441313453181 := by
  unfold tailWord_5617481
  simp only [CollatzResearch.WordTrace]
  refine ⟨204886364161833201219020297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136590909441222134146013531 204886364161833201219020297)
  ·
    refine ⟨153664773121374900914265223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204886364161833201219020297 153664773121374900914265223)
    ·
      refine ⟨230497159682062351371397835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153664773121374900914265223 230497159682062351371397835)
      ·
        refine ⟨345745739523093527057096753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230497159682062351371397835 345745739523093527057096753)
        ·
          refine ⟨259309304642320145292822565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 345745739523093527057096753 259309304642320145292822565)
          ·
            refine ⟨48620494620435027242404231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 259309304642320145292822565 48620494620435027242404231)
            ·
              refine ⟨72930741930652540863606347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48620494620435027242404231 72930741930652540863606347)
              ·
                refine ⟨109396112895978811295409521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72930741930652540863606347 109396112895978811295409521)
                ·
                  refine ⟨82047084671984108471557141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109396112895978811295409521 82047084671984108471557141)
                  ·
                    refine ⟨3845957093999255084604241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 82047084671984108471557141 3845957093999255084604241)
                    ·
                      refine ⟨2884467820499441313453181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845957093999255084604241 2884467820499441313453181)
                      ·
                        rfl

theorem cell23_5617481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 6, 2].length) (baseStart_5617481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617481 prefixEnd_5617481 := by exact prefixLift 5617481
  have htrace : WordTrace (prefixWord ++ tailWord_5617481) baseStart_5617481 baseEnd_5617481 := by
    simpa [prefixWord, tailWord_5617481, baseEnd_5617481] using wordTrace_append hprefix tailTrace_5617481
  have hstable : (prefixWord ++ tailWord_5617481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617481).length < 2 ^ (prefixWord ++ tailWord_5617481).sum := by decide
  have hdescent : baseEnd_5617481 < baseStart_5617481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617485 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_5617485 : Nat := 118140960795 + 5617485 * 2 ^ 59
def prefixEnd_5617485 : Nat := 4983230072969 + 3 ^ 40 * 5617485 * 2
def baseEnd_5617485 : Nat := 2884469874422059297803163

theorem tailTrace_5617485 : CollatzResearch.WordTrace tailWord_5617485 prefixEnd_5617485 2884469874422059297803163 := by
  unfold tailWord_5617485
  simp only [CollatzResearch.WordTrace]
  refine ⟨204886510053818709902165909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136591006702545806601443939 204886510053818709902165909)
  ·
    refine ⟨9604055158772752026664027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 204886510053818709902165909 9604055158772752026664027)
    ·
      refine ⟨14406082738159128039996041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9604055158772752026664027 14406082738159128039996041)
      ·
        refine ⟨10804562053619346029997031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14406082738159128039996041 10804562053619346029997031)
        ·
          refine ⟨16206843080429019044995547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10804562053619346029997031 16206843080429019044995547)
          ·
            refine ⟨24310264620643528567493321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16206843080429019044995547 24310264620643528567493321)
            ·
              refine ⟨18232698465482646425619991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24310264620643528567493321 18232698465482646425619991)
              ·
                refine ⟨27349047698223969638429987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18232698465482646425619991 27349047698223969638429987)
                ·
                  refine ⟨41023571547335954457644981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27349047698223969638429987 41023571547335954457644981)
                  ·
                    refine ⟨3845959832562745730404217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41023571547335954457644981 3845959832562745730404217)
                    ·
                      refine ⟨2884469874422059297803163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3845959832562745730404217 2884469874422059297803163)
                      ·
                        rfl

theorem cell23_5617485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_5617485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617485 prefixEnd_5617485 := by exact prefixLift 5617485
  have htrace : WordTrace (prefixWord ++ tailWord_5617485) baseStart_5617485 baseEnd_5617485 := by
    simpa [prefixWord, tailWord_5617485, baseEnd_5617485] using wordTrace_append hprefix tailTrace_5617485
  have hstable : (prefixWord ++ tailWord_5617485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617485).length < 2 ^ (prefixWord ++ tailWord_5617485).sum := by decide
  have hdescent : baseEnd_5617485 < baseStart_5617485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617492 : List Nat := [2, 4, 1, 1, 3, 1, 3, 3, 1, 1, 3]
def baseStart_5617492 : Nat := 118140960795 + 5617492 * 2 ^ 59
def prefixEnd_5617492 : Nat := 4983230072969 + 3 ^ 40 * 5617492 * 2
def baseEnd_5617492 : Nat := 2884473468786640770415631

theorem tailTrace_5617492 : CollatzResearch.WordTrace tailWord_5617492 prefixEnd_5617492 2884473468786640770415631 := by
  unfold tailWord_5617492
  simp only [CollatzResearch.WordTrace]
  refine ⟨102443382682396675048835365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136591176909862233398447153 102443382682396675048835365)
  ·
    refine ⟨19208134252949376571656631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 102443382682396675048835365 19208134252949376571656631)
    ·
      refine ⟨28812201379424064857484947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19208134252949376571656631 28812201379424064857484947)
      ·
        refine ⟨43218302069136097286227421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28812201379424064857484947 43218302069136097286227421)
        ·
          refine ⟨16206863275926036482335283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 43218302069136097286227421 16206863275926036482335283)
          ·
            refine ⟨24310294913889054723502925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16206863275926036482335283 24310294913889054723502925)
            ·
              refine ⟨9116360592708395521313597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24310294913889054723502925 9116360592708395521313597)
              ·
                refine ⟨3418635222265648320492599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9116360592708395521313597 3418635222265648320492599)
                ·
                  refine ⟨5127952833398472480738899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3418635222265648320492599 5127952833398472480738899)
                  ·
                    refine ⟨7691929250097708721108349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5127952833398472480738899 7691929250097708721108349)
                    ·
                      refine ⟨2884473468786640770415631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7691929250097708721108349 2884473468786640770415631)
                      ·
                        rfl

theorem cell23_5617492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 3, 1, 1, 3].length) (baseStart_5617492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617492 prefixEnd_5617492 := by exact prefixLift 5617492
  have htrace : WordTrace (prefixWord ++ tailWord_5617492) baseStart_5617492 baseEnd_5617492 := by
    simpa [prefixWord, tailWord_5617492, baseEnd_5617492] using wordTrace_append hprefix tailTrace_5617492
  have hstable : (prefixWord ++ tailWord_5617492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617492).length < 2 ^ (prefixWord ++ tailWord_5617492).sum := by decide
  have hdescent : baseEnd_5617492 < baseStart_5617492 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617504 : List Nat := [2, 1, 1, 3, 3, 2, 11]
def baseStart_5617504 : Nat := 118140960795 + 5617504 * 2 ^ 59
def prefixEnd_5617504 : Nat := 4983230072969 + 3 ^ 40 * 5617504 * 2
def baseEnd_5617504 : Nat := 35610859636475243499575

theorem tailTrace_5617504 : CollatzResearch.WordTrace tailWord_5617504 prefixEnd_5617504 35610859636475243499575 := by
  unfold tailWord_5617504
  simp only [CollatzResearch.WordTrace]
  refine ⟨102443601520374938073553783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136591468693833250764738377 102443601520374938073553783)
  ·
    refine ⟨153665402280562407110330675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102443601520374938073553783 153665402280562407110330675)
    ·
      refine ⟨230498103420843610665496013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153665402280562407110330675 230498103420843610665496013)
      ·
        refine ⟨86436788782816353999561005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 230498103420843610665496013 86436788782816353999561005)
        ·
          refine ⟨32413795793556132749835377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 86436788782816353999561005 32413795793556132749835377)
          ·
            refine ⟨24310346845167099562376533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32413795793556132749835377 24310346845167099562376533)
            ·
              refine ⟨35610859636475243499575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 24310346845167099562376533 35610859636475243499575)
              ·
                rfl

theorem cell23_5617504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 11].length) (baseStart_5617504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617504 prefixEnd_5617504 := by exact prefixLift 5617504
  have htrace : WordTrace (prefixWord ++ tailWord_5617504) baseStart_5617504 baseEnd_5617504 := by
    simpa [prefixWord, tailWord_5617504, baseEnd_5617504] using wordTrace_append hprefix tailTrace_5617504
  have hstable : (prefixWord ++ tailWord_5617504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617504).length < 2 ^ (prefixWord ++ tailWord_5617504).sum := by decide
  have hdescent : baseEnd_5617504 < baseStart_5617504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617518 : List Nat := [4, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_5617518 : Nat := 118140960795 + 5617518 * 2 ^ 59
def prefixEnd_5617518 : Nat := 4983230072969 + 3 ^ 40 * 5617518 * 2
def baseEnd_5617518 : Nat := 2884486819283657668690511

theorem tailTrace_5617518 : CollatzResearch.WordTrace tailWord_5617518 prefixEnd_5617518 2884486819283657668690511 := by
  unfold tailWord_5617518
  simp only [CollatzResearch.WordTrace]
  refine ⟨25610964207837394567264651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136591809108466104358744805 25610964207837394567264651)
  ·
    refine ⟨38416446311756091850896977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25610964207837394567264651 38416446311756091850896977)
    ·
      refine ⟨28812334733817068888172733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38416446311756091850896977 28812334733817068888172733)
      ·
        refine ⟨10804625525181400833064775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28812334733817068888172733 10804625525181400833064775)
        ·
          refine ⟨16206938287772101249597163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10804625525181400833064775 16206938287772101249597163)
          ·
            refine ⟨24310407431658151874395745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16206938287772101249597163 24310407431658151874395745)
            ·
              refine ⟨18232805573743613905796809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24310407431658151874395745 18232805573743613905796809)
              ·
                refine ⟨13674604180307710429347607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18232805573743613905796809 13674604180307710429347607)
                ·
                  refine ⟨20511906270461565644021411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13674604180307710429347607 20511906270461565644021411)
                  ·
                    refine ⟨30767859405692348466032117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20511906270461565644021411 30767859405692348466032117)
                    ·
                      refine ⟨2884486819283657668690511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30767859405692348466032117 2884486819283657668690511)
                      ·
                        rfl

theorem cell23_5617518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_5617518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617518 prefixEnd_5617518 := by exact prefixLift 5617518
  have htrace : WordTrace (prefixWord ++ tailWord_5617518) baseStart_5617518 baseEnd_5617518 := by
    simpa [prefixWord, tailWord_5617518, baseEnd_5617518] using wordTrace_append hprefix tailTrace_5617518
  have hstable : (prefixWord ++ tailWord_5617518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617518).length < 2 ^ (prefixWord ++ tailWord_5617518).sum := by decide
  have hdescent : baseEnd_5617518 < baseStart_5617518 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617531 : List Nat := [1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 3]
def baseStart_5617531 : Nat := 118140960795 + 5617531 * 2 ^ 59
def prefixEnd_5617531 : Nat := 4983230072969 + 3 ^ 40 * 5617531 * 2
def baseEnd_5617531 : Nat := 2884493494532166117827951

theorem tailTrace_5617531 : CollatzResearch.WordTrace tailWord_5617531 prefixEnd_5617531 2884493494532166117827951 := by
  unfold tailWord_5617531
  simp only [CollatzResearch.WordTrace]
  refine ⟨204888187811652059758340447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136592125207768039838893631 204888187811652059758340447)
  ·
    refine ⟨307332281717478089637510671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204888187811652059758340447 307332281717478089637510671)
    ·
      refine ⟨460998422576217134456266007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307332281717478089637510671 460998422576217134456266007)
      ·
        refine ⟨691497633864325701684399011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 460998422576217134456266007 691497633864325701684399011)
        ·
          refine ⟨1037246450796488552526598517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691497633864325701684399011 1037246450796488552526598517)
          ·
            refine ⟨97241854762170801799368611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1037246450796488552526598517 97241854762170801799368611)
            ·
              refine ⟨145862782143256202699052917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97241854762170801799368611 145862782143256202699052917)
              ·
                refine ⟨13674635825930269003036211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145862782143256202699052917 13674635825930269003036211)
                ·
                  refine ⟨20511953738895403504554317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13674635825930269003036211 20511953738895403504554317)
                  ·
                    refine ⟨7691982652085776314207869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20511953738895403504554317 7691982652085776314207869)
                    ·
                      refine ⟨2884493494532166117827951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7691982652085776314207869 2884493494532166117827951)
                      ·
                        rfl

theorem cell23_5617531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 3].length) (baseStart_5617531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617531 prefixEnd_5617531 := by exact prefixLift 5617531
  have htrace : WordTrace (prefixWord ++ tailWord_5617531) baseStart_5617531 baseEnd_5617531 := by
    simpa [prefixWord, tailWord_5617531, baseEnd_5617531] using wordTrace_append hprefix tailTrace_5617531
  have hstable : (prefixWord ++ tailWord_5617531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617531).length < 2 ^ (prefixWord ++ tailWord_5617531).sum := by decide
  have hdescent : baseEnd_5617531 < baseStart_5617531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617565 : List Nat := [1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_5617565 : Nat := 118140960795 + 5617565 * 2 ^ 59
def prefixEnd_5617565 : Nat := 4983230072969 + 3 ^ 40 * 5617565 * 2
def baseEnd_5617565 : Nat := 2884510952874418984802795

theorem tailTrace_5617565 : CollatzResearch.WordTrace tailWord_5617565 prefixEnd_5617565 2884510952874418984802795 := by
  unfold tailWord_5617565
  simp only [CollatzResearch.WordTrace]
  refine ⟨204889427893528883565078149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136592951929019255710052099 204889427893528883565078149)
  ·
    refine ⟨38416767730036665668452153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 204889427893528883565078149 38416767730036665668452153)
    ·
      refine ⟨28812575797527499251339115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38416767730036665668452153 28812575797527499251339115)
      ·
        refine ⟨43218863696291248877008673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28812575797527499251339115 43218863696291248877008673)
        ·
          refine ⟨32414147772218436657756505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 43218863696291248877008673 32414147772218436657756505)
          ·
            refine ⟨24310610829163827493317379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32414147772218436657756505 24310610829163827493317379)
            ·
              refine ⟨36465916243745741239976069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24310610829163827493317379 36465916243745741239976069)
              ·
                refine ⟨6837359295702326482495513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36465916243745741239976069 6837359295702326482495513)
                ·
                  refine ⟨5128019471776744861871635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6837359295702326482495513 5128019471776744861871635)
                  ·
                    refine ⟨7692029207665117292807453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5128019471776744861871635 7692029207665117292807453)
                    ·
                      refine ⟨2884510952874418984802795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7692029207665117292807453 2884510952874418984802795)
                      ·
                        rfl

theorem cell23_5617565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_5617565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617565 prefixEnd_5617565 := by exact prefixLift 5617565
  have htrace : WordTrace (prefixWord ++ tailWord_5617565) baseStart_5617565 baseEnd_5617565 := by
    simpa [prefixWord, tailWord_5617565, baseEnd_5617565] using wordTrace_append hprefix tailTrace_5617565
  have hstable : (prefixWord ++ tailWord_5617565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617565).length < 2 ^ (prefixWord ++ tailWord_5617565).sum := by decide
  have hdescent : baseEnd_5617565 < baseStart_5617565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617575 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_5617575 : Nat := 118140960795 + 5617575 * 2 ^ 59
def prefixEnd_5617575 : Nat := 4983230072969 + 3 ^ 40 * 5617575 * 2
def baseEnd_5617575 : Nat := 2884516087680963945677749

theorem tailTrace_5617575 : CollatzResearch.WordTrace tailWord_5617575 prefixEnd_5617575 2884516087680963945677749 := by
  unfold tailWord_5617575
  simp only [CollatzResearch.WordTrace]
  refine ⟨204889792623492655272942179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136593195082328436848628119 204889792623492655272942179)
  ·
    refine ⟨307334688935238982909413269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204889792623492655272942179 307334688935238982909413269)
    ·
      refine ⟨14406313543839327323878747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 307334688935238982909413269 14406313543839327323878747)
      ·
        refine ⟨21609470315758990985818121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14406313543839327323878747 21609470315758990985818121)
        ·
          refine ⟨16207102736819243239363591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21609470315758990985818121 16207102736819243239363591)
          ·
            refine ⟨24310654105228864859045387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16207102736819243239363591 24310654105228864859045387)
            ·
              refine ⟨36465981157843297288568081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24310654105228864859045387 36465981157843297288568081)
              ·
                refine ⟨27349485868382472966426061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36465981157843297288568081 27349485868382472966426061)
                ·
                  refine ⟨10256057200643427362409773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27349485868382472966426061 10256057200643427362409773)
                  ·
                    refine ⟨3846021450241285260903665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10256057200643427362409773 3846021450241285260903665)
                    ·
                      refine ⟨2884516087680963945677749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846021450241285260903665 2884516087680963945677749)
                      ·
                        rfl

theorem cell23_5617575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_5617575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617575 prefixEnd_5617575 := by exact prefixLift 5617575
  have htrace : WordTrace (prefixWord ++ tailWord_5617575) baseStart_5617575 baseEnd_5617575 := by
    simpa [prefixWord, tailWord_5617575, baseEnd_5617575] using wordTrace_append hprefix tailTrace_5617575
  have hstable : (prefixWord ++ tailWord_5617575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617575).length < 2 ^ (prefixWord ++ tailWord_5617575).sum := by decide
  have hdescent : baseEnd_5617575 < baseStart_5617575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617591 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_5617591 : Nat := 118140960795 + 5617591 * 2 ^ 59
def prefixEnd_5617591 : Nat := 4983230072969 + 3 ^ 40 * 5617591 * 2
def baseEnd_5617591 : Nat := 2884524303371435883077675

theorem tailTrace_5617591 : CollatzResearch.WordTrace tailWord_5617591 prefixEnd_5617591 2884524303371435883077675 := by
  unfold tailWord_5617591
  simp only [CollatzResearch.WordTrace]
  refine ⟨204890376191434690005524627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136593584127623126670349751 204890376191434690005524627)
  ·
    refine ⟨307335564287152035008286941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204890376191434690005524627 307335564287152035008286941)
    ·
      refine ⟨115250836607682013128107603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307335564287152035008286941 115250836607682013128107603)
      ·
        refine ⟨172876254911523019692161405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115250836607682013128107603 172876254911523019692161405)
        ·
          refine ⟨64828595591821132384560527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172876254911523019692161405 64828595591821132384560527)
          ·
            refine ⟨97242893387731698576840791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64828595591821132384560527 97242893387731698576840791)
            ·
              refine ⟨145864340081597547865261187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97242893387731698576840791 145864340081597547865261187)
              ·
                refine ⟨218796510122396321797891781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 145864340081597547865261187 218796510122396321797891781)
                ·
                  refine ⟨41024345647949310337104709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218796510122396321797891781 41024345647949310337104709)
                  ·
                    refine ⟨7692064808990495688207133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 41024345647949310337104709 7692064808990495688207133)
                    ·
                      refine ⟨2884524303371435883077675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7692064808990495688207133 2884524303371435883077675)
                      ·
                        rfl

theorem cell23_5617591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_5617591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617591 prefixEnd_5617591 := by exact prefixLift 5617591
  have htrace : WordTrace (prefixWord ++ tailWord_5617591) baseStart_5617591 baseEnd_5617591 := by
    simpa [prefixWord, tailWord_5617591, baseEnd_5617591] using wordTrace_append hprefix tailTrace_5617591
  have hstable : (prefixWord ++ tailWord_5617591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617591).length < 2 ^ (prefixWord ++ tailWord_5617591).sum := by decide
  have hdescent : baseEnd_5617591 < baseStart_5617591 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617639 : List Nat := [1, 1, 5, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_5617639 : Nat := 118140960795 + 5617639 * 2 ^ 59
def prefixEnd_5617639 : Nat := 4983230072969 + 3 ^ 40 * 5617639 * 2
def baseEnd_5617639 : Nat := 2884548950442851695277455

theorem tailTrace_5617639 : CollatzResearch.WordTrace tailWord_5617639 prefixEnd_5617639 2884548950442851695277455 := by
  unfold tailWord_5617639
  simp only [CollatzResearch.WordTrace]
  refine ⟨204892126895260794203271971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136594751263507196135514647 204892126895260794203271971)
  ·
    refine ⟨307338190342891191304907957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204892126895260794203271971 307338190342891191304907957)
    ·
      refine ⟨28812955344646049184835121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 307338190342891191304907957 28812955344646049184835121)
      ·
        refine ⟨21609716508484536888626341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28812955344646049184835121 21609716508484536888626341)
        ·
          refine ⟨4051821845340850666617439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21609716508484536888626341 4051821845340850666617439)
          ·
            refine ⟨6077732768011275999926159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051821845340850666617439 6077732768011275999926159)
            ·
              refine ⟨9116599152016913999889239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6077732768011275999926159 9116599152016913999889239)
              ·
                refine ⟨13674898728025370999833859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9116599152016913999889239 13674898728025370999833859)
                ·
                  refine ⟨20512348092038056499750789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13674898728025370999833859 20512348092038056499750789)
                  ·
                    refine ⟨3846065267257135593703273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20512348092038056499750789 3846065267257135593703273)
                    ·
                      refine ⟨2884548950442851695277455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846065267257135593703273 2884548950442851695277455)
                      ·
                        rfl

theorem cell23_5617639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_5617639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617639 prefixEnd_5617639 := by exact prefixLift 5617639
  have htrace : WordTrace (prefixWord ++ tailWord_5617639) baseStart_5617639 baseEnd_5617639 := by
    simpa [prefixWord, tailWord_5617639, baseEnd_5617639] using wordTrace_append hprefix tailTrace_5617639
  have hstable : (prefixWord ++ tailWord_5617639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617639).length < 2 ^ (prefixWord ++ tailWord_5617639).sum := by decide
  have hdescent : baseEnd_5617639 < baseStart_5617639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617648 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 2, 5, 2]
def baseStart_5617648 : Nat := 118140960795 + 5617648 * 2 ^ 59
def prefixEnd_5617648 : Nat := 4983230072969 + 3 ^ 40 * 5617648 * 2
def baseEnd_5617648 : Nat := 2884553571768742160064913

theorem tailTrace_5617648 : CollatzResearch.WordTrace tailWord_5617648 prefixEnd_5617648 2884553571768742160064913 := by
  unfold tailWord_5617648
  simp only [CollatzResearch.WordTrace]
  refine ⟨102446227576114094370174799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136594970101485459160233065 102446227576114094370174799)
  ·
    refine ⟨153669341364171141555262199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 102446227576114094370174799 153669341364171141555262199)
    ·
      refine ⟨230504012046256712332893299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 153669341364171141555262199 230504012046256712332893299)
      ·
        refine ⟨345756018069385068499339949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 230504012046256712332893299 345756018069385068499339949)
        ·
          refine ⟨129658506776019400687252481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 345756018069385068499339949 129658506776019400687252481)
          ·
            refine ⟨97243880082014550515439361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 129658506776019400687252481 97243880082014550515439361)
            ·
              refine ⟨72932910061510912886579521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 97243880082014550515439361 72932910061510912886579521)
              ·
                refine ⟨54699682546133184664934641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72932910061510912886579521 54699682546133184664934641)
                ·
                  refine ⟨41024761909599888498700981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54699682546133184664934641 41024761909599888498700981)
                  ·
                    refine ⟨3846071429024989546753217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 41024761909599888498700981 3846071429024989546753217)
                    ·
                      refine ⟨2884553571768742160064913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846071429024989546753217 2884553571768742160064913)
                      ·
                        rfl

theorem cell23_5617648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 2, 5, 2].length) (baseStart_5617648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617648 prefixEnd_5617648 := by exact prefixLift 5617648
  have htrace : WordTrace (prefixWord ++ tailWord_5617648) baseStart_5617648 baseEnd_5617648 := by
    simpa [prefixWord, tailWord_5617648, baseEnd_5617648] using wordTrace_append hprefix tailTrace_5617648
  have hstable : (prefixWord ++ tailWord_5617648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617648).length < 2 ^ (prefixWord ++ tailWord_5617648).sum := by decide
  have hdescent : baseEnd_5617648 < baseStart_5617648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617662 : List Nat := [4, 2, 2, 2, 1, 1, 3, 3, 5]
def baseStart_5617662 : Nat := 118140960795 + 5617662 * 2 ^ 59
def prefixEnd_5617662 : Nat := 4983230072969 + 3 ^ 40 * 5617662 * 2
def baseEnd_5617662 : Nat := 320506751166433900587761

theorem tailTrace_5617662 : CollatzResearch.WordTrace tailWord_5617662 prefixEnd_5617662 320506751166433900587761 := by
  unfold tailWord_5617662
  simp only [CollatzResearch.WordTrace]
  refine ⟨25611620721772183641419905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 136595310516118312754239493 25611620721772183641419905)
  ·
    refine ⟨19208715541329137731064929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25611620721772183641419905 19208715541329137731064929)
    ·
      refine ⟨14406536655996853298298697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19208715541329137731064929 14406536655996853298298697)
      ·
        refine ⟨10804902491997639973724023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14406536655996853298298697 10804902491997639973724023)
        ·
          refine ⟨16207353737996459960586035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10804902491997639973724023 16207353737996459960586035)
          ·
            refine ⟨24311030606994689940879053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16207353737996459960586035 24311030606994689940879053)
            ·
              refine ⟨9116636477623008727829645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24311030606994689940879053 9116636477623008727829645)
              ·
                refine ⟨3418738679108628272936117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9116636477623008727829645 3418738679108628272936117)
                ·
                  refine ⟨320506751166433900587761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3418738679108628272936117 320506751166433900587761)
                  ·
                    rfl

theorem cell23_5617662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_5617662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617662 prefixEnd_5617662 := by exact prefixLift 5617662
  have htrace : WordTrace (prefixWord ++ tailWord_5617662) baseStart_5617662 baseEnd_5617662 := by
    simpa [prefixWord, tailWord_5617662, baseEnd_5617662] using wordTrace_append hprefix tailTrace_5617662
  have hstable : (prefixWord ++ tailWord_5617662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617662).length < 2 ^ (prefixWord ++ tailWord_5617662).sum := by decide
  have hdescent : baseEnd_5617662 < baseStart_5617662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617691 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 4]
def baseStart_5617691 : Nat := 118140960795 + 5617691 * 2 ^ 59
def prefixEnd_5617691 : Nat := 4983230072969 + 3 ^ 40 * 5617691 * 2
def baseEnd_5617691 : Nat := 2884575651436885491827215

theorem tailTrace_5617691 : CollatzResearch.WordTrace tailWord_5617691 prefixEnd_5617691 2884575651436885491827215 := by
  unfold tailWord_5617691
  simp only [CollatzResearch.WordTrace]
  refine ⟨204894023491072407084164927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136596015660714938056109951 204894023491072407084164927)
  ·
    refine ⟨307341035236608610626247391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204894023491072407084164927 307341035236608610626247391)
    ·
      refine ⟨461011552854912915939371087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307341035236608610626247391 461011552854912915939371087)
      ·
        refine ⟨691517329282369373909056631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461011552854912915939371087 691517329282369373909056631)
        ·
          refine ⟨1037275993923554060863584947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691517329282369373909056631 1037275993923554060863584947)
          ·
            refine ⟨1555913990885331091295377421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037275993923554060863584947 1555913990885331091295377421)
            ·
              refine ⟨583467746581999159235766533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1555913990885331091295377421 583467746581999159235766533)
              ·
                refine ⟨109400202484124842356706225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 583467746581999159235766533 109400202484124842356706225)
                ·
                  refine ⟨82050151863093631767529669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 109400202484124842356706225 82050151863093631767529669)
                  ·
                    refine ⟨15384403474330055956411813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 82050151863093631767529669 15384403474330055956411813)
                    ·
                      refine ⟨2884575651436885491827215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15384403474330055956411813 2884575651436885491827215)
                      ·
                        rfl

theorem cell23_5617691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 4].length) (baseStart_5617691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617691 prefixEnd_5617691 := by exact prefixLift 5617691
  have htrace : WordTrace (prefixWord ++ tailWord_5617691) baseStart_5617691 baseEnd_5617691 := by
    simpa [prefixWord, tailWord_5617691, baseEnd_5617691] using wordTrace_append hprefix tailTrace_5617691
  have hstable : (prefixWord ++ tailWord_5617691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617691).length < 2 ^ (prefixWord ++ tailWord_5617691).sum := by decide
  have hdescent : baseEnd_5617691 < baseStart_5617691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617745 : List Nat := [1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 3]
def baseStart_5617745 : Nat := 118140960795 + 5617745 * 2 ^ 59
def prefixEnd_5617745 : Nat := 4983230072969 + 3 ^ 40 * 5617745 * 2
def baseEnd_5617745 : Nat := 2884603379392228280551967

theorem tailTrace_5617745 : CollatzResearch.WordTrace tailWord_5617745 prefixEnd_5617745 2884603379392228280551967 := by
  unfold tailWord_5617745
  simp only [CollatzResearch.WordTrace]
  refine ⟨204895993032876774306630689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136597328688584516204420459 204895993032876774306630689)
  ·
    refine ⟨153671994774657580729973017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204895993032876774306630689 153671994774657580729973017)
    ·
      refine ⟨115253996080993185547479763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 153671994774657580729973017 115253996080993185547479763)
      ·
        refine ⟨172880994121489778321219645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115253996080993185547479763 172880994121489778321219645)
        ·
          refine ⟨64830372795558666870457367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172880994121489778321219645 64830372795558666870457367)
          ·
            refine ⟨97245559193338000305686051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64830372795558666870457367 97245559193338000305686051)
            ·
              refine ⟨145868338790007000458529077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 97245559193338000305686051 145868338790007000458529077)
              ·
                refine ⟨13675156761563156292987101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 145868338790007000458529077 13675156761563156292987101)
                ·
                  refine ⟨5128183785586183609870163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13675156761563156292987101 5128183785586183609870163)
                  ·
                    refine ⟨7692275678379275414805245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5128183785586183609870163 7692275678379275414805245)
                    ·
                      refine ⟨2884603379392228280551967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7692275678379275414805245 2884603379392228280551967)
                      ·
                        rfl

theorem cell23_5617745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_5617745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617745 prefixEnd_5617745 := by exact prefixLift 5617745
  have htrace : WordTrace (prefixWord ++ tailWord_5617745) baseStart_5617745 baseEnd_5617745 := by
    simpa [prefixWord, tailWord_5617745, baseEnd_5617745] using wordTrace_append hprefix tailTrace_5617745
  have hstable : (prefixWord ++ tailWord_5617745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617745).length < 2 ^ (prefixWord ++ tailWord_5617745).sum := by decide
  have hdescent : baseEnd_5617745 < baseStart_5617745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617772 : List Nat := [2, 2, 1, 1, 3, 3, 3, 1, 2, 3, 2]
def baseStart_5617772 : Nat := 118140960795 + 5617772 * 2 ^ 59
def prefixEnd_5617772 : Nat := 4983230072969 + 3 ^ 40 * 5617772 * 2
def baseEnd_5617772 : Nat := 2884617243369899674914343

theorem tailTrace_5617772 : CollatzResearch.WordTrace tailWord_5617772 prefixEnd_5617772 2884617243369899674914343 := by
  unfold tailWord_5617772
  simp only [CollatzResearch.WordTrace]
  refine ⟨102448488901889478958931785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 136597985202519305278575713 102448488901889478958931785)
  ·
    refine ⟨76836366676417109219198839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 102448488901889478958931785 76836366676417109219198839)
    ·
      refine ⟨115254550014625663828798259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76836366676417109219198839 115254550014625663828798259)
      ·
        refine ⟨172881825021938495743197389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 115254550014625663828798259 172881825021938495743197389)
        ·
          refine ⟨64830684383226935903699021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172881825021938495743197389 64830684383226935903699021)
          ·
            refine ⟨24311506643710100963887133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64830684383226935903699021 24311506643710100963887133)
            ·
              refine ⟨9116814991391287861457675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24311506643710100963887133 9116814991391287861457675)
              ·
                refine ⟨13675222487086931792186513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9116814991391287861457675 13675222487086931792186513)
                ·
                  refine ⟨10256416865315198844139885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13675222487086931792186513 10256416865315198844139885)
                  ·
                    refine ⟨3846156324493199566552457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10256416865315198844139885 3846156324493199566552457)
                    ·
                      refine ⟨2884617243369899674914343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3846156324493199566552457 2884617243369899674914343)
                      ·
                        rfl

theorem cell23_5617772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 3, 2].length) (baseStart_5617772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617772 prefixEnd_5617772 := by exact prefixLift 5617772
  have htrace : WordTrace (prefixWord ++ tailWord_5617772) baseStart_5617772 baseEnd_5617772 := by
    simpa [prefixWord, tailWord_5617772, baseEnd_5617772] using wordTrace_append hprefix tailTrace_5617772
  have hstable : (prefixWord ++ tailWord_5617772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617772).length < 2 ^ (prefixWord ++ tailWord_5617772).sum := by decide
  have hdescent : baseEnd_5617772 < baseStart_5617772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617782 : List Nat := [5, 1, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_5617782 : Nat := 118140960795 + 5617782 * 2 ^ 59
def prefixEnd_5617782 : Nat := 4983230072969 + 3 ^ 40 * 5617782 * 2
def baseEnd_5617782 : Nat := 961540792725481545263099

theorem tailTrace_5617782 : CollatzResearch.WordTrace tailWord_5617782 prefixEnd_5617782 961540792725481545263099 := by
  unfold tailWord_5617782
  simp only [CollatzResearch.WordTrace]
  refine ⟨12806083908358920601607975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 136598228355828486417151733 12806083908358920601607975)
  ·
    refine ⟨19209125862538380902411963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12806083908358920601607975 19209125862538380902411963)
    ·
      refine ⟨28813688793807571353617945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19209125862538380902411963 28813688793807571353617945)
      ·
        refine ⟨21610266595355678515213459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28813688793807571353617945 21610266595355678515213459)
        ·
          refine ⟨32415399893033517772820189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21610266595355678515213459 32415399893033517772820189)
          ·
            refine ⟨12155774959887569164807571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32415399893033517772820189 12155774959887569164807571)
            ·
              refine ⟨18233662439831353747211357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12155774959887569164807571 18233662439831353747211357)
              ·
                refine ⟨6837623414936757655204259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18233662439831353747211357 6837623414936757655204259)
                ·
                  refine ⟨10256435122405136482806389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6837623414936757655204259 10256435122405136482806389)
                  ·
                    refine ⟨961540792725481545263099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10256435122405136482806389 961540792725481545263099)
                    ·
                      rfl

theorem cell23_5617782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_5617782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617782 prefixEnd_5617782 := by exact prefixLift 5617782
  have htrace : WordTrace (prefixWord ++ tailWord_5617782) baseStart_5617782 baseEnd_5617782 := by
    simpa [prefixWord, tailWord_5617782, baseEnd_5617782] using wordTrace_append hprefix tailTrace_5617782
  have hstable : (prefixWord ++ tailWord_5617782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617782).length < 2 ^ (prefixWord ++ tailWord_5617782).sum := by decide
  have hdescent : baseEnd_5617782 < baseStart_5617782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617795 : List Nat := [1, 1, 1, 3, 3, 4, 1, 1, 4, 4]
def baseStart_5617795 : Nat := 118140960795 + 5617795 * 2 ^ 59
def prefixEnd_5617795 : Nat := 4983230072969 + 3 ^ 40 * 5617795 * 2
def baseEnd_5617795 : Nat := 961543017808317694975579

theorem tailTrace_5617795 : CollatzResearch.WordTrace tailWord_5617795 prefixEnd_5617795 961543017808317694975579 := by
  unfold tailWord_5617795
  simp only [CollatzResearch.WordTrace]
  refine ⟨204897816682695632845950839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136598544455130421897300559 204897816682695632845950839)
  ·
    refine ⟨307346725024043449268926259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204897816682695632845950839 307346725024043449268926259)
    ·
      refine ⟨461020087536065173903389389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 307346725024043449268926259 461020087536065173903389389)
      ·
        refine ⟨172882532826024440213771021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 461020087536065173903389389 172882532826024440213771021)
        ·
          refine ⟨64830949809759165080164133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 172882532826024440213771021 64830949809759165080164133)
          ·
            refine ⟨12155803089329843452530775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64830949809759165080164133 12155803089329843452530775)
            ·
              refine ⟨18233704633994765178796163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12155803089329843452530775 18233704633994765178796163)
              ·
                refine ⟨27350556950992147768194245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18233704633994765178796163 27350556950992147768194245)
                ·
                  refine ⟨5128229428311027706536421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27350556950992147768194245 5128229428311027706536421)
                  ·
                    refine ⟨961543017808317694975579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5128229428311027706536421 961543017808317694975579)
                    ·
                      rfl

theorem cell23_5617795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 1, 4, 4].length) (baseStart_5617795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617795 prefixEnd_5617795 := by exact prefixLift 5617795
  have htrace : WordTrace (prefixWord ++ tailWord_5617795) baseStart_5617795 baseEnd_5617795 := by
    simpa [prefixWord, tailWord_5617795, baseEnd_5617795] using wordTrace_append hprefix tailTrace_5617795
  have hstable : (prefixWord ++ tailWord_5617795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617795).length < 2 ^ (prefixWord ++ tailWord_5617795).sum := by decide
  have hdescent : baseEnd_5617795 < baseStart_5617795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617815 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_5617815 : Nat := 118140960795 + 5617815 * 2 ^ 59
def prefixEnd_5617815 : Nat := 4983230072969 + 3 ^ 40 * 5617815 * 2
def baseEnd_5617815 : Nat := 2884639323038043006676645

theorem tailTrace_5617815 : CollatzResearch.WordTrace tailWord_5617815 prefixEnd_5617815 2884639323038043006676645 := by
  unfold tailWord_5617815
  simp only [CollatzResearch.WordTrace]
  refine ⟨204898546142623176261678899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136599030761748784174452599 204898546142623176261678899)
  ·
    refine ⟨307347819213934764392518349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 204898546142623176261678899 307347819213934764392518349)
    ·
      refine ⟨115255432205225536647194381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 307347819213934764392518349 115255432205225536647194381)
      ·
        refine ⟨43220787076959576242697893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 115255432205225536647194381 43220787076959576242697893)
        ·
          refine ⟨8103897576929920545505855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 43220787076959576242697893 8103897576929920545505855)
          ·
            refine ⟨12155846365394880818258783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8103897576929920545505855 12155846365394880818258783)
            ·
              refine ⟨18233769548092321227388175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12155846365394880818258783 18233769548092321227388175)
              ·
                refine ⟨27350654322138481841082263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18233769548092321227388175 27350654322138481841082263)
                ·
                  refine ⟨41025981483207722761623395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27350654322138481841082263 41025981483207722761623395)
                  ·
                    refine ⟨61538972224811584142435093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 41025981483207722761623395 61538972224811584142435093)
                    ·
                      refine ⟨2884639323038043006676645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 61538972224811584142435093 2884639323038043006676645)
                      ·
                        rfl

theorem cell23_5617815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_5617815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617815 prefixEnd_5617815 := by exact prefixLift 5617815
  have htrace : WordTrace (prefixWord ++ tailWord_5617815) baseStart_5617815 baseEnd_5617815 := by
    simpa [prefixWord, tailWord_5617815, baseEnd_5617815] using wordTrace_append hprefix tailTrace_5617815
  have hstable : (prefixWord ++ tailWord_5617815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617815).length < 2 ^ (prefixWord ++ tailWord_5617815).sum := by decide
  have hdescent : baseEnd_5617815 < baseStart_5617815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5617825 : List Nat := [1, 2, 3, 3, 1, 2, 4, 7]
def baseStart_5617825 : Nat := 118140960795 + 5617825 * 2 ^ 59
def prefixEnd_5617825 : Nat := 4983230072969 + 3 ^ 40 * 5617825 * 2
def baseEnd_5617825 : Nat := 106838683623873628427837

theorem tailTrace_5617825 : CollatzResearch.WordTrace tailWord_5617825 prefixEnd_5617825 106838683623873628427837 := by
  unfold tailWord_5617825
  simp only [CollatzResearch.WordTrace]
  refine ⟨204898910872586947969542929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 136599273915057965313028619 204898910872586947969542929)
  ·
    refine ⟨153674183154440210977157197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 204898910872586947969542929 153674183154440210977157197)
    ·
      refine ⟨57627818682915079116433949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 153674183154440210977157197 57627818682915079116433949)
      ·
        refine ⟨21610432006093154668662731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57627818682915079116433949 21610432006093154668662731)
        ·
          refine ⟨32415648009139732002994097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21610432006093154668662731 32415648009139732002994097)
          ·
            refine ⟨24311736006854799002245573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32415648009139732002994097 24311736006854799002245573)
            ·
              refine ⟨4558450501285274812921045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24311736006854799002245573 4558450501285274812921045)
              ·
                refine ⟨106838683623873628427837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4558450501285274812921045 106838683623873628427837)
                ·
                  rfl

theorem cell23_5617825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 4, 7].length) (baseStart_5617825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5617825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5617825 prefixEnd_5617825 := by exact prefixLift 5617825
  have htrace : WordTrace (prefixWord ++ tailWord_5617825) baseStart_5617825 baseEnd_5617825 := by
    simpa [prefixWord, tailWord_5617825, baseEnd_5617825] using wordTrace_append hprefix tailTrace_5617825
  have hstable : (prefixWord ++ tailWord_5617825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5617825).length < 2 ^ (prefixWord ++ tailWord_5617825).sum := by decide
  have hdescent : baseEnd_5617825 < baseStart_5617825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5617825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
