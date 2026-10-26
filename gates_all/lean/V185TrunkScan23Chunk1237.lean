import V185TrunkScan23Chunk1236

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7329094 : List Nat := [6, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3]
def baseStart_7329094 : Nat := 118140960795 + 7329094 * 2 ^ 59
def prefixEnd_7329094 : Nat := 4983230072969 + 3 ^ 40 * 7329094 * 2
def baseEnd_7329094 : Nat := 3763347983983453119719117

theorem tailTrace_7329094 : CollatzResearch.WordTrace tailWord_7329094 prefixEnd_7329094 3763347983983453119719117 := by
  unfold tailWord_7329094
  simp only [CollatzResearch.WordTrace]
  refine ⟨8353563090935988201456823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178209345939967748297745557 8353563090935988201456823)
  ·
    refine ⟨12530344636403982302185235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8353563090935988201456823 12530344636403982302185235)
    ·
      refine ⟨18795516954605973453277853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12530344636403982302185235 18795516954605973453277853)
      ·
        refine ⟨7048318857977240044979195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18795516954605973453277853 7048318857977240044979195)
        ·
          refine ⟨10572478286965860067468793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7048318857977240044979195 10572478286965860067468793)
          ·
            refine ⟨7929358715224395050601595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10572478286965860067468793 7929358715224395050601595)
            ·
              refine ⟨11894038072836592575902393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7929358715224395050601595 11894038072836592575902393)
              ·
                refine ⟨8920528554627444431926795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11894038072836592575902393 8920528554627444431926795)
                ·
                  refine ⟨13380792831941166647890193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8920528554627444431926795 13380792831941166647890193)
                  ·
                    refine ⟨10035594623955874985917645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13380792831941166647890193 10035594623955874985917645)
                    ·
                      refine ⟨3763347983983453119719117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10035594623955874985917645 3763347983983453119719117)
                      ·
                        rfl

theorem cell23_7329094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_7329094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329094 prefixEnd_7329094 := by exact prefixLift 7329094
  have htrace : WordTrace (prefixWord ++ tailWord_7329094) baseStart_7329094 baseEnd_7329094 := by
    simpa [prefixWord, tailWord_7329094, baseEnd_7329094] using wordTrace_append hprefix tailTrace_7329094
  have hstable : (prefixWord ++ tailWord_7329094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329094).length < 2 ^ (prefixWord ++ tailWord_7329094).sum := by decide
  have hdescent : baseEnd_7329094 < baseStart_7329094 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329096 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 1, 4, 2]
def baseStart_7329096 : Nat := 118140960795 + 7329096 * 2 ^ 59
def prefixEnd_7329096 : Nat := 4983230072969 + 3 ^ 40 * 7329096 * 2
def baseEnd_7329096 : Nat := 3763349010944762111894107

theorem tailTrace_7329096 : CollatzResearch.WordTrace tailWord_7329096 prefixEnd_7329096 3763349010944762111894107 := by
  unfold tailWord_7329096
  simp only [CollatzResearch.WordTrace]
  refine ⟨133657045927972188394095571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178209394570629584525460761 133657045927972188394095571)
  ·
    refine ⟨200485568891958282591143357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133657045927972188394095571 200485568891958282591143357)
    ·
      refine ⟨75182088334484355971678759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200485568891958282591143357 75182088334484355971678759)
      ·
        refine ⟨112773132501726533957518139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75182088334484355971678759 112773132501726533957518139)
        ·
          refine ⟨169159698752589800936277209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112773132501726533957518139 169159698752589800936277209)
          ·
            refine ⟨126869774064442350702207907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169159698752589800936277209 126869774064442350702207907)
            ·
              refine ⟨190304661096663526053311861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126869774064442350702207907 190304661096663526053311861)
              ·
                refine ⟨17841061977812205567497987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190304661096663526053311861 17841061977812205567497987)
                ·
                  refine ⟨26761592966718308351246981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17841061977812205567497987 26761592966718308351246981)
                  ·
                    refine ⟨5017798681259682815858809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26761592966718308351246981 5017798681259682815858809)
                    ·
                      refine ⟨3763349010944762111894107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017798681259682815858809 3763349010944762111894107)
                      ·
                        rfl

theorem cell23_7329096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_7329096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329096 prefixEnd_7329096 := by exact prefixLift 7329096
  have htrace : WordTrace (prefixWord ++ tailWord_7329096) baseStart_7329096 baseEnd_7329096 := by
    simpa [prefixWord, tailWord_7329096, baseEnd_7329096] using wordTrace_append hprefix tailTrace_7329096
  have hstable : (prefixWord ++ tailWord_7329096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329096).length < 2 ^ (prefixWord ++ tailWord_7329096).sum := by decide
  have hdescent : baseEnd_7329096 < baseStart_7329096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329100 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 1, 3, 2]
def baseStart_7329100 : Nat := 118140960795 + 7329100 * 2 ^ 59
def prefixEnd_7329100 : Nat := 4983230072969 + 3 ^ 40 * 7329100 * 2
def baseEnd_7329100 : Nat := 3763351064867380096244089

theorem tailTrace_7329100 : CollatzResearch.WordTrace tailWord_7329100 prefixEnd_7329100 3763351064867380096244089 := by
  unfold tailWord_7329100
  simp only [CollatzResearch.WordTrace]
  refine ⟨133657118873964942735668377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178209491831953256980891169 133657118873964942735668377)
  ·
    refine ⟨100242839155473707051751283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133657118873964942735668377 100242839155473707051751283)
    ·
      refine ⟨150364258733210560577626925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100242839155473707051751283 150364258733210560577626925)
      ·
        refine ⟨56386597024953960216610097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150364258733210560577626925 56386597024953960216610097)
        ·
          refine ⟨42289947768715470162457573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56386597024953960216610097 42289947768715470162457573)
          ·
            refine ⟨7929365206634150655460795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42289947768715470162457573 7929365206634150655460795)
            ·
              refine ⟨11894047809951225983191193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7929365206634150655460795 11894047809951225983191193)
              ·
                refine ⟨8920535857463419487393395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11894047809951225983191193 8920535857463419487393395)
                ·
                  refine ⟨13380803786195129231090093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8920535857463419487393395 13380803786195129231090093)
                  ·
                    refine ⟨5017801419823173461658785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13380803786195129231090093 5017801419823173461658785)
                    ·
                      refine ⟨3763351064867380096244089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5017801419823173461658785 3763351064867380096244089)
                      ·
                        rfl

theorem cell23_7329100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 1, 3, 2].length) (baseStart_7329100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329100 prefixEnd_7329100 := by exact prefixLift 7329100
  have htrace : WordTrace (prefixWord ++ tailWord_7329100) baseStart_7329100 baseEnd_7329100 := by
    simpa [prefixWord, tailWord_7329100, baseEnd_7329100] using wordTrace_append hprefix tailTrace_7329100
  have hstable : (prefixWord ++ tailWord_7329100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329100).length < 2 ^ (prefixWord ++ tailWord_7329100).sum := by decide
  have hdescent : baseEnd_7329100 < baseStart_7329100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329136 : List Nat := [2, 1, 1, 1, 4, 2, 3, 4, 5]
def baseStart_7329136 : Nat := 118140960795 + 7329136 * 2 ^ 59
def prefixEnd_7329136 : Nat := 4983230072969 + 3 ^ 40 * 7329136 * 2
def baseEnd_7329136 : Nat := 418152172241215772821547

theorem tailTrace_7329136 : CollatzResearch.WordTrace tailWord_7329136 prefixEnd_7329136 418152172241215772821547 := by
  unfold tailWord_7329136
  simp only [CollatzResearch.WordTrace]
  refine ⟨133657775387899731809823631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178210367183866309079764841 133657775387899731809823631)
  ·
    refine ⟨200486663081849597714735447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133657775387899731809823631 200486663081849597714735447)
    ·
      refine ⟨300729994622774396572103171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200486663081849597714735447 300729994622774396572103171)
      ·
        refine ⟨451094991934161594858154757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300729994622774396572103171 451094991934161594858154757)
        ·
          refine ⟨84580310987655299035904017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 451094991934161594858154757 84580310987655299035904017)
          ·
            refine ⟨63435233240741474276928013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84580310987655299035904017 63435233240741474276928013)
            ·
              refine ⟨23788212465278052853848005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63435233240741474276928013 23788212465278052853848005)
              ·
                refine ⟨4460289837239634910096501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23788212465278052853848005 4460289837239634910096501)
                ·
                  refine ⟨418152172241215772821547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4460289837239634910096501 418152172241215772821547)
                  ·
                    rfl

theorem cell23_7329136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 3, 4, 5].length) (baseStart_7329136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329136 prefixEnd_7329136 := by exact prefixLift 7329136
  have htrace : WordTrace (prefixWord ++ tailWord_7329136) baseStart_7329136 baseEnd_7329136 := by
    simpa [prefixWord, tailWord_7329136, baseEnd_7329136] using wordTrace_append hprefix tailTrace_7329136
  have hstable : (prefixWord ++ tailWord_7329136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329136).length < 2 ^ (prefixWord ++ tailWord_7329136).sum := by decide
  have hdescent : baseEnd_7329136 < baseStart_7329136 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329149 : List Nat := [1, 4, 1, 1, 2, 2, 2, 2, 1, 7]
def baseStart_7329149 : Nat := 118140960795 + 7329149 * 2 ^ 59
def prefixEnd_7329149 : Nat := 4983230072969 + 3 ^ 40 * 7329149 * 2
def baseEnd_7329149 : Nat := 1254458741806483468177121

theorem tailTrace_7329149 : CollatzResearch.WordTrace tailWord_7329149 prefixEnd_7329149 1254458741806483468177121 := by
  unfold tailWord_7329149
  simp only [CollatzResearch.WordTrace]
  refine ⟨267316024924752366839870501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178210683283168244559913667 267316024924752366839870501)
  ·
    refine ⟨50121754673391068782475719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267316024924752366839870501 50121754673391068782475719)
    ·
      refine ⟨75182632010086603173713579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50121754673391068782475719 75182632010086603173713579)
      ·
        refine ⟨112773948015129904760570369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75182632010086603173713579 112773948015129904760570369)
        ·
          refine ⟨84580461011347428570427777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112773948015129904760570369 84580461011347428570427777)
          ·
            refine ⟨63435345758510571427820833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84580461011347428570427777 63435345758510571427820833)
            ·
              refine ⟨47576509318882928570865625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63435345758510571427820833 47576509318882928570865625)
              ·
                refine ⟨35682381989162196428149219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47576509318882928570865625 35682381989162196428149219)
                ·
                  refine ⟨53523572983743294642223829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35682381989162196428149219 53523572983743294642223829)
                  ·
                    refine ⟨1254458741806483468177121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53523572983743294642223829 1254458741806483468177121)
                    ·
                      rfl

theorem cell23_7329149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 7].length) (baseStart_7329149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329149 prefixEnd_7329149 := by exact prefixLift 7329149
  have htrace : WordTrace (prefixWord ++ tailWord_7329149) baseStart_7329149 baseEnd_7329149 := by
    simpa [prefixWord, tailWord_7329149, baseEnd_7329149] using wordTrace_append hprefix tailTrace_7329149
  have hstable : (prefixWord ++ tailWord_7329149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329149).length < 2 ^ (prefixWord ++ tailWord_7329149).sum := by decide
  have hdescent : baseEnd_7329149 < baseStart_7329149 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329169 : List Nat := [1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 4]
def baseStart_7329169 : Nat := 118140960795 + 7329169 * 2 ^ 59
def prefixEnd_7329169 : Nat := 4983230072969 + 3 ^ 40 * 7329169 * 2
def baseEnd_7329169 : Nat := 3763386495032540326281271

theorem tailTrace_7329169 : CollatzResearch.WordTrace tailWord_7329169 prefixEnd_7329169 3763386495032540326281271 := by
  unfold tailWord_7329169
  simp only [CollatzResearch.WordTrace]
  refine ⟨267316754384679910255598561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178211169589786606837065707 267316754384679910255598561)
  ·
    refine ⟨200487565788509932691698921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267316754384679910255598561 200487565788509932691698921)
    ·
      refine ⟨150365674341382449518774191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200487565788509932691698921 150365674341382449518774191)
      ·
        refine ⟨225548511512073674278161287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150365674341382449518774191 225548511512073674278161287)
        ·
          refine ⟨338322767268110511417241931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225548511512073674278161287 338322767268110511417241931)
          ·
            refine ⟨507484150902165767125862897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338322767268110511417241931 507484150902165767125862897)
            ·
              refine ⟨380613113176624325344397173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507484150902165767125862897 380613113176624325344397173)
              ·
                refine ⟨35682479360308530501037235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380613113176624325344397173 35682479360308530501037235)
                ·
                  refine ⟨53523719040462795751555853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35682479360308530501037235 53523719040462795751555853)
                  ·
                    refine ⟨20071394640173548406833445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53523719040462795751555853 20071394640173548406833445)
                    ·
                      refine ⟨3763386495032540326281271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20071394640173548406833445 3763386495032540326281271)
                      ·
                        rfl

theorem cell23_7329169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_7329169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329169 prefixEnd_7329169 := by exact prefixLift 7329169
  have htrace : WordTrace (prefixWord ++ tailWord_7329169) baseStart_7329169 baseEnd_7329169 := by
    simpa [prefixWord, tailWord_7329169, baseEnd_7329169] using wordTrace_append hprefix tailTrace_7329169
  have hstable : (prefixWord ++ tailWord_7329169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329169).length < 2 ^ (prefixWord ++ tailWord_7329169).sum := by decide
  have hdescent : baseEnd_7329169 < baseStart_7329169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329196 : List Nat := [2, 2, 1, 1, 1, 1, 5, 3, 3, 4]
def baseStart_7329196 : Nat := 118140960795 + 7329196 * 2 ^ 59
def prefixEnd_7329196 : Nat := 4983230072969 + 3 ^ 40 * 7329196 * 2
def baseEnd_7329196 : Nat := 1254466786336737240214549

theorem tailTrace_7329196 : CollatzResearch.WordTrace tailWord_7329196 prefixEnd_7329196 1254466786336737240214549 := by
  unfold tailWord_7329196
  simp only [CollatzResearch.WordTrace]
  refine ⟨133658869577791046933415721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178211826103721395911220961 133658869577791046933415721)
  ·
    refine ⟨100244152183343285200061791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133658869577791046933415721 100244152183343285200061791)
    ·
      refine ⟨150366228275014927800092687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100244152183343285200061791 150366228275014927800092687)
      ·
        refine ⟨225549342412522391700139031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150366228275014927800092687 225549342412522391700139031)
        ·
          refine ⟨338324013618783587550208547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225549342412522391700139031 338324013618783587550208547)
          ·
            refine ⟨507486020428175381325312821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338324013618783587550208547 507486020428175381325312821)
            ·
              refine ⟨47576814415141441999248077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 507486020428175381325312821 47576814415141441999248077)
              ·
                refine ⟨17841305405678040749718029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47576814415141441999248077 17841305405678040749718029)
                ·
                  refine ⟨6690489527129265281144261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17841305405678040749718029 6690489527129265281144261)
                  ·
                    refine ⟨1254466786336737240214549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6690489527129265281144261 1254466786336737240214549)
                    ·
                      rfl

theorem cell23_7329196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 4].length) (baseStart_7329196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329196 prefixEnd_7329196 := by exact prefixLift 7329196
  have htrace : WordTrace (prefixWord ++ tailWord_7329196) baseStart_7329196 baseEnd_7329196 := by
    simpa [prefixWord, tailWord_7329196, baseEnd_7329196] using wordTrace_append hprefix tailTrace_7329196
  have hstable : (prefixWord ++ tailWord_7329196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329196).length < 2 ^ (prefixWord ++ tailWord_7329196).sum := by decide
  have hdescent : baseEnd_7329196 < baseStart_7329196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329230 : List Nat := [4, 1, 1, 1, 2, 1, 5, 3, 1, 4]
def baseStart_7329230 : Nat := 118140960795 + 7329230 * 2 ^ 59
def prefixEnd_7329230 : Nat := 4983230072969 + 3 ^ 40 * 7329230 * 2
def baseEnd_7329230 : Nat := 1254472605784154862539497

theorem tailTrace_7329230 : CollatzResearch.WordTrace tailWord_7329230 prefixEnd_7329230 1254472605784154862539497 := by
  unfold tailWord_7329230
  simp only [CollatzResearch.WordTrace]
  refine ⟨33414872404682364709196143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178212652824972611782379429 33414872404682364709196143)
  ·
    refine ⟨50122308607023547063794215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33414872404682364709196143 50122308607023547063794215)
    ·
      refine ⟨75183462910535320595691323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50122308607023547063794215 75183462910535320595691323)
      ·
        refine ⟨112775194365802980893536985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75183462910535320595691323 112775194365802980893536985)
        ·
          refine ⟨84581395774352235670152739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112775194365802980893536985 84581395774352235670152739)
          ·
            refine ⟨126872093661528353505229109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84581395774352235670152739 126872093661528353505229109)
            ·
              refine ⟨11894258780768283141115229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126872093661528353505229109 11894258780768283141115229)
              ·
                refine ⟨4460347042788106177918211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11894258780768283141115229 4460347042788106177918211)
                ·
                  refine ⟨6690520564182159266877317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4460347042788106177918211 6690520564182159266877317)
                  ·
                    refine ⟨1254472605784154862539497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6690520564182159266877317 1254472605784154862539497)
                    ·
                      rfl

theorem cell23_7329230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_7329230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329230 prefixEnd_7329230 := by exact prefixLift 7329230
  have htrace : WordTrace (prefixWord ++ tailWord_7329230) baseStart_7329230 baseEnd_7329230 := by
    simpa [prefixWord, tailWord_7329230, baseEnd_7329230] using wordTrace_append hprefix tailTrace_7329230
  have hstable : (prefixWord ++ tailWord_7329230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329230).length < 2 ^ (prefixWord ++ tailWord_7329230).sum := by decide
  have hdescent : baseEnd_7329230 < baseStart_7329230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329256 : List Nat := [2, 1, 4, 1, 1, 2, 2, 2, 3, 5]
def baseStart_7329256 : Nat := 118140960795 + 7329256 * 2 ^ 59
def prefixEnd_7329256 : Nat := 4983230072969 + 3 ^ 40 * 7329256 * 2
def baseEnd_7329256 : Nat := 1254477055949827161964457

theorem tailTrace_7329256 : CollatzResearch.WordTrace tailWord_7329256 prefixEnd_7329256 1254477055949827161964457 := by
  unfold tailWord_7329256
  simp only [CollatzResearch.WordTrace]
  refine ⟨133659963767682362057007811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178213285023576482742677081 133659963767682362057007811)
  ·
    refine ⟨200489945651523543085511717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133659963767682362057007811 200489945651523543085511717)
    ·
      refine ⟨37591864809660664328533447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200489945651523543085511717 37591864809660664328533447)
      ·
        refine ⟨56387797214490996492800171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37591864809660664328533447 56387797214490996492800171)
        ·
          refine ⟨84581695821736494739200257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56387797214490996492800171 84581695821736494739200257)
          ·
            refine ⟨63436271866302371054400193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84581695821736494739200257 63436271866302371054400193)
            ·
              refine ⟨47577203899726778290800145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63436271866302371054400193 47577203899726778290800145)
              ·
                refine ⟨35682902924795083718100109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47577203899726778290800145 35682902924795083718100109)
                ·
                  refine ⟨13381088596798156394287541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35682902924795083718100109 13381088596798156394287541)
                  ·
                    refine ⟨1254477055949827161964457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13381088596798156394287541 1254477055949827161964457)
                    ·
                      rfl

theorem cell23_7329256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_7329256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329256 prefixEnd_7329256 := by exact prefixLift 7329256
  have htrace : WordTrace (prefixWord ++ tailWord_7329256) baseStart_7329256 baseEnd_7329256 := by
    simpa [prefixWord, tailWord_7329256, baseEnd_7329256] using wordTrace_append hprefix tailTrace_7329256
  have hstable : (prefixWord ++ tailWord_7329256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329256).length < 2 ^ (prefixWord ++ tailWord_7329256).sum := by decide
  have hdescent : baseEnd_7329256 < baseStart_7329256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329290 : List Nat := [3, 1, 2, 2, 2, 3, 3, 1, 1, 5]
def baseStart_7329290 : Nat := 118140960795 + 7329290 * 2 ^ 59
def prefixEnd_7329290 : Nat := 4983230072969 + 3 ^ 40 * 7329290 * 2
def baseEnd_7329290 : Nat := 1254482875397244784289405

theorem tailTrace_7329290 : CollatzResearch.WordTrace tailWord_7329290 prefixEnd_7329290 1254482875397244784289405 := by
  unfold tailWord_7329290
  simp only [CollatzResearch.WordTrace]
  refine ⟨66830291904310386980188331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178214111744827698613835549 66830291904310386980188331)
  ·
    refine ⟨100245437856465580470282497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66830291904310386980188331 100245437856465580470282497)
    ·
      refine ⟨75184078392349185352711873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100245437856465580470282497 75184078392349185352711873)
      ·
        refine ⟨56388058794261889014533905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75184078392349185352711873 56388058794261889014533905)
        ·
          refine ⟨42291044095696416760900429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56388058794261889014533905 42291044095696416760900429)
          ·
            refine ⟨15859141535886156285337661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42291044095696416760900429 15859141535886156285337661)
            ·
              refine ⟨5947178075957308607001623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15859141535886156285337661 5947178075957308607001623)
              ·
                refine ⟨8920767113935962910502435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947178075957308607001623 8920767113935962910502435)
                ·
                  refine ⟨13381150670903944365753653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8920767113935962910502435 13381150670903944365753653)
                  ·
                    refine ⟨1254482875397244784289405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13381150670903944365753653 1254482875397244784289405)
                    ·
                      rfl

theorem cell23_7329290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_7329290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329290 prefixEnd_7329290 := by exact prefixLift 7329290
  have htrace : WordTrace (prefixWord ++ tailWord_7329290) baseStart_7329290 baseEnd_7329290 := by
    simpa [prefixWord, tailWord_7329290, baseEnd_7329290] using wordTrace_append hprefix tailTrace_7329290
  have hstable : (prefixWord ++ tailWord_7329290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329290).length < 2 ^ (prefixWord ++ tailWord_7329290).sum := by decide
  have hdescent : baseEnd_7329290 < baseStart_7329290 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329299 : List Nat := [1, 1, 1, 2, 1, 17]
def baseStart_7329299 : Nat := 118140960795 + 7329299 * 2 ^ 59
def prefixEnd_7329299 : Nat := 4983230072969 + 3 ^ 40 * 7329299 * 2
def baseEnd_7329299 : Nat := 15487461923940842871011

theorem tailTrace_7329299 : CollatzResearch.WordTrace tailWord_7329299 prefixEnd_7329299 15487461923940842871011 := by
  unfold tailWord_7329299
  simp only [CollatzResearch.WordTrace]
  refine ⟨267321495874208942457830951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178214330582805961638553967 267321495874208942457830951)
  ·
    refine ⟨400982243811313413686746427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267321495874208942457830951 400982243811313413686746427)
    ·
      refine ⟨601473365716970120530119641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400982243811313413686746427 601473365716970120530119641)
      ·
        refine ⟨451105024287727590397589731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601473365716970120530119641 451105024287727590397589731)
        ·
          refine ⟨676657536431591385596384597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451105024287727590397589731 676657536431591385596384597)
          ·
            refine ⟨15487461923940842871011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 17 676657536431591385596384597 15487461923940842871011)
            ·
              rfl

theorem cell23_7329299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 17].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 17].length) (baseStart_7329299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329299 prefixEnd_7329299 := by exact prefixLift 7329299
  have htrace : WordTrace (prefixWord ++ tailWord_7329299) baseStart_7329299 baseEnd_7329299 := by
    simpa [prefixWord, tailWord_7329299, baseEnd_7329299] using wordTrace_append hprefix tailTrace_7329299
  have hstable : (prefixWord ++ tailWord_7329299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329299).length < 2 ^ (prefixWord ++ tailWord_7329299).sum := by decide
  have hdescent : baseEnd_7329299 < baseStart_7329299 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329306 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_7329306 : Nat := 118140960795 + 7329306 * 2 ^ 59
def prefixEnd_7329306 : Nat := 4983230072969 + 3 ^ 40 * 7329306 * 2
def baseEnd_7329306 : Nat := 3763456841882206290268141

theorem tailTrace_7329306 : CollatzResearch.WordTrace tailWord_7329306 prefixEnd_7329306 3763456841882206290268141 := by
  unfold tailWord_7329306
  simp only [CollatzResearch.WordTrace]
  refine ⟨66830437796295895663333943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178214500790122388435557181 66830437796295895663333943)
  ·
    refine ⟨100245656694443843495000915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66830437796295895663333943 100245656694443843495000915)
    ·
      refine ⟨150368485041665765242501373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100245656694443843495000915 150368485041665765242501373)
      ·
        refine ⟨56388181890624661965938015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150368485041665765242501373 56388181890624661965938015)
        ·
          refine ⟨84582272835936992948907023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56388181890624661965938015 84582272835936992948907023)
          ·
            refine ⟨126873409253905489423360535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84582272835936992948907023 126873409253905489423360535)
            ·
              refine ⟨190310113880858234135040803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126873409253905489423360535 190310113880858234135040803)
              ·
                refine ⟨285465170821287351202561205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190310113880858234135040803 285465170821287351202561205)
                ·
                  refine ⟨26762359764495689175240113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285465170821287351202561205 26762359764495689175240113)
                  ·
                    refine ⟨20071769823371766881430085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26762359764495689175240113 20071769823371766881430085)
                    ·
                      refine ⟨3763456841882206290268141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20071769823371766881430085 3763456841882206290268141)
                      ·
                        rfl

theorem cell23_7329306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_7329306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329306 prefixEnd_7329306 := by exact prefixLift 7329306
  have htrace : WordTrace (prefixWord ++ tailWord_7329306) baseStart_7329306 baseEnd_7329306 := by
    simpa [prefixWord, tailWord_7329306, baseEnd_7329306] using wordTrace_append hprefix tailTrace_7329306
  have hstable : (prefixWord ++ tailWord_7329306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329306).length < 2 ^ (prefixWord ++ tailWord_7329306).sum := by decide
  have hdescent : baseEnd_7329306 < baseStart_7329306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329313 : List Nat := [1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 3]
def baseStart_7329313 : Nat := 118140960795 + 7329313 * 2 ^ 59
def prefixEnd_7329313 : Nat := 4983230072969 + 3 ^ 40 * 7329313 * 2
def baseEnd_7329313 : Nat := 3763460436246787762880609

theorem tailTrace_7329313 : CollatzResearch.WordTrace tailWord_7329313 prefixEnd_7329313 3763460436246787762880609 := by
  unfold tailWord_7329313
  simp only [CollatzResearch.WordTrace]
  refine ⟨267322006496158222848840593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178214670997438815232560395 267322006496158222848840593)
  ·
    refine ⟨200491504872118667136630445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267322006496158222848840593 200491504872118667136630445)
    ·
      refine ⟨75184314327044500176236417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200491504872118667136630445 75184314327044500176236417)
      ·
        refine ⟨56388235745283375132177313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75184314327044500176236417 56388235745283375132177313)
        ·
          refine ⟨42291176808962531349132985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56388235745283375132177313 42291176808962531349132985)
          ·
            refine ⟨31718382606721898511849739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42291176808962531349132985 31718382606721898511849739)
            ·
              refine ⟨47577573910082847767774609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31718382606721898511849739 47577573910082847767774609)
              ·
                refine ⟨35683180432562135825830957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47577573910082847767774609 35683180432562135825830957)
                ·
                  refine ⟨13381192662210800934686609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35683180432562135825830957 13381192662210800934686609)
                  ·
                    refine ⟨10035894496658100701014957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13381192662210800934686609 10035894496658100701014957)
                    ·
                      refine ⟨3763460436246787762880609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10035894496658100701014957 3763460436246787762880609)
                      ·
                        rfl

theorem cell23_7329313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 2, 3, 2, 3].length) (baseStart_7329313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329313 prefixEnd_7329313 := by exact prefixLift 7329313
  have htrace : WordTrace (prefixWord ++ tailWord_7329313) baseStart_7329313 baseEnd_7329313 := by
    simpa [prefixWord, tailWord_7329313, baseEnd_7329313] using wordTrace_append hprefix tailTrace_7329313
  have hstable : (prefixWord ++ tailWord_7329313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329313).length < 2 ^ (prefixWord ++ tailWord_7329313).sum := by decide
  have hdescent : baseEnd_7329313 < baseStart_7329313 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329320 : List Nat := [2, 1, 5, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7329320 : Nat := 118140960795 + 7329320 * 2 ^ 59
def prefixEnd_7329320 : Nat := 4983230072969 + 3 ^ 40 * 7329320 * 2
def baseEnd_7329320 : Nat := 1254488010203789745164359

theorem tailTrace_7329320 : CollatzResearch.WordTrace tailWord_7329320 prefixEnd_7329320 1254488010203789745164359 := by
  unfold tailWord_7329320
  simp only [CollatzResearch.WordTrace]
  refine ⟨133661130903566431522172707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178214841204755242029563609 133661130903566431522172707)
  ·
    refine ⟨200491696355349647283259061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133661130903566431522172707 200491696355349647283259061)
    ·
      refine ⟨18796096533314029432805537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200491696355349647283259061 18796096533314029432805537)
      ·
        refine ⟨14097072399985522074604153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18796096533314029432805537 14097072399985522074604153)
        ·
          refine ⟨10572804299989141555953115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14097072399985522074604153 10572804299989141555953115)
          ·
            refine ⟨15859206449983712333929673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10572804299989141555953115 15859206449983712333929673)
            ·
              refine ⟨11894404837487784250447255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15859206449983712333929673 11894404837487784250447255)
              ·
                refine ⟨17841607256231676375670883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11894404837487784250447255 17841607256231676375670883)
                ·
                  refine ⟨26762410884347514563506325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17841607256231676375670883 26762410884347514563506325)
                  ·
                    refine ⟨1254488010203789745164359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26762410884347514563506325 1254488010203789745164359)
                    ·
                      rfl

theorem cell23_7329320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7329320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329320 prefixEnd_7329320 := by exact prefixLift 7329320
  have htrace : WordTrace (prefixWord ++ tailWord_7329320) baseStart_7329320 baseEnd_7329320 := by
    simpa [prefixWord, tailWord_7329320, baseEnd_7329320] using wordTrace_append hprefix tailTrace_7329320
  have hstable : (prefixWord ++ tailWord_7329320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329320).length < 2 ^ (prefixWord ++ tailWord_7329320).sum := by decide
  have hdescent : baseEnd_7329320 < baseStart_7329320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329333 : List Nat := [1, 3, 3, 1, 1, 4, 3, 7]
def baseStart_7329333 : Nat := 118140960795 + 7329333 * 2 ^ 59
def prefixEnd_7329333 : Nat := 4983230072969 + 3 ^ 40 * 7329333 * 2
def baseEnd_7329333 : Nat := 139387803920736210541871

theorem tailTrace_7329333 : CollatzResearch.WordTrace tailWord_7329333 prefixEnd_7329333 139387803920736210541871 := by
  unfold tailWord_7329333
  simp only [CollatzResearch.WordTrace]
  refine ⟨267322735956085766264568653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178215157304057177509712435 267322735956085766264568653)
  ·
    refine ⟨100246025983532162349213245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267322735956085766264568653 100246025983532162349213245)
    ·
      refine ⟨37592259743824560880954967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100246025983532162349213245 37592259743824560880954967)
      ·
        refine ⟨56388389615736841321432451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37592259743824560880954967 56388389615736841321432451)
        ·
          refine ⟨84582584423605261982148677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56388389615736841321432451 84582584423605261982148677)
          ·
            refine ⟨15859234579425986621652877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84582584423605261982148677 15859234579425986621652877)
            ·
              refine ⟨5947212967284744983119829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15859234579425986621652877 5947212967284744983119829)
              ·
                refine ⟨139387803920736210541871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5947212967284744983119829 139387803920736210541871)
                ·
                  rfl

theorem cell23_7329333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 3, 7].length) (baseStart_7329333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329333 prefixEnd_7329333 := by exact prefixLift 7329333
  have htrace : WordTrace (prefixWord ++ tailWord_7329333) baseStart_7329333 baseEnd_7329333 := by
    simpa [prefixWord, tailWord_7329333, baseEnd_7329333] using wordTrace_append hprefix tailTrace_7329333
  have hstable : (prefixWord ++ tailWord_7329333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329333).length < 2 ^ (prefixWord ++ tailWord_7329333).sum := by decide
  have hdescent : baseEnd_7329333 < baseStart_7329333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329343 : List Nat := [1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 3]
def baseStart_7329343 : Nat := 118140960795 + 7329343 * 2 ^ 59
def prefixEnd_7329343 : Nat := 4983230072969 + 3 ^ 40 * 7329343 * 2
def baseEnd_7329343 : Nat := 3763475840666422645505471

theorem tailTrace_7329343 : CollatzResearch.WordTrace tailWord_7329343 prefixEnd_7329343 3763475840666422645505471 := by
  unfold tailWord_7329343
  simp only [CollatzResearch.WordTrace]
  refine ⟨267323100686049537972432683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178215400457366358648288455 267323100686049537972432683)
  ·
    refine ⟨400984651029074306958649025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267323100686049537972432683 400984651029074306958649025)
    ·
      refine ⟨300738488271805730218986769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400984651029074306958649025 300738488271805730218986769)
      ·
        refine ⟨225553866203854297664240077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300738488271805730218986769 225553866203854297664240077)
        ·
          refine ⟨84582699826445361624090029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225553866203854297664240077 84582699826445361624090029)
          ·
            refine ⟨31718512434917010609033761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84582699826445361624090029 31718512434917010609033761)
            ·
              refine ⟨23788884326187757956775321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31718512434917010609033761 23788884326187757956775321)
              ·
                refine ⟨17841663244640818467581491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23788884326187757956775321 17841663244640818467581491)
                ·
                  refine ⟨26762494866961227701372237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17841663244640818467581491 26762494866961227701372237)
                  ·
                    refine ⟨10035935575110460388014589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26762494866961227701372237 10035935575110460388014589)
                    ·
                      refine ⟨3763475840666422645505471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10035935575110460388014589 3763475840666422645505471)
                      ·
                        rfl

theorem cell23_7329343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 2, 1, 3, 3].length) (baseStart_7329343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329343 prefixEnd_7329343 := by exact prefixLift 7329343
  have htrace : WordTrace (prefixWord ++ tailWord_7329343) baseStart_7329343 baseEnd_7329343 := by
    simpa [prefixWord, tailWord_7329343, baseEnd_7329343] using wordTrace_append hprefix tailTrace_7329343
  have hstable : (prefixWord ++ tailWord_7329343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329343).length < 2 ^ (prefixWord ++ tailWord_7329343).sum := by decide
  have hdescent : baseEnd_7329343 < baseStart_7329343 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329350 : List Nat := [6, 1, 1, 1, 3, 1, 10]
def baseStart_7329350 : Nat := 118140960795 + 7329350 * 2 ^ 59
def prefixEnd_7329350 : Nat := 4983230072969 + 3 ^ 40 * 7329350 * 2
def baseEnd_7329350 : Nat := 46462709074456840964419

theorem tailTrace_7329350 : CollatzResearch.WordTrace tailWord_7329350 prefixEnd_7329350 46462709074456840964419 := by
  unfold tailWord_7329350
  simp only [CollatzResearch.WordTrace]
  refine ⟨8353854874907005567748047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 178215570664682785445291669 8353854874907005567748047)
  ·
    refine ⟨12530782312360508351622071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8353854874907005567748047 12530782312360508351622071)
    ·
      refine ⟨18796173468540762527433107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12530782312360508351622071 18796173468540762527433107)
      ·
        refine ⟨28194260202811143791149661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18796173468540762527433107 28194260202811143791149661)
        ·
          refine ⟨10572847576054178921681123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28194260202811143791149661 10572847576054178921681123)
          ·
            refine ⟨15859271364081268382521685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10572847576054178921681123 15859271364081268382521685)
            ·
              refine ⟨46462709074456840964419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15859271364081268382521685 46462709074456840964419)
              ·
                rfl

theorem cell23_7329350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 10].length) (baseStart_7329350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329350 prefixEnd_7329350 := by exact prefixLift 7329350
  have htrace : WordTrace (prefixWord ++ tailWord_7329350) baseStart_7329350 baseEnd_7329350 := by
    simpa [prefixWord, tailWord_7329350, baseEnd_7329350] using wordTrace_append hprefix tailTrace_7329350
  have hstable : (prefixWord ++ tailWord_7329350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329350).length < 2 ^ (prefixWord ++ tailWord_7329350).sum := by decide
  have hdescent : baseEnd_7329350 < baseStart_7329350 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329377 : List Nat := [1, 2, 3, 1, 1, 3, 5, 1, 2, 1, 3]
def baseStart_7329377 : Nat := 118140960795 + 7329377 * 2 ^ 59
def prefixEnd_7329377 : Nat := 4983230072969 + 3 ^ 40 * 7329377 * 2
def baseEnd_7329377 : Nat := 3763493299008675512480315

theorem tailTrace_7329377 : CollatzResearch.WordTrace tailWord_7329377 prefixEnd_7329377 3763493299008675512480315 := by
  unfold tailWord_7329377
  simp only [CollatzResearch.WordTrace]
  refine ⟨267324340767926361779170385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178216227178617574519446923 267324340767926361779170385)
  ·
    refine ⟨200493255575944771334377789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267324340767926361779170385 200493255575944771334377789)
    ·
      refine ⟨75184970840979289250391671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200493255575944771334377789 75184970840979289250391671)
      ·
        refine ⟨112777456261468933875587507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75184970840979289250391671 112777456261468933875587507)
        ·
          refine ⟨169166184392203400813381261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112777456261468933875587507 169166184392203400813381261)
          ·
            refine ⟨63437319147076275305017973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169166184392203400813381261 63437319147076275305017973)
            ·
              refine ⟨5947248670038400809845435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63437319147076275305017973 5947248670038400809845435)
              ·
                refine ⟨8920873005057601214768153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947248670038400809845435 8920873005057601214768153)
                ·
                  refine ⟨6690654753793200911076115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8920873005057601214768153 6690654753793200911076115)
                  ·
                    refine ⟨10035982130689801366614173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6690654753793200911076115 10035982130689801366614173)
                    ·
                      refine ⟨3763493299008675512480315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10035982130689801366614173 3763493299008675512480315)
                      ·
                        rfl

theorem cell23_7329377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 5, 1, 2, 1, 3].length) (baseStart_7329377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329377 prefixEnd_7329377 := by exact prefixLift 7329377
  have htrace : WordTrace (prefixWord ++ tailWord_7329377) baseStart_7329377 baseEnd_7329377 := by
    simpa [prefixWord, tailWord_7329377, baseEnd_7329377] using wordTrace_append hprefix tailTrace_7329377
  have hstable : (prefixWord ++ tailWord_7329377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329377).length < 2 ^ (prefixWord ++ tailWord_7329377).sum := by decide
  have hdescent : baseEnd_7329377 < baseStart_7329377 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329428 : List Nat := [2, 4, 2, 2, 3, 1, 2, 1, 2, 1, 3]
def baseStart_7329428 : Nat := 118140960795 + 7329428 * 2 ^ 59
def prefixEnd_7329428 : Nat := 4983230072969 + 3 ^ 40 * 7329428 * 2
def baseEnd_7329428 : Nat := 3763519486522054812942581

theorem tailTrace_7329428 : CollatzResearch.WordTrace tailWord_7329428 prefixEnd_7329428 3763519486522054812942581 := by
  unfold tailWord_7329428
  simp only [CollatzResearch.WordTrace]
  refine ⟨133663100445370798744638469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178217467260494398326184625 133663100445370798744638469)
  ·
    refine ⟨25061831333507024764619713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133663100445370798744638469 25061831333507024764619713)
    ·
      refine ⟨18796373500130268573464785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25061831333507024764619713 18796373500130268573464785)
      ·
        refine ⟨14097280125097701430098589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18796373500130268573464785 14097280125097701430098589)
        ·
          refine ⟨5286480046911638036286971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14097280125097701430098589 5286480046911638036286971)
          ·
            refine ⟨7929720070367457054430457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286480046911638036286971 7929720070367457054430457)
            ·
              refine ⟨5947290052775592790822843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7929720070367457054430457 5947290052775592790822843)
              ·
                refine ⟨8920935079163389186234265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947290052775592790822843 8920935079163389186234265)
                ·
                  refine ⟨6690701309372541889675699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8920935079163389186234265 6690701309372541889675699)
                  ·
                    refine ⟨10036051964058812834513549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6690701309372541889675699 10036051964058812834513549)
                    ·
                      refine ⟨3763519486522054812942581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10036051964058812834513549 3763519486522054812942581)
                      ·
                        rfl

theorem cell23_7329428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_7329428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329428 prefixEnd_7329428 := by exact prefixLift 7329428
  have htrace : WordTrace (prefixWord ++ tailWord_7329428) baseStart_7329428 baseEnd_7329428 := by
    simpa [prefixWord, tailWord_7329428, baseEnd_7329428] using wordTrace_append hprefix tailTrace_7329428
  have hstable : (prefixWord ++ tailWord_7329428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329428).length < 2 ^ (prefixWord ++ tailWord_7329428).sum := by decide
  have hdescent : baseEnd_7329428 < baseStart_7329428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329463 : List Nat := [1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 5]
def baseStart_7329463 : Nat := 118140960795 + 7329463 * 2 ^ 59
def prefixEnd_7329463 : Nat := 4983230072969 + 3 ^ 40 * 7329463 * 2
def baseEnd_7329463 : Nat := 3763537458344962176004919

theorem tailTrace_7329463 : CollatzResearch.WordTrace tailWord_7329463 prefixEnd_7329463 3763537458344962176004919 := by
  unfold tailWord_7329463
  simp only [CollatzResearch.WordTrace]
  refine ⟨267327477445614798466801043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178218318297076532311200695 267327477445614798466801043)
  ·
    refine ⟨400991216168422197700201565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267327477445614798466801043 400991216168422197700201565)
    ·
      refine ⟨150371706063158324137575587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 400991216168422197700201565 150371706063158324137575587)
      ·
        refine ⟨225557559094737486206363381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150371706063158324137575587 225557559094737486206363381)
        ·
          refine ⟨21146021165131639331846567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225557559094737486206363381 21146021165131639331846567)
          ·
            refine ⟨31719031747697458997769851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21146021165131639331846567 31719031747697458997769851)
            ·
              refine ⟨47578547621546188496654777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31719031747697458997769851 47578547621546188496654777)
              ·
                refine ⟨35683910716159641372491083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47578547621546188496654777 35683910716159641372491083)
                ·
                  refine ⟨53525866074239462058736625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35683910716159641372491083 53525866074239462058736625)
                  ·
                    refine ⟨40144399555679596544052469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53525866074239462058736625 40144399555679596544052469)
                    ·
                      refine ⟨3763537458344962176004919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40144399555679596544052469 3763537458344962176004919)
                      ·
                        rfl

theorem cell23_7329463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_7329463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329463 prefixEnd_7329463 := by exact prefixLift 7329463
  have htrace : WordTrace (prefixWord ++ tailWord_7329463) baseStart_7329463 baseEnd_7329463 := by
    simpa [prefixWord, tailWord_7329463, baseEnd_7329463] using wordTrace_append hprefix tailTrace_7329463
  have hstable : (prefixWord ++ tailWord_7329463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329463).length < 2 ^ (prefixWord ++ tailWord_7329463).sum := by decide
  have hdescent : baseEnd_7329463 < baseStart_7329463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329470 : List Nat := [4, 2, 1, 1, 2, 2, 2, 2, 2, 5]
def baseStart_7329470 : Nat := 118140960795 + 7329470 * 2 ^ 59
def prefixEnd_7329470 : Nat := 4983230072969 + 3 ^ 40 * 7329470 * 2
def baseEnd_7329470 : Nat := 1254513684236514549539129

theorem tailTrace_7329470 : CollatzResearch.WordTrace tailWord_7329470 prefixEnd_7329470 1254513684236514549539129 := by
  unfold tailWord_7329470
  simp only [CollatzResearch.WordTrace]
  refine ⟨33415966594573679832788233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178218488504392959108203909 33415966594573679832788233)
  ·
    refine ⟨25061974945930259874591175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33415966594573679832788233 25061974945930259874591175)
    ·
      refine ⟨37592962418895389811886763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25061974945930259874591175 37592962418895389811886763)
      ·
        refine ⟨56389443628343084717830145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37592962418895389811886763 56389443628343084717830145)
        ·
          refine ⟨42292082721257313538372609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56389443628343084717830145 42292082721257313538372609)
          ·
            refine ⟨31719062040942985153779457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42292082721257313538372609 31719062040942985153779457)
            ·
              refine ⟨23789296530707238865334593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31719062040942985153779457 23789296530707238865334593)
              ·
                refine ⟨17841972398030429149000945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23789296530707238865334593 17841972398030429149000945)
                ·
                  refine ⟨13381479298522821861750709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17841972398030429149000945 13381479298522821861750709)
                  ·
                    refine ⟨1254513684236514549539129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13381479298522821861750709 1254513684236514549539129)
                    ·
                      rfl

theorem cell23_7329470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_7329470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329470 prefixEnd_7329470 := by exact prefixLift 7329470
  have htrace : WordTrace (prefixWord ++ tailWord_7329470) baseStart_7329470 baseEnd_7329470 := by
    simpa [prefixWord, tailWord_7329470, baseEnd_7329470] using wordTrace_append hprefix tailTrace_7329470
  have hstable : (prefixWord ++ tailWord_7329470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329470).length < 2 ^ (prefixWord ++ tailWord_7329470).sum := by decide
  have hdescent : baseEnd_7329470 < baseStart_7329470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329483 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 7, 4]
def baseStart_7329483 : Nat := 118140960795 + 7329483 * 2 ^ 59
def prefixEnd_7329483 : Nat := 4983230072969 + 3 ^ 40 * 7329483 * 2
def baseEnd_7329483 : Nat := 1254515909319350699251609

theorem tailTrace_7329483 : CollatzResearch.WordTrace tailWord_7329483 prefixEnd_7329483 1254515909319350699251609 := by
  unfold tailWord_7329483
  simp only [CollatzResearch.WordTrace]
  refine ⟨267328206905542341882529103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178218804603694894588352735 267328206905542341882529103)
  ·
    refine ⟨400992310358313512823793655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267328206905542341882529103 400992310358313512823793655)
    ·
      refine ⟨601488465537470269235690483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400992310358313512823793655 601488465537470269235690483)
      ·
        refine ⟨902232698306205403853535725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601488465537470269235690483 902232698306205403853535725)
        ·
          refine ⟨338337261864827026445075897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 902232698306205403853535725 338337261864827026445075897)
          ·
            refine ⟨253752946398620269833806923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338337261864827026445075897 253752946398620269833806923)
            ·
              refine ⟨380629419597930404750710385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253752946398620269833806923 380629419597930404750710385)
              ·
                refine ⟨285472064698447803563032789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380629419597930404750710385 285472064698447803563032789)
                ·
                  refine ⟨6690751516369870396008581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 285472064698447803563032789 6690751516369870396008581)
                  ·
                    refine ⟨1254515909319350699251609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6690751516369870396008581 1254515909319350699251609)
                    ·
                      rfl

theorem cell23_7329483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 7, 4].length) (baseStart_7329483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329483 prefixEnd_7329483 := by exact prefixLift 7329483
  have htrace : WordTrace (prefixWord ++ tailWord_7329483) baseStart_7329483 baseEnd_7329483 := by
    simpa [prefixWord, tailWord_7329483, baseEnd_7329483] using wordTrace_append hprefix tailTrace_7329483
  have hstable : (prefixWord ++ tailWord_7329483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329483).length < 2 ^ (prefixWord ++ tailWord_7329483).sum := by decide
  have hdescent : baseEnd_7329483 < baseStart_7329483 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329534 : List Nat := [4, 2, 2, 1, 3, 1, 2, 1, 3, 4]
def baseStart_7329534 : Nat := 118140960795 + 7329534 * 2 ^ 59
def prefixEnd_7329534 : Nat := 4983230072969 + 3 ^ 40 * 7329534 * 2
def baseEnd_7329534 : Nat := 1254524638490477132739031

theorem tailTrace_7329534 : CollatzResearch.WordTrace tailWord_7329534 prefixEnd_7329534 1254524638490477132739031 := by
  unfold tailWord_7329534
  simp only [CollatzResearch.WordTrace]
  refine ⟨33416258378544697199079457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178220044685571718395090437 33416258378544697199079457)
  ·
    refine ⟨25062193783908522899309593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33416258378544697199079457 25062193783908522899309593)
    ·
      refine ⟨18796645337931392174482195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25062193783908522899309593 18796645337931392174482195)
      ·
        refine ⟨28194968006897088261723293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18796645337931392174482195 28194968006897088261723293)
        ·
          refine ⟨10573113002586408098146235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28194968006897088261723293 10573113002586408098146235)
          ·
            refine ⟨15859669503879612147219353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10573113002586408098146235 15859669503879612147219353)
            ·
              refine ⟨11894752127909709110414515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15859669503879612147219353 11894752127909709110414515)
              ·
                refine ⟨17842128191864563665621773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11894752127909709110414515 17842128191864563665621773)
                ·
                  refine ⟨6690798071949211374608165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17842128191864563665621773 6690798071949211374608165)
                  ·
                    refine ⟨1254524638490477132739031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6690798071949211374608165 1254524638490477132739031)
                    ·
                      rfl

theorem cell23_7329534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_7329534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329534 prefixEnd_7329534 := by exact prefixLift 7329534
  have htrace : WordTrace (prefixWord ++ tailWord_7329534) baseStart_7329534 baseEnd_7329534 := by
    simpa [prefixWord, tailWord_7329534, baseEnd_7329534] using wordTrace_append hprefix tailTrace_7329534
  have hstable : (prefixWord ++ tailWord_7329534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329534).length < 2 ^ (prefixWord ++ tailWord_7329534).sum := by decide
  have hdescent : baseEnd_7329534 < baseStart_7329534 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329557 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 3]
def baseStart_7329557 : Nat := 118140960795 + 7329557 * 2 ^ 59
def prefixEnd_7329557 : Nat := 4983230072969 + 3 ^ 40 * 7329557 * 2
def baseEnd_7329557 : Nat := 3763585725526484808229487

theorem tailTrace_7329557 : CollatzResearch.WordTrace tailWord_7329557 prefixEnd_7329557 3763585725526484808229487 := by
  unfold tailWord_7329557
  simp only [CollatzResearch.WordTrace]
  refine ⟨267330905907274252520722925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178220603938182835013815283 267330905907274252520722925)
  ·
    refine ⟨100249089715227844695271097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267330905907274252520722925 100249089715227844695271097)
    ·
      refine ⟨75186817286420883521453323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100249089715227844695271097 75186817286420883521453323)
      ·
        refine ⟨112780225929631325282179985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75186817286420883521453323 112780225929631325282179985)
        ·
          refine ⟨84585169447223493961634989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112780225929631325282179985 84585169447223493961634989)
          ·
            refine ⟨31719438542708810235613121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84585169447223493961634989 31719438542708810235613121)
            ·
              refine ⟨23789578907031607676709841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31719438542708810235613121 23789578907031607676709841)
              ·
                refine ⟨17842184180273705757532381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23789578907031607676709841 17842184180273705757532381)
                ·
                  refine ⟨6690819067602639659074643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17842184180273705757532381 6690819067602639659074643)
                  ·
                    refine ⟨10036228601403959488611965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6690819067602639659074643 10036228601403959488611965)
                    ·
                      refine ⟨3763585725526484808229487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10036228601403959488611965 3763585725526484808229487)
                      ·
                        rfl

theorem cell23_7329557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 3, 1, 3].length) (baseStart_7329557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329557 prefixEnd_7329557 := by exact prefixLift 7329557
  have htrace : WordTrace (prefixWord ++ tailWord_7329557) baseStart_7329557 baseEnd_7329557 := by
    simpa [prefixWord, tailWord_7329557, baseEnd_7329557] using wordTrace_append hprefix tailTrace_7329557
  have hstable : (prefixWord ++ tailWord_7329557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329557).length < 2 ^ (prefixWord ++ tailWord_7329557).sum := by decide
  have hdescent : baseEnd_7329557 < baseStart_7329557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329560 : List Nat := [2, 1, 2, 3, 1, 1, 3, 4, 1, 5]
def baseStart_7329560 : Nat := 118140960795 + 7329560 * 2 ^ 59
def prefixEnd_7329560 : Nat := 4983230072969 + 3 ^ 40 * 7329560 * 2
def baseEnd_7329560 : Nat := 1254529088656149432163991

theorem tailTrace_7329560 : CollatzResearch.WordTrace tailWord_7329560 prefixEnd_7329560 1254529088656149432163991 := by
  unfold tailWord_7329560
  simp only [CollatzResearch.WordTrace]
  refine ⟨133665507663131692016541067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178220676884175589355388089 133665507663131692016541067)
  ·
    refine ⟨200498261494697538024811601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133665507663131692016541067 200498261494697538024811601)
    ·
      refine ⟨150373696121023153518608701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200498261494697538024811601 150373696121023153518608701)
      ·
        refine ⟨56390136045383682569478263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150373696121023153518608701 56390136045383682569478263)
        ·
          refine ⟨84585204068075523854217395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56390136045383682569478263 84585204068075523854217395)
          ·
            refine ⟨126877806102113285781326093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84585204068075523854217395 126877806102113285781326093)
            ·
              refine ⟨47579177288292482167997285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126877806102113285781326093 47579177288292482167997285)
              ·
                refine ⟨8921095741554840406499491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47579177288292482167997285 8921095741554840406499491)
                ·
                  refine ⟨13381643612332260609749237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8921095741554840406499491 13381643612332260609749237)
                  ·
                    refine ⟨1254529088656149432163991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13381643612332260609749237 1254529088656149432163991)
                    ·
                      rfl

theorem cell23_7329560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 4, 1, 5].length) (baseStart_7329560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329560 prefixEnd_7329560 := by exact prefixLift 7329560
  have htrace : WordTrace (prefixWord ++ tailWord_7329560) baseStart_7329560 baseEnd_7329560 := by
    simpa [prefixWord, tailWord_7329560, baseEnd_7329560] using wordTrace_append hprefix tailTrace_7329560
  have hstable : (prefixWord ++ tailWord_7329560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329560).length < 2 ^ (prefixWord ++ tailWord_7329560).sum := by decide
  have hdescent : baseEnd_7329560 < baseStart_7329560 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329567 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 2, 3, 2]
def baseStart_7329567 : Nat := 118140960795 + 7329567 * 2 ^ 59
def prefixEnd_7329567 : Nat := 4983230072969 + 3 ^ 40 * 7329567 * 2
def baseEnd_7329567 : Nat := 3763590860333029769104441

theorem tailTrace_7329567 : CollatzResearch.WordTrace tailWord_7329567 prefixEnd_7329567 3763590860333029769104441 := by
  unfold tailWord_7329567
  simp only [CollatzResearch.WordTrace]
  refine ⟨267331270637238024228586955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178220847091492016152391303 267331270637238024228586955)
  ·
    refine ⟨400996905955857036342880433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267331270637238024228586955 400996905955857036342880433)
    ·
      refine ⟨300747679466892777257160325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400996905955857036342880433 300747679466892777257160325)
      ·
        refine ⟨56390189900042395735717561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300747679466892777257160325 56390189900042395735717561)
        ·
          refine ⟨42292642425031796801788171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56390189900042395735717561 42292642425031796801788171)
          ·
            refine ⟨63438963637547695202682257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42292642425031796801788171 63438963637547695202682257)
            ·
              refine ⟨47579222728160771402011693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63438963637547695202682257 47579222728160771402011693)
              ·
                refine ⟨17842208523060289275754385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47579222728160771402011693 17842208523060289275754385)
                ·
                  refine ⟨13381656392295216956815789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17842208523060289275754385 13381656392295216956815789)
                  ·
                    refine ⟨5018121147110706358805921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13381656392295216956815789 5018121147110706358805921)
                    ·
                      refine ⟨3763590860333029769104441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5018121147110706358805921 3763590860333029769104441)
                      ·
                        rfl

theorem cell23_7329567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 3, 2].length) (baseStart_7329567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329567 prefixEnd_7329567 := by exact prefixLift 7329567
  have htrace : WordTrace (prefixWord ++ tailWord_7329567) baseStart_7329567 baseEnd_7329567 := by
    simpa [prefixWord, tailWord_7329567, baseEnd_7329567] using wordTrace_append hprefix tailTrace_7329567
  have hstable : (prefixWord ++ tailWord_7329567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329567).length < 2 ^ (prefixWord ++ tailWord_7329567).sum := by decide
  have hdescent : baseEnd_7329567 < baseStart_7329567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329583 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 5]
def baseStart_7329583 : Nat := 118140960795 + 7329583 * 2 ^ 59
def prefixEnd_7329583 : Nat := 4983230072969 + 3 ^ 40 * 7329583 * 2
def baseEnd_7329583 : Nat := 3763599076023501706504367

theorem tailTrace_7329583 : CollatzResearch.WordTrace tailWord_7329583 prefixEnd_7329583 3763599076023501706504367 := by
  unfold tailWord_7329583
  simp only [CollatzResearch.WordTrace]
  refine ⟨267331854205180058961169403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178221236136786705974112935 267331854205180058961169403)
  ·
    refine ⟨400997781307770088441754105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267331854205180058961169403 400997781307770088441754105)
    ·
      refine ⟨300748335980827566331315579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 400997781307770088441754105 300748335980827566331315579)
      ·
        refine ⟨451122503971241349496973369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300748335980827566331315579 451122503971241349496973369)
        ·
          refine ⟨338341877978431012122730027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451122503971241349496973369 338341877978431012122730027)
          ·
            refine ⟨507512816967646518184095041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338341877978431012122730027 507512816967646518184095041)
            ·
              refine ⟨380634612725734888638071281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507512816967646518184095041 380634612725734888638071281)
              ·
                refine ⟨285475959544301166478553461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380634612725734888638071281 285475959544301166478553461)
                ·
                  refine ⟨26763371207278234357364387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285475959544301166478553461 26763371207278234357364387)
                  ·
                    refine ⟨40145056810917351536046581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26763371207278234357364387 40145056810917351536046581)
                    ·
                      refine ⟨3763599076023501706504367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40145056810917351536046581 3763599076023501706504367)
                      ·
                        rfl

theorem cell23_7329583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 5, 1, 5].length) (baseStart_7329583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329583 prefixEnd_7329583 := by exact prefixLift 7329583
  have htrace : WordTrace (prefixWord ++ tailWord_7329583) baseStart_7329583 baseEnd_7329583 := by
    simpa [prefixWord, tailWord_7329583, baseEnd_7329583] using wordTrace_append hprefix tailTrace_7329583
  have hstable : (prefixWord ++ tailWord_7329583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329583).length < 2 ^ (prefixWord ++ tailWord_7329583).sum := by decide
  have hdescent : baseEnd_7329583 < baseStart_7329583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329603 : List Nat := [1, 1, 1, 3, 1, 5, 1, 10]
def baseStart_7329603 : Nat := 118140960795 + 7329603 * 2 ^ 59
def prefixEnd_7329603 : Nat := 4983230072969 + 3 ^ 40 * 7329603 * 2
def baseEnd_7329603 : Nat := 139392938727281171416825

theorem tailTrace_7329603 : CollatzResearch.WordTrace tailWord_7329603 prefixEnd_7329603 139392938727281171416825 := by
  unfold tailWord_7329603
  simp only [CollatzResearch.WordTrace]
  refine ⟨267332583665107602376897463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178221722443405068251264975 267332583665107602376897463)
  ·
    refine ⟨400998875497661403565346195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267332583665107602376897463 400998875497661403565346195)
    ·
      refine ⟨601498313246492105348019293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 400998875497661403565346195 601498313246492105348019293)
      ·
        refine ⟨225561867467434539505507235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601498313246492105348019293 225561867467434539505507235)
        ·
          refine ⟨338342801201151809258260853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225561867467434539505507235 338342801201151809258260853)
          ·
            refine ⟨31719637612607982117961955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 338342801201151809258260853 31719637612607982117961955)
            ·
              refine ⟨47579456418911973176942933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31719637612607982117961955 47579456418911973176942933)
              ·
                refine ⟨139392938727281171416825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47579456418911973176942933 139392938727281171416825)
                ·
                  rfl

theorem cell23_7329603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 10].length) (baseStart_7329603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329603 prefixEnd_7329603 := by exact prefixLift 7329603
  have htrace : WordTrace (prefixWord ++ tailWord_7329603) baseStart_7329603 baseEnd_7329603 := by
    simpa [prefixWord, tailWord_7329603, baseEnd_7329603] using wordTrace_append hprefix tailTrace_7329603
  have hstable : (prefixWord ++ tailWord_7329603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329603).length < 2 ^ (prefixWord ++ tailWord_7329603).sum := by decide
  have hdescent : baseEnd_7329603 < baseStart_7329603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329610 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_7329610 : Nat := 118140960795 + 7329610 * 2 ^ 59
def prefixEnd_7329610 : Nat := 4983230072969 + 3 ^ 40 * 7329610 * 2
def baseEnd_7329610 : Nat := 3763612940001173100866743

theorem tailTrace_7329610 : CollatzResearch.WordTrace tailWord_7329610 prefixEnd_7329610 3763612940001173100866743 := by
  unfold tailWord_7329610
  simp only [CollatzResearch.WordTrace]
  refine ⟨66833209744020560643100571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178221892650721495048268189 66833209744020560643100571)
  ·
    refine ⟨100249814616030840964650857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66833209744020560643100571 100249814616030840964650857)
    ·
      refine ⟨75187360962023130723488143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100249814616030840964650857 75187360962023130723488143)
      ·
        refine ⟨112781041443034696085232215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75187360962023130723488143 112781041443034696085232215)
        ·
          refine ⟨169171562164552044127848323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112781041443034696085232215 169171562164552044127848323)
          ·
            refine ⟨253757343246828066191772485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169171562164552044127848323 253757343246828066191772485)
            ·
              refine ⟨47579501858780262410957341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253757343246828066191772485 47579501858780262410957341)
              ·
                refine ⟨17842313197042598404109003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47579501858780262410957341 17842313197042598404109003)
                ·
                  refine ⟨26763469795563897606163505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17842313197042598404109003 26763469795563897606163505)
                  ·
                    refine ⟨20072602346672923204622629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26763469795563897606163505 20072602346672923204622629)
                    ·
                      refine ⟨3763612940001173100866743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20072602346672923204622629 3763612940001173100866743)
                      ·
                        rfl

theorem cell23_7329610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_7329610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329610 prefixEnd_7329610 := by exact prefixLift 7329610
  have htrace : WordTrace (prefixWord ++ tailWord_7329610) baseStart_7329610 baseEnd_7329610 := by
    simpa [prefixWord, tailWord_7329610, baseEnd_7329610] using wordTrace_append hprefix tailTrace_7329610
  have hstable : (prefixWord ++ tailWord_7329610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329610).length < 2 ^ (prefixWord ++ tailWord_7329610).sum := by decide
  have hdescent : baseEnd_7329610 < baseStart_7329610 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329617 : List Nat := [1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 3]
def baseStart_7329617 : Nat := 118140960795 + 7329617 * 2 ^ 59
def prefixEnd_7329617 : Nat := 4983230072969 + 3 ^ 40 * 7329617 * 2
def baseEnd_7329617 : Nat := 3763616534365754573479211

theorem tailTrace_7329617 : CollatzResearch.WordTrace tailWord_7329617 prefixEnd_7329617 3763616534365754573479211 := by
  unfold tailWord_7329617
  simp only [CollatzResearch.WordTrace]
  refine ⟨267333094287056882767907105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178222062858037921845271403 267333094287056882767907105)
  ·
    refine ⟨200499820715292662075930329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267333094287056882767907105 200499820715292662075930329)
    ·
      refine ⟨150374865536469496556947747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200499820715292662075930329 150374865536469496556947747)
      ·
        refine ⟨225562298304704244835421621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150374865536469496556947747 225562298304704244835421621)
        ·
          refine ⟨21146465466066022953320777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225562298304704244835421621 21146465466066022953320777)
          ·
            refine ⟨15859849099549517214990583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21146465466066022953320777 15859849099549517214990583)
            ·
              refine ⟨23789773649324275822485875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15859849099549517214990583 23789773649324275822485875)
              ·
                refine ⟨35684660473986413733728813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23789773649324275822485875 35684660473986413733728813)
                ·
                  refine ⟨13381747677744905150148305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35684660473986413733728813 13381747677744905150148305)
                  ·
                    refine ⟨10036310758308678862611229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13381747677744905150148305 10036310758308678862611229)
                    ·
                      refine ⟨3763616534365754573479211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10036310758308678862611229 3763616534365754573479211)
                      ·
                        rfl

theorem cell23_7329617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_7329617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329617 prefixEnd_7329617 := by exact prefixLift 7329617
  have htrace : WordTrace (prefixWord ++ tailWord_7329617) baseStart_7329617 baseEnd_7329617 := by
    simpa [prefixWord, tailWord_7329617, baseEnd_7329617] using wordTrace_append hprefix tailTrace_7329617
  have hstable : (prefixWord ++ tailWord_7329617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329617).length < 2 ^ (prefixWord ++ tailWord_7329617).sum := by decide
  have hdescent : baseEnd_7329617 < baseStart_7329617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329620 : List Nat := [2, 4, 1, 1, 3, 1, 2, 9]
def baseStart_7329620 : Nat := 118140960795 + 7329620 * 2 ^ 59
def prefixEnd_7329620 : Nat := 4983230072969 + 3 ^ 40 * 7329620 * 2
def baseEnd_7329620 : Nat := 139393262029915483768211

theorem tailTrace_7329620 : CollatzResearch.WordTrace tailWord_7329620 prefixEnd_7329620 139393262029915483768211 := by
  unfold tailWord_7329620
  simp only [CollatzResearch.WordTrace]
  refine ⟨133666601853023007140133157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178222135804030676186844209 133666601853023007140133157)
  ·
    refine ⟨25062487847441813838774967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133666601853023007140133157 25062487847441813838774967)
    ·
      refine ⟨37593731771162720758162451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25062487847441813838774967 37593731771162720758162451)
      ·
        refine ⟨56390597656744081137243677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37593731771162720758162451 56390597656744081137243677)
        ·
          refine ⟨21146474121279030426466379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56390597656744081137243677 21146474121279030426466379)
          ·
            refine ⟨31719711181918545639699569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21146474121279030426466379 31719711181918545639699569)
            ·
              refine ⟨23789783386438909229774677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31719711181918545639699569 23789783386438909229774677)
              ·
                refine ⟨139393262029915483768211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23789783386438909229774677 139393262029915483768211)
                ·
                  rfl

theorem cell23_7329620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 2, 9].length) (baseStart_7329620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329620 prefixEnd_7329620 := by exact prefixLift 7329620
  have htrace : WordTrace (prefixWord ++ tailWord_7329620) baseStart_7329620 baseEnd_7329620 := by
    simpa [prefixWord, tailWord_7329620, baseEnd_7329620] using wordTrace_append hprefix tailTrace_7329620
  have hstable : (prefixWord ++ tailWord_7329620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329620).length < 2 ^ (prefixWord ++ tailWord_7329620).sum := by decide
  have hdescent : baseEnd_7329620 < baseStart_7329620 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329634 : List Nat := [3, 3, 2, 1, 2, 3, 1, 1, 1, 1, 5]
def baseStart_7329634 : Nat := 118140960795 + 7329634 * 2 ^ 59
def prefixEnd_7329634 : Nat := 4983230072969 + 3 ^ 40 * 7329634 * 2
def baseEnd_7329634 : Nat := 3763625263536881006966633

theorem tailTrace_7329634 : CollatzResearch.WordTrace tailWord_7329634 prefixEnd_7329634 3763625263536881006966633 := by
  unfold tailWord_7329634
  simp only [CollatzResearch.WordTrace]
  refine ⟨66833428581998823667818989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178222476218663529780850637 66833428581998823667818989)
  ·
    refine ⟨25062535718249558875432121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66833428581998823667818989 25062535718249558875432121)
    ·
      refine ⟨18796901788687169156574091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25062535718249558875432121 18796901788687169156574091)
      ·
        refine ⟨28195352683030753734861137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18796901788687169156574091 28195352683030753734861137)
        ·
          refine ⟨21146514512273065301145853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28195352683030753734861137 21146514512273065301145853)
          ·
            refine ⟨7929942942102399487929695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21146514512273065301145853 7929942942102399487929695)
            ·
              refine ⟨11894914413153599231894543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7929942942102399487929695 11894914413153599231894543)
              ·
                refine ⟨17842371619730398847841815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11894914413153599231894543 17842371619730398847841815)
                ·
                  refine ⟨26763557429595598271762723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17842371619730398847841815 26763557429595598271762723)
                  ·
                    refine ⟨40145336144393397407644085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26763557429595598271762723 40145336144393397407644085)
                    ·
                      refine ⟨3763625263536881006966633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40145336144393397407644085 3763625263536881006966633)
                      ·
                        rfl

theorem cell23_7329634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_7329634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329634 prefixEnd_7329634 := by exact prefixLift 7329634
  have htrace : WordTrace (prefixWord ++ tailWord_7329634) baseStart_7329634 baseEnd_7329634 := by
    simpa [prefixWord, tailWord_7329634, baseEnd_7329634] using wordTrace_append hprefix tailTrace_7329634
  have hstable : (prefixWord ++ tailWord_7329634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329634).length < 2 ^ (prefixWord ++ tailWord_7329634).sum := by decide
  have hdescent : baseEnd_7329634 < baseStart_7329634 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329642 : List Nat := [3, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_7329642 : Nat := 118140960795 + 7329642 * 2 ^ 59
def prefixEnd_7329642 : Nat := 4983230072969 + 3 ^ 40 * 7329642 * 2
def baseEnd_7329642 : Nat := 3763629371382116975666597

theorem tailTrace_7329642 : CollatzResearch.WordTrace tailWord_7329642 prefixEnd_7329642 3763629371382116975666597 := by
  unfold tailWord_7329642
  simp only [CollatzResearch.WordTrace]
  refine ⟨66833501527991578009391795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178222670741310874691711453 66833501527991578009391795)
  ·
    refine ⟨100250252291987367014087693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66833501527991578009391795 100250252291987367014087693)
    ·
      refine ⟨37593844609495262630282885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100250252291987367014087693 37593844609495262630282885)
      ·
        refine ⟨7048845864280361743178041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37593844609495262630282885 7048845864280361743178041)
        ·
          refine ⟨5286634398210271307383531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7048845864280361743178041 5286634398210271307383531)
          ·
            refine ⟨7929951597315406961075297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286634398210271307383531 7929951597315406961075297)
            ·
              refine ⟨5947463697986555220806473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7929951597315406961075297 5947463697986555220806473)
              ·
                refine ⟨4460597773489916415604855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5947463697986555220806473 4460597773489916415604855)
                ·
                  refine ⟨6690896660234874623407283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4460597773489916415604855 6690896660234874623407283)
                  ·
                    refine ⟨10036344990352311935110925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6690896660234874623407283 10036344990352311935110925)
                    ·
                      refine ⟨3763629371382116975666597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10036344990352311935110925 3763629371382116975666597)
                      ·
                        rfl

theorem cell23_7329642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_7329642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329642 prefixEnd_7329642 := by exact prefixLift 7329642
  have htrace : WordTrace (prefixWord ++ tailWord_7329642) baseStart_7329642 baseEnd_7329642 := by
    simpa [prefixWord, tailWord_7329642, baseEnd_7329642] using wordTrace_append hprefix tailTrace_7329642
  have hstable : (prefixWord ++ tailWord_7329642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329642).length < 2 ^ (prefixWord ++ tailWord_7329642).sum := by decide
  have hdescent : baseEnd_7329642 < baseStart_7329642 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329654 : List Nat := [5, 1, 1, 3, 2, 2, 1, 8]
def baseStart_7329654 : Nat := 118140960795 + 7329654 * 2 ^ 59
def prefixEnd_7329654 : Nat := 4983230072969 + 3 ^ 40 * 7329654 * 2
def baseEnd_7329654 : Nat := 139393908635184108470983

theorem tailTrace_7329654 : CollatzResearch.WordTrace tailWord_7329654 prefixEnd_7329654 139393908635184108470983 := by
  unfold tailWord_7329654
  simp only [CollatzResearch.WordTrace]
  refine ⟨16708402736745177380437751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178222962525281892058002677 16708402736745177380437751)
  ·
    refine ⟨25062604105117766070656627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16708402736745177380437751 25062604105117766070656627)
    ·
      refine ⟨37593906157676649105984941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25062604105117766070656627 37593906157676649105984941)
      ·
        refine ⟨14097714809128743414744353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37593906157676649105984941 14097714809128743414744353)
        ·
          refine ⟨10573286106846557561058265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14097714809128743414744353 10573286106846557561058265)
          ·
            refine ⟨7929964580134918170793699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10573286106846557561058265 7929964580134918170793699)
            ·
              refine ⟨11894946870202377256190549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7929964580134918170793699 11894946870202377256190549)
              ·
                refine ⟨139393908635184108470983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11894946870202377256190549 139393908635184108470983)
                ·
                  rfl

theorem cell23_7329654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 1, 8].length) (baseStart_7329654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329654 prefixEnd_7329654 := by exact prefixLift 7329654
  have htrace : WordTrace (prefixWord ++ tailWord_7329654) baseStart_7329654 baseEnd_7329654 := by
    simpa [prefixWord, tailWord_7329654, baseEnd_7329654] using wordTrace_append hprefix tailTrace_7329654
  have hstable : (prefixWord ++ tailWord_7329654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329654).length < 2 ^ (prefixWord ++ tailWord_7329654).sum := by decide
  have hdescent : baseEnd_7329654 < baseStart_7329654 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329657 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 5, 3, 2]
def baseStart_7329657 : Nat := 118140960795 + 7329657 * 2 ^ 59
def prefixEnd_7329657 : Nat := 4983230072969 + 3 ^ 40 * 7329657 * 2
def baseEnd_7329657 : Nat := 3763637073591934416979027

theorem tailTrace_7329657 : CollatzResearch.WordTrace tailWord_7329657 prefixEnd_7329657 3763637073591934416979027 := by
  unfold tailWord_7329657
  simp only [CollatzResearch.WordTrace]
  refine ⟨267334553206911969599363225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178223035471274646399575483 267334553206911969599363225)
  ·
    refine ⟨200500914905183977199522419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267334553206911969599363225 200500914905183977199522419)
    ·
      refine ⟨300751372357775965799283629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200500914905183977199522419 300751372357775965799283629)
      ·
        refine ⟨112781764634165987174731361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300751372357775965799283629 112781764634165987174731361)
        ·
          refine ⟨84586323475624490381048521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112781764634165987174731361 84586323475624490381048521)
          ·
            refine ⟨63439742606718367785786391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84586323475624490381048521 63439742606718367785786391)
            ·
              refine ⟨95159613910077551678679587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63439742606718367785786391 95159613910077551678679587)
              ·
                refine ⟨142739420865116327518019381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95159613910077551678679587 142739420865116327518019381)
                ·
                  refine ⟨13381820706104655704814317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142739420865116327518019381 13381820706104655704814317)
                  ·
                    refine ⟨5018182764789245889305369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13381820706104655704814317 5018182764789245889305369)
                    ·
                      refine ⟨3763637073591934416979027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5018182764789245889305369 3763637073591934416979027)
                      ·
                        rfl

theorem cell23_7329657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 5, 3, 2].length) (baseStart_7329657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329657 prefixEnd_7329657 := by exact prefixLift 7329657
  have htrace : WordTrace (prefixWord ++ tailWord_7329657) baseStart_7329657 baseEnd_7329657 := by
    simpa [prefixWord, tailWord_7329657, baseEnd_7329657] using wordTrace_append hprefix tailTrace_7329657
  have hstable : (prefixWord ++ tailWord_7329657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329657).length < 2 ^ (prefixWord ++ tailWord_7329657).sum := by decide
  have hdescent : baseEnd_7329657 < baseStart_7329657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329698 : List Nat := [3, 3, 1, 2, 3, 2, 1, 2, 2, 1, 3]
def baseStart_7329698 : Nat := 118140960795 + 7329698 * 2 ^ 59
def prefixEnd_7329698 : Nat := 4983230072969 + 3 ^ 40 * 7329698 * 2
def baseEnd_7329698 : Nat := 3763658126298768756566339

theorem tailTrace_7329698 : CollatzResearch.WordTrace tailWord_7329698 prefixEnd_7329698 3763658126298768756566339 := by
  unfold tailWord_7329698
  simp only [CollatzResearch.WordTrace]
  refine ⟨66834012149940858400401437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178224032399842289067737165 66834012149940858400401437)
  ·
    refine ⟨25062754556227821900150539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66834012149940858400401437 25062754556227821900150539)
    ·
      refine ⟨37594131834341732850225809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25062754556227821900150539 37594131834341732850225809)
      ·
        refine ⟨28195598875756299637669357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37594131834341732850225809 28195598875756299637669357)
        ·
          refine ⟨10573349578408612364126009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28195598875756299637669357 10573349578408612364126009)
          ·
            refine ⟨7930012183806459273094507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10573349578408612364126009 7930012183806459273094507)
            ·
              refine ⟨11895018275709688909641761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930012183806459273094507 11895018275709688909641761)
              ·
                refine ⟨8921263706782266682231321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11895018275709688909641761 8921263706782266682231321)
                ·
                  refine ⟨6690947780086700011673491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8921263706782266682231321 6690947780086700011673491)
                  ·
                    refine ⟨10036421670130050017510237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6690947780086700011673491 10036421670130050017510237)
                    ·
                      refine ⟨3763658126298768756566339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10036421670130050017510237 3763658126298768756566339)
                      ·
                        rfl

theorem cell23_7329698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_7329698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329698 prefixEnd_7329698 := by exact prefixLift 7329698
  have htrace : WordTrace (prefixWord ++ tailWord_7329698) baseStart_7329698 baseEnd_7329698 := by
    simpa [prefixWord, tailWord_7329698, baseEnd_7329698] using wordTrace_append hprefix tailTrace_7329698
  have hstable : (prefixWord ++ tailWord_7329698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329698).length < 2 ^ (prefixWord ++ tailWord_7329698).sum := by decide
  have hdescent : baseEnd_7329698 < baseStart_7329698 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329717 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 4]
def baseStart_7329717 : Nat := 118140960795 + 7329717 * 2 ^ 59
def prefixEnd_7329717 : Nat := 4983230072969 + 3 ^ 40 * 7329717 * 2
def baseEnd_7329717 : Nat := 3763667882431204182228751

theorem tailTrace_7329717 : CollatzResearch.WordTrace tailWord_7329717 prefixEnd_7329717 3763667882431204182228751 := by
  unfold tailWord_7329717
  simp only [CollatzResearch.WordTrace]
  refine ⟨267336741586694599846547405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178224494391129733231031603 267336741586694599846547405)
  ·
    refine ⟨100251278095010474942455277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267336741586694599846547405 100251278095010474942455277)
    ·
      refine ⟨37594229285628928103420729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100251278095010474942455277 37594229285628928103420729)
      ·
        refine ⟨28195671964221696077565547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37594229285628928103420729 28195671964221696077565547)
        ·
          refine ⟨42293507946332544116348321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28195671964221696077565547 42293507946332544116348321)
          ·
            refine ⟨31720130959749408087261241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42293507946332544116348321 31720130959749408087261241)
            ·
              refine ⟨23790098219812056065445931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31720130959749408087261241 23790098219812056065445931)
              ·
                refine ⟨35685147329718084098168897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23790098219812056065445931 35685147329718084098168897)
                ·
                  refine ⟨26763860497288563073626673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35685147329718084098168897 26763860497288563073626673)
                  ·
                    refine ⟨20072895372966422305220005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26763860497288563073626673 20072895372966422305220005)
                    ·
                      refine ⟨3763667882431204182228751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20072895372966422305220005 3763667882431204182228751)
                      ·
                        rfl

theorem cell23_7329717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_7329717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329717 prefixEnd_7329717 := by exact prefixLift 7329717
  have htrace : WordTrace (prefixWord ++ tailWord_7329717) baseStart_7329717 baseEnd_7329717 := by
    simpa [prefixWord, tailWord_7329717, baseEnd_7329717] using wordTrace_append hprefix tailTrace_7329717
  have hstable : (prefixWord ++ tailWord_7329717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329717).length < 2 ^ (prefixWord ++ tailWord_7329717).sum := by decide
  have hdescent : baseEnd_7329717 < baseStart_7329717 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329787 : List Nat := [1, 1, 1, 1, 1, 3, 4, 4, 3, 4]
def baseStart_7329787 : Nat := 118140960795 + 7329787 * 2 ^ 59
def prefixEnd_7329787 : Nat := 4983230072969 + 3 ^ 40 * 7329787 * 2
def baseEnd_7329787 : Nat := 1254567942025672969451143

theorem tailTrace_7329787 : CollatzResearch.WordTrace tailWord_7329787 prefixEnd_7329787 1254567942025672969451143 := by
  unfold tailWord_7329787
  simp only [CollatzResearch.WordTrace]
  refine ⟨267339294696441001801595615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178226196464294001201063743 267339294696441001801595615)
  ·
    refine ⟨401008942044661502702393423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267339294696441001801595615 401008942044661502702393423)
    ·
      refine ⟨601513413066992254053590135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401008942044661502702393423 601513413066992254053590135)
      ·
        refine ⟨902270119600488381080385203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601513413066992254053590135 902270119600488381080385203)
        ·
          refine ⟨1353405179400732571620577805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902270119600488381080385203 1353405179400732571620577805)
          ·
            refine ⟨507526942275274714357716677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1353405179400732571620577805 507526942275274714357716677)
            ·
              refine ⟨95161301676614008942071877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 507526942275274714357716677 95161301676614008942071877)
              ·
                refine ⟨17842744064365126676638477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95161301676614008942071877 17842744064365126676638477)
                ·
                  refine ⟨6691029024136922503739429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17842744064365126676638477 6691029024136922503739429)
                  ·
                    refine ⟨1254567942025672969451143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6691029024136922503739429 1254567942025672969451143)
                    ·
                      rfl

theorem cell23_7329787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 3, 4].length) (baseStart_7329787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329787 prefixEnd_7329787 := by exact prefixLift 7329787
  have htrace : WordTrace (prefixWord ++ tailWord_7329787) baseStart_7329787 baseEnd_7329787 := by
    simpa [prefixWord, tailWord_7329787, baseEnd_7329787] using wordTrace_append hprefix tailTrace_7329787
  have hstable : (prefixWord ++ tailWord_7329787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329787).length < 2 ^ (prefixWord ++ tailWord_7329787).sum := by decide
  have hdescent : baseEnd_7329787 < baseStart_7329787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329812 : List Nat := [2, 4, 3, 2, 2, 1, 2, 2, 5]
def baseStart_7329812 : Nat := 118140960795 + 7329812 * 2 ^ 59
def prefixEnd_7329812 : Nat := 4983230072969 + 3 ^ 40 * 7329812 * 2
def baseEnd_7329812 : Nat := 418190740343709034504535

theorem tailTrace_7329812 : CollatzResearch.WordTrace tailWord_7329812 prefixEnd_7329812 418190740343709034504535 := by
  unfold tailWord_7329812
  simp only [CollatzResearch.WordTrace]
  refine ⟨133670103260675215535627845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178226804347566954047503793 133670103260675215535627845)
  ·
    refine ⟨25063144361376602912930221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 133670103260675215535627845 25063144361376602912930221)
    ·
      refine ⟨9398679135516226092348833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25063144361376602912930221 9398679135516226092348833)
      ·
        refine ⟨7049009351637169569261625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9398679135516226092348833 7049009351637169569261625)
        ·
          refine ⟨5286757013727877176946219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7049009351637169569261625 5286757013727877176946219)
          ·
            refine ⟨7930135520591815765419329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286757013727877176946219 7930135520591815765419329)
            ·
              refine ⟨5947601640443861824064497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7930135520591815765419329 5947601640443861824064497)
              ·
                refine ⟨4460701230332896368048373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5947601640443861824064497 4460701230332896368048373)
                ·
                  refine ⟨418190740343709034504535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4460701230332896368048373 418190740343709034504535)
                  ·
                    rfl

theorem cell23_7329812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_7329812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329812 prefixEnd_7329812 := by exact prefixLift 7329812
  have htrace : WordTrace (prefixWord ++ tailWord_7329812) baseStart_7329812 baseEnd_7329812 := by
    simpa [prefixWord, tailWord_7329812, baseEnd_7329812] using wordTrace_append hprefix tailTrace_7329812
  have hstable : (prefixWord ++ tailWord_7329812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329812).length < 2 ^ (prefixWord ++ tailWord_7329812).sum := by decide
  have hdescent : baseEnd_7329812 < baseStart_7329812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329834 : List Nat := [3, 1, 4, 1, 2, 1, 2, 3, 6]
def baseStart_7329834 : Nat := 118140960795 + 7329834 * 2 ^ 59
def prefixEnd_7329834 : Nat := 4983230072969 + 3 ^ 40 * 7329834 * 2
def baseEnd_7329834 : Nat := 418191995518642247162857

theorem tailTrace_7329834 : CollatzResearch.WordTrace tailWord_7329834 prefixEnd_7329834 418191995518642247162857 := by
  unfold tailWord_7329834
  simp only [CollatzResearch.WordTrace]
  refine ⟨66835252231817682207139139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178227339284847152552371037 66835252231817682207139139)
  ·
    refine ⟨100252878347726523310708709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66835252231817682207139139 100252878347726523310708709)
    ·
      refine ⟨18797414690198723120757883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100252878347726523310708709 18797414690198723120757883)
      ·
        refine ⟨28196122035298084681136825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18797414690198723120757883 28196122035298084681136825)
        ·
          refine ⟨21147091526473563510852619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28196122035298084681136825 21147091526473563510852619)
          ·
            refine ⟨31720637289710345266278929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21147091526473563510852619 31720637289710345266278929)
            ·
              refine ⟨23790477967282758949709197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31720637289710345266278929 23790477967282758949709197)
              ·
                refine ⟨8921429237731034606140949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23790477967282758949709197 8921429237731034606140949)
                ·
                  refine ⟨418191995518642247162857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8921429237731034606140949 418191995518642247162857)
                  ·
                    rfl

theorem cell23_7329834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 3, 6].length) (baseStart_7329834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329834 prefixEnd_7329834 := by exact prefixLift 7329834
  have htrace : WordTrace (prefixWord ++ tailWord_7329834) baseStart_7329834 baseEnd_7329834 := by
    simpa [prefixWord, tailWord_7329834, baseEnd_7329834] using wordTrace_append hprefix tailTrace_7329834
  have hstable : (prefixWord ++ tailWord_7329834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329834).length < 2 ^ (prefixWord ++ tailWord_7329834).sum := by decide
  have hdescent : baseEnd_7329834 < baseStart_7329834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329847 : List Nat := [1, 1, 3, 1, 2, 2, 4, 1, 3, 5]
def baseStart_7329847 : Nat := 118140960795 + 7329847 * 2 ^ 59
def prefixEnd_7329847 : Nat := 4983230072969 + 3 ^ 40 * 7329847 * 2
def baseEnd_7329847 : Nat := 1254578211638762891201051

theorem tailTrace_7329847 : CollatzResearch.WordTrace tailWord_7329847 prefixEnd_7329847 1254578211638762891201051 := by
  unfold tailWord_7329847
  simp only [CollatzResearch.WordTrace]
  refine ⟨267341483076223632048779795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178227655384149088032519863 267341483076223632048779795)
  ·
    refine ⟨401012224614335448073169693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267341483076223632048779795 401012224614335448073169693)
    ·
      refine ⟨150379584230375793027438635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401012224614335448073169693 150379584230375793027438635)
      ·
        refine ⟨225569376345563689541157953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150379584230375793027438635 225569376345563689541157953)
        ·
          refine ⟨169177032259172767155868465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225569376345563689541157953 169177032259172767155868465)
          ·
            refine ⟨126882774194379575366901349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169177032259172767155868465 126882774194379575366901349)
            ·
              refine ⟨23790520161446170381294003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126882774194379575366901349 23790520161446170381294003)
              ·
                refine ⟨35685780242169255571941005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23790520161446170381294003 35685780242169255571941005)
                ·
                  refine ⟨13382167590813470839477877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35685780242169255571941005 13382167590813470839477877)
                  ·
                    refine ⟨1254578211638762891201051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13382167590813470839477877 1254578211638762891201051)
                    ·
                      rfl

theorem cell23_7329847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 1, 3, 5].length) (baseStart_7329847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329847 prefixEnd_7329847 := by exact prefixLift 7329847
  have htrace : WordTrace (prefixWord ++ tailWord_7329847) baseStart_7329847 baseEnd_7329847 := by
    simpa [prefixWord, tailWord_7329847, baseEnd_7329847] using wordTrace_append hprefix tailTrace_7329847
  have hstable : (prefixWord ++ tailWord_7329847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329847).length < 2 ^ (prefixWord ++ tailWord_7329847).sum := by decide
  have hdescent : baseEnd_7329847 < baseStart_7329847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329848 : List Nat := [2, 1, 2, 1, 7, 1, 1, 1, 2, 2, 3]
def baseStart_7329848 : Nat := 118140960795 + 7329848 * 2 ^ 59
def prefixEnd_7329848 : Nat := 4983230072969 + 3 ^ 40 * 7329848 * 2
def baseEnd_7329848 : Nat := 3763735148396943169690649

theorem tailTrace_7329848 : CollatzResearch.WordTrace tailWord_7329848 prefixEnd_7329848 3763735148396943169690649 := by
  unfold tailWord_7329848
  simp only [CollatzResearch.WordTrace]
  refine ⟨133670759774610004609783099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178227679699480006146377465 133670759774610004609783099)
  ·
    refine ⟨200506139661915006914674649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133670759774610004609783099 200506139661915006914674649)
    ·
      refine ⟨150379604746436255186005987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200506139661915006914674649 150379604746436255186005987)
      ·
        refine ⟨225569407119654382779008981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150379604746436255186005987 225569407119654382779008981)
        ·
          refine ⟨5286782979366899596383023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 225569407119654382779008981 5286782979366899596383023)
          ·
            refine ⟨7930174469050349394574535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286782979366899596383023 7930174469050349394574535)
            ·
              refine ⟨11895261703575524091861803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930174469050349394574535 11895261703575524091861803)
              ·
                refine ⟨17842892555363286137792705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11895261703575524091861803 17842892555363286137792705)
                ·
                  refine ⟨13382169416522464603344529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17842892555363286137792705 13382169416522464603344529)
                  ·
                    refine ⟨10036627062391848452508397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13382169416522464603344529 10036627062391848452508397)
                    ·
                      refine ⟨3763735148396943169690649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10036627062391848452508397 3763735148396943169690649)
                      ·
                        rfl

theorem cell23_7329848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 1, 2, 2, 3].length) (baseStart_7329848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329848 prefixEnd_7329848 := by exact prefixLift 7329848
  have htrace : WordTrace (prefixWord ++ tailWord_7329848) baseStart_7329848 baseEnd_7329848 := by
    simpa [prefixWord, tailWord_7329848, baseEnd_7329848] using wordTrace_append hprefix tailTrace_7329848
  have hstable : (prefixWord ++ tailWord_7329848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329848).length < 2 ^ (prefixWord ++ tailWord_7329848).sum := by decide
  have hdescent : baseEnd_7329848 < baseStart_7329848 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329887 : List Nat := [1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 3]
def baseStart_7329887 : Nat := 118140960795 + 7329887 * 2 ^ 59
def prefixEnd_7329887 : Nat := 4983230072969 + 3 ^ 40 * 7329887 * 2
def baseEnd_7329887 : Nat := 3763755174142468517102969

theorem tailTrace_7329887 : CollatzResearch.WordTrace tailWord_7329887 prefixEnd_7329887 3763755174142468517102969 := by
  unfold tailWord_7329887
  simp only [CollatzResearch.WordTrace]
  refine ⟨267342941996078718880235915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178228627997385812586823943 267342941996078718880235915)
  ·
    refine ⟨401014412994118078320353873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267342941996078718880235915 401014412994118078320353873)
    ·
      refine ⟨300760809745588558740265405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401014412994118078320353873 300760809745588558740265405)
      ·
        refine ⟨112785303654595709527599527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300760809745588558740265405 112785303654595709527599527)
        ·
          refine ⟨169177955481893564291399291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112785303654595709527599527 169177955481893564291399291)
          ·
            refine ⟨253766933222840346437098937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169177955481893564291399291 253766933222840346437098937)
            ·
              refine ⟨190325199917130259827824203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253766933222840346437098937 190325199917130259827824203)
              ·
                refine ⟨285487799875695389741736305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190325199917130259827824203 285487799875695389741736305)
                ·
                  refine ⟨214115849906771542306302229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285487799875695389741736305 214115849906771542306302229)
                  ·
                    refine ⟨10036680464379916045607917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214115849906771542306302229 10036680464379916045607917)
                    ·
                      refine ⟨3763755174142468517102969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10036680464379916045607917 3763755174142468517102969)
                      ·
                        rfl

theorem cell23_7329887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_7329887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329887 prefixEnd_7329887 := by exact prefixLift 7329887
  have htrace : WordTrace (prefixWord ++ tailWord_7329887) baseStart_7329887 baseEnd_7329887 := by
    simpa [prefixWord, tailWord_7329887, baseEnd_7329887] using wordTrace_append hprefix tailTrace_7329887
  have hstable : (prefixWord ++ tailWord_7329887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329887).length < 2 ^ (prefixWord ++ tailWord_7329887).sum := by decide
  have hdescent : baseEnd_7329887 < baseStart_7329887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329897 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 6]
def baseStart_7329897 : Nat := 118140960795 + 7329897 * 2 ^ 59
def prefixEnd_7329897 : Nat := 4983230072969 + 3 ^ 40 * 7329897 * 2
def baseEnd_7329897 : Nat := 3763760308949013477977923

theorem tailTrace_7329897 : CollatzResearch.WordTrace tailWord_7329897 prefixEnd_7329897 3763760308949013477977923 := by
  unfold tailWord_7329897
  simp only [CollatzResearch.WordTrace]
  refine ⟨267343306726042490588099945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178228871150694993725399963 267343306726042490588099945)
  ·
    refine ⟨200507480044531867941074959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267343306726042490588099945 200507480044531867941074959)
    ·
      refine ⟨300761220066797801911612439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200507480044531867941074959 300761220066797801911612439)
      ·
        refine ⟨451141830100196702867418659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300761220066797801911612439 451141830100196702867418659)
        ·
          refine ⟨676712745150295054301127989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451141830100196702867418659 676712745150295054301127989)
          ·
            refine ⟨63441819857840161340730749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 676712745150295054301127989 63441819857840161340730749)
            ·
              refine ⟨23790682446690060502774031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63441819857840161340730749 23790682446690060502774031)
              ·
                refine ⟨35686023670035090754161047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23790682446690060502774031 35686023670035090754161047)
                ·
                  refine ⟨53529035505052636131241571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35686023670035090754161047 53529035505052636131241571)
                  ·
                    refine ⟨80293553257578954196862357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53529035505052636131241571 80293553257578954196862357)
                    ·
                      refine ⟨3763760308949013477977923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80293553257578954196862357 3763760308949013477977923)
                      ·
                        rfl

theorem cell23_7329897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 1, 6].length) (baseStart_7329897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329897 prefixEnd_7329897 := by exact prefixLift 7329897
  have htrace : WordTrace (prefixWord ++ tailWord_7329897) baseStart_7329897 baseEnd_7329897 := by
    simpa [prefixWord, tailWord_7329897, baseEnd_7329897] using wordTrace_append hprefix tailTrace_7329897
  have hstable : (prefixWord ++ tailWord_7329897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329897).length < 2 ^ (prefixWord ++ tailWord_7329897).sum := by decide
  have hdescent : baseEnd_7329897 < baseStart_7329897 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329901 : List Nat := [1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 4]
def baseStart_7329901 : Nat := 118140960795 + 7329901 * 2 ^ 59
def prefixEnd_7329901 : Nat := 4983230072969 + 3 ^ 40 * 7329901 * 2
def baseEnd_7329901 : Nat := 3763762362871631462327905

theorem tailTrace_7329901 : CollatzResearch.WordTrace tailWord_7329901 prefixEnd_7329901 3763762362871631462327905 := by
  unfold tailWord_7329901
  simp only [CollatzResearch.WordTrace]
  refine ⟨267343452618027999271245557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178228968412018666180830371 267343452618027999271245557)
  ·
    refine ⟨25063448682940124931679271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267343452618027999271245557 25063448682940124931679271)
    ·
      refine ⟨37595173024410187397518907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25063448682940124931679271 37595173024410187397518907)
      ·
        refine ⟨56392759536615281096278361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37595173024410187397518907 56392759536615281096278361)
        ·
          refine ⟨42294569652461460822208771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56392759536615281096278361 42294569652461460822208771)
          ·
            refine ⟨63441854478692191233313157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42294569652461460822208771 63441854478692191233313157)
            ·
              refine ⟨11895347714754785856246217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63441854478692191233313157 11895347714754785856246217)
              ·
                refine ⟨8921510786066089392184663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11895347714754785856246217 8921510786066089392184663)
                ·
                  refine ⟨13382266179099134088276995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8921510786066089392184663 13382266179099134088276995)
                  ·
                    refine ⟨20073399268648701132415493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13382266179099134088276995 20073399268648701132415493)
                    ·
                      refine ⟨3763762362871631462327905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20073399268648701132415493 3763762362871631462327905)
                      ·
                        rfl

theorem cell23_7329901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_7329901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329901 prefixEnd_7329901 := by exact prefixLift 7329901
  have htrace : WordTrace (prefixWord ++ tailWord_7329901) baseStart_7329901 baseEnd_7329901 := by
    simpa [prefixWord, tailWord_7329901, baseEnd_7329901] using wordTrace_append hprefix tailTrace_7329901
  have hstable : (prefixWord ++ tailWord_7329901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329901).length < 2 ^ (prefixWord ++ tailWord_7329901).sum := by decide
  have hdescent : baseEnd_7329901 < baseStart_7329901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329921 : List Nat := [1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 5]
def baseStart_7329921 : Nat := 118140960795 + 7329921 * 2 ^ 59
def prefixEnd_7329921 : Nat := 4983230072969 + 3 ^ 40 * 7329921 * 2
def baseEnd_7329921 : Nat := 3763772632484721384077813

theorem tailTrace_7329921 : CollatzResearch.WordTrace tailWord_7329921 prefixEnd_7329921 3763772632484721384077813 := by
  unfold tailWord_7329921
  simp only [CollatzResearch.WordTrace]
  refine ⟨267344182077955542686973617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178229454718637028457982411 267344182077955542686973617)
  ·
    refine ⟨200508136558466657015230213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267344182077955542686973617 200508136558466657015230213)
    ·
      refine ⟨37595275604712498190355665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200508136558466657015230213 37595275604712498190355665)
      ·
        refine ⟨28196456703534373642766749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37595275604712498190355665 28196456703534373642766749)
        ·
          refine ⟨10573671263825390116037531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28196456703534373642766749 10573671263825390116037531)
          ·
            refine ⟨15860506895738085174056297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10573671263825390116037531 15860506895738085174056297)
            ·
              refine ⟨11895380171803563880542223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15860506895738085174056297 11895380171803563880542223)
              ·
                refine ⟨17843070257705345820813335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11895380171803563880542223 17843070257705345820813335)
                ·
                  refine ⟨26764605386558018731220003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17843070257705345820813335 26764605386558018731220003)
                  ·
                    refine ⟨40146908079837028096830005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26764605386558018731220003 40146908079837028096830005)
                    ·
                      refine ⟨3763772632484721384077813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40146908079837028096830005 3763772632484721384077813)
                      ·
                        rfl

theorem cell23_7329921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_7329921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329921 prefixEnd_7329921 := by exact prefixLift 7329921
  have htrace : WordTrace (prefixWord ++ tailWord_7329921) baseStart_7329921 baseEnd_7329921 := by
    simpa [prefixWord, tailWord_7329921, baseEnd_7329921] using wordTrace_append hprefix tailTrace_7329921
  have hstable : (prefixWord ++ tailWord_7329921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329921).length < 2 ^ (prefixWord ++ tailWord_7329921).sum := by decide
  have hdescent : baseEnd_7329921 < baseStart_7329921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329967 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 4, 6]
def baseStart_7329967 : Nat := 118140960795 + 7329967 * 2 ^ 59
def prefixEnd_7329967 : Nat := 4983230072969 + 3 ^ 40 * 7329967 * 2
def baseEnd_7329967 : Nat := 1254598750864942734700867

theorem tailTrace_7329967 : CollatzResearch.WordTrace tailWord_7329967 prefixEnd_7329967 1254598750864942734700867 := by
  unfold tailWord_7329967
  simp only [CollatzResearch.WordTrace]
  refine ⟨267345859835788892543148155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178230573223859261695432103 267345859835788892543148155)
  ·
    refine ⟨401018789753683338814722233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267345859835788892543148155 401018789753683338814722233)
    ·
      refine ⟨300764092315262504111041675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401018789753683338814722233 300764092315262504111041675)
      ·
        refine ⟨451146138472893756166562513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300764092315262504111041675 451146138472893756166562513)
        ·
          refine ⟨338359603854670317124921885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451146138472893756166562513 338359603854670317124921885)
          ·
            refine ⟨126884851445501368921845707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338359603854670317124921885 126884851445501368921845707)
            ·
              refine ⟨190327277168252053382768561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126884851445501368921845707 190327277168252053382768561)
              ·
                refine ⟨142745457876189040037076421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190327277168252053382768561 142745457876189040037076421)
                ·
                  refine ⟨26764773351785445006951829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142745457876189040037076421 26764773351785445006951829)
                  ·
                    refine ⟨1254598750864942734700867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26764773351785445006951829 1254598750864942734700867)
                    ·
                      rfl

theorem cell23_7329967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 4, 6].length) (baseStart_7329967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329967 prefixEnd_7329967 := by exact prefixLift 7329967
  have htrace : WordTrace (prefixWord ++ tailWord_7329967) baseStart_7329967 baseEnd_7329967 := by
    simpa [prefixWord, tailWord_7329967, baseEnd_7329967] using wordTrace_append hprefix tailTrace_7329967
  have hstable : (prefixWord ++ tailWord_7329967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329967).length < 2 ^ (prefixWord ++ tailWord_7329967).sum := by decide
  have hdescent : baseEnd_7329967 < baseStart_7329967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329972 : List Nat := [2, 5, 3, 1, 1, 2, 1, 1, 1, 1, 5]
def baseStart_7329972 : Nat := 118140960795 + 7329972 * 2 ^ 59
def prefixEnd_7329972 : Nat := 4983230072969 + 3 ^ 40 * 7329972 * 2
def baseEnd_7329972 : Nat := 3763798819998100684540079

theorem tailTrace_7329972 : CollatzResearch.WordTrace tailWord_7329972 prefixEnd_7329972 3763798819998100684540079 := by
  unfold tailWord_7329972
  simp only [CollatzResearch.WordTrace]
  refine ⟨133673021100385389198540085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178230694800513852264720113 133673021100385389198540085)
  ·
    refine ⟨12531845728161130237363133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 133673021100385389198540085 12531845728161130237363133)
    ·
      refine ⟨4699442148060423839011175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12531845728161130237363133 4699442148060423839011175)
      ·
        refine ⟨7049163222090635758516763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4699442148060423839011175 7049163222090635758516763)
        ·
          refine ⟨10573744833135953637775145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7049163222090635758516763 10573744833135953637775145)
          ·
            refine ⟨7930308624851965228331359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10573744833135953637775145 7930308624851965228331359)
            ·
              refine ⟨11895462937277947842497039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7930308624851965228331359 11895462937277947842497039)
              ·
                refine ⟨17843194405916921763745559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11895462937277947842497039 17843194405916921763745559)
                ·
                  refine ⟨26764791608875382645618339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17843194405916921763745559 26764791608875382645618339)
                  ·
                    refine ⟨40147187413313073968427509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26764791608875382645618339 40147187413313073968427509)
                    ·
                      refine ⟨3763798819998100684540079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40147187413313073968427509 3763798819998100684540079)
                      ·
                        rfl

theorem cell23_7329972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_7329972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329972 prefixEnd_7329972 := by exact prefixLift 7329972
  have htrace : WordTrace (prefixWord ++ tailWord_7329972) baseStart_7329972 baseEnd_7329972 := by
    simpa [prefixWord, tailWord_7329972, baseEnd_7329972] using wordTrace_append hprefix tailTrace_7329972
  have hstable : (prefixWord ++ tailWord_7329972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329972).length < 2 ^ (prefixWord ++ tailWord_7329972).sum := by decide
  have hdescent : baseEnd_7329972 < baseStart_7329972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329986 : List Nat := [3, 5, 1, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_7329986 : Nat := 118140960795 + 7329986 * 2 ^ 59
def prefixEnd_7329986 : Nat := 4983230072969 + 3 ^ 40 * 7329986 * 2
def baseEnd_7329986 : Nat := 3763806008727263629765015

theorem tailTrace_7329986 : CollatzResearch.WordTrace tailWord_7329986 prefixEnd_7329986 3763806008727263629765015 := by
  unfold tailWord_7329986
  simp only [CollatzResearch.WordTrace]
  refine ⟨66836638205680014697022453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178231035215146705858726541 66836638205680014697022453)
  ·
    refine ⟨6265934831782501377845855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66836638205680014697022453 6265934831782501377845855)
    ·
      refine ⟨9398902247673752066768783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6265934831782501377845855 9398902247673752066768783)
      ·
        refine ⟨14098353371510628100153175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9398902247673752066768783 14098353371510628100153175)
        ·
          refine ⟨21147530057265942150229763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14098353371510628100153175 21147530057265942150229763)
          ·
            refine ⟨31721295085898913225344645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21147530057265942150229763 31721295085898913225344645)
            ·
              refine ⟨5947742828606046229752121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31721295085898913225344645 5947742828606046229752121)
              ·
                refine ⟨4460807121454534672314091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5947742828606046229752121 4460807121454534672314091)
                ·
                  refine ⟨6691210682181802008471137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4460807121454534672314091 6691210682181802008471137)
                  ·
                    refine ⟨5018408011636351506353353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6691210682181802008471137 5018408011636351506353353)
                    ·
                      refine ⟨3763806008727263629765015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5018408011636351506353353 3763806008727263629765015)
                      ·
                        rfl

theorem cell23_7329986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_7329986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329986 prefixEnd_7329986 := by exact prefixLift 7329986
  have htrace : WordTrace (prefixWord ++ tailWord_7329986) baseStart_7329986 baseEnd_7329986 := by
    simpa [prefixWord, tailWord_7329986, baseEnd_7329986] using wordTrace_append hprefix tailTrace_7329986
  have hstable : (prefixWord ++ tailWord_7329986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329986).length < 2 ^ (prefixWord ++ tailWord_7329986).sum := by decide
  have hdescent : baseEnd_7329986 < baseStart_7329986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7329994 : List Nat := [3, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3]
def baseStart_7329994 : Nat := 118140960795 + 7329994 * 2 ^ 59
def prefixEnd_7329994 : Nat := 4983230072969 + 3 ^ 40 * 7329994 * 2
def baseEnd_7329994 : Nat := 3763810116572499598464977

theorem tailTrace_7329994 : CollatzResearch.WordTrace tailWord_7329994 prefixEnd_7329994 3763810116572499598464977 := by
  unfold tailWord_7329994
  simp only [CollatzResearch.WordTrace]
  refine ⟨66836711151672769038595259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178231229737794050769587357 66836711151672769038595259)
  ·
    refine ⟨100255066727509153557892889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66836711151672769038595259 100255066727509153557892889)
    ·
      refine ⟨75191300045631865168419667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100255066727509153557892889 75191300045631865168419667)
      ·
        refine ⟨112786950068447797752629501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75191300045631865168419667 112786950068447797752629501)
        ·
          refine ⟨42295106275667924157236063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112786950068447797752629501 42295106275667924157236063)
          ·
            refine ⟨63442659413501886235854095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42295106275667924157236063 63442659413501886235854095)
            ·
              refine ⟨95163989120252829353781143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63442659413501886235854095 95163989120252829353781143)
              ·
                refine ⟨142745983680379244030671715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95163989120252829353781143 142745983680379244030671715)
                ·
                  refine ⟨214118975520568866046007573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142745983680379244030671715 214118975520568866046007573)
                  ·
                    refine ⟨10036826977526665595906605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214118975520568866046007573 10036826977526665595906605)
                    ·
                      refine ⟨3763810116572499598464977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10036826977526665595906605 3763810116572499598464977)
                      ·
                        rfl

theorem cell23_7329994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_7329994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7329994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7329994 prefixEnd_7329994 := by exact prefixLift 7329994
  have htrace : WordTrace (prefixWord ++ tailWord_7329994) baseStart_7329994 baseEnd_7329994 := by
    simpa [prefixWord, tailWord_7329994, baseEnd_7329994] using wordTrace_append hprefix tailTrace_7329994
  have hstable : (prefixWord ++ tailWord_7329994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7329994).length < 2 ^ (prefixWord ++ tailWord_7329994).sum := by decide
  have hdescent : baseEnd_7329994 < baseStart_7329994 := by decide
  rcases family_descends (prefixWord ++ tailWord_7329994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330008 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 1, 4, 2]
def baseStart_7330008 : Nat := 118140960795 + 7330008 * 2 ^ 59
def prefixEnd_7330008 : Nat := 4983230072969 + 3 ^ 40 * 7330008 * 2
def baseEnd_7330008 : Nat := 3763817305301662543689913

theorem tailTrace_7330008 : CollatzResearch.WordTrace tailWord_7330008 prefixEnd_7330008 3763817305301662543689913 := by
  unfold tailWord_7330008
  simp only [CollatzResearch.WordTrace]
  refine ⟨133673677614320178272695339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178231570152426904363593785 133673677614320178272695339)
  ·
    refine ⟨200510516421480267409043009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133673677614320178272695339 200510516421480267409043009)
    ·
      refine ⟨150382887316110200556782257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200510516421480267409043009 150382887316110200556782257)
      ·
        refine ⟨112787165487082650417586693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150382887316110200556782257 112787165487082650417586693)
        ·
          refine ⟨21147593528827996953297505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112787165487082650417586693 21147593528827996953297505)
          ·
            refine ⟨15860695146620997714973129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21147593528827996953297505 15860695146620997714973129)
            ·
              refine ⟨11895521359965748286229847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15860695146620997714973129 11895521359965748286229847)
              ·
                refine ⟨17843282039948622429344771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11895521359965748286229847 17843282039948622429344771)
                ·
                  refine ⟨26764923059922933644017157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17843282039948622429344771 26764923059922933644017157)
                  ·
                    refine ⟨5018423073735550058253217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26764923059922933644017157 5018423073735550058253217)
                    ·
                      refine ⟨3763817305301662543689913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5018423073735550058253217 3763817305301662543689913)
                      ·
                        rfl

theorem cell23_7330008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 1, 4, 2].length) (baseStart_7330008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330008 prefixEnd_7330008 := by exact prefixLift 7330008
  have htrace : WordTrace (prefixWord ++ tailWord_7330008) baseStart_7330008 baseEnd_7330008 := by
    simpa [prefixWord, tailWord_7330008, baseEnd_7330008] using wordTrace_append hprefix tailTrace_7330008
  have hstable : (prefixWord ++ tailWord_7330008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330008).length < 2 ^ (prefixWord ++ tailWord_7330008).sum := by decide
  have hdescent : baseEnd_7330008 < baseStart_7330008 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330029 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 1, 3, 2]
def baseStart_7330029 : Nat := 118140960795 + 7330029 * 2 ^ 59
def prefixEnd_7330029 : Nat := 4983230072969 + 3 ^ 40 * 7330029 * 2
def baseEnd_7330029 : Nat := 3763828088395406961527317

theorem tailTrace_7330029 : CollatzResearch.WordTrace tailWord_7330029 prefixEnd_7330029 3763828088395406961527317 := by
  unfold tailWord_7330029
  simp only [CollatzResearch.WordTrace]
  refine ⟨267348121161564277131905141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178232080774376184754603427 267348121161564277131905141)
  ·
    refine ⟨25063886358896650981116107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267348121161564277131905141 25063886358896650981116107)
    ·
      refine ⟨37595829538344976471674161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25063886358896650981116107 37595829538344976471674161)
      ·
        refine ⟨28196872153758732353755621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37595829538344976471674161 28196872153758732353755621)
        ·
          refine ⟨5286913528829762316329179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28196872153758732353755621 5286913528829762316329179)
          ·
            refine ⟨7930370293244643474493769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5286913528829762316329179 7930370293244643474493769)
            ·
              refine ⟨5947777719933482605870327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7930370293244643474493769 5947777719933482605870327)
              ·
                refine ⟨8921666579900223908805491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5947777719933482605870327 8921666579900223908805491)
                ·
                  refine ⟨13382499869850335863208237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8921666579900223908805491 13382499869850335863208237)
                  ·
                    refine ⟨5018437451193875948703089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13382499869850335863208237 5018437451193875948703089)
                    ·
                      refine ⟨3763828088395406961527317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5018437451193875948703089 3763828088395406961527317)
                      ·
                        rfl

theorem cell23_7330029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_7330029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330029 prefixEnd_7330029 := by exact prefixLift 7330029
  have htrace : WordTrace (prefixWord ++ tailWord_7330029) baseStart_7330029 baseEnd_7330029 := by
    simpa [prefixWord, tailWord_7330029, baseEnd_7330029] using wordTrace_append hprefix tailTrace_7330029
  have hstable : (prefixWord ++ tailWord_7330029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330029).length < 2 ^ (prefixWord ++ tailWord_7330029).sum := by decide
  have hdescent : baseEnd_7330029 < baseStart_7330029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330031 : List Nat := [1, 1, 2, 1, 6, 1, 1, 5, 5]
def baseStart_7330031 : Nat := 118140960795 + 7330031 * 2 ^ 59
def prefixEnd_7330031 : Nat := 4983230072969 + 3 ^ 40 * 7330031 * 2
def baseEnd_7330031 : Nat := 418203235039635105966923

theorem tailTrace_7330031 : CollatzResearch.WordTrace tailWord_7330031 prefixEnd_7330031 418203235039635105966923 := by
  unfold tailWord_7330031
  simp only [CollatzResearch.WordTrace]
  refine ⟨267348194107557031473477947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178232129405038020982318631 267348194107557031473477947)
  ·
    refine ⟨401022291161335547210216921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267348194107557031473477947 401022291161335547210216921)
    ·
      refine ⟨300766718371001660407662691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401022291161335547210216921 300766718371001660407662691)
      ·
        refine ⟨451150077556502490611494037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300766718371001660407662691 451150077556502490611494037)
        ·
          refine ⟨21147659885461054247413783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 451150077556502490611494037 21147659885461054247413783)
          ·
            refine ⟨31721489828191581371120675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21147659885461054247413783 31721489828191581371120675)
            ·
              refine ⟨47582234742287372056681013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31721489828191581371120675 47582234742287372056681013)
              ·
                refine ⟨4460834507089441130313845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47582234742287372056681013 4460834507089441130313845)
                ·
                  refine ⟨418203235039635105966923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4460834507089441130313845 418203235039635105966923)
                  ·
                    rfl

theorem cell23_7330031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 5, 5].length) (baseStart_7330031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330031 prefixEnd_7330031 := by exact prefixLift 7330031
  have htrace : WordTrace (prefixWord ++ tailWord_7330031) baseStart_7330031 baseEnd_7330031 := by
    simpa [prefixWord, tailWord_7330031, baseEnd_7330031] using wordTrace_append hprefix tailTrace_7330031
  have hstable : (prefixWord ++ tailWord_7330031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330031).length < 2 ^ (prefixWord ++ tailWord_7330031).sum := by decide
  have hdescent : baseEnd_7330031 < baseStart_7330031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330078 : List Nat := [4, 3, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_7330078 : Nat := 118140960795 + 7330078 * 2 ^ 59
def prefixEnd_7330078 : Nat := 4983230072969 + 3 ^ 40 * 7330078 * 2
def baseEnd_7330078 : Nat := 1254617749649159089938197

theorem tailTrace_7330078 : CollatzResearch.WordTrace tailWord_7330078 prefixEnd_7330078 1254617749649159089938197 := by
  unfold tailWord_7330078
  simp only [CollatzResearch.WordTrace]
  refine ⟨33418738542298344812554861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178233272225591172333625925 33418738542298344812554861)
  ·
    refine ⟨12532026953361879304708073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33418738542298344812554861 12532026953361879304708073)
    ·
      refine ⟨9399020215021409478531055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12532026953361879304708073 9399020215021409478531055)
      ·
        refine ⟨14098530322532114217796583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9399020215021409478531055 14098530322532114217796583)
        ·
          refine ⟨21147795483798171326694875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14098530322532114217796583 21147795483798171326694875)
          ·
            refine ⟨31721693225697256990042313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21147795483798171326694875 31721693225697256990042313)
            ·
              refine ⟨23791269919272942742531735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31721693225697256990042313 23791269919272942742531735)
              ·
                refine ⟨35686904878909414113797603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23791269919272942742531735 35686904878909414113797603)
                ·
                  refine ⟨53530357318364121170696405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35686904878909414113797603 53530357318364121170696405)
                  ·
                    refine ⟨1254617749649159089938197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53530357318364121170696405 1254617749649159089938197)
                    ·
                      rfl

theorem cell23_7330078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_7330078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330078 prefixEnd_7330078 := by exact prefixLift 7330078
  have htrace : WordTrace (prefixWord ++ tailWord_7330078) baseStart_7330078 baseEnd_7330078 := by
    simpa [prefixWord, tailWord_7330078, baseEnd_7330078] using wordTrace_append hprefix tailTrace_7330078
  have hstable : (prefixWord ++ tailWord_7330078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330078).length < 2 ^ (prefixWord ++ tailWord_7330078).sum := by decide
  have hdescent : baseEnd_7330078 < baseStart_7330078 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330081 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 1, 6, 2]
def baseStart_7330081 : Nat := 118140960795 + 7330081 * 2 ^ 59
def prefixEnd_7330081 : Nat := 4983230072969 + 3 ^ 40 * 7330081 * 2
def baseEnd_7330081 : Nat := 3763854789389440758077077

theorem tailTrace_7330081 : CollatzResearch.WordTrace tailWord_7330081 prefixEnd_7330081 3763854789389440758077077 := by
  unfold tailWord_7330081
  simp only [CollatzResearch.WordTrace]
  refine ⟨267350017757375890012798097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178233345171583926675198731 267350017757375890012798097)
  ·
    refine ⟨200512513318031917509598573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267350017757375890012798097 200512513318031917509598573)
    ·
      refine ⟨75192192494261969066099465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200512513318031917509598573 75192192494261969066099465)
      ·
        refine ⟨56394144370696476799574599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75192192494261969066099465 56394144370696476799574599)
        ·
          refine ⟨84591216556044715199361899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56394144370696476799574599 84591216556044715199361899)
          ·
            refine ⟨126886824834067072799042849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84591216556044715199361899 126886824834067072799042849)
            ·
              refine ⟨95165118625550304599282137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126886824834067072799042849 95165118625550304599282137)
              ·
                refine ⟨71373838969162728449461603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95165118625550304599282137 71373838969162728449461603)
                ·
                  refine ⟨107060758453744092674192405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71373838969162728449461603 107060758453744092674192405)
                  ·
                    refine ⟨5018473052519254344102769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107060758453744092674192405 5018473052519254344102769)
                    ·
                      refine ⟨3763854789389440758077077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5018473052519254344102769 3763854789389440758077077)
                      ·
                        rfl

theorem cell23_7330081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 6, 2].length) (baseStart_7330081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330081 prefixEnd_7330081 := by exact prefixLift 7330081
  have htrace : WordTrace (prefixWord ++ tailWord_7330081) baseStart_7330081 baseEnd_7330081 := by
    simpa [prefixWord, tailWord_7330081, baseEnd_7330081] using wordTrace_append hprefix tailTrace_7330081
  have hstable : (prefixWord ++ tailWord_7330081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330081).length < 2 ^ (prefixWord ++ tailWord_7330081).sum := by decide
  have hdescent : baseEnd_7330081 < baseStart_7330081 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330098 : List Nat := [3, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4]
def baseStart_7330098 : Nat := 118140960795 + 7330098 * 2 ^ 59
def prefixEnd_7330098 : Nat := 4983230072969 + 3 ^ 40 * 7330098 * 2
def baseEnd_7330098 : Nat := 3763863518560567191564499

theorem tailTrace_7330098 : CollatzResearch.WordTrace tailWord_7330098 prefixEnd_7330098 3763863518560567191564499 := by
  unfold tailWord_7330098
  simp only [CollatzResearch.WordTrace]
  refine ⟨66837659449578575479041737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178233758532209534610777965 66837659449578575479041737)
  ·
    refine ⟨50128244587183931609281303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66837659449578575479041737 50128244587183931609281303)
    ·
      refine ⟨75192366880775897413921955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50128244587183931609281303 75192366880775897413921955)
      ·
        refine ⟨112788550321163846120882933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75192366880775897413921955 112788550321163846120882933)
        ·
          refine ⟨10573926592609110573832775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112788550321163846120882933 10573926592609110573832775)
          ·
            refine ⟨15860889888913665860749163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10573926592609110573832775 15860889888913665860749163)
            ·
              refine ⟨23791334833370498791123745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15860889888913665860749163 23791334833370498791123745)
              ·
                refine ⟨17843501125027874093342809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23791334833370498791123745 17843501125027874093342809)
                ·
                  refine ⟨13382625843770905570007107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17843501125027874093342809 13382625843770905570007107)
                  ·
                    refine ⟨20073938765656358355010661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13382625843770905570007107 20073938765656358355010661)
                    ·
                      refine ⟨3763863518560567191564499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20073938765656358355010661 3763863518560567191564499)
                      ·
                        rfl

theorem cell23_7330098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4].length) (baseStart_7330098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330098 prefixEnd_7330098 := by exact prefixLift 7330098
  have htrace : WordTrace (prefixWord ++ tailWord_7330098) baseStart_7330098 baseEnd_7330098 := by
    simpa [prefixWord, tailWord_7330098, baseEnd_7330098] using wordTrace_append hprefix tailTrace_7330098
  have hstable : (prefixWord ++ tailWord_7330098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330098).length < 2 ^ (prefixWord ++ tailWord_7330098).sum := by decide
  have hdescent : baseEnd_7330098 < baseStart_7330098 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330104 : List Nat := [2, 1, 2, 1, 3, 1, 4, 1, 8]
def baseStart_7330104 : Nat := 118140960795 + 7330104 * 2 ^ 59
def prefixEnd_7330104 : Nat := 4983230072969 + 3 ^ 40 * 7330104 * 2
def baseEnd_7330104 : Nat := 418207399938277129787719

theorem tailTrace_7330104 : CollatzResearch.WordTrace tailWord_7330104 prefixEnd_7330104 418207399938277129787719 := by
  unfold tailWord_7330104
  simp only [CollatzResearch.WordTrace]
  refine ⟨133675428318146282470442683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178233904424195043293923577 133675428318146282470442683)
  ·
    refine ⟨200513142477219423705664025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133675428318146282470442683 200513142477219423705664025)
    ·
      refine ⟨150384856857914567779248019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200513142477219423705664025 150384856857914567779248019)
      ·
        refine ⟨225577285286871851668872029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150384856857914567779248019 225577285286871851668872029)
        ·
          refine ⟨84591481982576944375827011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225577285286871851668872029 84591481982576944375827011)
          ·
            refine ⟨126887222973865416563740517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84591481982576944375827011 126887222973865416563740517)
            ·
              refine ⟨23791354307599765605701347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126887222973865416563740517 23791354307599765605701347)
              ·
                refine ⟨35687031461399648408552021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23791354307599765605701347 35687031461399648408552021)
                ·
                  refine ⟨418207399938277129787719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35687031461399648408552021 418207399938277129787719)
                  ·
                    rfl

theorem cell23_7330104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 1, 8].length) (baseStart_7330104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330104 prefixEnd_7330104 := by exact prefixLift 7330104
  have htrace : WordTrace (prefixWord ++ tailWord_7330104) baseStart_7330104 baseEnd_7330104 := by
    simpa [prefixWord, tailWord_7330104, baseEnd_7330104] using wordTrace_append hprefix tailTrace_7330104
  have hstable : (prefixWord ++ tailWord_7330104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330104).length < 2 ^ (prefixWord ++ tailWord_7330104).sum := by decide
  have hdescent : baseEnd_7330104 < baseStart_7330104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330171 : List Nat := [1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 4]
def baseStart_7330171 : Nat := 118140960795 + 7330171 * 2 ^ 59
def prefixEnd_7330171 : Nat := 4983230072969 + 3 ^ 40 * 7330171 * 2
def baseEnd_7330171 : Nat := 3763901002648345405951663

theorem tailTrace_7330171 : CollatzResearch.WordTrace tailWord_7330171 prefixEnd_7330171 3763901002648345405951663 := by
  unfold tailWord_7330171
  simp only [CollatzResearch.WordTrace]
  refine ⟨267353300327049835383574367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178235533551366556922382911 267353300327049835383574367)
  ·
    refine ⟨401029950490574753075361551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267353300327049835383574367 401029950490574753075361551)
    ·
      refine ⟨601544925735862129613042327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401029950490574753075361551 601544925735862129613042327)
      ·
        refine ⟨902317388603793194419563491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601544925735862129613042327 902317388603793194419563491)
        ·
          refine ⟨1353476082905689791629345237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902317388603793194419563491 1353476082905689791629345237)
          ·
            refine ⟨31722095693102104491312779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 1353476082905689791629345237 31722095693102104491312779)
            ·
              refine ⟨47583143539653156736969169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31722095693102104491312779 47583143539653156736969169)
              ·
                refine ⟨35687357654739867552726877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47583143539653156736969169 35687357654739867552726877)
                ·
                  refine ⟨13382759120527450332272579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35687357654739867552726877 13382759120527450332272579)
                  ·
                    refine ⟨20074138680791175498408869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13382759120527450332272579 20074138680791175498408869)
                    ·
                      refine ⟨3763901002648345405951663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20074138680791175498408869 3763901002648345405951663)
                      ·
                        rfl

theorem cell23_7330171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 2, 3, 1, 4].length) (baseStart_7330171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330171 prefixEnd_7330171 := by exact prefixLift 7330171
  have htrace : WordTrace (prefixWord ++ tailWord_7330171) baseStart_7330171 baseEnd_7330171 := by
    simpa [prefixWord, tailWord_7330171, baseEnd_7330171] using wordTrace_append hprefix tailTrace_7330171
  have hstable : (prefixWord ++ tailWord_7330171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330171).length < 2 ^ (prefixWord ++ tailWord_7330171).sum := by decide
  have hdescent : baseEnd_7330171 < baseStart_7330171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330181 : List Nat := [1, 3, 1, 1, 3, 1, 1, 2, 6, 4]
def baseStart_7330181 : Nat := 118140960795 + 7330181 * 2 ^ 59
def prefixEnd_7330181 : Nat := 4983230072969 + 3 ^ 40 * 7330181 * 2
def baseEnd_7330181 : Nat := 1254635379151630122275539

theorem tailTrace_7330181 : CollatzResearch.WordTrace tailWord_7330181 prefixEnd_7330181 1254635379151630122275539 := by
  unfold tailWord_7330181
  simp only [CollatzResearch.WordTrace]
  refine ⟨267353665057013607091438397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178235776704675738060958931 267353665057013607091438397)
  ·
    refine ⟨100257624396380102659289399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267353665057013607091438397 100257624396380102659289399)
    ·
      refine ⟨150386436594570153988934099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100257624396380102659289399 150386436594570153988934099)
      ·
        refine ⟨225579654891855230983401149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150386436594570153988934099 225579654891855230983401149)
        ·
          refine ⟨84592370584445711618775431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225579654891855230983401149 84592370584445711618775431)
          ·
            refine ⟨126888555876668567428163147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84592370584445711618775431 126888555876668567428163147)
            ·
              refine ⟨190332833815002851142244721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126888555876668567428163147 190332833815002851142244721)
              ·
                refine ⟨142749625361252138356683541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190332833815002851142244721 142749625361252138356683541)
                ·
                  refine ⟨6691388688808693985469541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142749625361252138356683541 6691388688808693985469541)
                  ·
                    refine ⟨1254635379151630122275539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6691388688808693985469541 1254635379151630122275539)
                    ·
                      rfl

theorem cell23_7330181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 2, 6, 4].length) (baseStart_7330181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330181 prefixEnd_7330181 := by exact prefixLift 7330181
  have htrace : WordTrace (prefixWord ++ tailWord_7330181) baseStart_7330181 baseEnd_7330181 := by
    simpa [prefixWord, tailWord_7330181, baseEnd_7330181] using wordTrace_append hprefix tailTrace_7330181
  have hstable : (prefixWord ++ tailWord_7330181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330181).length < 2 ^ (prefixWord ++ tailWord_7330181).sum := by decide
  have hdescent : baseEnd_7330181 < baseStart_7330181 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330201 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 4]
def baseStart_7330201 : Nat := 118140960795 + 7330201 * 2 ^ 59
def prefixEnd_7330201 : Nat := 4983230072969 + 3 ^ 40 * 7330201 * 2
def baseEnd_7330201 : Nat := 3763916407067980288576525

theorem tailTrace_7330201 : CollatzResearch.WordTrace tailWord_7330201 prefixEnd_7330201 3763916407067980288576525 := by
  unfold tailWord_7330201
  simp only [CollatzResearch.WordTrace]
  refine ⟨267354394516941150507166457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178236263011294100338110971 267354394516941150507166457)
  ·
    refine ⟨200515795887705862880374843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267354394516941150507166457 200515795887705862880374843)
    ·
      refine ⟨300773693831558794320562265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200515795887705862880374843 300773693831558794320562265)
      ·
        refine ⟨225580270373669095740421699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300773693831558794320562265 225580270373669095740421699)
        ·
          refine ⟨338370405560503643610632549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225580270373669095740421699 338370405560503643610632549)
          ·
            refine ⟨63444451042594433176993603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338370405560503643610632549 63444451042594433176993603)
            ·
              refine ⟨95166676563891649765490405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63444451042594433176993603 95166676563891649765490405)
              ·
                refine ⟨17843751855729684331029451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95166676563891649765490405 17843751855729684331029451)
                ·
                  refine ⟨26765627783594526496544177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17843751855729684331029451 26765627783594526496544177)
                  ·
                    refine ⟨20074220837695894872408133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26765627783594526496544177 20074220837695894872408133)
                    ·
                      refine ⟨3763916407067980288576525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20074220837695894872408133 3763916407067980288576525)
                      ·
                        rfl

theorem cell23_7330201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_7330201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330201 prefixEnd_7330201 := by exact prefixLift 7330201
  have htrace : WordTrace (prefixWord ++ tailWord_7330201) baseStart_7330201 baseEnd_7330201 := by
    simpa [prefixWord, tailWord_7330201, baseEnd_7330201] using wordTrace_append hprefix tailTrace_7330201
  have hstable : (prefixWord ++ tailWord_7330201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330201).length < 2 ^ (prefixWord ++ tailWord_7330201).sum := by decide
  have hdescent : baseEnd_7330201 < baseStart_7330201 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330205 : List Nat := [1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 4]
def baseStart_7330205 : Nat := 118140960795 + 7330205 * 2 ^ 59
def prefixEnd_7330205 : Nat := 4983230072969 + 3 ^ 40 * 7330205 * 2
def baseEnd_7330205 : Nat := 3763918460990598272926507

theorem tailTrace_7330205 : CollatzResearch.WordTrace tailWord_7330205 prefixEnd_7330205 3763918460990598272926507 := by
  unfold tailWord_7330205
  simp only [CollatzResearch.WordTrace]
  refine ⟨267354540408926659190312069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178236360272617772793541379 267354540408926659190312069)
  ·
    refine ⟨50128976326673748598183513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267354540408926659190312069 50128976326673748598183513)
    ·
      refine ⟨37596732245005311448637635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50128976326673748598183513 37596732245005311448637635)
      ·
        refine ⟨56395098367507967172956453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37596732245005311448637635 56395098367507967172956453)
        ·
          refine ⟨10574080943907743844929335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56395098367507967172956453 10574080943907743844929335)
          ·
            refine ⟨15861121415861615767394003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10574080943907743844929335 15861121415861615767394003)
            ·
              refine ⟨23791682123792423651091005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15861121415861615767394003 23791682123792423651091005)
              ·
                refine ⟨8921880796422158869159127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23791682123792423651091005 8921880796422158869159127)
                ·
                  refine ⟨13382821194633238303738691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8921880796422158869159127 13382821194633238303738691)
                  ·
                    refine ⟨20074231791949857455608037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13382821194633238303738691 20074231791949857455608037)
                    ·
                      refine ⟨3763918460990598272926507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20074231791949857455608037 3763918460990598272926507)
                      ·
                        rfl

theorem cell23_7330205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_7330205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330205 prefixEnd_7330205 := by exact prefixLift 7330205
  have htrace : WordTrace (prefixWord ++ tailWord_7330205) baseStart_7330205 baseEnd_7330205 := by
    simpa [prefixWord, tailWord_7330205, baseEnd_7330205] using wordTrace_append hprefix tailTrace_7330205
  have hstable : (prefixWord ++ tailWord_7330205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330205).length < 2 ^ (prefixWord ++ tailWord_7330205).sum := by decide
  have hdescent : baseEnd_7330205 < baseStart_7330205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330215 : List Nat := [1, 1, 6, 1, 1, 2, 3, 2, 2, 4]
def baseStart_7330215 : Nat := 118140960795 + 7330215 * 2 ^ 59
def prefixEnd_7330215 : Nat := 4983230072969 + 3 ^ 40 * 7330215 * 2
def baseEnd_7330215 : Nat := 1254641198599047744600487

theorem tailTrace_7330215 : CollatzResearch.WordTrace tailWord_7330215 prefixEnd_7330215 1254641198599047744600487 := by
  unfold tailWord_7330215
  simp only [CollatzResearch.WordTrace]
  refine ⟨267354905138890430898176099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178236603425926953932117399 267354905138890430898176099)
  ·
    refine ⟨401032357708335646347264149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267354905138890430898176099 401032357708335646347264149)
    ·
      refine ⟨18798391767578233422528007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 401032357708335646347264149 18798391767578233422528007)
      ·
        refine ⟨28197587651367350133792011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18798391767578233422528007 28197587651367350133792011)
        ·
          refine ⟨42296381477051025200688017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28197587651367350133792011 42296381477051025200688017)
          ·
            refine ⟨31722286107788268900516013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42296381477051025200688017 31722286107788268900516013)
            ·
              refine ⟨11895857290420600837693505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31722286107788268900516013 11895857290420600837693505)
              ·
                refine ⟨8921892967815450628270129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11895857290420600837693505 8921892967815450628270129)
                ·
                  refine ⟨6691419725861587971202597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8921892967815450628270129 6691419725861587971202597)
                  ·
                    refine ⟨1254641198599047744600487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6691419725861587971202597 1254641198599047744600487)
                    ·
                      rfl

theorem cell23_7330215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_7330215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330215 prefixEnd_7330215 := by exact prefixLift 7330215
  have htrace : WordTrace (prefixWord ++ tailWord_7330215) baseStart_7330215 baseEnd_7330215 := by
    simpa [prefixWord, tailWord_7330215, baseEnd_7330215] using wordTrace_append hprefix tailTrace_7330215
  have hstable : (prefixWord ++ tailWord_7330215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330215).length < 2 ^ (prefixWord ++ tailWord_7330215).sum := by decide
  have hdescent : baseEnd_7330215 < baseStart_7330215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330265 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 1, 3, 2]
def baseStart_7330265 : Nat := 118140960795 + 7330265 * 2 ^ 59
def prefixEnd_7330265 : Nat := 4983230072969 + 3 ^ 40 * 7330265 * 2
def baseEnd_7330265 : Nat := 3763949269829868038176231

theorem tailTrace_7330265 : CollatzResearch.WordTrace tailWord_7330265 prefixEnd_7330265 3763949269829868038176231 := by
  unfold tailWord_7330265
  simp only [CollatzResearch.WordTrace]
  refine ⟨267356728788709289437496249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178237819192472859624997499 267356728788709289437496249)
  ·
    refine ⟨200517546591531967078122187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267356728788709289437496249 200517546591531967078122187)
    ·
      refine ⟨300776319887297950617183281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200517546591531967078122187 300776319887297950617183281)
      ·
        refine ⟨225582239915473462962887461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300776319887297950617183281 225582239915473462962887461)
        ·
          refine ⟨42296669984151274305541399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225582239915473462962887461 42296669984151274305541399)
          ·
            refine ⟨63445004976226911458312099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42296669984151274305541399 63445004976226911458312099)
            ·
              refine ⟨95167507464340367187468149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63445004976226911458312099 95167507464340367187468149)
              ·
                refine ⟨8921953824781909423825139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95167507464340367187468149 8921953824781909423825139)
                ·
                  refine ⟨13382930737172864135737709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8921953824781909423825139 13382930737172864135737709)
                  ·
                    refine ⟨5018599026439824050901641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13382930737172864135737709 5018599026439824050901641)
                    ·
                      refine ⟨3763949269829868038176231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5018599026439824050901641 3763949269829868038176231)
                      ·
                        rfl

theorem cell23_7330265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 1, 3, 2].length) (baseStart_7330265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330265 prefixEnd_7330265 := by exact prefixLift 7330265
  have htrace : WordTrace (prefixWord ++ tailWord_7330265) baseStart_7330265 baseEnd_7330265 := by
    simpa [prefixWord, tailWord_7330265, baseEnd_7330265] using wordTrace_append hprefix tailTrace_7330265
  have hstable : (prefixWord ++ tailWord_7330265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330265).length < 2 ^ (prefixWord ++ tailWord_7330265).sum := by decide
  have hdescent : baseEnd_7330265 < baseStart_7330265 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330291 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 4]
def baseStart_7330291 : Nat := 118140960795 + 7330291 * 2 ^ 59
def prefixEnd_7330291 : Nat := 4983230072969 + 3 ^ 40 * 7330291 * 2
def baseEnd_7330291 : Nat := 3763962620326884936451111

theorem tailTrace_7330291 : CollatzResearch.WordTrace tailWord_7330291 prefixEnd_7330291 3763962620326884936451111 := by
  unfold tailWord_7330291
  simp only [CollatzResearch.WordTrace]
  refine ⟨267357677086615095877942727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178238451391076730585295151 267357677086615095877942727)
  ·
    refine ⟨401036515629922643816914091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267357677086615095877942727 401036515629922643816914091)
    ·
      refine ⟨601554773444883965725371137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401036515629922643816914091 601554773444883965725371137)
      ·
        refine ⟨451166080083662974294028353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601554773444883965725371137 451166080083662974294028353)
        ·
          refine ⟨338374560062747230720521265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451166080083662974294028353 338374560062747230720521265)
          ·
            refine ⟨253780920047060423040390949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338374560062747230720521265 253780920047060423040390949)
            ·
              refine ⟨47583922508823829320073303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253780920047060423040390949 47583922508823829320073303)
              ·
                refine ⟨71375883763235743980109955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47583922508823829320073303 71375883763235743980109955)
                ·
                  refine ⟨107063825644853615970164933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71375883763235743980109955 107063825644853615970164933)
                  ·
                    refine ⟨20074467308410052994405925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107063825644853615970164933 20074467308410052994405925)
                    ·
                      refine ⟨3763962620326884936451111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20074467308410052994405925 3763962620326884936451111)
                      ·
                        rfl

theorem cell23_7330291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 1, 4, 4].length) (baseStart_7330291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330291 prefixEnd_7330291 := by exact prefixLift 7330291
  have htrace : WordTrace (prefixWord ++ tailWord_7330291) baseStart_7330291 baseEnd_7330291 := by
    simpa [prefixWord, tailWord_7330291, baseEnd_7330291] using wordTrace_append hprefix tailTrace_7330291
  have hstable : (prefixWord ++ tailWord_7330291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330291).length < 2 ^ (prefixWord ++ tailWord_7330291).sum := by decide
  have hdescent : baseEnd_7330291 < baseStart_7330291 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330301 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 9]
def baseStart_7330301 : Nat := 118140960795 + 7330301 * 2 ^ 59
def prefixEnd_7330301 : Nat := 4983230072969 + 3 ^ 40 * 7330301 * 2
def baseEnd_7330301 : Nat := 418218639459269988591785

theorem tailTrace_7330301 : CollatzResearch.WordTrace tailWord_7330301 prefixEnd_7330301 418218639459269988591785 := by
  unfold tailWord_7330301
  simp only [CollatzResearch.WordTrace]
  refine ⟨267358041816578867585806757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178238694544385911723871171 267358041816578867585806757)
  ·
    refine ⟨50129632840608537672338767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267358041816578867585806757 50129632840608537672338767)
    ·
      refine ⟨75194449260912806508508151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50129632840608537672338767 75194449260912806508508151)
      ·
        refine ⟨112791673891369209762762227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75194449260912806508508151 112791673891369209762762227)
        ·
          refine ⟨169187510837053814644143341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112791673891369209762762227 169187510837053814644143341)
          ·
            refine ⟨63445316563895180491553753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169187510837053814644143341 63445316563895180491553753)
            ·
              refine ⟨47583987422921385368665315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63445316563895180491553753 47583987422921385368665315)
              ·
                refine ⟨71375981134382078052997973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47583987422921385368665315 71375981134382078052997973)
                ·
                  refine ⟨418218639459269988591785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71375981134382078052997973 418218639459269988591785)
                  ·
                    rfl

theorem cell23_7330301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_7330301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330301 prefixEnd_7330301 := by exact prefixLift 7330301
  have htrace : WordTrace (prefixWord ++ tailWord_7330301) baseStart_7330301 baseEnd_7330301 := by
    simpa [prefixWord, tailWord_7330301, baseEnd_7330301] using wordTrace_append hprefix tailTrace_7330301
  have hstable : (prefixWord ++ tailWord_7330301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330301).length < 2 ^ (prefixWord ++ tailWord_7330301).sum := by decide
  have hdescent : baseEnd_7330301 < baseStart_7330301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330365 : List Nat := [1, 4, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_7330365 : Nat := 118140960795 + 7330365 * 2 ^ 59
def prefixEnd_7330365 : Nat := 4983230072969 + 3 ^ 40 * 7330365 * 2
def baseEnd_7330365 : Nat := 1254666872631772548975257

theorem tailTrace_7330365 : CollatzResearch.WordTrace tailWord_7330365 prefixEnd_7330365 1254666872631772548975257 := by
  unfold tailWord_7330365
  simp only [CollatzResearch.WordTrace]
  refine ⟨267360376088347006516136549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178240250725564671010757699 267360376088347006516136549)
  ·
    refine ⟨50130070516565063721775603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267360376088347006516136549 50130070516565063721775603)
    ·
      refine ⟨75195105774847595582663405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50130070516565063721775603 75195105774847595582663405)
      ·
        refine ⟨28198164665567848343498777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75195105774847595582663405 28198164665567848343498777)
        ·
          refine ⟨21148623499175886257624083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28198164665567848343498777 21148623499175886257624083)
          ·
            refine ⟨31722935248763829386436125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21148623499175886257624083 31722935248763829386436125)
            ·
              refine ⟨11896100718286436019913547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31722935248763829386436125 11896100718286436019913547)
              ·
                refine ⟨17844151077429654029870321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11896100718286436019913547 17844151077429654029870321)
                ·
                  refine ⟨13383113308072240522402741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17844151077429654029870321 13383113308072240522402741)
                  ·
                    refine ⟨1254666872631772548975257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13383113308072240522402741 1254666872631772548975257)
                    ·
                      rfl

theorem cell23_7330365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_7330365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330365 prefixEnd_7330365 := by exact prefixLift 7330365
  have htrace : WordTrace (prefixWord ++ tailWord_7330365) baseStart_7330365 baseEnd_7330365 := by
    simpa [prefixWord, tailWord_7330365, baseEnd_7330365] using wordTrace_append hprefix tailTrace_7330365
  have hstable : (prefixWord ++ tailWord_7330365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330365).length < 2 ^ (prefixWord ++ tailWord_7330365).sum := by decide
  have hdescent : baseEnd_7330365 < baseStart_7330365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330385 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 2, 4, 2]
def baseStart_7330385 : Nat := 118140960795 + 7330385 * 2 ^ 59
def prefixEnd_7330385 : Nat := 4983230072969 + 3 ^ 40 * 7330385 * 2
def baseEnd_7330385 : Nat := 3764010887508407568675679

theorem tailTrace_7330385 : CollatzResearch.WordTrace tailWord_7330385 prefixEnd_7330385 3764010887508407568675679 := by
  unfold tailWord_7330385
  simp only [CollatzResearch.WordTrace]
  refine ⟨267361105548274549931864609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178240737032183033287909739 267361105548274549931864609)
  ·
    refine ⟨200520829161205912448898457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267361105548274549931864609 200520829161205912448898457)
    ·
      refine ⟨150390621870904434336673843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200520829161205912448898457 150390621870904434336673843)
      ·
        refine ⟨225585932806356651505010765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150390621870904434336673843 225585932806356651505010765)
        ·
          refine ⟨84594724802383744314379037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225585932806356651505010765 84594724802383744314379037)
          ·
            refine ⟨31723021800893904117892139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84594724802383744314379037 31723021800893904117892139)
            ·
              refine ⟨47584532701340856176838209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31723021800893904117892139 47584532701340856176838209)
              ·
                refine ⟨35688399526005642132628657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47584532701340856176838209 35688399526005642132628657)
                ·
                  refine ⟨26766299644504231599471493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35688399526005642132628657 26766299644504231599471493)
                  ·
                    refine ⟨5018681183344543424900905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26766299644504231599471493 5018681183344543424900905)
                    ·
                      refine ⟨3764010887508407568675679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5018681183344543424900905 3764010887508407568675679)
                      ·
                        rfl

theorem cell23_7330385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 2, 4, 2].length) (baseStart_7330385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330385 prefixEnd_7330385 := by exact prefixLift 7330385
  have htrace : WordTrace (prefixWord ++ tailWord_7330385) baseStart_7330385 baseEnd_7330385 := by
    simpa [prefixWord, tailWord_7330385, baseEnd_7330385] using wordTrace_append hprefix tailTrace_7330385
  have hstable : (prefixWord ++ tailWord_7330385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330385).length < 2 ^ (prefixWord ++ tailWord_7330385).sum := by decide
  have hdescent : baseEnd_7330385 < baseStart_7330385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330435 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 3]
def baseStart_7330435 : Nat := 118140960795 + 7330435 * 2 ^ 59
def prefixEnd_7330435 : Nat := 4983230072969 + 3 ^ 40 * 7330435 * 2
def baseEnd_7330435 : Nat := 3764036561541132373050449

theorem tailTrace_7330435 : CollatzResearch.WordTrace tailWord_7330435 prefixEnd_7330435 3764036561541132373050449 := by
  unfold tailWord_7330435
  simp only [CollatzResearch.WordTrace]
  refine ⟨267362929198093408471184759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178241952798728938980789839 267362929198093408471184759)
  ·
    refine ⟨401044393797140112706777139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267362929198093408471184759 401044393797140112706777139)
    ·
      refine ⟨601566590695710169060165709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401044393797140112706777139 601566590695710169060165709)
      ·
        refine ⟨225587471510891313397562141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601566590695710169060165709 225587471510891313397562141)
        ·
          refine ⟨84595301816584242524085803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225587471510891313397562141 84595301816584242524085803)
          ·
            refine ⟨126892952724876363786128705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84595301816584242524085803 126892952724876363786128705)
            ·
              refine ⟨95169714543657272839596529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126892952724876363786128705 95169714543657272839596529)
              ·
                refine ⟨71377285907742954629697397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95169714543657272839596529 71377285907742954629697397)
                ·
                  refine ⟨6691620553850901996534131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 71377285907742954629697397 6691620553850901996534131)
                  ·
                    refine ⟨10037430830776352994801197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6691620553850901996534131 10037430830776352994801197)
                    ·
                      refine ⟨3764036561541132373050449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10037430830776352994801197 3764036561541132373050449)
                      ·
                        rfl

theorem cell23_7330435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 1, 3].length) (baseStart_7330435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330435 prefixEnd_7330435 := by exact prefixLift 7330435
  have htrace : WordTrace (prefixWord ++ tailWord_7330435) baseStart_7330435 baseEnd_7330435 := by
    simpa [prefixWord, tailWord_7330435, baseEnd_7330435] using wordTrace_append hprefix tailTrace_7330435
  have hstable : (prefixWord ++ tailWord_7330435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330435).length < 2 ^ (prefixWord ++ tailWord_7330435).sum := by decide
  have hdescent : baseEnd_7330435 < baseStart_7330435 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330485 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 3, 6]
def baseStart_7330485 : Nat := 118140960795 + 7330485 * 2 ^ 59
def prefixEnd_7330485 : Nat := 4983230072969 + 3 ^ 40 * 7330485 * 2
def baseEnd_7330485 : Nat := 1254687411857952392475073

theorem tailTrace_7330485 : CollatzResearch.WordTrace tailWord_7330485 prefixEnd_7330485 1254687411857952392475073 := by
  unfold tailWord_7330485
  simp only [CollatzResearch.WordTrace]
  refine ⟨267364752847912267010504909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178243168565274844673669939 267364752847912267010504909)
  ·
    refine ⟨100261782317967100128939341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267364752847912267010504909 100261782317967100128939341)
    ·
      refine ⟨37598168369237662548352253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100261782317967100128939341 37598168369237662548352253)
      ·
        refine ⟨14099313138464123455632095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37598168369237662548352253 14099313138464123455632095)
        ·
          refine ⟨21148969707696185183448143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14099313138464123455632095 21148969707696185183448143)
          ·
            refine ⟨31723454561544277775172215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21148969707696185183448143 31723454561544277775172215)
            ·
              refine ⟨47585181842316416662758323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31723454561544277775172215 47585181842316416662758323)
              ·
                refine ⟨71377772763474624994137485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47585181842316416662758323 71377772763474624994137485)
                ·
                  refine ⟨26766664786302984372801557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71377772763474624994137485 26766664786302984372801557)
                  ·
                    refine ⟨1254687411857952392475073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26766664786302984372801557 1254687411857952392475073)
                    ·
                      rfl

theorem cell23_7330485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_7330485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330485 prefixEnd_7330485 := by exact prefixLift 7330485
  have htrace : WordTrace (prefixWord ++ tailWord_7330485) baseStart_7330485 baseEnd_7330485 := by
    simpa [prefixWord, tailWord_7330485, baseEnd_7330485] using wordTrace_append hprefix tailTrace_7330485
  have hstable : (prefixWord ++ tailWord_7330485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330485).length < 2 ^ (prefixWord ++ tailWord_7330485).sum := by decide
  have hdescent : baseEnd_7330485 < baseStart_7330485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330495 : List Nat := [1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 5]
def baseStart_7330495 : Nat := 118140960795 + 7330495 * 2 ^ 59
def prefixEnd_7330495 : Nat := 4983230072969 + 3 ^ 40 * 7330495 * 2
def baseEnd_7330495 : Nat := 3764067370380402138300173

theorem tailTrace_7330495 : CollatzResearch.WordTrace tailWord_7330495 prefixEnd_7330495 3764067370380402138300173 := by
  unfold tailWord_7330495
  simp only [CollatzResearch.WordTrace]
  refine ⟨267365117577876038718368939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178243411718584025812245959 267365117577876038718368939)
  ·
    refine ⟨401047676366814058077553409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267365117577876038718368939 401047676366814058077553409)
    ·
      refine ⟨300785757275110543558165057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401047676366814058077553409 300785757275110543558165057)
      ·
        refine ⟨225589317956332907668623793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300785757275110543558165057 225589317956332907668623793)
        ·
          refine ⟨169191988467249680751467845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225589317956332907668623793 169191988467249680751467845)
          ·
            refine ⟨31723497837609315140900221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169191988467249680751467845 31723497837609315140900221)
            ·
              refine ⟨11896311689103493177837583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31723497837609315140900221 11896311689103493177837583)
              ·
                refine ⟨17844467533655239766756375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11896311689103493177837583 17844467533655239766756375)
                ·
                  refine ⟨26766701300482859650134563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17844467533655239766756375 26766701300482859650134563)
                  ·
                    refine ⟨40150051950724289475201845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26766701300482859650134563 40150051950724289475201845)
                    ·
                      refine ⟨3764067370380402138300173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40150051950724289475201845 3764067370380402138300173)
                      ·
                        rfl

theorem cell23_7330495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 5].length) (baseStart_7330495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330495 prefixEnd_7330495 := by exact prefixLift 7330495
  have htrace : WordTrace (prefixWord ++ tailWord_7330495) baseStart_7330495 baseEnd_7330495 := by
    simpa [prefixWord, tailWord_7330495, baseEnd_7330495] using wordTrace_append hprefix tailTrace_7330495
  have hstable : (prefixWord ++ tailWord_7330495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330495).length < 2 ^ (prefixWord ++ tailWord_7330495).sum := by decide
  have hdescent : baseEnd_7330495 < baseStart_7330495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330528 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 4, 7]
def baseStart_7330528 : Nat := 118140960795 + 7330528 * 2 ^ 59
def prefixEnd_7330528 : Nat := 4983230072969 + 3 ^ 40 * 7330528 * 2
def baseEnd_7330528 : Nat := 1254694771747333503062507

theorem tailTrace_7330528 : CollatzResearch.WordTrace tailWord_7330528 prefixEnd_7330528 1254694771747333503062507 := by
  unfold tailWord_7330528
  simp only [CollatzResearch.WordTrace]
  refine ⟨133683160593378242677160119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178244214124504323569546825 133683160593378242677160119)
  ·
    refine ⟨200524740890067364015740179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133683160593378242677160119 200524740890067364015740179)
    ·
      refine ⟨300787111335101046023610269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200524740890067364015740179 300787111335101046023610269)
      ·
        refine ⟨112795166750662892258853851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300787111335101046023610269 112795166750662892258853851)
        ·
          refine ⟨169192750125994338388280777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112795166750662892258853851 169192750125994338388280777)
          ·
            refine ⟨126894562594495753791210583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169192750125994338388280777 126894562594495753791210583)
            ·
              refine ⟨190341843891743630686815875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126894562594495753791210583 190341843891743630686815875)
              ·
                refine ⟨285512765837615446030223813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190341843891743630686815875 285512765837615446030223813)
                ·
                  refine ⟨53533643594552896130666965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285512765837615446030223813 53533643594552896130666965)
                  ·
                    refine ⟨1254694771747333503062507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 53533643594552896130666965 1254694771747333503062507)
                    ·
                      rfl

theorem cell23_7330528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 4, 7].length) (baseStart_7330528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330528 prefixEnd_7330528 := by exact prefixLift 7330528
  have htrace : WordTrace (prefixWord ++ tailWord_7330528) baseStart_7330528 baseEnd_7330528 := by
    simpa [prefixWord, tailWord_7330528, baseEnd_7330528] using wordTrace_append hprefix tailTrace_7330528
  have hstable : (prefixWord ++ tailWord_7330528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330528).length < 2 ^ (prefixWord ++ tailWord_7330528).sum := by decide
  have hdescent : baseEnd_7330528 < baseStart_7330528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330542 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3]
def baseStart_7330542 : Nat := 118140960795 + 7330542 * 2 ^ 59
def prefixEnd_7330542 : Nat := 4983230072969 + 3 ^ 40 * 7330542 * 2
def baseEnd_7330542 : Nat := 3764091503971163454412457

theorem tailTrace_7330542 : CollatzResearch.WordTrace tailWord_7330542 prefixEnd_7330542 3764091503971163454412457 := by
  unfold tailWord_7330542
  simp only [CollatzResearch.WordTrace]
  refine ⟨33420853976088220718166235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178244554539137177163553253 33420853976088220718166235)
  ·
    refine ⟨50131280964132331077249353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33420853976088220718166235 50131280964132331077249353)
    ·
      refine ⟨37598460723099248307937015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50131280964132331077249353 37598460723099248307937015)
      ·
        refine ⟨56397691084648872461905523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37598460723099248307937015 56397691084648872461905523)
        ·
          refine ⟨84596536626973308692858285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56397691084648872461905523 84596536626973308692858285)
          ·
            refine ⟨31723701235114990759821857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84596536626973308692858285 31723701235114990759821857)
            ·
              refine ⟨23792775926336243069866393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31723701235114990759821857 23792775926336243069866393)
              ·
                refine ⟨17844581944752182302399795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23792775926336243069866393 17844581944752182302399795)
                ·
                  refine ⟨26766872917128273453599693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17844581944752182302399795 26766872917128273453599693)
                  ·
                    refine ⟨10037577343923102545099885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26766872917128273453599693 10037577343923102545099885)
                    ·
                      refine ⟨3764091503971163454412457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10037577343923102545099885 3764091503971163454412457)
                      ·
                        rfl

theorem cell23_7330542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 1, 3, 3].length) (baseStart_7330542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330542 prefixEnd_7330542 := by exact prefixLift 7330542
  have htrace : WordTrace (prefixWord ++ tailWord_7330542) baseStart_7330542 baseEnd_7330542 := by
    simpa [prefixWord, tailWord_7330542, baseEnd_7330542] using wordTrace_append hprefix tailTrace_7330542
  have hstable : (prefixWord ++ tailWord_7330542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330542).length < 2 ^ (prefixWord ++ tailWord_7330542).sum := by decide
  have hdescent : baseEnd_7330542 < baseStart_7330542 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330546 : List Nat := [3, 2, 1, 3, 1, 4, 2, 1, 1, 2, 3]
def baseStart_7330546 : Nat := 118140960795 + 7330546 * 2 ^ 59
def prefixEnd_7330546 : Nat := 4983230072969 + 3 ^ 40 * 7330546 * 2
def baseEnd_7330546 : Nat := 3764093557893781438762439

theorem tailTrace_7330546 : CollatzResearch.WordTrace tailWord_7330546 prefixEnd_7330546 3764093557893781438762439 := by
  unfold tailWord_7330546
  simp only [CollatzResearch.WordTrace]
  refine ⟨66841744425172818607118873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178244651800460849618983661 66841744425172818607118873)
  ·
    refine ⟨50131308318879613955339155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66841744425172818607118873 50131308318879613955339155)
    ·
      refine ⟨75196962478319420933008733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50131308318879613955339155 75196962478319420933008733)
      ·
        refine ⟨28198860929369782849878275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75196962478319420933008733 28198860929369782849878275)
        ·
          refine ⟨42298291394054674274817413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28198860929369782849878275 42298291394054674274817413)
          ·
            refine ⟨7930929636385251426528265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42298291394054674274817413 7930929636385251426528265)
            ·
              refine ⟨5948197227288938569896199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7930929636385251426528265 5948197227288938569896199)
              ·
                refine ⟨8922295840933407854844299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5948197227288938569896199 8922295840933407854844299)
                ·
                  refine ⟨13383443761400111782266449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8922295840933407854844299 13383443761400111782266449)
                  ·
                    refine ⟨10037582821050083836699837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13383443761400111782266449 10037582821050083836699837)
                    ·
                      refine ⟨3764093557893781438762439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10037582821050083836699837 3764093557893781438762439)
                      ·
                        rfl

theorem cell23_7330546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 1, 1, 2, 3].length) (baseStart_7330546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330546 prefixEnd_7330546 := by exact prefixLift 7330546
  have htrace : WordTrace (prefixWord ++ tailWord_7330546) baseStart_7330546 baseEnd_7330546 := by
    simpa [prefixWord, tailWord_7330546, baseEnd_7330546] using wordTrace_append hprefix tailTrace_7330546
  have hstable : (prefixWord ++ tailWord_7330546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330546).length < 2 ^ (prefixWord ++ tailWord_7330546).sum := by decide
  have hdescent : baseEnd_7330546 < baseStart_7330546 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330549 : List Nat := [1, 3, 6, 1, 1, 1, 10]
def baseStart_7330549 : Nat := 118140960795 + 7330549 * 2 ^ 59
def prefixEnd_7330549 : Nat := 4983230072969 + 3 ^ 40 * 7330549 * 2
def baseEnd_7330549 : Nat := 46470309855996850950925

theorem tailTrace_7330549 : CollatzResearch.WordTrace tailWord_7330549 prefixEnd_7330549 46470309855996850950925 := by
  unfold tailWord_7330549
  simp only [CollatzResearch.WordTrace]
  refine ⟨267367087119680405940834701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178244724746453603960556467 267367087119680405940834701)
  ·
    refine ⟨100262657669880152227813013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267367087119680405940834701 100262657669880152227813013)
    ·
      refine ⟨4699812078275632135678735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100262657669880152227813013 4699812078275632135678735)
      ·
        refine ⟨7049718117413448203518103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4699812078275632135678735 7049718117413448203518103)
        ·
          refine ⟨10574577176120172305277155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7049718117413448203518103 10574577176120172305277155)
          ·
            refine ⟨15861865764180258457915733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10574577176120172305277155 15861865764180258457915733)
            ·
              refine ⟨46470309855996850950925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15861865764180258457915733 46470309855996850950925)
              ·
                rfl

theorem cell23_7330549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 10].length) (baseStart_7330549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330549 prefixEnd_7330549 := by exact prefixLift 7330549
  have htrace : WordTrace (prefixWord ++ tailWord_7330549) baseStart_7330549 baseEnd_7330549 := by
    simpa [prefixWord, tailWord_7330549, baseEnd_7330549] using wordTrace_append hprefix tailTrace_7330549
  have hstable : (prefixWord ++ tailWord_7330549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330549).length < 2 ^ (prefixWord ++ tailWord_7330549).sum := by decide
  have hdescent : baseEnd_7330549 < baseStart_7330549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330633 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 2, 2, 2]
def baseStart_7330633 : Nat := 118140960795 + 7330633 * 2 ^ 59
def prefixEnd_7330633 : Nat := 4983230072969 + 3 ^ 40 * 7330633 * 2
def baseEnd_7330633 : Nat := 3764138230710722598374539

theorem tailTrace_7330633 : CollatzResearch.WordTrace tailWord_7330633 prefixEnd_7330633 3764138230710722598374539 := by
  unfold tailWord_7330633
  simp only [CollatzResearch.WordTrace]
  refine ⟨267370150851376088286892553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178246767234250725524595035 267370150851376088286892553)
  ·
    refine ⟨200527613138532066215169415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267370150851376088286892553 200527613138532066215169415)
    ·
      refine ⟨300791419707798099322754123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200527613138532066215169415 300791419707798099322754123)
      ·
        refine ⟨451187129561697148984131185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300791419707798099322754123 451187129561697148984131185)
        ·
          refine ⟨338390347171272861738098389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451187129561697148984131185 338390347171272861738098389)
          ·
            refine ⟨7931023761826707696986681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 338390347171272861738098389 7931023761826707696986681)
            ·
              refine ⟨5948267821370030772740011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7931023761826707696986681 5948267821370030772740011)
              ·
                refine ⟨8922401732055046159110017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5948267821370030772740011 8922401732055046159110017)
                ·
                  refine ⟨6691801299041284619332513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8922401732055046159110017 6691801299041284619332513)
                  ·
                    refine ⟨5018850974280963464499385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6691801299041284619332513 5018850974280963464499385)
                    ·
                      refine ⟨3764138230710722598374539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5018850974280963464499385 3764138230710722598374539)
                      ·
                        rfl

theorem cell23_7330633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 2, 2, 2].length) (baseStart_7330633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330633 prefixEnd_7330633 := by exact prefixLift 7330633
  have htrace : WordTrace (prefixWord ++ tailWord_7330633) baseStart_7330633 baseEnd_7330633 := by
    simpa [prefixWord, tailWord_7330633, baseEnd_7330633] using wordTrace_append hprefix tailTrace_7330633
  have hstable : (prefixWord ++ tailWord_7330633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330633).length < 2 ^ (prefixWord ++ tailWord_7330633).sum := by decide
  have hdescent : baseEnd_7330633 < baseStart_7330633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330645 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 7]
def baseStart_7330645 : Nat := 118140960795 + 7330645 * 2 ^ 59
def prefixEnd_7330645 : Nat := 4983230072969 + 3 ^ 40 * 7330645 * 2
def baseEnd_7330645 : Nat := 3764144392478576551424483

theorem tailTrace_7330645 : CollatzResearch.WordTrace tailWord_7330645 prefixEnd_7330645 3764144392478576551424483 := by
  unfold tailWord_7330645
  simp only [CollatzResearch.WordTrace]
  refine ⟨267370588527332614336329389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178247059018221742890886259 267370588527332614336329389)
  ·
    refine ⟨100263970697749730376123521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267370588527332614336329389 100263970697749730376123521)
    ·
      refine ⟨75197978023312297782092641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100263970697749730376123521 75197978023312297782092641)
      ·
        refine ⟨56398483517484223336569481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75197978023312297782092641 56398483517484223336569481)
        ·
          refine ⟨42298862638113167502427111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56398483517484223336569481 42298862638113167502427111)
          ·
            refine ⟨63448293957169751253640667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42298862638113167502427111 63448293957169751253640667)
            ·
              refine ⟨95172440935754626880461001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63448293957169751253640667 95172440935754626880461001)
              ·
                refine ⟨71379330701815970160345751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95172440935754626880461001 71379330701815970160345751)
                ·
                  refine ⟨107068996052723955240518627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71379330701815970160345751 107068996052723955240518627)
                  ·
                    refine ⟨160603494079085932860777941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107068996052723955240518627 160603494079085932860777941)
                    ·
                      refine ⟨3764144392478576551424483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160603494079085932860777941 3764144392478576551424483)
                      ·
                        rfl

theorem cell23_7330645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_7330645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330645 prefixEnd_7330645 := by exact prefixLift 7330645
  have htrace : WordTrace (prefixWord ++ tailWord_7330645) baseStart_7330645 baseEnd_7330645 := by
    simpa [prefixWord, tailWord_7330645, baseEnd_7330645] using wordTrace_append hprefix tailTrace_7330645
  have hstable : (prefixWord ++ tailWord_7330645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330645).length < 2 ^ (prefixWord ++ tailWord_7330645).sum := by decide
  have hdescent : baseEnd_7330645 < baseStart_7330645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330672 : List Nat := [2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 4]
def baseStart_7330672 : Nat := 118140960795 + 7330672 * 2 ^ 59
def prefixEnd_7330672 : Nat := 4983230072969 + 3 ^ 40 * 7330672 * 2
def baseEnd_7330672 : Nat := 3764158256456247945786859

theorem tailTrace_7330672 : CollatzResearch.WordTrace tailWord_7330672 prefixEnd_7330672 3764158256456247945786859 := by
  unfold tailWord_7330672
  simp only [CollatzResearch.WordTrace]
  refine ⟨133685786649117398973781135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178247715532156531965041513 133685786649117398973781135)
  ·
    refine ⟨200528679973676098460671703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133685786649117398973781135 200528679973676098460671703)
    ·
      refine ⟨300793019960514147691007555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200528679973676098460671703 300793019960514147691007555)
      ·
        refine ⟨451189529940771221536511333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300793019960514147691007555 451189529940771221536511333)
        ·
          refine ⟨84598036863894604038095875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 451189529940771221536511333 84598036863894604038095875)
          ·
            refine ⟨126897055295841906057143813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84598036863894604038095875 126897055295841906057143813)
            ·
              refine ⟨23793197867970357385714465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126897055295841906057143813 23793197867970357385714465)
              ·
                refine ⟨17844898400977768039285849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23793197867970357385714465 17844898400977768039285849)
                ·
                  refine ⟨13383673800733326029464387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17844898400977768039285849 13383673800733326029464387)
                  ·
                    refine ⟨20075510701099989044196581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13383673800733326029464387 20075510701099989044196581)
                    ·
                      refine ⟨3764158256456247945786859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20075510701099989044196581 3764158256456247945786859)
                      ·
                        rfl

theorem cell23_7330672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 4].length) (baseStart_7330672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330672 prefixEnd_7330672 := by exact prefixLift 7330672
  have htrace : WordTrace (prefixWord ++ tailWord_7330672) baseStart_7330672 baseEnd_7330672 := by
    simpa [prefixWord, tailWord_7330672, baseEnd_7330672] using wordTrace_append hprefix tailTrace_7330672
  have hstable : (prefixWord ++ tailWord_7330672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330672).length < 2 ^ (prefixWord ++ tailWord_7330672).sum := by decide
  have hdescent : baseEnd_7330672 < baseStart_7330672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330682 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 3, 4]
def baseStart_7330682 : Nat := 118140960795 + 7330682 * 2 ^ 59
def prefixEnd_7330682 : Nat := 4983230072969 + 3 ^ 40 * 7330682 * 2
def baseEnd_7330682 : Nat := 1254721130420930968887271

theorem tailTrace_7330682 : CollatzResearch.WordTrace tailWord_7330682 prefixEnd_7330682 1254721130420930968887271 := by
  unfold tailWord_7330682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66842984507049642413856575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178247958685465713103617533 66842984507049642413856575)
  ·
    refine ⟨100264476760574463620784863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66842984507049642413856575 100264476760574463620784863)
    ·
      refine ⟨150396715140861695431177295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100264476760574463620784863 150396715140861695431177295)
      ·
        refine ⟨225595072711292543146765943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150396715140861695431177295 225595072711292543146765943)
        ·
          refine ⟨338392609066938814720148915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225595072711292543146765943 338392609066938814720148915)
          ·
            refine ⟨507588913600408222080223373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338392609066938814720148915 507588913600408222080223373)
            ·
              refine ⟨190345842600153083280083765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507588913600408222080223373 190345842600153083280083765)
              ·
                refine ⟨17844922743764351557507853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190345842600153083280083765 17844922743764351557507853)
                ·
                  refine ⟨6691846028911631834065445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17844922743764351557507853 6691846028911631834065445)
                  ·
                    refine ⟨1254721130420930968887271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6691846028911631834065445 1254721130420930968887271)
                    ·
                      rfl

theorem cell23_7330682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 3, 4].length) (baseStart_7330682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330682 prefixEnd_7330682 := by exact prefixLift 7330682
  have htrace : WordTrace (prefixWord ++ tailWord_7330682) baseStart_7330682 baseEnd_7330682 := by
    simpa [prefixWord, tailWord_7330682, baseEnd_7330682] using wordTrace_append hprefix tailTrace_7330682
  have hstable : (prefixWord ++ tailWord_7330682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330682).length < 2 ^ (prefixWord ++ tailWord_7330682).sum := by decide
  have hdescent : baseEnd_7330682 < baseStart_7330682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330692 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_7330692 : Nat := 118140960795 + 7330692 * 2 ^ 59
def prefixEnd_7330692 : Nat := 4983230072969 + 3 ^ 40 * 7330692 * 2
def baseEnd_7330692 : Nat := 3764168526069337867536767

theorem tailTrace_7330692 : CollatzResearch.WordTrace tailWord_7330692 prefixEnd_7330692 3764168526069337867536767 := by
  unfold tailWord_7330692
  simp only [CollatzResearch.WordTrace]
  refine ⟨133686151379081170681645165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178248201838774894242193553 133686151379081170681645165)
  ·
    refine ⟨50132306767155439005616937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133686151379081170681645165 50132306767155439005616937)
    ·
      refine ⟨37599230075366579254212703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50132306767155439005616937 37599230075366579254212703)
      ·
        refine ⟨56398845113049868881319055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37599230075366579254212703 56398845113049868881319055)
        ·
          refine ⟨84598267669574803321978583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56398845113049868881319055 84598267669574803321978583)
          ·
            refine ⟨126897401504362204982967875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84598267669574803321978583 126897401504362204982967875)
            ·
              refine ⟨190346102256543307474451813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126897401504362204982967875 190346102256543307474451813)
              ·
                refine ⟨35689894173101870151459715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 190346102256543307474451813 35689894173101870151459715)
                ·
                  refine ⟨53534841259652805227189573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35689894173101870151459715 53534841259652805227189573)
                  ·
                    refine ⟨10037782736184900980098045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53534841259652805227189573 10037782736184900980098045)
                    ·
                      refine ⟨3764168526069337867536767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10037782736184900980098045 3764168526069337867536767)
                      ·
                        rfl

theorem cell23_7330692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_7330692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330692 prefixEnd_7330692 := by exact prefixLift 7330692
  have htrace : WordTrace (prefixWord ++ tailWord_7330692) baseStart_7330692 baseEnd_7330692 := by
    simpa [prefixWord, tailWord_7330692, baseEnd_7330692] using wordTrace_append hprefix tailTrace_7330692
  have hstable : (prefixWord ++ tailWord_7330692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330692).length < 2 ^ (prefixWord ++ tailWord_7330692).sum := by decide
  have hdescent : baseEnd_7330692 < baseStart_7330692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330709 : List Nat := [1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 3]
def baseStart_7330709 : Nat := 118140960795 + 7330709 * 2 ^ 59
def prefixEnd_7330709 : Nat := 4983230072969 + 3 ^ 40 * 7330709 * 2
def baseEnd_7330709 : Nat := 3764177255240464301024189

theorem tailTrace_7330709 : CollatzResearch.WordTrace tailWord_7330709 prefixEnd_7330709 3764177255240464301024189 := by
  unfold tailWord_7330709
  simp only [CollatzResearch.WordTrace]
  refine ⟨267372922799100753266659181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178248615199400502177772787 267372922799100753266659181)
  ·
    refine ⟨100264846049662782474997193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267372922799100753266659181 100264846049662782474997193)
    ·
      refine ⟨75198634537247086856247895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100264846049662782474997193 75198634537247086856247895)
      ·
        refine ⟨112797951805870630284371843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75198634537247086856247895 112797951805870630284371843)
        ·
          refine ⟨169196927708805945426557765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112797951805870630284371843 169196927708805945426557765)
          ·
            refine ⟨31724423945401114767479581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169196927708805945426557765 31724423945401114767479581)
            ·
              refine ⟨11896658979525418037804843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31724423945401114767479581 11896658979525418037804843)
              ·
                refine ⟨17844988469288127056707265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11896658979525418037804843 17844988469288127056707265)
                ·
                  refine ⟨13383741351966095292530449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17844988469288127056707265 13383741351966095292530449)
                  ·
                    refine ⟨10037806013974571469397837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13383741351966095292530449 10037806013974571469397837)
                    ·
                      refine ⟨3764177255240464301024189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10037806013974571469397837 3764177255240464301024189)
                      ·
                        rfl

theorem cell23_7330709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 2, 3].length) (baseStart_7330709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330709 prefixEnd_7330709 := by exact prefixLift 7330709
  have htrace : WordTrace (prefixWord ++ tailWord_7330709) baseStart_7330709 baseEnd_7330709 := by
    simpa [prefixWord, tailWord_7330709, baseEnd_7330709] using wordTrace_append hprefix tailTrace_7330709
  have hstable : (prefixWord ++ tailWord_7330709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330709).length < 2 ^ (prefixWord ++ tailWord_7330709).sum := by decide
  have hdescent : baseEnd_7330709 < baseStart_7330709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330733 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_7330733 : Nat := 118140960795 + 7330733 * 2 ^ 59
def prefixEnd_7330733 : Nat := 4983230072969 + 3 ^ 40 * 7330733 * 2
def baseEnd_7330733 : Nat := 1254729859592057402374693

theorem tailTrace_7330733 : CollatzResearch.WordTrace tailWord_7330733 prefixEnd_7330733 1254729859592057402374693 := by
  unfold tailWord_7330733
  simp only [CollatzResearch.WordTrace]
  refine ⟨267373798151013805365532853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178249198767342536910355235 267373798151013805365532853)
  ·
    refine ⟨25066293576657544253018705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267373798151013805365532853 25066293576657544253018705)
    ·
      refine ⟨18799720182493158189764029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25066293576657544253018705 18799720182493158189764029)
      ·
        refine ⟨7049895068434934321161511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18799720182493158189764029 7049895068434934321161511)
        ·
          refine ⟨10574842602652401481742267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7049895068434934321161511 10574842602652401481742267)
          ·
            refine ⟨15862263903978602222613401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10574842602652401481742267 15862263903978602222613401)
            ·
              refine ⟨11896697927983951666960051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15862263903978602222613401 11896697927983951666960051)
              ·
                refine ⟨17845046891975927500440077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11896697927983951666960051 17845046891975927500440077)
                ·
                  refine ⟨6691892584490972812665029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17845046891975927500440077 6691892584490972812665029)
                  ·
                    refine ⟨1254729859592057402374693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6691892584490972812665029 1254729859592057402374693)
                    ·
                      rfl

theorem cell23_7330733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_7330733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330733 prefixEnd_7330733 := by exact prefixLift 7330733
  have htrace : WordTrace (prefixWord ++ tailWord_7330733) baseStart_7330733 baseEnd_7330733 := by
    simpa [prefixWord, tailWord_7330733, baseEnd_7330733] using wordTrace_append hprefix tailTrace_7330733
  have hstable : (prefixWord ++ tailWord_7330733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330733).length < 2 ^ (prefixWord ++ tailWord_7330733).sum := by decide
  have hdescent : baseEnd_7330733 < baseStart_7330733 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330735 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 7]
def baseStart_7330735 : Nat := 118140960795 + 7330735 * 2 ^ 59
def prefixEnd_7330735 : Nat := 4983230072969 + 3 ^ 40 * 7330735 * 2
def baseEnd_7330735 : Nat := 3764190605737481199299069

theorem tailTrace_7330735 : CollatzResearch.WordTrace tailWord_7330735 prefixEnd_7330735 3764190605737481199299069 := by
  unfold tailWord_7330735
  simp only [CollatzResearch.WordTrace]
  refine ⟨267373871097006559707105659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178249247398004373138070439 267373871097006559707105659)
  ·
    refine ⟨401060806645509839560658489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267373871097006559707105659 401060806645509839560658489)
    ·
      refine ⟨300795604984132379670493867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401060806645509839560658489 300795604984132379670493867)
      ·
        refine ⟨451193407476198569505740801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300795604984132379670493867 451193407476198569505740801)
        ·
          refine ⟨338395055607148927129305601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451193407476198569505740801 338395055607148927129305601)
          ·
            refine ⟨253796291705361695346979201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338395055607148927129305601 253796291705361695346979201)
            ·
              refine ⟨190347218779021271510234401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253796291705361695346979201 190347218779021271510234401)
              ·
                refine ⟨142760414084265953632675801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190347218779021271510234401 142760414084265953632675801)
                ·
                  refine ⟨107070310563199465224506851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142760414084265953632675801 107070310563199465224506851)
                  ·
                    refine ⟨160605465844799197836760277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 107070310563199465224506851 160605465844799197836760277)
                    ·
                      refine ⟨3764190605737481199299069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 160605465844799197836760277 3764190605737481199299069)
                      ·
                        rfl

theorem cell23_7330735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 7].length) (baseStart_7330735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330735 prefixEnd_7330735 := by exact prefixLift 7330735
  have htrace : WordTrace (prefixWord ++ tailWord_7330735) baseStart_7330735 baseEnd_7330735 := by
    simpa [prefixWord, tailWord_7330735, baseEnd_7330735] using wordTrace_append hprefix tailTrace_7330735
  have hstable : (prefixWord ++ tailWord_7330735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330735).length < 2 ^ (prefixWord ++ tailWord_7330735).sum := by decide
  have hdescent : baseEnd_7330735 < baseStart_7330735 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330792 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 1, 1, 6]
def baseStart_7330792 : Nat := 118140960795 + 7330792 * 2 ^ 59
def prefixEnd_7330792 : Nat := 4983230072969 + 3 ^ 40 * 7330792 * 2
def baseEnd_7330792 : Nat := 3764219874134787476286307

theorem tailTrace_7330792 : CollatzResearch.WordTrace tailWord_7330792 prefixEnd_7330792 3764219874134787476286307 := by
  unfold tailWord_7330792
  simp only [CollatzResearch.WordTrace]
  refine ⟨133687975028900029220965315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178250633371866705627953753 133687975028900029220965315)
  ·
    refine ⟨200531962543350043831447973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133687975028900029220965315 200531962543350043831447973)
    ·
      refine ⟨37599742976878133218396495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 200531962543350043831447973 37599742976878133218396495)
      ·
        refine ⟨56399614465317199827594743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37599742976878133218396495 56399614465317199827594743)
        ·
          refine ⟨84599421697975799741392115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56399614465317199827594743 84599421697975799741392115)
          ·
            refine ⟨126899132546963699612088173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84599421697975799741392115 126899132546963699612088173)
            ·
              refine ⟨47587174705111387354533065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126899132546963699612088173 47587174705111387354533065)
              ·
                refine ⟨35690381028833540515899799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47587174705111387354533065 35690381028833540515899799)
                ·
                  refine ⟨53535571543250310773849699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35690381028833540515899799 53535571543250310773849699)
                  ·
                    refine ⟨80303357314875466160774549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53535571543250310773849699 80303357314875466160774549)
                    ·
                      refine ⟨3764219874134787476286307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80303357314875466160774549 3764219874134787476286307)
                      ·
                        rfl

theorem cell23_7330792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_7330792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330792 prefixEnd_7330792 := by exact prefixLift 7330792
  have htrace : WordTrace (prefixWord ++ tailWord_7330792) baseStart_7330792 baseEnd_7330792 := by
    simpa [prefixWord, tailWord_7330792, baseEnd_7330792] using wordTrace_append hprefix tailTrace_7330792
  have hstable : (prefixWord ++ tailWord_7330792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330792).length < 2 ^ (prefixWord ++ tailWord_7330792).sum := by decide
  have hdescent : baseEnd_7330792 < baseStart_7330792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330847 : List Nat := [1, 1, 2, 4, 1, 5, 2, 2, 1, 2, 2]
def baseStart_7330847 : Nat := 118140960795 + 7330847 * 2 ^ 59
def prefixEnd_7330847 : Nat := 4983230072969 + 3 ^ 40 * 7330847 * 2
def baseEnd_7330847 : Nat := 3764248115570784761098555

theorem tailTrace_7330847 : CollatzResearch.WordTrace tailWord_7330847 prefixEnd_7330847 3764248115570784761098555 := by
  unfold tailWord_7330847
  simp only [CollatzResearch.WordTrace]
  refine ⟨267377956072600802835182795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178251970715067201890121863 267377956072600802835182795)
  ·
    refine ⟨401066934108901204252774193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267377956072600802835182795 401066934108901204252774193)
    ·
      refine ⟨300800200581675903189580645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401066934108901204252774193 300800200581675903189580645)
      ·
        refine ⟨56400037609064231848046371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300800200581675903189580645 56400037609064231848046371)
        ·
          refine ⟨84600056413596347772069557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56400037609064231848046371 84600056413596347772069557)
          ·
            refine ⟨7931255288774657603631521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84600056413596347772069557 7931255288774657603631521)
            ·
              refine ⟨5948441466580993202723641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7931255288774657603631521 5948441466580993202723641)
              ·
                refine ⟨4461331099935744902042731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5948441466580993202723641 4461331099935744902042731)
                ·
                  refine ⟨6691996649903617353064097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4461331099935744902042731 6691996649903617353064097)
                  ·
                    refine ⟨5018997487427713014798073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6691996649903617353064097 5018997487427713014798073)
                    ·
                      refine ⟨3764248115570784761098555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5018997487427713014798073 3764248115570784761098555)
                      ·
                        rfl

theorem cell23_7330847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 2, 1, 2, 2].length) (baseStart_7330847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330847 prefixEnd_7330847 := by exact prefixLift 7330847
  have htrace : WordTrace (prefixWord ++ tailWord_7330847) baseStart_7330847 baseEnd_7330847 := by
    simpa [prefixWord, tailWord_7330847, baseEnd_7330847] using wordTrace_append hprefix tailTrace_7330847
  have hstable : (prefixWord ++ tailWord_7330847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330847).length < 2 ^ (prefixWord ++ tailWord_7330847).sum := by decide
  have hdescent : baseEnd_7330847 < baseStart_7330847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330892 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 11]
def baseStart_7330892 : Nat := 118140960795 + 7330892 * 2 ^ 59
def prefixEnd_7330892 : Nat := 4983230072969 + 3 ^ 40 * 7330892 * 2
def baseEnd_7330892 : Nat := 418252358022248565003983

theorem tailTrace_7330892 : CollatzResearch.WordTrace tailWord_7330892 prefixEnd_7330892 418252358022248565003983 := by
  unfold tailWord_7330892
  simp only [CollatzResearch.WordTrace]
  refine ⟨133689798678718887760285465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178253064904958517013713953 133689798678718887760285465)
  ·
    refine ⟨100267349009039165820214099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133689798678718887760285465 100267349009039165820214099)
    ·
      refine ⟨150401023513558748730321149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100267349009039165820214099 150401023513558748730321149)
      ·
        refine ⟨56400383817584530773870431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150401023513558748730321149 56400383817584530773870431)
        ·
          refine ⟨84600575726376796160805647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56400383817584530773870431 84600575726376796160805647)
          ·
            refine ⟨126900863589565194241208471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84600575726376796160805647 126900863589565194241208471)
            ·
              refine ⟨190351295384347791361812707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126900863589565194241208471 190351295384347791361812707)
              ·
                refine ⟨285526943076521687042719061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190351295384347791361812707 285526943076521687042719061)
                ·
                  refine ⟨418252358022248565003983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 285526943076521687042719061 418252358022248565003983)
                  ·
                    rfl

theorem cell23_7330892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_7330892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330892 prefixEnd_7330892 := by exact prefixLift 7330892
  have htrace : WordTrace (prefixWord ++ tailWord_7330892) baseStart_7330892 baseEnd_7330892 := by
    simpa [prefixWord, tailWord_7330892, baseEnd_7330892] using wordTrace_append hprefix tailTrace_7330892
  have hstable : (prefixWord ++ tailWord_7330892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330892).length < 2 ^ (prefixWord ++ tailWord_7330892).sum := by decide
  have hdescent : baseEnd_7330892 < baseStart_7330892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330976 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 1, 6, 2]
def baseStart_7330976 : Nat := 118140960795 + 7330976 * 2 ^ 59
def prefixEnd_7330976 : Nat := 4983230072969 + 3 ^ 40 * 7330976 * 2
def baseEnd_7330976 : Nat := 3764314354575214756385461

theorem tailTrace_7330976 : CollatzResearch.WordTrace tailWord_7330976 prefixEnd_7330976 3764314354575214756385461 := by
  unfold tailWord_7330976
  simp only [CollatzResearch.WordTrace]
  refine ⟨133691330544566728933314391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178255107392755638577752521 133691330544566728933314391)
  ·
    refine ⟨200536995816850093399971587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133691330544566728933314391 200536995816850093399971587)
    ·
      refine ⟨300805493725275140099957381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200536995816850093399971587 300805493725275140099957381)
      ·
        refine ⟨56401030073489088768742009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300805493725275140099957381 56401030073489088768742009)
        ·
          refine ⟨42300772555116816576556507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56401030073489088768742009 42300772555116816576556507)
          ·
            refine ⟨63451158832675224864834761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42300772555116816576556507 63451158832675224864834761)
            ·
              refine ⟨47588369124506418648626071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63451158832675224864834761 47588369124506418648626071)
              ·
                refine ⟨71382553686759627972939107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47588369124506418648626071 71382553686759627972939107)
                ·
                  refine ⟨107073830530139441959408661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71382553686759627972939107 107073830530139441959408661)
                  ·
                    refine ⟨5019085806100286341847281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107073830530139441959408661 5019085806100286341847281)
                    ·
                      refine ⟨3764314354575214756385461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019085806100286341847281 3764314354575214756385461)
                      ·
                        rfl

theorem cell23_7330976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 1, 6, 2].length) (baseStart_7330976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330976 prefixEnd_7330976 := by exact prefixLift 7330976
  have htrace : WordTrace (prefixWord ++ tailWord_7330976) baseStart_7330976 baseEnd_7330976 := by
    simpa [prefixWord, tailWord_7330976, baseEnd_7330976] using wordTrace_append hprefix tailTrace_7330976
  have hstable : (prefixWord ++ tailWord_7330976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330976).length < 2 ^ (prefixWord ++ tailWord_7330976).sum := by decide
  have hdescent : baseEnd_7330976 < baseStart_7330976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330979 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 3]
def baseStart_7330979 : Nat := 118140960795 + 7330979 * 2 ^ 59
def prefixEnd_7330979 : Nat := 4983230072969 + 3 ^ 40 * 7330979 * 2
def baseEnd_7330979 : Nat := 3764315895017178244647947

theorem tailTrace_7330979 : CollatzResearch.WordTrace tailWord_7330979 prefixEnd_7330979 3764315895017178244647947 := by
  unfold tailWord_7330979
  simp only [CollatzResearch.WordTrace]
  refine ⟨267382770508122589378987991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178255180338748392919325327 267382770508122589378987991)
  ·
    refine ⟨401074155762183884068481987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267382770508122589378987991 401074155762183884068481987)
    ·
      refine ⟨601611233643275826102722981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401074155762183884068481987 601611233643275826102722981)
      ·
        refine ⟨112802106308114217394260559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 601611233643275826102722981 112802106308114217394260559)
        ·
          refine ⟨169203159462171326091390839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112802106308114217394260559 169203159462171326091390839)
          ·
            refine ⟨253804739193256989137086259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169203159462171326091390839 253804739193256989137086259)
            ·
              refine ⟨380707108789885483705629389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253804739193256989137086259 380707108789885483705629389)
              ·
                refine ⟨142765165796207056389611021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380707108789885483705629389 142765165796207056389611021)
                ·
                  refine ⟨53536937173577646146104133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142765165796207056389611021 53536937173577646146104133)
                  ·
                    refine ⟨10038175720045808652394525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53536937173577646146104133 10038175720045808652394525)
                    ·
                      refine ⟨3764315895017178244647947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10038175720045808652394525 3764315895017178244647947)
                      ·
                        rfl

theorem cell23_7330979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 4, 3].length) (baseStart_7330979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330979 prefixEnd_7330979 := by exact prefixLift 7330979
  have htrace : WordTrace (prefixWord ++ tailWord_7330979) baseStart_7330979 baseEnd_7330979 := by
    simpa [prefixWord, tailWord_7330979, baseEnd_7330979] using wordTrace_append hprefix tailTrace_7330979
  have hstable : (prefixWord ++ tailWord_7330979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330979).length < 2 ^ (prefixWord ++ tailWord_7330979).sum := by decide
  have hdescent : baseEnd_7330979 < baseStart_7330979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7330993 : List Nat := [1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 4]
def baseStart_7330993 : Nat := 118140960795 + 7330993 * 2 ^ 59
def prefixEnd_7330993 : Nat := 4983230072969 + 3 ^ 40 * 7330993 * 2
def baseEnd_7330993 : Nat := 3764323083746341189872883

theorem tailTrace_7330993 : CollatzResearch.WordTrace tailWord_7330993 prefixEnd_7330993 3764323083746341189872883 := by
  unfold tailWord_7330993
  simp only [CollatzResearch.WordTrace]
  refine ⟨267383281130071869769997633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178255520753381246513331755 267383281130071869769997633)
  ·
    refine ⟨200537460847553902327498225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267383281130071869769997633 200537460847553902327498225)
    ·
      refine ⟨150403095635665426745623669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200537460847553902327498225 150403095635665426745623669)
      ·
        refine ⟨14100290215843633757402219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150403095635665426745623669 14100290215843633757402219)
        ·
          refine ⟨21150435323765450636103329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14100290215843633757402219 21150435323765450636103329)
          ·
            refine ⟨15862826492824087977077497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21150435323765450636103329 15862826492824087977077497)
            ·
              refine ⟨11897119869618065982808123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15862826492824087977077497 11897119869618065982808123)
              ·
                refine ⟨17845679804427098974212185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11897119869618065982808123 17845679804427098974212185)
                ·
                  refine ⟨13384259853320324230659139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17845679804427098974212185 13384259853320324230659139)
                  ·
                    refine ⟨20076389779980486345988709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13384259853320324230659139 20076389779980486345988709)
                    ·
                      refine ⟨3764323083746341189872883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20076389779980486345988709 3764323083746341189872883)
                      ·
                        rfl

theorem cell23_7330993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_7330993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7330993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7330993 prefixEnd_7330993 := by exact prefixLift 7330993
  have htrace : WordTrace (prefixWord ++ tailWord_7330993) baseStart_7330993 baseEnd_7330993 := by
    simpa [prefixWord, tailWord_7330993, baseEnd_7330993] using wordTrace_append hprefix tailTrace_7330993
  have hstable : (prefixWord ++ tailWord_7330993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7330993).length < 2 ^ (prefixWord ++ tailWord_7330993).sum := by decide
  have hdescent : baseEnd_7330993 < baseStart_7330993 := by decide
  rcases family_descends (prefixWord ++ tailWord_7330993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331047 : List Nat := [1, 1, 5, 3, 3, 1, 1, 1, 2, 2, 3]
def baseStart_7331047 : Nat := 118140960795 + 7331047 * 2 ^ 59
def prefixEnd_7331047 : Nat := 4983230072969 + 3 ^ 40 * 7331047 * 2
def baseEnd_7331047 : Nat := 3764350811701683978597635

theorem tailTrace_7331047 : CollatzResearch.WordTrace tailWord_7331047 prefixEnd_7331047 3764350811701683978597635 := by
  unfold tailWord_7331047
  simp only [CollatzResearch.WordTrace]
  refine ⟨267385250671876236992463395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178256833781250824661642263 267385250671876236992463395)
  ·
    refine ⟨401077876007814355488695093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267385250671876236992463395 401077876007814355488695093)
    ·
      refine ⟨37601050875732595827065165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 401077876007814355488695093 37601050875732595827065165)
      ·
        refine ⟨14100394078399723435149437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37601050875732595827065165 14100394078399723435149437)
        ·
          refine ⟨5287647779399896288181039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14100394078399723435149437 5287647779399896288181039)
          ·
            refine ⟨7931471669099844432271559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287647779399896288181039 7931471669099844432271559)
            ·
              refine ⟨11897207503649766648407339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7931471669099844432271559 11897207503649766648407339)
              ·
                refine ⟨17845811255474649972611009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11897207503649766648407339 17845811255474649972611009)
                ·
                  refine ⟨13384358441605987479458257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17845811255474649972611009 13384358441605987479458257)
                  ·
                    refine ⟨10038268831204490609593693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13384358441605987479458257 10038268831204490609593693)
                    ·
                      refine ⟨3764350811701683978597635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10038268831204490609593693 3764350811701683978597635)
                      ·
                        rfl

theorem cell23_7331047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_7331047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331047 prefixEnd_7331047 := by exact prefixLift 7331047
  have htrace : WordTrace (prefixWord ++ tailWord_7331047) baseStart_7331047 baseEnd_7331047 := by
    simpa [prefixWord, tailWord_7331047, baseEnd_7331047] using wordTrace_append hprefix tailTrace_7331047
  have hstable : (prefixWord ++ tailWord_7331047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331047).length < 2 ^ (prefixWord ++ tailWord_7331047).sum := by decide
  have hdescent : baseEnd_7331047 < baseStart_7331047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331086 : List Nat := [4, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_7331086 : Nat := 118140960795 + 7331086 * 2 ^ 59
def prefixEnd_7331086 : Nat := 4983230072969 + 3 ^ 40 * 7331086 * 2
def baseEnd_7331086 : Nat := 3764370837447209326009955

theorem tailTrace_7331086 : CollatzResearch.WordTrace tailWord_7331086 prefixEnd_7331086 3764370837447209326009955 := by
  unfold tailWord_7331086
  simp only [CollatzResearch.WordTrace]
  refine ⟨33423334139841868331641639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178257782079156631102088741 33423334139841868331641639)
  ·
    refine ⟨50135001209762802497462459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33423334139841868331641639 50135001209762802497462459)
    ·
      refine ⟨75202501814644203746193689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50135001209762802497462459 75202501814644203746193689)
      ·
        refine ⟨56401876360983152809645267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75202501814644203746193689 56401876360983152809645267)
        ·
          refine ⟨84602814541474729214467901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56401876360983152809645267 84602814541474729214467901)
          ·
            refine ⟨31726055453053023455425463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84602814541474729214467901 31726055453053023455425463)
            ·
              refine ⟨47589083179579535183138195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31726055453053023455425463 47589083179579535183138195)
              ·
                refine ⟨71383624769369302774707293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47589083179579535183138195 71383624769369302774707293)
                ·
                  refine ⟨26768859288513488540515235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71383624769369302774707293 26768859288513488540515235)
                  ·
                    refine ⟨40153288932770232810772853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26768859288513488540515235 40153288932770232810772853)
                    ·
                      refine ⟨3764370837447209326009955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40153288932770232810772853 3764370837447209326009955)
                      ·
                        rfl

theorem cell23_7331086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_7331086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331086 prefixEnd_7331086 := by exact prefixLift 7331086
  have htrace : WordTrace (prefixWord ++ tailWord_7331086) baseStart_7331086 baseEnd_7331086 := by
    simpa [prefixWord, tailWord_7331086, baseEnd_7331086] using wordTrace_append hprefix tailTrace_7331086
  have hstable : (prefixWord ++ tailWord_7331086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331086).length < 2 ^ (prefixWord ++ tailWord_7331086).sum := by decide
  have hdescent : baseEnd_7331086 < baseStart_7331086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331089 : List Nat := [1, 2, 2, 1, 1, 4, 2, 10]
def baseStart_7331089 : Nat := 118140960795 + 7331089 * 2 ^ 59
def prefixEnd_7331089 : Nat := 4983230072969 + 3 ^ 40 * 7331089 * 2
def baseEnd_7331089 : Nat := 139421199181080474602683

theorem tailTrace_7331089 : CollatzResearch.WordTrace tailWord_7331089 prefixEnd_7331089 139421199181080474602683 := by
  unfold tailWord_7331089
  simp only [CollatzResearch.WordTrace]
  refine ⟨267386782537724078165492321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178257855025149385443661547 267386782537724078165492321)
  ·
    refine ⟨200540086903293058624119241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267386782537724078165492321 200540086903293058624119241)
    ·
      refine ⟨150405065177469793968089431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200540086903293058624119241 150405065177469793968089431)
      ·
        refine ⟨225607597766204690952134147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150405065177469793968089431 225607597766204690952134147)
        ·
          refine ⟨338411396649307036428201221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225607597766204690952134147 338411396649307036428201221)
          ·
            refine ⟨63452136871745069330287729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338411396649307036428201221 63452136871745069330287729)
            ·
              refine ⟨47589102653808801997715797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63452136871745069330287729 47589102653808801997715797)
              ·
                refine ⟨139421199181080474602683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 47589102653808801997715797 139421199181080474602683)
                ·
                  rfl

theorem cell23_7331089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 10].length) (baseStart_7331089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331089 prefixEnd_7331089 := by exact prefixLift 7331089
  have htrace : WordTrace (prefixWord ++ tailWord_7331089) baseStart_7331089 baseEnd_7331089 := by
    simpa [prefixWord, tailWord_7331089, baseEnd_7331089] using wordTrace_append hprefix tailTrace_7331089
  have hstable : (prefixWord ++ tailWord_7331089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331089).length < 2 ^ (prefixWord ++ tailWord_7331089).sum := by decide
  have hdescent : baseEnd_7331089 < baseStart_7331089 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331096 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 1, 1, 6]
def baseStart_7331096 : Nat := 118140960795 + 7331096 * 2 ^ 59
def prefixEnd_7331096 : Nat := 4983230072969 + 3 ^ 40 * 7331096 * 2
def baseEnd_7331096 : Nat := 3764375972253754286884909

theorem tailTrace_7331096 : CollatzResearch.WordTrace tailWord_7331096 prefixEnd_7331096 3764375972253754286884909 := by
  unfold tailWord_7331096
  simp only [CollatzResearch.WordTrace]
  refine ⟨133693518924349359180498571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178258025232465812240664761 133693518924349359180498571)
  ·
    refine ⟨200540278386524038770747857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133693518924349359180498571 200540278386524038770747857)
    ·
      refine ⟨150405208789893029078060893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200540278386524038770747857 150405208789893029078060893)
      ·
        refine ⟨56401953296209885904272835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150405208789893029078060893 56401953296209885904272835)
        ·
          refine ⟨84602929944314828856409253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56401953296209885904272835 84602929944314828856409253)
          ·
            refine ⟨15863049364559030410576735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84602929944314828856409253 15863049364559030410576735)
            ·
              refine ⟨23794574046838545615865103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15863049364559030410576735 23794574046838545615865103)
              ·
                refine ⟨35691861070257818423797655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23794574046838545615865103 35691861070257818423797655)
                ·
                  refine ⟨53537791605386727635696483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35691861070257818423797655 53537791605386727635696483)
                  ·
                    refine ⟨80306687408080091453544725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53537791605386727635696483 80306687408080091453544725)
                    ·
                      refine ⟨3764375972253754286884909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80306687408080091453544725 3764375972253754286884909)
                      ·
                        rfl

theorem cell23_7331096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 1, 6].length) (baseStart_7331096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331096 prefixEnd_7331096 := by exact prefixLift 7331096
  have htrace : WordTrace (prefixWord ++ tailWord_7331096) baseStart_7331096 baseEnd_7331096 := by
    simpa [prefixWord, tailWord_7331096, baseEnd_7331096] using wordTrace_append hprefix tailTrace_7331096
  have hstable : (prefixWord ++ tailWord_7331096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331096).length < 2 ^ (prefixWord ++ tailWord_7331096).sum := by decide
  have hdescent : baseEnd_7331096 < baseStart_7331096 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331100 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 3, 2, 2]
def baseStart_7331100 : Nat := 118140960795 + 7331100 * 2 ^ 59
def prefixEnd_7331100 : Nat := 4983230072969 + 3 ^ 40 * 7331100 * 2
def baseEnd_7331100 : Nat := 3764378026176372271234891

theorem tailTrace_7331100 : CollatzResearch.WordTrace tailWord_7331100 prefixEnd_7331100 3764378026176372271234891 := by
  unfold tailWord_7331100
  simp only [CollatzResearch.WordTrace]
  refine ⟨133693591870342113522071377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178258122493789484696095169 133693591870342113522071377)
  ·
    refine ⟨100270193902756585141553533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133693591870342113522071377 100270193902756585141553533)
    ·
      refine ⟨37601322713533719428082575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100270193902756585141553533 37601322713533719428082575)
      ·
        refine ⟨56401984070300579142123863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37601322713533719428082575 56401984070300579142123863)
        ·
          refine ⟨84602976105450868713185795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56401984070300579142123863 84602976105450868713185795)
          ·
            refine ⟨126904464158176303069778693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84602976105450868713185795 126904464158176303069778693)
            ·
              refine ⟨23794587029658056825583505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126904464158176303069778693 23794587029658056825583505)
              ·
                refine ⟨17845940272243542619187629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23794587029658056825583505 17845940272243542619187629)
                ·
                  refine ⟨6692227602091328482195361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17845940272243542619187629 6692227602091328482195361)
                  ·
                    refine ⟨5019170701568496361646521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6692227602091328482195361 5019170701568496361646521)
                    ·
                      refine ⟨3764378026176372271234891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019170701568496361646521 3764378026176372271234891)
                      ·
                        rfl

theorem cell23_7331100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 3, 2, 2].length) (baseStart_7331100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331100 prefixEnd_7331100 := by exact prefixLift 7331100
  have htrace : WordTrace (prefixWord ++ tailWord_7331100) baseStart_7331100 baseEnd_7331100 := by
    simpa [prefixWord, tailWord_7331100, baseEnd_7331100] using wordTrace_append hprefix tailTrace_7331100
  have hstable : (prefixWord ++ tailWord_7331100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331100).length < 2 ^ (prefixWord ++ tailWord_7331100).sum := by decide
  have hdescent : baseEnd_7331100 < baseStart_7331100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331116 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 3]
def baseStart_7331116 : Nat := 118140960795 + 7331116 * 2 ^ 59
def prefixEnd_7331116 : Nat := 4983230072969 + 3 ^ 40 * 7331116 * 2
def baseEnd_7331116 : Nat := 3764386241866844208634817

theorem tailTrace_7331116 : CollatzResearch.WordTrace tailWord_7331116 prefixEnd_7331116 3764386241866844208634817 := by
  unfold tailWord_7331116
  simp only [CollatzResearch.WordTrace]
  refine ⟨133693883654313130888362601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178258511539084174517816801 133693883654313130888362601)
  ·
    refine ⟨100270412740734848166271951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133693883654313130888362601 100270412740734848166271951)
    ·
      refine ⟨150405619111102272249407927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100270412740734848166271951 150405619111102272249407927)
      ·
        refine ⟨225608428666653408374111891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150405619111102272249407927 225608428666653408374111891)
        ·
          refine ⟨338412642999980112561167837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225608428666653408374111891 338412642999980112561167837)
          ·
            refine ⟨126904741124992542210437939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338412642999980112561167837 126904741124992542210437939)
            ·
              refine ⟨190357111687488813315656909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126904741124992542210437939 190357111687488813315656909)
              ·
                refine ⟨71383916882808304993371341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190357111687488813315656909 71383916882808304993371341)
                ·
                  refine ⟨26768968831053114372514253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71383916882808304993371341 26768968831053114372514253)
                  ·
                    refine ⟨10038363311644917889692845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26768968831053114372514253 10038363311644917889692845)
                    ·
                      refine ⟨3764386241866844208634817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10038363311644917889692845 3764386241866844208634817)
                      ·
                        rfl

theorem cell23_7331116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 3].length) (baseStart_7331116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331116 prefixEnd_7331116 := by exact prefixLift 7331116
  have htrace : WordTrace (prefixWord ++ tailWord_7331116) baseStart_7331116 baseEnd_7331116 := by
    simpa [prefixWord, tailWord_7331116, baseEnd_7331116] using wordTrace_append hprefix tailTrace_7331116
  have hstable : (prefixWord ++ tailWord_7331116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331116).length < 2 ^ (prefixWord ++ tailWord_7331116).sum := by decide
  have hdescent : baseEnd_7331116 < baseStart_7331116 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331119 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 1, 9]
def baseStart_7331119 : Nat := 118140960795 + 7331119 * 2 ^ 59
def prefixEnd_7331119 : Nat := 4983230072969 + 3 ^ 40 * 7331119 * 2
def baseEnd_7331119 : Nat := 1254795927436269232299101

theorem tailTrace_7331119 : CollatzResearch.WordTrace tailWord_7331119 prefixEnd_7331119 1254795927436269232299101 := by
  unfold tailWord_7331119
  simp only [CollatzResearch.WordTrace]
  refine ⟨267387876727615393289084411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178258584485076928859389607 267387876727615393289084411)
  ·
    refine ⟨401081815091423089933626617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267387876727615393289084411 401081815091423089933626617)
    ·
      refine ⟨300811361318567317450219963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401081815091423089933626617 300811361318567317450219963)
      ·
        refine ⟨451217041977850976175329945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300811361318567317450219963 451217041977850976175329945)
        ·
          refine ⟨338412781483388232131497459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451217041977850976175329945 338412781483388232131497459)
          ·
            refine ⟨507619172225082348197246189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338412781483388232131497459 507619172225082348197246189)
            ·
              refine ⟨190357189584405880573967321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507619172225082348197246189 190357189584405880573967321)
              ·
                refine ⟨142767892188304410430475491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190357189584405880573967321 142767892188304410430475491)
                ·
                  refine ⟨214151838282456615645713237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142767892188304410430475491 214151838282456615645713237)
                  ·
                    refine ⟨1254795927436269232299101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 214151838282456615645713237 1254795927436269232299101)
                    ·
                      rfl

theorem cell23_7331119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 9].length) (baseStart_7331119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331119 prefixEnd_7331119 := by exact prefixLift 7331119
  have htrace : WordTrace (prefixWord ++ tailWord_7331119) baseStart_7331119 baseEnd_7331119 := by
    simpa [prefixWord, tailWord_7331119, baseEnd_7331119] using wordTrace_append hprefix tailTrace_7331119
  have hstable : (prefixWord ++ tailWord_7331119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331119).length < 2 ^ (prefixWord ++ tailWord_7331119).sum := by decide
  have hdescent : baseEnd_7331119 < baseStart_7331119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331150 : List Nat := [4, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_7331150 : Nat := 118140960795 + 7331150 * 2 ^ 59
def prefixEnd_7331150 : Nat := 4983230072969 + 3 ^ 40 * 7331150 * 2
def baseEnd_7331150 : Nat := 3764403700209097075609661

theorem tailTrace_7331150 : CollatzResearch.WordTrace tailWord_7331150 prefixEnd_7331150 3764403700209097075609661 := by
  unfold tailWord_7331150
  simp only [CollatzResearch.WordTrace]
  refine ⟨33423625923812885697932863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178259338260335390388975269 33423625923812885697932863)
  ·
    refine ⟨50135438885719328546899295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33423625923812885697932863 50135438885719328546899295)
    ·
      refine ⟨75203158328578992820348943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50135438885719328546899295 75203158328578992820348943)
      ·
        refine ⟨112804737492868489230523415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75203158328578992820348943 112804737492868489230523415)
        ·
          refine ⟨169207106239302733845785123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112804737492868489230523415 169207106239302733845785123)
          ·
            refine ⟨253810659358954100768677685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169207106239302733845785123 253810659358954100768677685)
            ·
              refine ⟨23794749314901946947063533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253810659358954100768677685 23794749314901946947063533)
              ·
                refine ⟨8923030993088230105148825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23794749314901946947063533 8923030993088230105148825)
                ·
                  refine ⟨6692273244816172578861619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8923030993088230105148825 6692273244816172578861619)
                  ·
                    refine ⟨10038409867224258868292429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6692273244816172578861619 10038409867224258868292429)
                    ·
                      refine ⟨3764403700209097075609661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10038409867224258868292429 3764403700209097075609661)
                      ·
                        rfl

theorem cell23_7331150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_7331150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331150 prefixEnd_7331150 := by exact prefixLift 7331150
  have htrace : WordTrace (prefixWord ++ tailWord_7331150) baseStart_7331150 baseEnd_7331150 := by
    simpa [prefixWord, tailWord_7331150, baseEnd_7331150] using wordTrace_append hprefix tailTrace_7331150
  have hstable : (prefixWord ++ tailWord_7331150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331150).length < 2 ^ (prefixWord ++ tailWord_7331150).sum := by decide
  have hdescent : baseEnd_7331150 < baseStart_7331150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331196 : List Nat := [2, 2, 2, 1, 1, 1, 4, 3, 7]
def baseStart_7331196 : Nat := 118140960795 + 7331196 * 2 ^ 59
def prefixEnd_7331196 : Nat := 4983230072969 + 3 ^ 40 * 7331196 * 2
def baseEnd_7331196 : Nat := 418269702257689321737161

theorem tailTrace_7331196 : CollatzResearch.WordTrace tailWord_7331196 prefixEnd_7331196 418269702257689321737161 := by
  unfold tailWord_7331196
  simp only [CollatzResearch.WordTrace]
  refine ⟨133695342574168217719818721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178260456765557623626424961 133695342574168217719818721)
  ·
    refine ⟨100271506930626163289864041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133695342574168217719818721 100271506930626163289864041)
    ·
      refine ⟨75203630197969622467398031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100271506930626163289864041 75203630197969622467398031)
      ·
        refine ⟨112805445296954433701097047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75203630197969622467398031 112805445296954433701097047)
        ·
          refine ⟨169208167945431650551645571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112805445296954433701097047 169208167945431650551645571)
          ·
            refine ⟨253812251918147475827468357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169208167945431650551645571 253812251918147475827468357)
            ·
              refine ⟨47589797234652651717650317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253812251918147475827468357 47589797234652651717650317)
              ·
                refine ⟨17846173962994744394118869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47589797234652651717650317 17846173962994744394118869)
                ·
                  refine ⟨418269702257689321737161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17846173962994744394118869 418269702257689321737161)
                  ·
                    rfl

theorem cell23_7331196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 3, 7].length) (baseStart_7331196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331196 prefixEnd_7331196 := by exact prefixLift 7331196
  have htrace : WordTrace (prefixWord ++ tailWord_7331196) baseStart_7331196 baseEnd_7331196 := by
    simpa [prefixWord, tailWord_7331196, baseEnd_7331196] using wordTrace_append hprefix tailTrace_7331196
  have hstable : (prefixWord ++ tailWord_7331196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331196).length < 2 ^ (prefixWord ++ tailWord_7331196).sum := by decide
  have hdescent : baseEnd_7331196 < baseStart_7331196 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331203 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 4]
def baseStart_7331203 : Nat := 118140960795 + 7331203 * 2 ^ 59
def prefixEnd_7331203 : Nat := 4983230072969 + 3 ^ 40 * 7331203 * 2
def baseEnd_7331203 : Nat := 3764430914683785368246917

theorem tailTrace_7331203 : CollatzResearch.WordTrace tailWord_7331203 prefixEnd_7331203 3764430914683785368246917 := by
  unfold tailWord_7331203
  simp only [CollatzResearch.WordTrace]
  refine ⟨267390940459311075635142263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178260626972874050423428175 267390940459311075635142263)
  ·
    refine ⟨401086410688966613452713395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267390940459311075635142263 401086410688966613452713395)
    ·
      refine ⟨601629616033449920179070093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401086410688966613452713395 601629616033449920179070093)
      ·
        refine ⟨225611106012543720067151285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601629616033449920179070093 225611106012543720067151285)
        ·
          refine ⟨21151041188675973756295433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 225611106012543720067151285 21151041188675973756295433)
          ·
            refine ⟨15863280891506980317221575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21151041188675973756295433 15863280891506980317221575)
            ·
              refine ⟨23794921337260470475832363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15863280891506980317221575 23794921337260470475832363)
              ·
                refine ⟨35692382005890705713748545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23794921337260470475832363 35692382005890705713748545)
                ·
                  refine ⟨26769286504418029285311409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35692382005890705713748545 26769286504418029285311409)
                  ·
                    refine ⟨20076964878313521963983557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26769286504418029285311409 20076964878313521963983557)
                    ·
                      refine ⟨3764430914683785368246917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20076964878313521963983557 3764430914683785368246917)
                      ·
                        rfl

theorem cell23_7331203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 4].length) (baseStart_7331203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331203 prefixEnd_7331203 := by exact prefixLift 7331203
  have htrace : WordTrace (prefixWord ++ tailWord_7331203) baseStart_7331203 baseEnd_7331203 := by
    simpa [prefixWord, tailWord_7331203, baseEnd_7331203] using wordTrace_append hprefix tailTrace_7331203
  have hstable : (prefixWord ++ tailWord_7331203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331203).length < 2 ^ (prefixWord ++ tailWord_7331203).sum := by decide
  have hdescent : baseEnd_7331203 < baseStart_7331203 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331207 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 2, 2, 2]
def baseStart_7331207 : Nat := 118140960795 + 7331207 * 2 ^ 59
def prefixEnd_7331207 : Nat := 4983230072969 + 3 ^ 40 * 7331207 * 2
def baseEnd_7331207 : Nat := 3764432968606403352596899

theorem tailTrace_7331207 : CollatzResearch.WordTrace tailWord_7331207 prefixEnd_7331207 3764432968606403352596899 := by
  unfold tailWord_7331207
  simp only [CollatzResearch.WordTrace]
  refine ⟨267391086351296584318287875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178260724234197722878858583 267391086351296584318287875)
  ·
    refine ⟨401086629526944876477431813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267391086351296584318287875 401086629526944876477431813)
    ·
      refine ⟨75203743036302164339518465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401086629526944876477431813 75203743036302164339518465)
      ·
        refine ⟨56402807277226623254638849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75203743036302164339518465 56402807277226623254638849)
        ·
          refine ⟨42302105457919967440979137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56402807277226623254638849 42302105457919967440979137)
          ·
            refine ⟨31726579093439975580734353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42302105457919967440979137 31726579093439975580734353)
            ·
              refine ⟨23794934320079981685550765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31726579093439975580734353 23794934320079981685550765)
              ·
                refine ⟨8923100370029993132081537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23794934320079981685550765 8923100370029993132081537)
                ·
                  refine ⟨6692325277522494849061153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8923100370029993132081537 6692325277522494849061153)
                  ·
                    refine ⟨5019243958141871136795865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6692325277522494849061153 5019243958141871136795865)
                    ·
                      refine ⟨3764432968606403352596899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019243958141871136795865 3764432968606403352596899)
                      ·
                        rfl

theorem cell23_7331207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 2, 2, 2].length) (baseStart_7331207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331207 prefixEnd_7331207 := by exact prefixLift 7331207
  have htrace : WordTrace (prefixWord ++ tailWord_7331207) baseStart_7331207 baseEnd_7331207 := by
    simpa [prefixWord, tailWord_7331207, baseEnd_7331207] using wordTrace_append hprefix tailTrace_7331207
  have hstable : (prefixWord ++ tailWord_7331207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331207).length < 2 ^ (prefixWord ++ tailWord_7331207).sum := by decide
  have hdescent : baseEnd_7331207 < baseStart_7331207 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331228 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 1, 3, 2]
def baseStart_7331228 : Nat := 118140960795 + 7331228 * 2 ^ 59
def prefixEnd_7331228 : Nat := 4983230072969 + 3 ^ 40 * 7331228 * 2
def baseEnd_7331228 : Nat := 3764443751700147770434303

theorem tailTrace_7331228 : CollatzResearch.WordTrace tailWord_7331228 prefixEnd_7331228 3764443751700147770434303 := by
  unfold tailWord_7331228
  simp only [CollatzResearch.WordTrace]
  refine ⟨133695926142110252452401169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178261234856147003269868225 133695926142110252452401169)
  ·
    refine ⟨100271944606582689339300877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133695926142110252452401169 100271944606582689339300877)
    ·
      refine ⟨37601979227468508502237829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100271944606582689339300877 37601979227468508502237829)
      ·
        refine ⟨7050371105150345344169593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37601979227468508502237829 7050371105150345344169593)
        ·
          refine ⟨5287778328862759008127195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7050371105150345344169593 5287778328862759008127195)
          ·
            refine ⟨7931667493294138512190793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5287778328862759008127195 7931667493294138512190793)
            ·
              refine ⟨5948750619970603884143095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7931667493294138512190793 5948750619970603884143095)
              ·
                refine ⟨8923125929955905826214643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5948750619970603884143095 8923125929955905826214643)
                ·
                  refine ⟨13384688894933858739321965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8923125929955905826214643 13384688894933858739321965)
                  ·
                    refine ⟨5019258335600197027245737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13384688894933858739321965 5019258335600197027245737)
                    ·
                      refine ⟨3764443751700147770434303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019258335600197027245737 3764443751700147770434303)
                      ·
                        rfl

theorem cell23_7331228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_7331228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331228 prefixEnd_7331228 := by exact prefixLift 7331228
  have htrace : WordTrace (prefixWord ++ tailWord_7331228) baseStart_7331228 baseEnd_7331228 := by
    simpa [prefixWord, tailWord_7331228, baseEnd_7331228] using wordTrace_append hprefix tailTrace_7331228
  have hstable : (prefixWord ++ tailWord_7331228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331228).length < 2 ^ (prefixWord ++ tailWord_7331228).sum := by decide
  have hdescent : baseEnd_7331228 < baseStart_7331228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331303 : List Nat := [1, 1, 5, 2, 1, 2, 2, 1, 8]
def baseStart_7331303 : Nat := 118140960795 + 7331303 * 2 ^ 59
def prefixEnd_7331303 : Nat := 4983230072969 + 3 ^ 40 * 7331303 * 2
def baseEnd_7331303 : Nat := 418275806972137219666273

theorem tailTrace_7331303 : CollatzResearch.WordTrace tailWord_7331303 prefixEnd_7331303 418275806972137219666273 := by
  unfold tailWord_7331303
  simp only [CollatzResearch.WordTrace]
  refine ⟨267394587758948792713782563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178263058505965861809188375 267394587758948792713782563)
  ·
    refine ⟨401091881638423189070673845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267394587758948792713782563 401091881638423189070673845)
    ·
      refine ⟨37602363903602173975375673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 401091881638423189070673845 37602363903602173975375673)
      ·
        refine ⟨28201772927701630481531755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37602363903602173975375673 28201772927701630481531755)
        ·
          refine ⟨42302659391552445722297633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28201772927701630481531755 42302659391552445722297633)
          ·
            refine ⟨31726994543664334291723225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42302659391552445722297633 31726994543664334291723225)
            ·
              refine ⟨23795245907748250718792419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31726994543664334291723225 23795245907748250718792419)
              ·
                refine ⟨35692868861622376078188629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23795245907748250718792419 35692868861622376078188629)
                ·
                  refine ⟨418275806972137219666273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35692868861622376078188629 418275806972137219666273)
                  ·
                    rfl

theorem cell23_7331303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 1, 8].length) (baseStart_7331303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331303 prefixEnd_7331303 := by exact prefixLift 7331303
  have htrace : WordTrace (prefixWord ++ tailWord_7331303) baseStart_7331303 baseEnd_7331303 := by
    simpa [prefixWord, tailWord_7331303, baseEnd_7331303] using wordTrace_append hprefix tailTrace_7331303
  have hstable : (prefixWord ++ tailWord_7331303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331303).length < 2 ^ (prefixWord ++ tailWord_7331303).sum := by decide
  have hdescent : baseEnd_7331303 < baseStart_7331303 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331320 : List Nat := [2, 1, 2, 1, 1, 5, 4, 1, 6]
def baseStart_7331320 : Nat := 118140960795 + 7331320 * 2 ^ 59
def prefixEnd_7331320 : Nat := 4983230072969 + 3 ^ 40 * 7331320 * 2
def baseEnd_7331320 : Nat := 418276776880040156720431

theorem tailTrace_7331320 : CollatzResearch.WordTrace tailWord_7331320 prefixEnd_7331320 418276776880040156720431 := by
  unfold tailWord_7331320
  simp only [CollatzResearch.WordTrace]
  refine ⟨133697603899943602308575707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178263471866591469744767609 133697603899943602308575707)
  ·
    refine ⟨200546405849915403462863561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133697603899943602308575707 200546405849915403462863561)
    ·
      refine ⟨150409804387436552597147671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200546405849915403462863561 150409804387436552597147671)
      ·
        refine ⟨225614706581154828895721507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150409804387436552597147671 225614706581154828895721507)
        ·
          refine ⟨338422059871732243343582261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225614706581154828895721507 338422059871732243343582261)
          ·
            refine ⟨31727068112974897813460837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 338422059871732243343582261 31727068112974897813460837)
            ·
              refine ⟨5948825271182793340023907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31727068112974897813460837 5948825271182793340023907)
              ·
                refine ⟨8923237906774190010035861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5948825271182793340023907 8923237906774190010035861)
                ·
                  refine ⟨418276776880040156720431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8923237906774190010035861 418276776880040156720431)
                  ·
                    rfl

theorem cell23_7331320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 4, 1, 6].length) (baseStart_7331320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331320 prefixEnd_7331320 := by exact prefixLift 7331320
  have htrace : WordTrace (prefixWord ++ tailWord_7331320) baseStart_7331320 baseEnd_7331320 := by
    simpa [prefixWord, tailWord_7331320, baseEnd_7331320] using wordTrace_append hprefix tailTrace_7331320
  have hstable : (prefixWord ++ tailWord_7331320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331320).length < 2 ^ (prefixWord ++ tailWord_7331320).sum := by decide
  have hdescent : baseEnd_7331320 < baseStart_7331320 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331353 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 4]
def baseStart_7331353 : Nat := 118140960795 + 7331353 * 2 ^ 59
def prefixEnd_7331353 : Nat := 4983230072969 + 3 ^ 40 * 7331353 * 2
def baseEnd_7331353 : Nat := 3764507936781959781371227

theorem tailTrace_7331353 : CollatzResearch.WordTrace tailWord_7331353 prefixEnd_7331353 3764507936781959781371227 := by
  unfold tailWord_7331353
  simp only [CollatzResearch.WordTrace]
  refine ⟨267396411408767651253102713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178264274272511767502068475 267396411408767651253102713)
  ·
    refine ⟨200547308556575738439827035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267396411408767651253102713 200547308556575738439827035)
    ·
      refine ⟨300820962834863607659740553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200547308556575738439827035 300820962834863607659740553)
      ·
        refine ⟨225615722126147705744805415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300820962834863607659740553 225615722126147705744805415)
        ·
          refine ⟨338423583189221558617208123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225615722126147705744805415 338423583189221558617208123)
          ·
            refine ⟨507635374783832337925812185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338423583189221558617208123 507635374783832337925812185)
            ·
              refine ⟨380726531087874253444359139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507635374783832337925812185 380726531087874253444359139)
              ·
                refine ⟨571089796631811380166538709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380726531087874253444359139 571089796631811380166538709)
                ·
                  refine ⟨13384917108558079222653251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 571089796631811380166538709 13384917108558079222653251)
                  ·
                    refine ⟨20077375662837118833979877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13384917108558079222653251 20077375662837118833979877)
                    ·
                      refine ⟨3764507936781959781371227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20077375662837118833979877 3764507936781959781371227)
                      ·
                        rfl

theorem cell23_7331353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_7331353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331353 prefixEnd_7331353 := by exact prefixLift 7331353
  have htrace : WordTrace (prefixWord ++ tailWord_7331353) baseStart_7331353 baseEnd_7331353 := by
    simpa [prefixWord, tailWord_7331353, baseEnd_7331353] using wordTrace_append hprefix tailTrace_7331353
  have hstable : (prefixWord ++ tailWord_7331353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331353).length < 2 ^ (prefixWord ++ tailWord_7331353).sum := by decide
  have hdescent : baseEnd_7331353 < baseStart_7331353 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331357 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 2, 3, 2]
def baseStart_7331357 : Nat := 118140960795 + 7331357 * 2 ^ 59
def prefixEnd_7331357 : Nat := 4983230072969 + 3 ^ 40 * 7331357 * 2
def baseEnd_7331357 : Nat := 3764509990704577765721209

theorem tailTrace_7331357 : CollatzResearch.WordTrace tailWord_7331357 prefixEnd_7331357 3764509990704577765721209 := by
  unfold tailWord_7331357
  simp only [CollatzResearch.WordTrace]
  refine ⟨267396557300753159936248325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178264371533835439957498883 267396557300753159936248325)
  ·
    refine ⟨50136854493891217488046561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267396557300753159936248325 50136854493891217488046561)
    ·
      refine ⟨37602640870418413116034921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50136854493891217488046561 37602640870418413116034921)
      ·
        refine ⟨28201980652813809837026191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37602640870418413116034921 28201980652813809837026191)
        ·
          refine ⟨42302970979220714755539287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28201980652813809837026191 42302970979220714755539287)
          ·
            refine ⟨63454456468831072133308931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42302970979220714755539287 63454456468831072133308931)
            ·
              refine ⟨95181684703246608199963397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63454456468831072133308931 95181684703246608199963397)
              ·
                refine ⟨17846565881858739037493137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95181684703246608199963397 17846565881858739037493137)
                ·
                  refine ⟨13384924411394054278119853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17846565881858739037493137 13384924411394054278119853)
                  ·
                    refine ⟨5019346654272770354294945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13384924411394054278119853 5019346654272770354294945)
                    ·
                      refine ⟨3764509990704577765721209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019346654272770354294945 3764509990704577765721209)
                      ·
                        rfl

theorem cell23_7331357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_7331357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331357 prefixEnd_7331357 := by exact prefixLift 7331357
  have htrace : WordTrace (prefixWord ++ tailWord_7331357) baseStart_7331357 baseEnd_7331357 := by
    simpa [prefixWord, tailWord_7331357, baseEnd_7331357] using wordTrace_append hprefix tailTrace_7331357
  have hstable : (prefixWord ++ tailWord_7331357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331357).length < 2 ^ (prefixWord ++ tailWord_7331357).sum := by decide
  have hdescent : baseEnd_7331357 < baseStart_7331357 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331370 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4]
def baseStart_7331370 : Nat := 118140960795 + 7331370 * 2 ^ 59
def prefixEnd_7331370 : Nat := 4983230072969 + 3 ^ 40 * 7331370 * 2
def baseEnd_7331370 : Nat := 3764516665953086214858649

theorem tailTrace_7331370 : CollatzResearch.WordTrace tailWord_7331370 prefixEnd_7331370 3764516665953086214858649 := by
  unfold tailWord_7331370
  simp only [CollatzResearch.WordTrace]
  refine ⟨66849257862426515789117891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178264687633137375437647709 66849257862426515789117891)
  ·
    refine ⟨100273886793639773683676837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66849257862426515789117891 100273886793639773683676837)
    ·
      refine ⟨18801353773807457565689407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100273886793639773683676837 18801353773807457565689407)
      ·
        refine ⟨28202030660711186348534111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18801353773807457565689407 28202030660711186348534111)
        ·
          refine ⟨42303045991066779522801167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28202030660711186348534111 42303045991066779522801167)
          ·
            refine ⟨63454568986600169284201751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42303045991066779522801167 63454568986600169284201751)
            ·
              refine ⟨95181853479900253926302627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63454568986600169284201751 95181853479900253926302627)
              ·
                refine ⟨142772780219850380889453941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95181853479900253926302627 142772780219850380889453941)
                ·
                  refine ⟨13384948145610973208386307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142772780219850380889453941 13384948145610973208386307)
                  ·
                    refine ⟨20077422218416459812579461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13384948145610973208386307 20077422218416459812579461)
                    ·
                      refine ⟨3764516665953086214858649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20077422218416459812579461 3764516665953086214858649)
                      ·
                        rfl

theorem cell23_7331370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_7331370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331370 prefixEnd_7331370 := by exact prefixLift 7331370
  have htrace : WordTrace (prefixWord ++ tailWord_7331370) baseStart_7331370 baseEnd_7331370 := by
    simpa [prefixWord, tailWord_7331370, baseEnd_7331370] using wordTrace_append hprefix tailTrace_7331370
  have hstable : (prefixWord ++ tailWord_7331370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331370).length < 2 ^ (prefixWord ++ tailWord_7331370).sum := by decide
  have hdescent : baseEnd_7331370 < baseStart_7331370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331404 : List Nat := [2, 2, 1, 3, 1, 5, 2, 1, 1, 1, 4]
def baseStart_7331404 : Nat := 118140960795 + 7331404 * 2 ^ 59
def prefixEnd_7331404 : Nat := 4983230072969 + 3 ^ 40 * 7331404 * 2
def baseEnd_7331404 : Nat := 3764534124295339081833493

theorem tailTrace_7331404 : CollatzResearch.WordTrace tailWord_7331404 prefixEnd_7331404 3764534124295339081833493 := by
  unfold tailWord_7331404
  simp only [CollatzResearch.WordTrace]
  refine ⟨133699135765791443481604633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178265514354388591308806177 133699135765791443481604633)
  ·
    refine ⟨100274351824343582611203475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133699135765791443481604633 100274351824343582611203475)
    ·
      refine ⟨150411527736515373916805213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100274351824343582611203475 150411527736515373916805213)
      ·
        refine ⟨56404322901193265218801955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150411527736515373916805213 56404322901193265218801955)
        ·
          refine ⟨84606484351789897828202933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56404322901193265218801955 84606484351789897828202933)
          ·
            refine ⟨7931857907980302921394025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84606484351789897828202933 7931857907980302921394025)
            ·
              refine ⟨5948893430985227191045519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7931857907980302921394025 5948893430985227191045519)
              ·
                refine ⟨8923340146477840786568279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5948893430985227191045519 8923340146477840786568279)
                ·
                  refine ⟨13385010219716761179852419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8923340146477840786568279 13385010219716761179852419)
                  ·
                    refine ⟨20077515329575141769778629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13385010219716761179852419 20077515329575141769778629)
                    ·
                      refine ⟨3764534124295339081833493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20077515329575141769778629 3764534124295339081833493)
                      ·
                        rfl

theorem cell23_7331404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 1, 1, 1, 4].length) (baseStart_7331404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331404 prefixEnd_7331404 := by exact prefixLift 7331404
  have htrace : WordTrace (prefixWord ++ tailWord_7331404) baseStart_7331404 baseEnd_7331404 := by
    simpa [prefixWord, tailWord_7331404, baseEnd_7331404] using wordTrace_append hprefix tailTrace_7331404
  have hstable : (prefixWord ++ tailWord_7331404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331404).length < 2 ^ (prefixWord ++ tailWord_7331404).sum := by decide
  have hdescent : baseEnd_7331404 < baseStart_7331404 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331413 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 6]
def baseStart_7331413 : Nat := 118140960795 + 7331413 * 2 ^ 59
def prefixEnd_7331413 : Nat := 4983230072969 + 3 ^ 40 * 7331413 * 2
def baseEnd_7331413 : Nat := 3764538745621229546620951

theorem tailTrace_7331413 : CollatzResearch.WordTrace tailWord_7331413 prefixEnd_7331413 3764538745621229546620951 := by
  unfold tailWord_7331413
  simp only [CollatzResearch.WordTrace]
  refine ⟨267398599788550281500286893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178265733192366854333524595 267398599788550281500286893)
  ·
    refine ⟨100274474920706355562607585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267398599788550281500286893 100274474920706355562607585)
    ·
      refine ⟨75205856190529766671955689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100274474920706355562607585 75205856190529766671955689)
      ·
        refine ⟨56404392142897325003966767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75205856190529766671955689 56404392142897325003966767)
        ·
          refine ⟨84606588214345987505950151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56404392142897325003966767 84606588214345987505950151)
          ·
            refine ⟨126909882321518981258925227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84606588214345987505950151 126909882321518981258925227)
            ·
              refine ⟨190364823482278471888387841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126909882321518981258925227 190364823482278471888387841)
              ·
                refine ⟨142773617611708853916290881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190364823482278471888387841 142773617611708853916290881)
                ·
                  refine ⟨107080213208781640437218161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142773617611708853916290881 107080213208781640437218161)
                  ·
                    refine ⟨80310159906586230327913621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 107080213208781640437218161 80310159906586230327913621)
                    ·
                      refine ⟨3764538745621229546620951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80310159906586230327913621 3764538745621229546620951)
                      ·
                        rfl

theorem cell23_7331413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_7331413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331413 prefixEnd_7331413 := by exact prefixLift 7331413
  have htrace : WordTrace (prefixWord ++ tailWord_7331413) baseStart_7331413 baseEnd_7331413 := by
    simpa [prefixWord, tailWord_7331413, baseEnd_7331413] using wordTrace_append hprefix tailTrace_7331413
  have hstable : (prefixWord ++ tailWord_7331413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331413).length < 2 ^ (prefixWord ++ tailWord_7331413).sum := by decide
  have hdescent : baseEnd_7331413 < baseStart_7331413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331443 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 4]
def baseStart_7331443 : Nat := 118140960795 + 7331443 * 2 ^ 59
def prefixEnd_7331443 : Nat := 4983230072969 + 3 ^ 40 * 7331443 * 2
def baseEnd_7331443 : Nat := 3764554150040864429245813

theorem tailTrace_7331443 : CollatzResearch.WordTrace tailWord_7331443 prefixEnd_7331443 3764554150040864429245813 := by
  unfold tailWord_7331443
  simp only [CollatzResearch.WordTrace]
  refine ⟨267399693978441596623878983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178266462652294397749252655 267399693978441596623878983)
  ·
    refine ⟨401099540967662394935818475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267399693978441596623878983 401099540967662394935818475)
    ·
      refine ⟨601649311451493592403727713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401099540967662394935818475 601649311451493592403727713)
      ·
        refine ⟨451236983588620194302795785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601649311451493592403727713 451236983588620194302795785)
        ·
          refine ⟨338427737691465145727096839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451236983588620194302795785 338427737691465145727096839)
          ·
            refine ⟨507641606537197718590645259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338427737691465145727096839 507641606537197718590645259)
            ·
              refine ⟨761462409805796577885967889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507641606537197718590645259 761462409805796577885967889)
              ·
                refine ⟨571096807354347433414475917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761462409805796577885967889 571096807354347433414475917)
                ·
                  refine ⟨214161302757880287530428469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 571096807354347433414475917 214161302757880287530428469)
                  ·
                    refine ⟨20077622133551276955977669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 214161302757880287530428469 20077622133551276955977669)
                    ·
                      refine ⟨3764554150040864429245813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20077622133551276955977669 3764554150040864429245813)
                      ·
                        rfl

theorem cell23_7331443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 4].length) (baseStart_7331443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331443 prefixEnd_7331443 := by exact prefixLift 7331443
  have htrace : WordTrace (prefixWord ++ tailWord_7331443) baseStart_7331443 baseEnd_7331443 := by
    simpa [prefixWord, tailWord_7331443, baseEnd_7331443] using wordTrace_append hprefix tailTrace_7331443
  have hstable : (prefixWord ++ tailWord_7331443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331443).length < 2 ^ (prefixWord ++ tailWord_7331443).sum := by decide
  have hdescent : baseEnd_7331443 < baseStart_7331443 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331473 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 6]
def baseStart_7331473 : Nat := 118140960795 + 7331473 * 2 ^ 59
def prefixEnd_7331473 : Nat := 4983230072969 + 3 ^ 40 * 7331473 * 2
def baseEnd_7331473 : Nat := 3764569554460499311870675

theorem tailTrace_7331473 : CollatzResearch.WordTrace tailWord_7331473 prefixEnd_7331473 3764569554460499311870675 := by
  unfold tailWord_7331473
  simp only [CollatzResearch.WordTrace]
  refine ⟨267400788168332911747471073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178267192112221941164980715 267400788168332911747471073)
  ·
    refine ⟨200550591126249683810603305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267400788168332911747471073 200550591126249683810603305)
    ·
      refine ⟨150412943344687262857952479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200550591126249683810603305 150412943344687262857952479)
      ·
        refine ⟨225619415017030894286928719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150412943344687262857952479 225619415017030894286928719)
        ·
          refine ⟨338429122525546341430393079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225619415017030894286928719 338429122525546341430393079)
          ·
            refine ⟨507643683788319512145589619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338429122525546341430393079 507643683788319512145589619)
            ·
              refine ⟨761465525682479268218384429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507643683788319512145589619 761465525682479268218384429)
              ·
                refine ⟨285549572130929725581894161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 761465525682479268218384429 285549572130929725581894161)
                ·
                  refine ⟨214162179098197294186420621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285549572130929725581894161 214162179098197294186420621)
                  ·
                    refine ⟨80310817161823985319907733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214162179098197294186420621 80310817161823985319907733)
                    ·
                      refine ⟨3764569554460499311870675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80310817161823985319907733 3764569554460499311870675)
                      ·
                        rfl

theorem cell23_7331473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 6].length) (baseStart_7331473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331473 prefixEnd_7331473 := by exact prefixLift 7331473
  have htrace : WordTrace (prefixWord ++ tailWord_7331473) baseStart_7331473 baseEnd_7331473 := by
    simpa [prefixWord, tailWord_7331473, baseEnd_7331473] using wordTrace_append hprefix tailTrace_7331473
  have hstable : (prefixWord ++ tailWord_7331473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331473).length < 2 ^ (prefixWord ++ tailWord_7331473).sum := by decide
  have hdescent : baseEnd_7331473 < baseStart_7331473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331517 : List Nat := [1, 4, 1, 2, 1, 2, 2, 5, 5]
def baseStart_7331517 : Nat := 118140960795 + 7331517 * 2 ^ 59
def prefixEnd_7331517 : Nat := 4983230072969 + 3 ^ 40 * 7331517 * 2
def baseEnd_7331517 : Nat := 418288016401033015524497

theorem tailTrace_7331517 : CollatzResearch.WordTrace tailWord_7331517 prefixEnd_7331517 418288016401033015524497 := by
  unfold tailWord_7331517
  simp only [CollatzResearch.WordTrace]
  refine ⟨267402392980173507262072805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178268261986782338174715203 267402392980173507262072805)
  ·
    refine ⟨50137948683782532611638651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267402392980173507262072805 50137948683782532611638651)
    ·
      refine ⟨75206923025673798917457977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50137948683782532611638651 75206923025673798917457977)
      ·
        refine ⟨56405192269255349188093483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75206923025673798917457977 56405192269255349188093483)
        ·
          refine ⟨84607788403883023782140225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56405192269255349188093483 84607788403883023782140225)
          ·
            refine ⟨63455841302912267836605169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84607788403883023782140225 63455841302912267836605169)
            ·
              refine ⟨47591880977184200877453877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63455841302912267836605169 47591880977184200877453877)
              ·
                refine ⟨4461738841611018832261301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47591880977184200877453877 4461738841611018832261301)
                ·
                  refine ⟨418288016401033015524497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4461738841611018832261301 418288016401033015524497)
                  ·
                    rfl

theorem cell23_7331517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_7331517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331517 prefixEnd_7331517 := by exact prefixLift 7331517
  have htrace : WordTrace (prefixWord ++ tailWord_7331517) baseStart_7331517 baseEnd_7331517 := by
    simpa [prefixWord, tailWord_7331517, baseEnd_7331517] using wordTrace_append hprefix tailTrace_7331517
  have hstable : (prefixWord ++ tailWord_7331517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331517).length < 2 ^ (prefixWord ++ tailWord_7331517).sum := by decide
  have hdescent : baseEnd_7331517 < baseStart_7331517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331537 : List Nat := [1, 2, 2, 1, 2, 4, 1, 1, 2, 5, 2]
def baseStart_7331537 : Nat := 118140960795 + 7331537 * 2 ^ 59
def prefixEnd_7331537 : Nat := 4983230072969 + 3 ^ 40 * 7331537 * 2
def baseEnd_7331537 : Nat := 3764602417222387061470381

theorem tailTrace_7331537 : CollatzResearch.WordTrace tailWord_7331537 prefixEnd_7331537 3764602417222387061470381 := by
  unfold tailWord_7331537
  simp only [CollatzResearch.WordTrace]
  refine ⟨267403122440101050677800865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178268748293400700451867243 267403122440101050677800865)
  ·
    refine ⟨200552341830075788008350649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267403122440101050677800865 200552341830075788008350649)
    ·
      refine ⟨150414256372556841006262987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200552341830075788008350649 150414256372556841006262987)
      ·
        refine ⟨225621384558835261509394481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150414256372556841006262987 225621384558835261509394481)
        ·
          refine ⟨169216038419126446132045861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225621384558835261509394481 169216038419126446132045861)
          ·
            refine ⟨31728007203586208649758599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169216038419126446132045861 31728007203586208649758599)
            ·
              refine ⟨47592010805379312974637899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31728007203586208649758599 47592010805379312974637899)
              ·
                refine ⟨71388016208068969461956849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47592010805379312974637899 71388016208068969461956849)
                ·
                  refine ⟨53541012156051727096467637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71388016208068969461956849 53541012156051727096467637)
                  ·
                    refine ⟨5019469889629849415293841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53541012156051727096467637 5019469889629849415293841)
                    ·
                      refine ⟨3764602417222387061470381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019469889629849415293841 3764602417222387061470381)
                      ·
                        rfl

theorem cell23_7331537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 5, 2].length) (baseStart_7331537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331537 prefixEnd_7331537 := by exact prefixLift 7331537
  have htrace : WordTrace (prefixWord ++ tailWord_7331537) baseStart_7331537 baseEnd_7331537 := by
    simpa [prefixWord, tailWord_7331537, baseEnd_7331537] using wordTrace_append hprefix tailTrace_7331537
  have hstable : (prefixWord ++ tailWord_7331537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331537).length < 2 ^ (prefixWord ++ tailWord_7331537).sum := by decide
  have hdescent : baseEnd_7331537 < baseStart_7331537 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331567 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 1, 6, 2]
def baseStart_7331567 : Nat := 118140960795 + 7331567 * 2 ^ 59
def prefixEnd_7331567 : Nat := 4983230072969 + 3 ^ 40 * 7331567 * 2
def baseEnd_7331567 : Nat := 3764617821642021944095243

theorem tailTrace_7331567 : CollatzResearch.WordTrace tailWord_7331567 prefixEnd_7331567 3764617821642021944095243 := by
  unfold tailWord_7331567
  simp only [CollatzResearch.WordTrace]
  refine ⟨267404216629992365801392955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178269477753328243867595303 267404216629992365801392955)
  ·
    refine ⟨401106324944988548702089433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267404216629992365801392955 401106324944988548702089433)
    ·
      refine ⟨300829743708741411526567075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401106324944988548702089433 300829743708741411526567075)
      ·
        refine ⟨451244615563112117289850613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300829743708741411526567075 451244615563112117289850613)
        ·
          refine ⟨42304182709041760995923495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 451244615563112117289850613 42304182709041760995923495)
          ·
            refine ⟨63456274063562641493885243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42304182709041760995923495 63456274063562641493885243)
            ·
              refine ⟨95184411095343962240827865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63456274063562641493885243 95184411095343962240827865)
              ·
                refine ⟨71388308321507971680620899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95184411095343962240827865 71388308321507971680620899)
                ·
                  refine ⟨107082462482261957520931349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71388308321507971680620899 107082462482261957520931349)
                  ·
                    refine ⟨5019490428856029258793657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107082462482261957520931349 5019490428856029258793657)
                    ·
                      refine ⟨3764617821642021944095243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019490428856029258793657 3764617821642021944095243)
                      ·
                        rfl

theorem cell23_7331567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 1, 6, 2].length) (baseStart_7331567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331567 prefixEnd_7331567 := by exact prefixLift 7331567
  have htrace : WordTrace (prefixWord ++ tailWord_7331567) baseStart_7331567 baseEnd_7331567 := by
    simpa [prefixWord, tailWord_7331567, baseEnd_7331567] using wordTrace_append hprefix tailTrace_7331567
  have hstable : (prefixWord ++ tailWord_7331567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331567).length < 2 ^ (prefixWord ++ tailWord_7331567).sum := by decide
  have hdescent : baseEnd_7331567 < baseStart_7331567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331580 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 1, 3, 6]
def baseStart_7331580 : Nat := 118140960795 + 7331580 * 2 ^ 59
def prefixEnd_7331580 : Nat := 4983230072969 + 3 ^ 40 * 7331580 * 2
def baseEnd_7331580 : Nat := 3764624496890530393232683

theorem tailTrace_7331580 : CollatzResearch.WordTrace tailWord_7331580 prefixEnd_7331580 3764624496890530393232683 := by
  unfold tailWord_7331580
  simp only [CollatzResearch.WordTrace]
  refine ⟨133702345389472634510808097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178269793852630179347744129 133702345389472634510808097)
  ·
    refine ⟨100276759042104475883106073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133702345389472634510808097 100276759042104475883106073)
    ·
      refine ⟨75207569281578356912329555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100276759042104475883106073 75207569281578356912329555)
      ·
        refine ⟨112811353922367535368494333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75207569281578356912329555 112811353922367535368494333)
        ·
          refine ⟨42304257720887825763185375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 112811353922367535368494333 42304257720887825763185375)
          ·
            refine ⟨63456386581331738644778063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42304257720887825763185375 63456386581331738644778063)
            ·
              refine ⟨95184579871997607967167095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63456386581331738644778063 95184579871997607967167095)
              ·
                refine ⟨142776869807996411950750643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95184579871997607967167095 142776869807996411950750643)
                ·
                  refine ⟨214165304711994617926125965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142776869807996411950750643 214165304711994617926125965)
                  ·
                    refine ⟨80311989266997981722297237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 214165304711994617926125965 80311989266997981722297237)
                    ·
                      refine ⟨3764624496890530393232683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80311989266997981722297237 3764624496890530393232683)
                      ·
                        rfl

theorem cell23_7331580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_7331580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331580 prefixEnd_7331580 := by exact prefixLift 7331580
  have htrace : WordTrace (prefixWord ++ tailWord_7331580) baseStart_7331580 baseEnd_7331580 := by
    simpa [prefixWord, tailWord_7331580, baseEnd_7331580] using wordTrace_append hprefix tailTrace_7331580
  have hstable : (prefixWord ++ tailWord_7331580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331580).length < 2 ^ (prefixWord ++ tailWord_7331580).sum := by decide
  have hdescent : baseEnd_7331580 < baseStart_7331580 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331587 : List Nat := [1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 3]
def baseStart_7331587 : Nat := 118140960795 + 7331587 * 2 ^ 59
def prefixEnd_7331587 : Nat := 4983230072969 + 3 ^ 40 * 7331587 * 2
def baseEnd_7331587 : Nat := 3764628091255111865845151

theorem tailTrace_7331587 : CollatzResearch.WordTrace tailWord_7331587 prefixEnd_7331587 3764628091255111865845151 := by
  unfold tailWord_7331587
  simp only [CollatzResearch.WordTrace]
  refine ⟨267404946089919909217121015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178269964059946606144747343 267404946089919909217121015)
  ·
    refine ⟨401107419134879863825681523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267404946089919909217121015 401107419134879863825681523)
    ·
      refine ⟨601661128702319795738522285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401107419134879863825681523 601661128702319795738522285)
      ·
        refine ⟨225622923263369923401945857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601661128702319795738522285 225622923263369923401945857)
        ·
          refine ⟨169217192447527442551459393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225622923263369923401945857 169217192447527442551459393)
          ·
            refine ⟨126912894335645581913594545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169217192447527442551459393 126912894335645581913594545)
            ·
              refine ⟨95184670751734186435195909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126912894335645581913594545 95184670751734186435195909)
              ·
                refine ⟨17847125765950159956599233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95184670751734186435195909 17847125765950159956599233)
                ·
                  refine ⟨13385344324462619967449425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17847125765950159956599233 13385344324462619967449425)
                  ·
                    refine ⟨10039008243346964975587069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13385344324462619967449425 10039008243346964975587069)
                    ·
                      refine ⟨3764628091255111865845151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10039008243346964975587069 3764628091255111865845151)
                      ·
                        rfl

theorem cell23_7331587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 2, 3].length) (baseStart_7331587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331587 prefixEnd_7331587 := by exact prefixLift 7331587
  have htrace : WordTrace (prefixWord ++ tailWord_7331587) baseStart_7331587 baseEnd_7331587 := by
    simpa [prefixWord, tailWord_7331587, baseEnd_7331587] using wordTrace_append hprefix tailTrace_7331587
  have hstable : (prefixWord ++ tailWord_7331587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331587).length < 2 ^ (prefixWord ++ tailWord_7331587).sum := by decide
  have hdescent : baseEnd_7331587 < baseStart_7331587 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331594 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 3, 4]
def baseStart_7331594 : Nat := 118140960795 + 7331594 * 2 ^ 59
def prefixEnd_7331594 : Nat := 4983230072969 + 3 ^ 40 * 7331594 * 2
def baseEnd_7331594 : Nat := 1254877228539897779485873

theorem tailTrace_7331594 : CollatzResearch.WordTrace tailWord_7331594 prefixEnd_7331594 1254877228539897779485873 := by
  unfold tailWord_7331594
  simp only [CollatzResearch.WordTrace]
  refine ⟨66851300350223637353156459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178270134267263032941750557 66851300350223637353156459)
  ·
    refine ⟨100276950525335456029734689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66851300350223637353156459 100276950525335456029734689)
    ·
      refine ⟨75207712894001592022301017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100276950525335456029734689 75207712894001592022301017)
      ·
        refine ⟨56405784670501194016725763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75207712894001592022301017 56405784670501194016725763)
        ·
          refine ⟨84608677005751791025088645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56405784670501194016725763 84608677005751791025088645)
          ·
            refine ⟨15864126938578460817204121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84608677005751791025088645 15864126938578460817204121)
            ·
              refine ⟨11898095203933845612903091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15864126938578460817204121 11898095203933845612903091)
              ·
                refine ⟨17847142805900768419354637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11898095203933845612903091 17847142805900768419354637)
                ·
                  refine ⟨6692678552212788157257989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17847142805900768419354637 6692678552212788157257989)
                  ·
                    refine ⟨1254877228539897779485873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6692678552212788157257989 1254877228539897779485873)
                    ·
                      rfl

theorem cell23_7331594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 3, 4].length) (baseStart_7331594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331594 prefixEnd_7331594 := by exact prefixLift 7331594
  have htrace : WordTrace (prefixWord ++ tailWord_7331594) baseStart_7331594 baseEnd_7331594 := by
    simpa [prefixWord, tailWord_7331594, baseEnd_7331594] using wordTrace_append hprefix tailTrace_7331594
  have hstable : (prefixWord ++ tailWord_7331594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331594).length < 2 ^ (prefixWord ++ tailWord_7331594).sum := by decide
  have hdescent : baseEnd_7331594 < baseStart_7331594 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331627 : List Nat := [1, 1, 1, 1, 2, 1, 2, 2, 5, 5, 2]
def baseStart_7331627 : Nat := 118140960795 + 7331627 * 2 ^ 59
def prefixEnd_7331627 : Nat := 4983230072969 + 3 ^ 40 * 7331627 * 2
def baseEnd_7331627 : Nat := 3764648630481291709344967

theorem tailTrace_7331627 : CollatzResearch.WordTrace tailWord_7331627 prefixEnd_7331627 3764648630481291709344967 := by
  unfold tailWord_7331627
  simp only [CollatzResearch.WordTrace]
  refine ⟨267406405009774996048577135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178270936673183330699051423 267406405009774996048577135)
  ·
    refine ⟨401109607514662494072865703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267406405009774996048577135 401109607514662494072865703)
    ·
      refine ⟨601664411271993741109298555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401109607514662494072865703 601664411271993741109298555)
      ·
        refine ⟨902496616907990611663947833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601664411271993741109298555 902496616907990611663947833)
        ·
          refine ⟨676872462680992958747960875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 902496616907990611663947833 676872462680992958747960875)
          ·
            refine ⟨1015308694021489438121941313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676872462680992958747960875 1015308694021489438121941313)
            ·
              refine ⟨761481520516117078591455985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015308694021489438121941313 761481520516117078591455985)
              ·
                refine ⟨571111140387087808943591989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761481520516117078591455985 571111140387087808943591989)
                ·
                  refine ⟨53541669411289482088461749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 571111140387087808943591989 53541669411289482088461749)
                  ·
                    refine ⟨5019531507308388945793289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53541669411289482088461749 5019531507308388945793289)
                    ·
                      refine ⟨3764648630481291709344967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019531507308388945793289 3764648630481291709344967)
                      ·
                        rfl

theorem cell23_7331627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 2, 5, 5, 2].length) (baseStart_7331627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331627 prefixEnd_7331627 := by exact prefixLift 7331627
  have htrace : WordTrace (prefixWord ++ tailWord_7331627) baseStart_7331627 baseEnd_7331627 := by
    simpa [prefixWord, tailWord_7331627, baseEnd_7331627] using wordTrace_append hprefix tailTrace_7331627
  have hstable : (prefixWord ++ tailWord_7331627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331627).length < 2 ^ (prefixWord ++ tailWord_7331627).sum := by decide
  have hdescent : baseEnd_7331627 < baseStart_7331627 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331644 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 4, 3, 2]
def baseStart_7331644 : Nat := 118140960795 + 7331644 * 2 ^ 59
def prefixEnd_7331644 : Nat := 4983230072969 + 3 ^ 40 * 7331644 * 2
def baseEnd_7331644 : Nat := 3764657359652418142832389

theorem tailTrace_7331644 : CollatzResearch.WordTrace tailWord_7331644 prefixEnd_7331644 3764657359652418142832389 := by
  unfold tailWord_7331644
  simp only [CollatzResearch.WordTrace]
  refine ⟨133703512525356703975972993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178271350033808938634630657 133703512525356703975972993)
  ·
    refine ⟨100277634394017527981979745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133703512525356703975972993 100277634394017527981979745)
    ·
      refine ⟨75208225795513145986484809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100277634394017527981979745 75208225795513145986484809)
      ·
        refine ⟨56406169346634859489863607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75208225795513145986484809 56406169346634859489863607)
        ·
          refine ⟨84609254019952289234795411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56406169346634859489863607 84609254019952289234795411)
          ·
            refine ⟨126913881029928433852193117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84609254019952289234795411 126913881029928433852193117)
            ·
              refine ⟨47592705386223162694572419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126913881029928433852193117 47592705386223162694572419)
              ·
                refine ⟨71389058079334744041858629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47592705386223162694572419 71389058079334744041858629)
                ·
                  refine ⟨13385448389875264507848493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71389058079334744041858629 13385448389875264507848493)
                  ·
                    refine ⟨5019543146203224190443185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13385448389875264507848493 5019543146203224190443185)
                    ·
                      refine ⟨3764657359652418142832389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019543146203224190443185 3764657359652418142832389)
                      ·
                        rfl

theorem cell23_7331644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 4, 3, 2].length) (baseStart_7331644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331644 prefixEnd_7331644 := by exact prefixLift 7331644
  have htrace : WordTrace (prefixWord ++ tailWord_7331644) baseStart_7331644 baseEnd_7331644 := by
    simpa [prefixWord, tailWord_7331644, baseEnd_7331644] using wordTrace_append hprefix tailTrace_7331644
  have hstable : (prefixWord ++ tailWord_7331644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331644).length < 2 ^ (prefixWord ++ tailWord_7331644).sum := by decide
  have hdescent : baseEnd_7331644 < baseStart_7331644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331651 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 3]
def baseStart_7331651 : Nat := 118140960795 + 7331651 * 2 ^ 59
def prefixEnd_7331651 : Nat := 4983230072969 + 3 ^ 40 * 7331651 * 2
def baseEnd_7331651 : Nat := 3764660954016999615444857

theorem tailTrace_7331651 : CollatzResearch.WordTrace tailWord_7331651 prefixEnd_7331651 3764660954016999615444857 := by
  unfold tailWord_7331651
  simp only [CollatzResearch.WordTrace]
  refine ⟨267407280361688048147450807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178271520241125365431633871 267407280361688048147450807)
  ·
    refine ⟨401110920542532072221176211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267407280361688048147450807 401110920542532072221176211)
    ·
      refine ⟨601666380813798108331764317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401110920542532072221176211 601666380813798108331764317)
      ·
        refine ⟨225624892805174290624411619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601666380813798108331764317 225624892805174290624411619)
        ·
          refine ⟨338437339207761435936617429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225624892805174290624411619 338437339207761435936617429)
          ·
            refine ⟨7932125137681908654764471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 338437339207761435936617429 7932125137681908654764471)
            ·
              refine ⟨11898187706522862982146707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932125137681908654764471 11898187706522862982146707)
              ·
                refine ⟨17847281559784294473220061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11898187706522862982146707 17847281559784294473220061)
                ·
                  refine ⟨6692730584919110427457523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17847281559784294473220061 6692730584919110427457523)
                  ·
                    refine ⟨10039095877378665641186285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6692730584919110427457523 10039095877378665641186285)
                    ·
                      refine ⟨3764660954016999615444857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10039095877378665641186285 3764660954016999615444857)
                      ·
                        rfl

theorem cell23_7331651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 1, 3].length) (baseStart_7331651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331651 prefixEnd_7331651 := by exact prefixLift 7331651
  have htrace : WordTrace (prefixWord ++ tailWord_7331651) baseStart_7331651 baseEnd_7331651 := by
    simpa [prefixWord, tailWord_7331651, baseEnd_7331651] using wordTrace_append hprefix tailTrace_7331651
  have hstable : (prefixWord ++ tailWord_7331651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331651).length < 2 ^ (prefixWord ++ tailWord_7331651).sum := by decide
  have hdescent : baseEnd_7331651 < baseStart_7331651 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331657 : List Nat := [1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 4]
def baseStart_7331657 : Nat := 118140960795 + 7331657 * 2 ^ 59
def prefixEnd_7331657 : Nat := 4983230072969 + 3 ^ 40 * 7331657 * 2
def baseEnd_7331657 : Nat := 3764664034900926591969829

theorem tailTrace_7331657 : CollatzResearch.WordTrace tailWord_7331657 prefixEnd_7331657 3764664034900926591969829 := by
  unfold tailWord_7331657
  simp only [CollatzResearch.WordTrace]
  refine ⟨267407499199666311172169225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178271666133110874114779483 267407499199666311172169225)
  ·
    refine ⟨200555624399749733379126919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267407499199666311172169225 200555624399749733379126919)
    ·
      refine ⟨300833436599624600068690379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200555624399749733379126919 300833436599624600068690379)
      ·
        refine ⟨451250154899436900103035569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300833436599624600068690379 451250154899436900103035569)
        ·
          refine ⟨338437616174577675077276677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451250154899436900103035569 338437616174577675077276677)
          ·
            refine ⟨63457053032733314076989377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338437616174577675077276677 63457053032733314076989377)
            ·
              refine ⟨47592789774549985557742033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63457053032733314076989377 47592789774549985557742033)
              ·
                refine ⟨35694592330912489168306525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47592789774549985557742033 35694592330912489168306525)
                ·
                  refine ⟨13385472124092183438114947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35694592330912489168306525 13385472124092183438114947)
                  ·
                    refine ⟨20078208186138275157172421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13385472124092183438114947 20078208186138275157172421)
                    ·
                      refine ⟨3764664034900926591969829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20078208186138275157172421 3764664034900926591969829)
                      ·
                        rfl

theorem cell23_7331657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 4].length) (baseStart_7331657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331657 prefixEnd_7331657 := by exact prefixLift 7331657
  have htrace : WordTrace (prefixWord ++ tailWord_7331657) baseStart_7331657 baseEnd_7331657 := by
    simpa [prefixWord, tailWord_7331657, baseEnd_7331657] using wordTrace_append hprefix tailTrace_7331657
  have hstable : (prefixWord ++ tailWord_7331657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331657).length < 2 ^ (prefixWord ++ tailWord_7331657).sum := by decide
  have hdescent : baseEnd_7331657 < baseStart_7331657 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331671 : List Nat := [1, 1, 3, 2, 5, 2, 1, 2, 1, 5]
def baseStart_7331671 : Nat := 118140960795 + 7331671 * 2 ^ 59
def prefixEnd_7331671 : Nat := 4983230072969 + 3 ^ 40 * 7331671 * 2
def baseEnd_7331671 : Nat := 1254890407876696512398255

theorem tailTrace_7331671 : CollatzResearch.WordTrace tailWord_7331671 prefixEnd_7331671 1254890407876696512398255 := by
  unfold tailWord_7331671
  simp only [CollatzResearch.WordTrace]
  refine ⟨267408009821615591563178867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178272006547743727708785911 267408009821615591563178867)
  ·
    refine ⟨401112014732423387344768301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267408009821615591563178867 401112014732423387344768301)
    ·
      refine ⟨150417005524658770254288113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401112014732423387344768301 150417005524658770254288113)
      ·
        refine ⟨112812754143494077690716085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150417005524658770254288113 112812754143494077690716085)
        ·
          refine ⟨10576195700952569783504633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112812754143494077690716085 10576195700952569783504633)
          ·
            refine ⟨7932146775714427337628475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10576195700952569783504633 7932146775714427337628475)
            ·
              refine ⟨11898220163571641006442713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932146775714427337628475 11898220163571641006442713)
              ·
                refine ⟨8923665122678730754832035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11898220163571641006442713 8923665122678730754832035)
                ·
                  refine ⟨13385497684018096132248053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8923665122678730754832035 13385497684018096132248053)
                  ·
                    refine ⟨1254890407876696512398255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13385497684018096132248053 1254890407876696512398255)
                    ·
                      rfl

theorem cell23_7331671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 1, 5].length) (baseStart_7331671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331671 prefixEnd_7331671 := by exact prefixLift 7331671
  have htrace : WordTrace (prefixWord ++ tailWord_7331671) baseStart_7331671 baseEnd_7331671 := by
    simpa [prefixWord, tailWord_7331671, baseEnd_7331671] using wordTrace_append hprefix tailTrace_7331671
  have hstable : (prefixWord ++ tailWord_7331671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331671).length < 2 ^ (prefixWord ++ tailWord_7331671).sum := by decide
  have hdescent : baseEnd_7331671 < baseStart_7331671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331684 : List Nat := [2, 3, 1, 1, 5, 1, 1, 2, 1, 6]
def baseStart_7331684 : Nat := 118140960795 + 7331684 * 2 ^ 59
def prefixEnd_7331684 : Nat := 4983230072969 + 3 ^ 40 * 7331684 * 2
def baseEnd_7331684 : Nat := 1254892632959532662110735

theorem tailTrace_7331684 : CollatzResearch.WordTrace tailWord_7331684 prefixEnd_7331684 1254892632959532662110735 := by
  unfold tailWord_7331684
  simp only [CollatzResearch.WordTrace]
  refine ⟨133704241985284247391701053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178272322647045663188934737 133704241985284247391701053)
  ·
    refine ⟨50139090744481592771887895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133704241985284247391701053 50139090744481592771887895)
    ·
      refine ⟨75208636116722389157831843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50139090744481592771887895 75208636116722389157831843)
      ·
        refine ⟨112812954175083583736747765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75208636116722389157831843 112812954175083583736747765)
        ·
          refine ⟨10576214453914085975320103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 112812954175083583736747765 10576214453914085975320103)
          ·
            refine ⟨15864321680871128962980155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10576214453914085975320103 15864321680871128962980155)
            ·
              refine ⟨23796482521306693444470233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15864321680871128962980155 23796482521306693444470233)
              ·
                refine ⟨17847361890980020083352675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23796482521306693444470233 17847361890980020083352675)
                ·
                  refine ⟨26771042836470030125029013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17847361890980020083352675 26771042836470030125029013)
                  ·
                    refine ⟨1254892632959532662110735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26771042836470030125029013 1254892632959532662110735)
                    ·
                      rfl

theorem cell23_7331684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_7331684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331684 prefixEnd_7331684 := by exact prefixLift 7331684
  have htrace : WordTrace (prefixWord ++ tailWord_7331684) baseStart_7331684 baseEnd_7331684 := by
    simpa [prefixWord, tailWord_7331684, baseEnd_7331684] using wordTrace_append hprefix tailTrace_7331684
  have hstable : (prefixWord ++ tailWord_7331684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331684).length < 2 ^ (prefixWord ++ tailWord_7331684).sum := by decide
  have hdescent : baseEnd_7331684 < baseStart_7331684 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331701 : List Nat := [1, 3, 4, 1, 1, 1, 4, 2, 2, 4]
def baseStart_7331701 : Nat := 118140960795 + 7331701 * 2 ^ 59
def prefixEnd_7331701 : Nat := 4983230072969 + 3 ^ 40 * 7331701 * 2
def baseEnd_7331701 : Nat := 1254895542683241473273209

theorem tailTrace_7331701 : CollatzResearch.WordTrace tailWord_7331701 prefixEnd_7331701 1254895542683241473273209 := by
  unfold tailWord_7331701
  simp only [CollatzResearch.WordTrace]
  refine ⟨267409104011506906686770957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178272736007671271124513971 267409104011506906686770957)
  ·
    refine ⟨100278414004315090007539109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267409104011506906686770957 100278414004315090007539109)
    ·
      refine ⟨18802202625809079376413583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100278414004315090007539109 18802202625809079376413583)
      ·
        refine ⟨28203303938713619064620375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18802202625809079376413583 28203303938713619064620375)
        ·
          refine ⟨42304955908070428596930563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28203303938713619064620375 42304955908070428596930563)
          ·
            refine ⟨63457433862105642895395845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42304955908070428596930563 63457433862105642895395845)
            ·
              refine ⟨11898268849144808042886721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63457433862105642895395845 11898268849144808042886721)
              ·
                refine ⟨8923701636858606032165041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11898268849144808042886721 8923701636858606032165041)
                ·
                  refine ⟨6692776227643954524123781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8923701636858606032165041 6692776227643954524123781)
                  ·
                    refine ⟨1254895542683241473273209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6692776227643954524123781 1254895542683241473273209)
                    ·
                      rfl

theorem cell23_7331701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_7331701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331701 prefixEnd_7331701 := by exact prefixLift 7331701
  have htrace : WordTrace (prefixWord ++ tailWord_7331701) baseStart_7331701 baseEnd_7331701 := by
    simpa [prefixWord, tailWord_7331701, baseEnd_7331701] using wordTrace_append hprefix tailTrace_7331701
  have hstable : (prefixWord ++ tailWord_7331701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331701).length < 2 ^ (prefixWord ++ tailWord_7331701).sum := by decide
  have hdescent : baseEnd_7331701 < baseStart_7331701 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331707 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 3]
def baseStart_7331707 : Nat := 118140960795 + 7331707 * 2 ^ 59
def prefixEnd_7331707 : Nat := 4983230072969 + 3 ^ 40 * 7331707 * 2
def baseEnd_7331707 : Nat := 3764689708933651396344599

theorem tailTrace_7331707 : CollatzResearch.WordTrace tailWord_7331707 prefixEnd_7331707 3764689708933651396344599 := by
  unfold tailWord_7331707
  simp only [CollatzResearch.WordTrace]
  refine ⟨267409322849485169711489375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178272881899656779807659583 267409322849485169711489375)
  ·
    refine ⟨401113984274227754567234063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267409322849485169711489375 401113984274227754567234063)
    ·
      refine ⟨601670976411341631850851095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401113984274227754567234063 601670976411341631850851095)
      ·
        refine ⟨902506464617012447776276643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601670976411341631850851095 902506464617012447776276643)
        ·
          refine ⟨1353759696925518671664414965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902506464617012447776276643 1353759696925518671664414965)
          ·
            refine ⟨126914971586767375468538903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1353759696925518671664414965 126914971586767375468538903)
            ·
              refine ⟨190372457380151063202808355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126914971586767375468538903 190372457380151063202808355)
              ·
                refine ⟨285558686070226594804212533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190372457380151063202808355 285558686070226594804212533)
                ·
                  refine ⟨26771126819083743262894925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 285558686070226594804212533 26771126819083743262894925)
                  ·
                    refine ⟨10039172557156403723585597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26771126819083743262894925 10039172557156403723585597)
                    ·
                      refine ⟨3764689708933651396344599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10039172557156403723585597 3764689708933651396344599)
                      ·
                        rfl

theorem cell23_7331707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 3, 3].length) (baseStart_7331707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331707 prefixEnd_7331707 := by exact prefixLift 7331707
  have htrace : WordTrace (prefixWord ++ tailWord_7331707) baseStart_7331707 baseEnd_7331707 := by
    simpa [prefixWord, tailWord_7331707, baseEnd_7331707] using wordTrace_append hprefix tailTrace_7331707
  have hstable : (prefixWord ++ tailWord_7331707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331707).length < 2 ^ (prefixWord ++ tailWord_7331707).sum := by decide
  have hdescent : baseEnd_7331707 < baseStart_7331707 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331724 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 6, 1, 3]
def baseStart_7331724 : Nat := 118140960795 + 7331724 * 2 ^ 59
def prefixEnd_7331724 : Nat := 4983230072969 + 3 ^ 40 * 7331724 * 2
def baseEnd_7331724 : Nat := 3764698438104777829832021

theorem tailTrace_7331724 : CollatzResearch.WordTrace tailWord_7331724 prefixEnd_7331724 3764698438104777829832021 := by
  unfold tailWord_7331724
  simp only [CollatzResearch.WordTrace]
  refine ⟨133704971445211790807429113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178273295260282387743238817 133704971445211790807429113)
  ·
    refine ⟨100278728583908843105571835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133704971445211790807429113 100278728583908843105571835)
    ·
      refine ⟨150418092875863264658357753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100278728583908843105571835 150418092875863264658357753)
      ·
        refine ⟨112813569656897448493768315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150418092875863264658357753 112813569656897448493768315)
        ·
          refine ⟨169220354485346172740652473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112813569656897448493768315 169220354485346172740652473)
          ·
            refine ⟨126915265864009629555489355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169220354485346172740652473 126915265864009629555489355)
            ·
              refine ⟨190372898796014444333234033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126915265864009629555489355 190372898796014444333234033)
              ·
                refine ⟨142779674097010833249925525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190372898796014444333234033 142779674097010833249925525)
                ·
                  refine ⟨6692797223297382808590259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 142779674097010833249925525 6692797223297382808590259)
                  ·
                    refine ⟨10039195834946074212885389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6692797223297382808590259 10039195834946074212885389)
                    ·
                      refine ⟨3764698438104777829832021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10039195834946074212885389 3764698438104777829832021)
                      ·
                        rfl

theorem cell23_7331724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 6, 1, 3].length) (baseStart_7331724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331724 prefixEnd_7331724 := by exact prefixLift 7331724
  have htrace : WordTrace (prefixWord ++ tailWord_7331724) baseStart_7331724 baseEnd_7331724 := by
    simpa [prefixWord, tailWord_7331724, baseEnd_7331724] using wordTrace_append hprefix tailTrace_7331724
  have hstable : (prefixWord ++ tailWord_7331724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331724).length < 2 ^ (prefixWord ++ tailWord_7331724).sum := by decide
  have hdescent : baseEnd_7331724 < baseStart_7331724 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331742 : List Nat := [4, 3, 1, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_7331742 : Nat := 118140960795 + 7331742 * 2 ^ 59
def prefixEnd_7331742 : Nat := 4983230072969 + 3 ^ 40 * 7331742 * 2
def baseEnd_7331742 : Nat := 3764707680756558759406939

theorem tailTrace_7331742 : CollatzResearch.WordTrace tailWord_7331742 prefixEnd_7331742 3764707680756558759406939 := by
  unfold tailWord_7331742
  simp only [CollatzResearch.WordTrace]
  refine ⟨33426324925544796336126685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178273732936238913792675653 33426324925544796336126685)
  ·
    refine ⟨12534871847079298626047507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 33426324925544796336126685 12534871847079298626047507)
    ·
      refine ⟨18802307770618947939071261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12534871847079298626047507 18802307770618947939071261)
      ·
        refine ⟨7050865413982105477151723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18802307770618947939071261 7050865413982105477151723)
        ·
          refine ⟨10576298120973158215727585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7050865413982105477151723 10576298120973158215727585)
          ·
            refine ⟨7932223590729868661795689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10576298120973158215727585 7932223590729868661795689)
            ·
              refine ⟨5949167693047401496346767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7932223590729868661795689 5949167693047401496346767)
              ·
                refine ⟨8923751539571102244520151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5949167693047401496346767 8923751539571102244520151)
                ·
                  refine ⟨13385627309356653366780227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8923751539571102244520151 13385627309356653366780227)
                  ·
                    refine ⟨20078440964034980050170341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13385627309356653366780227 20078440964034980050170341)
                    ·
                      refine ⟨3764707680756558759406939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20078440964034980050170341 3764707680756558759406939)
                      ·
                        rfl

theorem cell23_7331742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_7331742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331742 prefixEnd_7331742 := by exact prefixLift 7331742
  have htrace : WordTrace (prefixWord ++ tailWord_7331742) baseStart_7331742 baseEnd_7331742 := by
    simpa [prefixWord, tailWord_7331742, baseEnd_7331742] using wordTrace_append hprefix tailTrace_7331742
  have hstable : (prefixWord ++ tailWord_7331742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331742).length < 2 ^ (prefixWord ++ tailWord_7331742).sum := by decide
  have hdescent : baseEnd_7331742 < baseStart_7331742 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331745 : List Nat := [1, 2, 3, 4, 2, 2, 2, 1, 1, 2, 3]
def baseStart_7331745 : Nat := 118140960795 + 7331745 * 2 ^ 59
def prefixEnd_7331745 : Nat := 4983230072969 + 3 ^ 40 * 7331745 * 2
def baseEnd_7331745 : Nat := 3764709221198522247669425

theorem tailTrace_7331745 : CollatzResearch.WordTrace tailWord_7331745 prefixEnd_7331745 3764709221198522247669425 := by
  unfold tailWord_7331745
  simp only [CollatzResearch.WordTrace]
  refine ⟨267410708823347502201372689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178273805882231668134248459 267410708823347502201372689)
  ·
    refine ⟨200558031617510626651029517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267410708823347502201372689 200558031617510626651029517)
    ·
      refine ⟨75209261856566484994136069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200558031617510626651029517 75209261856566484994136069)
      ·
        refine ⟨14101736598106215936400513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75209261856566484994136069 14101736598106215936400513)
        ·
          refine ⟨10576302448579661952300385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14101736598106215936400513 10576302448579661952300385)
          ·
            refine ⟨7932226836434746464225289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10576302448579661952300385 7932226836434746464225289)
            ·
              refine ⟨5949170127326059848168967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7932226836434746464225289 5949170127326059848168967)
              ·
                refine ⟨8923755190989089772253451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5949170127326059848168967 8923755190989089772253451)
                ·
                  refine ⟨13385632786483634658380177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8923755190989089772253451 13385632786483634658380177)
                  ·
                    refine ⟨10039224589862725993785133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13385632786483634658380177 10039224589862725993785133)
                    ·
                      refine ⟨3764709221198522247669425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10039224589862725993785133 3764709221198522247669425)
                      ·
                        rfl

theorem cell23_7331745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_7331745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331745 prefixEnd_7331745 := by exact prefixLift 7331745
  have htrace : WordTrace (prefixWord ++ tailWord_7331745) baseStart_7331745 baseEnd_7331745 := by
    simpa [prefixWord, tailWord_7331745, baseEnd_7331745] using wordTrace_append hprefix tailTrace_7331745
  have hstable : (prefixWord ++ tailWord_7331745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331745).length < 2 ^ (prefixWord ++ tailWord_7331745).sum := by decide
  have hdescent : baseEnd_7331745 < baseStart_7331745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331752 : List Nat := [2, 1, 6, 2, 2, 1, 1, 2, 2, 4]
def baseStart_7331752 : Nat := 118140960795 + 7331752 * 2 ^ 59
def prefixEnd_7331752 : Nat := 4983230072969 + 3 ^ 40 * 7331752 * 2
def baseEnd_7331752 : Nat := 1254904271854367906760631

theorem tailTrace_7331752 : CollatzResearch.WordTrace tailWord_7331752 prefixEnd_7331752 1254904271854367906760631 := by
  unfold tailWord_7331752
  simp only [CollatzResearch.WordTrace]
  refine ⟨133705482067161071198438755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178273976089548094931251673 133705482067161071198438755)
  ·
    refine ⟨200558223100741606797658133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133705482067161071198438755 200558223100741606797658133)
    ·
      refine ⟨9401166707847262818640225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 200558223100741606797658133 9401166707847262818640225)
      ·
        refine ⟨7050875030885447113980169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9401166707847262818640225 7050875030885447113980169)
        ·
          refine ⟨5288156273164085335485127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7050875030885447113980169 5288156273164085335485127)
          ·
            refine ⟨7932234409746128003227691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5288156273164085335485127 7932234409746128003227691)
            ·
              refine ⟨11898351614619192004841537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932234409746128003227691 11898351614619192004841537)
              ·
                refine ⟨8923763710964394003631153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11898351614619192004841537 8923763710964394003631153)
                ·
                  refine ⟨6692822783223295502723365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8923763710964394003631153 6692822783223295502723365)
                  ·
                    refine ⟨1254904271854367906760631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6692822783223295502723365 1254904271854367906760631)
                    ·
                      rfl

theorem cell23_7331752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_7331752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331752 prefixEnd_7331752 := by exact prefixLift 7331752
  have htrace : WordTrace (prefixWord ++ tailWord_7331752) baseStart_7331752 baseEnd_7331752 := by
    simpa [prefixWord, tailWord_7331752, baseEnd_7331752] using wordTrace_append hprefix tailTrace_7331752
  have hstable : (prefixWord ++ tailWord_7331752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331752).length < 2 ^ (prefixWord ++ tailWord_7331752).sum := by decide
  have hdescent : baseEnd_7331752 < baseStart_7331752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331767 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 5]
def baseStart_7331767 : Nat := 118140960795 + 7331767 * 2 ^ 59
def prefixEnd_7331767 : Nat := 4983230072969 + 3 ^ 40 * 7331767 * 2
def baseEnd_7331767 : Nat := 3764720517772921161594323

theorem tailTrace_7331767 : CollatzResearch.WordTrace tailWord_7331767 prefixEnd_7331767 3764720517772921161594323 := by
  unfold tailWord_7331767
  simp only [CollatzResearch.WordTrace]
  refine ⟨267411511229267799958673555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178274340819511866639115703 267411511229267799958673555)
  ·
    refine ⟨401117266843901699938010333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267411511229267799958673555 401117266843901699938010333)
    ·
      refine ⟨150418975066463137476753875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401117266843901699938010333 150418975066463137476753875)
      ·
        refine ⟨225628462599694706215130813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150418975066463137476753875 225628462599694706215130813)
        ·
          refine ⟨84610673474885514830674055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225628462599694706215130813 84610673474885514830674055)
          ·
            refine ⟨126916010212328272246011083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84610673474885514830674055 126916010212328272246011083)
            ·
              refine ⟨190374015318492408369016625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126916010212328272246011083 190374015318492408369016625)
              ·
                refine ⟨142780511488869306276762469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190374015318492408369016625 142780511488869306276762469)
                ·
                  refine ⟨26771345904162994926892963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142780511488869306276762469 26771345904162994926892963)
                  ·
                    refine ⟨40157018856244492390339445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26771345904162994926892963 40157018856244492390339445)
                    ·
                      refine ⟨3764720517772921161594323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40157018856244492390339445 3764720517772921161594323)
                      ·
                        rfl

theorem cell23_7331767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 1, 5].length) (baseStart_7331767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331767 prefixEnd_7331767 := by exact prefixLift 7331767
  have htrace : WordTrace (prefixWord ++ tailWord_7331767) baseStart_7331767 baseEnd_7331767 := by
    simpa [prefixWord, tailWord_7331767, baseEnd_7331767] using wordTrace_append hprefix tailTrace_7331767
  have hstable : (prefixWord ++ tailWord_7331767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331767).length < 2 ^ (prefixWord ++ tailWord_7331767).sum := by decide
  have hdescent : baseEnd_7331767 < baseStart_7331767 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331774 : List Nat := [4, 2, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_7331774 : Nat := 118140960795 + 7331774 * 2 ^ 59
def prefixEnd_7331774 : Nat := 4983230072969 + 3 ^ 40 * 7331774 * 2
def baseEnd_7331774 : Nat := 1254908037379167544735597

theorem tailTrace_7331774 : CollatzResearch.WordTrace tailWord_7331774 prefixEnd_7331774 1254908037379167544735597 := by
  unfold tailWord_7331774
  simp only [CollatzResearch.WordTrace]
  refine ⟨33426470817530305019272297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178274511026828293436118917 33426470817530305019272297)
  ·
    refine ⟨25069853113147728764454223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 33426470817530305019272297 25069853113147728764454223)
    ·
      refine ⟨37604779669721593146681335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25069853113147728764454223 37604779669721593146681335)
      ·
        refine ⟨56407169504582389720022003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37604779669721593146681335 56407169504582389720022003)
        ·
          refine ⟨84610754256873584580033005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56407169504582389720022003 84610754256873584580033005)
          ·
            refine ⟨31729032846327594217512377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84610754256873584580033005 31729032846327594217512377)
            ·
              refine ⟨23796774634745695663134283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31729032846327594217512377 23796774634745695663134283)
              ·
                refine ⟨35695161952118543494701425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23796774634745695663134283 35695161952118543494701425)
                ·
                  refine ⟨26771371464088907621026069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35695161952118543494701425 26771371464088907621026069)
                  ·
                    refine ⟨1254908037379167544735597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26771371464088907621026069 1254908037379167544735597)
                    ·
                      rfl

theorem cell23_7331774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_7331774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331774 prefixEnd_7331774 := by exact prefixLift 7331774
  have htrace : WordTrace (prefixWord ++ tailWord_7331774) baseStart_7331774 baseEnd_7331774 := by
    simpa [prefixWord, tailWord_7331774, baseEnd_7331774] using wordTrace_append hprefix tailTrace_7331774
  have hstable : (prefixWord ++ tailWord_7331774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331774).length < 2 ^ (prefixWord ++ tailWord_7331774).sum := by decide
  have hdescent : baseEnd_7331774 < baseStart_7331774 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331787 : List Nat := [1, 1, 1, 1, 3, 4, 1, 4, 7]
def baseStart_7331787 : Nat := 118140960795 + 7331787 * 2 ^ 59
def prefixEnd_7331787 : Nat := 4983230072969 + 3 ^ 40 * 7331787 * 2
def baseEnd_7331787 : Nat := 418303420820667898149359

theorem tailTrace_7331787 : CollatzResearch.WordTrace tailWord_7331787 prefixEnd_7331787 418303420820667898149359 := by
  unfold tailWord_7331787
  simp only [CollatzResearch.WordTrace]
  refine ⟨267412240689195343374401615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178274827126130228916267743 267412240689195343374401615)
  ·
    refine ⟨401118361033793015061602423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267412240689195343374401615 401118361033793015061602423)
    ·
      refine ⟨601677541550689522592403635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401118361033793015061602423 601677541550689522592403635)
      ·
        refine ⟨902516312326034283888605453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601677541550689522592403635 902516312326034283888605453)
        ·
          refine ⟨338443617122262856458227045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 902516312326034283888605453 338443617122262856458227045)
          ·
            refine ⟨63458178210424285585917571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338443617122262856458227045 63458178210424285585917571)
            ·
              refine ⟨95187267315636428378876357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63458178210424285585917571 95187267315636428378876357)
              ·
                refine ⟨17847612621681830321039317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95187267315636428378876357 17847612621681830321039317)
                ·
                  refine ⟨418303420820667898149359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17847612621681830321039317 418303420820667898149359)
                  ·
                    rfl

theorem cell23_7331787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 7].length) (baseStart_7331787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331787 prefixEnd_7331787 := by exact prefixLift 7331787
  have htrace : WordTrace (prefixWord ++ tailWord_7331787) baseStart_7331787 baseEnd_7331787 := by
    simpa [prefixWord, tailWord_7331787, baseEnd_7331787] using wordTrace_append hprefix tailTrace_7331787
  have hstable : (prefixWord ++ tailWord_7331787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331787).length < 2 ^ (prefixWord ++ tailWord_7331787).sum := by decide
  have hdescent : baseEnd_7331787 < baseStart_7331787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331857 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 9]
def baseStart_7331857 : Nat := 118140960795 + 7331857 * 2 ^ 59
def prefixEnd_7331857 : Nat := 4983230072969 + 3 ^ 40 * 7331857 * 2
def baseEnd_7331857 : Nat := 3764766731031825809468909

theorem tailTrace_7331857 : CollatzResearch.WordTrace tailWord_7331857 prefixEnd_7331857 3764766731031825809468909 := by
  unfold tailWord_7331857
  simp only [CollatzResearch.WordTrace]
  refine ⟨267414793798941745329449825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178276529199294496886299883 267414793798941745329449825)
  ·
    refine ⟨200561095349206308997087369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267414793798941745329449825 200561095349206308997087369)
    ·
      refine ⟨150420821511904731747815527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200561095349206308997087369 150420821511904731747815527)
      ·
        refine ⟨225631232267857097621723291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150420821511904731747815527 225631232267857097621723291)
        ·
          refine ⟨338446848401785646432584937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225631232267857097621723291 338446848401785646432584937)
          ·
            refine ⟨253835136301339234824438703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 338446848401785646432584937 253835136301339234824438703)
            ·
              refine ⟨380752704452008852236658055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253835136301339234824438703 380752704452008852236658055)
              ·
                refine ⟨571129056678013278354987083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380752704452008852236658055 571129056678013278354987083)
                ·
                  refine ⟨856693585017019917532480625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 571129056678013278354987083 856693585017019917532480625)
                  ·
                    refine ⟨642520188762764938149360469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 856693585017019917532480625 642520188762764938149360469)
                    ·
                      refine ⟨3764766731031825809468909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 642520188762764938149360469 3764766731031825809468909)
                      ·
                        rfl

theorem cell23_7331857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 9].length) (baseStart_7331857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331857 prefixEnd_7331857 := by exact prefixLift 7331857
  have htrace : WordTrace (prefixWord ++ tailWord_7331857) baseStart_7331857 baseEnd_7331857 := by
    simpa [prefixWord, tailWord_7331857, baseEnd_7331857] using wordTrace_append hprefix tailTrace_7331857
  have hstable : (prefixWord ++ tailWord_7331857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331857).length < 2 ^ (prefixWord ++ tailWord_7331857).sum := by decide
  have hdescent : baseEnd_7331857 < baseStart_7331857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331871 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 2, 4, 2]
def baseStart_7331871 : Nat := 118140960795 + 7331871 * 2 ^ 59
def prefixEnd_7331871 : Nat := 4983230072969 + 3 ^ 40 * 7331871 * 2
def baseEnd_7331871 : Nat := 3764773919760988754693845

theorem tailTrace_7331871 : CollatzResearch.WordTrace tailWord_7331871 prefixEnd_7331871 3764773919760988754693845 := by
  unfold tailWord_7331871
  simp only [CollatzResearch.WordTrace]
  refine ⟨267415304420891025720459467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178276869613927350480306311 267415304420891025720459467)
  ·
    refine ⟨401122956631336538580689201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267415304420891025720459467 401122956631336538580689201)
    ·
      refine ⟨300842217473502403935516901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401122956631336538580689201 300842217473502403935516901)
      ·
        refine ⟨56407915776281700737909419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300842217473502403935516901 56407915776281700737909419)
        ·
          refine ⟨84611873664422551106864129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56407915776281700737909419 84611873664422551106864129)
          ·
            refine ⟨63458905248316913330148097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84611873664422551106864129 63458905248316913330148097)
            ·
              refine ⟨47594178936237684997611073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63458905248316913330148097 47594178936237684997611073)
              ·
                refine ⟨35695634202178263748208305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47594178936237684997611073 35695634202178263748208305)
                ·
                  refine ⟨26771725651633697811156229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35695634202178263748208305 26771725651633697811156229)
                  ·
                    refine ⟨5019698559681318339591793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26771725651633697811156229 5019698559681318339591793)
                    ·
                      refine ⟨3764773919760988754693845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019698559681318339591793 3764773919760988754693845)
                      ·
                        rfl

theorem cell23_7331871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 4, 2].length) (baseStart_7331871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331871 prefixEnd_7331871 := by exact prefixLift 7331871
  have htrace : WordTrace (prefixWord ++ tailWord_7331871) baseStart_7331871 baseEnd_7331871 := by
    simpa [prefixWord, tailWord_7331871, baseEnd_7331871] using wordTrace_append hprefix tailTrace_7331871
  have hstable : (prefixWord ++ tailWord_7331871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331871).length < 2 ^ (prefixWord ++ tailWord_7331871).sum := by decide
  have hdescent : baseEnd_7331871 < baseStart_7331871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331874 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_7331874 : Nat := 118140960795 + 7331874 * 2 ^ 59
def prefixEnd_7331874 : Nat := 4983230072969 + 3 ^ 40 * 7331874 * 2
def baseEnd_7331874 : Nat := 3764775460202952242956331

theorem tailTrace_7331874 : CollatzResearch.WordTrace tailWord_7331874 prefixEnd_7331874 3764775460202952242956331 := by
  unfold tailWord_7331874
  simp only [CollatzResearch.WordTrace]
  refine ⟨66853853459970039308204669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178276942559920104821879117 66853853459970039308204669)
  ·
    refine ⟨25070195047488764740576751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 66853853459970039308204669 25070195047488764740576751)
    ·
      refine ⟨37605292571233147110865127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25070195047488764740576751 37605292571233147110865127)
      ·
        refine ⟨56407938856849720666297691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37605292571233147110865127 56407938856849720666297691)
        ·
          refine ⟨84611908285274580999446537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56407938856849720666297691 84611908285274580999446537)
          ·
            refine ⟨63458931213955935749584903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84611908285274580999446537 63458931213955935749584903)
            ·
              refine ⟨95188396820933903624377355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63458931213955935749584903 95188396820933903624377355)
              ·
                refine ⟨142782595231400855436566033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95188396820933903624377355 142782595231400855436566033)
                ·
                  refine ⟨107086946423550641577424525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142782595231400855436566033 107086946423550641577424525)
                  ·
                    refine ⟨40157604908831490591534197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107086946423550641577424525 40157604908831490591534197)
                    ·
                      refine ⟨3764775460202952242956331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40157604908831490591534197 3764775460202952242956331)
                      ·
                        rfl

theorem cell23_7331874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_7331874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331874 prefixEnd_7331874 := by exact prefixLift 7331874
  have htrace : WordTrace (prefixWord ++ tailWord_7331874) baseStart_7331874 baseEnd_7331874 := by
    simpa [prefixWord, tailWord_7331874, baseEnd_7331874] using wordTrace_append hprefix tailTrace_7331874
  have hstable : (prefixWord ++ tailWord_7331874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331874).length < 2 ^ (prefixWord ++ tailWord_7331874).sum := by decide
  have hdescent : baseEnd_7331874 < baseStart_7331874 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331921 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 3]
def baseStart_7331921 : Nat := 118140960795 + 7331921 * 2 ^ 59
def prefixEnd_7331921 : Nat := 4983230072969 + 3 ^ 40 * 7331921 * 2
def baseEnd_7331921 : Nat := 3764799593793713559068615

theorem tailTrace_7331921 : CollatzResearch.WordTrace tailWord_7331921 prefixEnd_7331921 3764799593793713559068615 := by
  unfold tailWord_7331921
  simp only [CollatzResearch.WordTrace]
  refine ⟨267417128070709884259779617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178278085380473256173186411 267417128070709884259779617)
  ·
    refine ⟨200562846053032413194834713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267417128070709884259779617 200562846053032413194834713)
    ·
      refine ⟨150422134539774309896126035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200562846053032413194834713 150422134539774309896126035)
      ·
        refine ⟨225633201809661464844189053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150422134539774309896126035 225633201809661464844189053)
        ·
          refine ⟨84612450678623049316570895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225633201809661464844189053 84612450678623049316570895)
          ·
            refine ⟨126918676017934573974856343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84612450678623049316570895 126918676017934573974856343)
            ·
              refine ⟨190378014026901860962284515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126918676017934573974856343 190378014026901860962284515)
              ·
                refine ⟨285567021040352791443426773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190378014026901860962284515 285567021040352791443426773)
                ·
                  refine ⟨6692977055633268549455315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 285567021040352791443426773 6692977055633268549455315)
                  ·
                    refine ⟨10039465583449902824182973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6692977055633268549455315 10039465583449902824182973)
                    ·
                      refine ⟨3764799593793713559068615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10039465583449902824182973 3764799593793713559068615)
                      ·
                        rfl

theorem cell23_7331921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 1, 3].length) (baseStart_7331921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331921 prefixEnd_7331921 := by exact prefixLift 7331921
  have htrace : WordTrace (prefixWord ++ tailWord_7331921) baseStart_7331921 baseEnd_7331921 := by
    simpa [prefixWord, tailWord_7331921, baseEnd_7331921] using wordTrace_append hprefix tailTrace_7331921
  have hstable : (prefixWord ++ tailWord_7331921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331921).length < 2 ^ (prefixWord ++ tailWord_7331921).sum := by decide
  have hdescent : baseEnd_7331921 < baseStart_7331921 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331958 : List Nat := [5, 1, 1, 2, 1, 2, 1, 4, 1, 5]
def baseStart_7331958 : Nat := 118140960795 + 7331958 * 2 ^ 59
def prefixEnd_7331958 : Nat := 4983230072969 + 3 ^ 40 * 7331958 * 2
def baseEnd_7331958 : Nat := 1254939530859309971435315

theorem tailTrace_7331958 : CollatzResearch.WordTrace tailWord_7331958 prefixEnd_7331958 1254939530859309971435315 := by
  unfold tailWord_7331958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16713654848223489973679783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178278985047717226385917685 16713654848223489973679783)
  ·
    refine ⟨25070482272335234960519675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16713654848223489973679783 25070482272335234960519675)
    ·
      refine ⟨37605723408502852440779513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25070482272335234960519675 37605723408502852440779513)
      ·
        refine ⟨28204292556377139330584635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37605723408502852440779513 28204292556377139330584635)
        ·
          refine ⟨42306438834565708995876953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28204292556377139330584635 42306438834565708995876953)
          ·
            refine ⟨31729829125924281746907715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42306438834565708995876953 31729829125924281746907715)
            ·
              refine ⟨47594743688886422620361573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31729829125924281746907715 47594743688886422620361573)
              ·
                refine ⟨8924014441666204241317795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47594743688886422620361573 8924014441666204241317795)
                ·
                  refine ⟨13386021662499306361976693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8924014441666204241317795 13386021662499306361976693)
                  ·
                    refine ⟨1254939530859309971435315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13386021662499306361976693 1254939530859309971435315)
                    ·
                      rfl

theorem cell23_7331958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_7331958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331958 prefixEnd_7331958 := by exact prefixLift 7331958
  have htrace : WordTrace (prefixWord ++ tailWord_7331958) baseStart_7331958 baseEnd_7331958 := by
    simpa [prefixWord, tailWord_7331958, baseEnd_7331958] using wordTrace_append hprefix tailTrace_7331958
  have hstable : (prefixWord ++ tailWord_7331958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331958).length < 2 ^ (prefixWord ++ tailWord_7331958).sum := by decide
  have hdescent : baseEnd_7331958 < baseStart_7331958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331971 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 4, 4]
def baseStart_7331971 : Nat := 118140960795 + 7331971 * 2 ^ 59
def prefixEnd_7331971 : Nat := 4983230072969 + 3 ^ 40 * 7331971 * 2
def baseEnd_7331971 : Nat := 1254941755942146121147795

theorem tailTrace_7331971 : CollatzResearch.WordTrace tailWord_7331971 prefixEnd_7331971 1254941755942146121147795 := by
  unfold tailWord_7331971
  simp only [CollatzResearch.WordTrace]
  refine ⟨267418951720528742799099767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178279301147019161866066511 267418951720528742799099767)
  ·
    refine ⟨401128427580793114198649651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267418951720528742799099767 401128427580793114198649651)
    ·
      refine ⟨601692641371189671297974477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401128427580793114198649651 601692641371189671297974477)
      ·
        refine ⟨225634740514196126736740429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601692641371189671297974477 225634740514196126736740429)
        ·
          refine ⟨84613027692823547526277661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225634740514196126736740429 84613027692823547526277661)
          ·
            refine ⟨31729885384808830322354123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84613027692823547526277661 31729885384808830322354123)
            ·
              refine ⟨47594828077213245483531185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31729885384808830322354123 47594828077213245483531185)
              ·
                refine ⟨35696121057909934112648389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47594828077213245483531185 35696121057909934112648389)
                ·
                  refine ⟨6693022698358112646121573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35696121057909934112648389 6693022698358112646121573)
                  ·
                    refine ⟨1254941755942146121147795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6693022698358112646121573 1254941755942146121147795)
                    ·
                      rfl

theorem cell23_7331971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 4, 4].length) (baseStart_7331971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331971 prefixEnd_7331971 := by exact prefixLift 7331971
  have htrace : WordTrace (prefixWord ++ tailWord_7331971) baseStart_7331971 baseEnd_7331971 := by
    simpa [prefixWord, tailWord_7331971, baseEnd_7331971] using wordTrace_append hprefix tailTrace_7331971
  have hstable : (prefixWord ++ tailWord_7331971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331971).length < 2 ^ (prefixWord ++ tailWord_7331971).sum := by decide
  have hdescent : baseEnd_7331971 < baseStart_7331971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7331978 : List Nat := [3, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4]
def baseStart_7331978 : Nat := 118140960795 + 7331978 * 2 ^ 59
def prefixEnd_7331978 : Nat := 4983230072969 + 3 ^ 40 * 7331978 * 2
def baseEnd_7331978 : Nat := 3764828862191019836055853

theorem tailTrace_7331978 : CollatzResearch.WordTrace tailWord_7331978 prefixEnd_7331978 3764828862191019836055853 := by
  unfold tailWord_7331978
  simp only [CollatzResearch.WordTrace]
  refine ⟨66854801757875845748651147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178279471354335588663069725 66854801757875845748651147)
  ·
    refine ⟨100282202636813768622976721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66854801757875845748651147 100282202636813768622976721)
    ·
      refine ⟨75211651977610326467232541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100282202636813768622976721 75211651977610326467232541)
      ·
        refine ⟨28204369491603872425212203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75211651977610326467232541 28204369491603872425212203)
        ·
          refine ⟨42306554237405808637818305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28204369491603872425212203 42306554237405808637818305)
          ·
            refine ⟨31729915678054356478363729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42306554237405808637818305 31729915678054356478363729)
            ·
              refine ⟨23797436758540767358772797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31729915678054356478363729 23797436758540767358772797)
              ·
                refine ⟨8924038784452787759539799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23797436758540767358772797 8924038784452787759539799)
                ·
                  refine ⟨13386058176679181639309699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8924038784452787759539799 13386058176679181639309699)
                  ·
                    refine ⟨20079087265018772458964549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13386058176679181639309699 20079087265018772458964549)
                    ·
                      refine ⟨3764828862191019836055853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20079087265018772458964549 3764828862191019836055853)
                      ·
                        rfl

theorem cell23_7331978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_7331978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7331978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7331978 prefixEnd_7331978 := by exact prefixLift 7331978
  have htrace : WordTrace (prefixWord ++ tailWord_7331978) baseStart_7331978 baseEnd_7331978 := by
    simpa [prefixWord, tailWord_7331978, baseEnd_7331978] using wordTrace_append hprefix tailTrace_7331978
  have hstable : (prefixWord ++ tailWord_7331978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7331978).length < 2 ^ (prefixWord ++ tailWord_7331978).sum := by decide
  have hdescent : baseEnd_7331978 < baseStart_7331978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7331978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332001 : List Nat := [1, 2, 3, 3, 1, 3, 2, 8]
def baseStart_7332001 : Nat := 118140960795 + 7332001 * 2 ^ 59
def prefixEnd_7332001 : Nat := 4983230072969 + 3 ^ 40 * 7332001 * 2
def baseEnd_7332001 : Nat := 139438543416521231335861

theorem tailTrace_7332001 : CollatzResearch.WordTrace tailWord_7332001 prefixEnd_7332001 139438543416521231335861 := by
  unfold tailWord_7332001
  simp only [CollatzResearch.WordTrace]
  refine ⟨267420045910420057922691857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178280030606946705281794571 267420045910420057922691857)
  ·
    refine ⟨200565034432815043442018893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267420045910420057922691857 200565034432815043442018893)
    ·
      refine ⟨75211887912305641290757085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200565034432815043442018893 75211887912305641290757085)
      ·
        refine ⟨28204457967114615484033907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75211887912305641290757085 28204457967114615484033907)
        ·
          refine ⟨42306686950671923226050861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28204457967114615484033907 42306686950671923226050861)
          ·
            refine ⟨15865007606501971209769073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42306686950671923226050861 15865007606501971209769073)
            ·
              refine ⟨11898755704876478407326805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15865007606501971209769073 11898755704876478407326805)
              ·
                refine ⟨139438543416521231335861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11898755704876478407326805 139438543416521231335861)
                ·
                  rfl

theorem cell23_7332001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 8].length) (baseStart_7332001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332001 prefixEnd_7332001 := by exact prefixLift 7332001
  have htrace : WordTrace (prefixWord ++ tailWord_7332001) baseStart_7332001 baseEnd_7332001 := by
    simpa [prefixWord, tailWord_7332001, baseEnd_7332001] using wordTrace_append hprefix tailTrace_7332001
  have hstable : (prefixWord ++ tailWord_7332001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332001).length < 2 ^ (prefixWord ++ tailWord_7332001).sum := by decide
  have hdescent : baseEnd_7332001 < baseStart_7332001 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332046 : List Nat := [4, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2]
def baseStart_7332046 : Nat := 118140960795 + 7332046 * 2 ^ 59
def prefixEnd_7332046 : Nat := 4983230072969 + 3 ^ 40 * 7332046 * 2
def baseEnd_7332046 : Nat := 3764863778875525570005541

theorem tailTrace_7332046 : CollatzResearch.WordTrace tailWord_7332046 prefixEnd_7332046 3764863778875525570005541 := by
  unfold tailWord_7332046
  simp only [CollatzResearch.WordTrace]
  refine ⟨33427710899407128826009999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178281124796838020405386661 33427710899407128826009999)
  ·
    refine ⟨50141566349110693239014999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33427710899407128826009999 50141566349110693239014999)
    ·
      refine ⟨75212349523666039858522499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50141566349110693239014999 75212349523666039858522499)
      ·
        refine ⟨112818524285499059787783749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75212349523666039858522499 112818524285499059787783749)
        ·
          refine ⟨21153473303531073710209453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112818524285499059787783749 21153473303531073710209453)
          ·
            refine ⟨7932552488824152641328545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21153473303531073710209453 7932552488824152641328545)
            ·
              refine ⟨5949414366618114480996409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7932552488824152641328545 5949414366618114480996409)
              ·
                refine ⟨4462060774963585860747307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949414366618114480996409 4462060774963585860747307)
                ·
                  refine ⟨6693091162445378791120961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462060774963585860747307 6693091162445378791120961)
                  ·
                    refine ⟨5019818371834034093340721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6693091162445378791120961 5019818371834034093340721)
                    ·
                      refine ⟨3764863778875525570005541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019818371834034093340721 3764863778875525570005541)
                      ·
                        rfl

theorem cell23_7332046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_7332046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332046 prefixEnd_7332046 := by exact prefixLift 7332046
  have htrace : WordTrace (prefixWord ++ tailWord_7332046) baseStart_7332046 baseEnd_7332046 := by
    simpa [prefixWord, tailWord_7332046, baseEnd_7332046] using wordTrace_append hprefix tailTrace_7332046
  have hstable : (prefixWord ++ tailWord_7332046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332046).length < 2 ^ (prefixWord ++ tailWord_7332046).sum := by decide
  have hdescent : baseEnd_7332046 < baseStart_7332046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332108 : List Nat := [2, 2, 1, 2, 2, 2, 1, 6, 5]
def baseStart_7332108 : Nat := 118140960795 + 7332108 * 2 ^ 59
def prefixEnd_7332108 : Nat := 4983230072969 + 3 ^ 40 * 7332108 * 2
def baseEnd_7332108 : Nat := 418321734964011591936695

theorem tailTrace_7332108 : CollatzResearch.WordTrace tailWord_7332108 prefixEnd_7332108 418321734964011591936695 := by
  unfold tailWord_7332108
  simp only [CollatzResearch.WordTrace]
  refine ⟨133711974260516207598418489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178282632347354943464557985 133711974260516207598418489)
  ·
    refine ⟨100283980695387155698813867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133711974260516207598418489 100283980695387155698813867)
    ·
      refine ⟨150425971043080733548220801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100283980695387155698813867 150425971043080733548220801)
      ·
        refine ⟨112819478282310550161165601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150425971043080733548220801 112819478282310550161165601)
        ·
          refine ⟨84614608711732912620874201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112819478282310550161165601 84614608711732912620874201)
          ·
            refine ⟨63460956533799684465655651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84614608711732912620874201 63460956533799684465655651)
            ·
              refine ⟨95191434800699526698483477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63460956533799684465655651 95191434800699526698483477)
              ·
                refine ⟨4462098506282790313991413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95191434800699526698483477 4462098506282790313991413)
                ·
                  refine ⟨418321734964011591936695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4462098506282790313991413 418321734964011591936695)
                  ·
                    rfl

theorem cell23_7332108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 1, 6, 5].length) (baseStart_7332108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332108 prefixEnd_7332108 := by exact prefixLift 7332108
  have htrace : WordTrace (prefixWord ++ tailWord_7332108) baseStart_7332108 baseEnd_7332108 := by
    simpa [prefixWord, tailWord_7332108, baseEnd_7332108] using wordTrace_append hprefix tailTrace_7332108
  have hstable : (prefixWord ++ tailWord_7332108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332108).length < 2 ^ (prefixWord ++ tailWord_7332108).sum := by decide
  have hdescent : baseEnd_7332108 < baseStart_7332108 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332119 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 2, 2, 2]
def baseStart_7332119 : Nat := 118140960795 + 7332119 * 2 ^ 59
def prefixEnd_7332119 : Nat := 4983230072969 + 3 ^ 40 * 7332119 * 2
def baseEnd_7332119 : Nat := 3764901262963303784392705

theorem tailTrace_7332119 : CollatzResearch.WordTrace tailWord_7332119 prefixEnd_7332119 3764901262963303784392705 := by
  unfold tailWord_7332119
  simp only [CollatzResearch.WordTrace]
  refine ⟨267424349723992564075487411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178282899815995042716991607 267424349723992564075487411)
  ·
    refine ⟨401136524585988846113231117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267424349723992564075487411 401136524585988846113231117)
    ·
      refine ⟨150426196719745817292461669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401136524585988846113231117 150426196719745817292461669)
      ·
        refine ⟨28204911884952340742336563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 150426196719745817292461669 28204911884952340742336563)
        ·
          refine ⟨42307367827428511113504845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28204911884952340742336563 42307367827428511113504845)
          ·
            refine ⟨15865262935285691667564317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42307367827428511113504845 15865262935285691667564317)
            ·
              refine ⟨5949473600732134375336619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15865262935285691667564317 5949473600732134375336619)
              ·
                refine ⟨8924210401098201563004929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5949473600732134375336619 8924210401098201563004929)
                ·
                  refine ⟨6693157800823651172253697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8924210401098201563004929 6693157800823651172253697)
                  ·
                    refine ⟨5019868350617738379190273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6693157800823651172253697 5019868350617738379190273)
                    ·
                      refine ⟨3764901262963303784392705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5019868350617738379190273 3764901262963303784392705)
                      ·
                        rfl

theorem cell23_7332119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_7332119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332119 prefixEnd_7332119 := by exact prefixLift 7332119
  have htrace : WordTrace (prefixWord ++ tailWord_7332119) baseStart_7332119 baseEnd_7332119 := by
    simpa [prefixWord, tailWord_7332119, baseEnd_7332119] using wordTrace_append hprefix tailTrace_7332119
  have hstable : (prefixWord ++ tailWord_7332119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332119).length < 2 ^ (prefixWord ++ tailWord_7332119).sum := by decide
  have hdescent : baseEnd_7332119 < baseStart_7332119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332171 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 4]
def baseStart_7332171 : Nat := 118140960795 + 7332171 * 2 ^ 59
def prefixEnd_7332171 : Nat := 4983230072969 + 3 ^ 40 * 7332171 * 2
def baseEnd_7332171 : Nat := 3764927963957337580942465

theorem tailTrace_7332171 : CollatzResearch.WordTrace tailWord_7332171 prefixEnd_7332171 3764927963957337580942465 := by
  unfold tailWord_7332171
  simp only [CollatzResearch.WordTrace]
  refine ⟨267426246319804176956380367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178284164213202784637586911 267426246319804176956380367)
  ·
    refine ⟨401139369479706265434570551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267426246319804176956380367 401139369479706265434570551)
    ·
      refine ⟨601709054219559398151855827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401139369479706265434570551 601709054219559398151855827)
      ·
        refine ⟨902563581329339097227783741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601709054219559398151855827 902563581329339097227783741)
        ·
          refine ⟨338461342998502161460418903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 902563581329339097227783741 338461342998502161460418903)
          ·
            refine ⟨507692014497753242190628355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338461342998502161460418903 507692014497753242190628355)
            ·
              refine ⟨761538021746629863285942533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507692014497753242190628355 761538021746629863285942533)
              ·
                refine ⟨142788379077493099366114225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 761538021746629863285942533 142788379077493099366114225)
                ·
                  refine ⟨107091284308119824524585669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 142788379077493099366114225 107091284308119824524585669)
                  ·
                    refine ⟨20079615807772467098359813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 107091284308119824524585669 20079615807772467098359813)
                    ·
                      refine ⟨3764927963957337580942465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20079615807772467098359813 3764927963957337580942465)
                      ·
                        rfl

theorem cell23_7332171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 4].length) (baseStart_7332171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332171 prefixEnd_7332171 := by exact prefixLift 7332171
  have htrace : WordTrace (prefixWord ++ tailWord_7332171) baseStart_7332171 baseEnd_7332171 := by
    simpa [prefixWord, tailWord_7332171, baseEnd_7332171] using wordTrace_append hprefix tailTrace_7332171
  have hstable : (prefixWord ++ tailWord_7332171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332171).length < 2 ^ (prefixWord ++ tailWord_7332171).sum := by decide
  have hdescent : baseEnd_7332171 < baseStart_7332171 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332178 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_7332178 : Nat := 118140960795 + 7332178 * 2 ^ 59
def prefixEnd_7332178 : Nat := 4983230072969 + 3 ^ 40 * 7332178 * 2
def baseEnd_7332178 : Nat := 3764931558321919053554933

theorem tailTrace_7332178 : CollatzResearch.WordTrace tailWord_7332178 prefixEnd_7332178 3764931558321919053554933 := by
  unfold tailWord_7332178
  simp only [CollatzResearch.WordTrace]
  refine ⟨66856625407694704287971297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178284334420519211434590125 66856625407694704287971297)
  ·
    refine ⟨50142469055771028215978473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66856625407694704287971297 50142469055771028215978473)
    ·
      refine ⟨37606851791828271161983855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50142469055771028215978473 37606851791828271161983855)
      ·
        refine ⟨56410277687742406742975783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37606851791828271161983855 56410277687742406742975783)
        ·
          refine ⟨84615416531613610114463675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56410277687742406742975783 84615416531613610114463675)
          ·
            refine ⟨126923124797420415171695513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84615416531613610114463675 126923124797420415171695513)
            ·
              refine ⟨95192343598065311378771635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126923124797420415171695513 95192343598065311378771635)
              ·
                refine ⟨142788515397097967068157453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95192343598065311378771635 142788515397097967068157453)
                ·
                  refine ⟨53545693273911737650559045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142788515397097967068157453 53545693273911737650559045)
                  ·
                    refine ⟨10039817488858450809479821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53545693273911737650559045 10039817488858450809479821)
                    ·
                      refine ⟨3764931558321919053554933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10039817488858450809479821 3764931558321919053554933)
                      ·
                        rfl

theorem cell23_7332178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_7332178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332178 prefixEnd_7332178 := by exact prefixLift 7332178
  have htrace : WordTrace (prefixWord ++ tailWord_7332178) baseStart_7332178 baseEnd_7332178 := by
    simpa [prefixWord, tailWord_7332178, baseEnd_7332178] using wordTrace_append hprefix tailTrace_7332178
  have hstable : (prefixWord ++ tailWord_7332178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332178).length < 2 ^ (prefixWord ++ tailWord_7332178).sum := by decide
  have hdescent : baseEnd_7332178 < baseStart_7332178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332195 : List Nat := [1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 3]
def baseStart_7332195 : Nat := 118140960795 + 7332195 * 2 ^ 59
def prefixEnd_7332195 : Nat := 4983230072969 + 3 ^ 40 * 7332195 * 2
def baseEnd_7332195 : Nat := 3764940287493045487042355

theorem tailTrace_7332195 : CollatzResearch.WordTrace tailWord_7332195 prefixEnd_7332195 3764940287493045487042355 := by
  unfold tailWord_7332195
  simp only [CollatzResearch.WordTrace]
  refine ⟨267427121671717229055254039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178284747781144819370169359 267427121671717229055254039)
  ·
    refine ⟨401140682507575843582881059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267427121671717229055254039 401140682507575843582881059)
    ·
      refine ⟨601711023761363765374321589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401140682507575843582881059 601711023761363765374321589)
      ·
        refine ⟨56410408477627853003842649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 601711023761363765374321589 56410408477627853003842649)
        ·
          refine ⟨42307806358220889752881987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56410408477627853003842649 42307806358220889752881987)
          ·
            refine ⟨63461709537331334629322981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42307806358220889752881987 63461709537331334629322981)
            ·
              refine ⟨11899070538249625242998059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63461709537331334629322981 11899070538249625242998059)
              ·
                refine ⟨17848605807374437864497089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11899070538249625242998059 17848605807374437864497089)
                ·
                  refine ⟨13386454355530828398372817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17848605807374437864497089 13386454355530828398372817)
                  ·
                    refine ⟨10039840766648121298779613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13386454355530828398372817 10039840766648121298779613)
                    ·
                      refine ⟨3764940287493045487042355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10039840766648121298779613 3764940287493045487042355)
                      ·
                        rfl

theorem cell23_7332195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 2, 3].length) (baseStart_7332195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332195 prefixEnd_7332195 := by exact prefixLift 7332195
  have htrace : WordTrace (prefixWord ++ tailWord_7332195) baseStart_7332195 baseEnd_7332195 := by
    simpa [prefixWord, tailWord_7332195, baseEnd_7332195] using wordTrace_append hprefix tailTrace_7332195
  have hstable : (prefixWord ++ tailWord_7332195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332195).length < 2 ^ (prefixWord ++ tailWord_7332195).sum := by decide
  have hdescent : baseEnd_7332195 < baseStart_7332195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332219 : List Nat := [1, 1, 1, 1, 1, 9, 2, 2, 1, 4]
def baseStart_7332219 : Nat := 118140960795 + 7332219 * 2 ^ 59
def prefixEnd_7332219 : Nat := 4983230072969 + 3 ^ 40 * 7332219 * 2
def baseEnd_7332219 : Nat := 1254984203676251131047415

theorem tailTrace_7332219 : CollatzResearch.WordTrace tailWord_7332219 prefixEnd_7332219 1254984203676251131047415 := by
  unfold tailWord_7332219
  simp only [CollatzResearch.WordTrace]
  refine ⟨267427997023630281154127711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178285331349086854102751807 267427997023630281154127711)
  ·
    refine ⟨401141995535445421731191567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267427997023630281154127711 401141995535445421731191567)
    ·
      refine ⟨601712993303168132596787351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401141995535445421731191567 601712993303168132596787351)
      ·
        refine ⟨902569489954752198895181027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601712993303168132596787351 902569489954752198895181027)
        ·
          refine ⟨1353854234932128298342771541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902569489954752198895181027 1353854234932128298342771541)
          ·
            refine ⟨7932739657805439248102177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1353854234932128298342771541 7932739657805439248102177)
            ·
              refine ⟨5949554743354079436076633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7932739657805439248102177 5949554743354079436076633)
              ·
                refine ⟨4462166057515559577057475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949554743354079436076633 4462166057515559577057475)
                ·
                  refine ⟨6693249086273339365586213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462166057515559577057475 6693249086273339365586213)
                  ·
                    refine ⟨1254984203676251131047415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6693249086273339365586213 1254984203676251131047415)
                    ·
                      rfl

theorem cell23_7332219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 2, 1, 4].length) (baseStart_7332219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332219 prefixEnd_7332219 := by exact prefixLift 7332219
  have htrace : WordTrace (prefixWord ++ tailWord_7332219) baseStart_7332219 baseEnd_7332219 := by
    simpa [prefixWord, tailWord_7332219, baseEnd_7332219] using wordTrace_append hprefix tailTrace_7332219
  have hstable : (prefixWord ++ tailWord_7332219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332219).length < 2 ^ (prefixWord ++ tailWord_7332219).sum := by decide
  have hdescent : baseEnd_7332219 < baseStart_7332219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332228 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 5, 5]
def baseStart_7332228 : Nat := 118140960795 + 7332228 * 2 ^ 59
def prefixEnd_7332228 : Nat := 4983230072969 + 3 ^ 40 * 7332228 * 2
def baseEnd_7332228 : Nat := 1254985744118214619309901

theorem tailTrace_7332228 : CollatzResearch.WordTrace tailWord_7332228 prefixEnd_7332228 1254985744118214619309901 := by
  unfold tailWord_7332228
  simp only [CollatzResearch.WordTrace]
  refine ⟨133714162640298837845602669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178285550187065117127470225 133714162640298837845602669)
  ·
    refine ⟨50142810990112064192101001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133714162640298837845602669 50142810990112064192101001)
    ·
      refine ⟨37607108242584048144075751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50142810990112064192101001 37607108242584048144075751)
      ·
        refine ⟨56410662363876072216113627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37607108242584048144075751 56410662363876072216113627)
        ·
          refine ⟨84615993545814108324170441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56410662363876072216113627 84615993545814108324170441)
          ·
            refine ⟨63461995159360581243127831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84615993545814108324170441 63461995159360581243127831)
            ·
              refine ⟨95192992739040871864691747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63461995159360581243127831 95192992739040871864691747)
              ·
                refine ⟨142789489108561307797037621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95192992739040871864691747 142789489108561307797037621)
                ·
                  refine ⟨13386514603927622605972277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 142789489108561307797037621 13386514603927622605972277)
                  ·
                    refine ⟨1254985744118214619309901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13386514603927622605972277 1254985744118214619309901)
                    ·
                      rfl

theorem cell23_7332228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_7332228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332228 prefixEnd_7332228 := by exact prefixLift 7332228
  have htrace : WordTrace (prefixWord ++ tailWord_7332228) baseStart_7332228 baseEnd_7332228 := by
    simpa [prefixWord, tailWord_7332228, baseEnd_7332228] using wordTrace_append hprefix tailTrace_7332228
  have hstable : (prefixWord ++ tailWord_7332228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332228).length < 2 ^ (prefixWord ++ tailWord_7332228).sum := by decide
  have hdescent : baseEnd_7332228 < baseStart_7332228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332246 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_7332246 : Nat := 118140960795 + 7332246 * 2 ^ 59
def prefixEnd_7332246 : Nat := 4983230072969 + 3 ^ 40 * 7332246 * 2
def baseEnd_7332246 : Nat := 3764966475006424787504621

theorem tailTrace_7332246 : CollatzResearch.WordTrace tailWord_7332246 prefixEnd_7332246 3764966475006424787504621 := by
  unfold tailWord_7332246
  simp only [CollatzResearch.WordTrace]
  refine ⟨16714311362158279047835037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178285987863021643176907061 16714311362158279047835037)
  ·
    refine ⟨6267866760809354642938139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16714311362158279047835037 6267866760809354642938139)
    ·
      refine ⟨9401800141214031964407209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6267866760809354642938139 9401800141214031964407209)
      ·
        refine ⟨7051350105910523973305407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9401800141214031964407209 7051350105910523973305407)
        ·
          refine ⟨10577025158865785959958111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051350105910523973305407 10577025158865785959958111)
          ·
            refine ⟨15865537738298678939937167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10577025158865785959958111 15865537738298678939937167)
            ·
              refine ⟨23798306607448018409905751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15865537738298678939937167 23798306607448018409905751)
              ·
                refine ⟨35697459911172027614858627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23798306607448018409905751 35697459911172027614858627)
                ·
                  refine ⟨53546189866758041422287941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35697459911172027614858627 53546189866758041422287941)
                  ·
                    refine ⟨10039910600017132766678989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53546189866758041422287941 10039910600017132766678989)
                    ·
                      refine ⟨3764966475006424787504621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10039910600017132766678989 3764966475006424787504621)
                      ·
                        rfl

theorem cell23_7332246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_7332246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332246 prefixEnd_7332246 := by exact prefixLift 7332246
  have htrace : WordTrace (prefixWord ++ tailWord_7332246) baseStart_7332246 baseEnd_7332246 := by
    simpa [prefixWord, tailWord_7332246, baseEnd_7332246] using wordTrace_append hprefix tailTrace_7332246
  have hstable : (prefixWord ++ tailWord_7332246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332246).length < 2 ^ (prefixWord ++ tailWord_7332246).sum := by decide
  have hdescent : baseEnd_7332246 < baseStart_7332246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332251 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 11]
def baseStart_7332251 : Nat := 118140960795 + 7332251 * 2 ^ 59
def prefixEnd_7332251 : Nat := 4983230072969 + 3 ^ 40 * 7332251 * 2
def baseEnd_7332251 : Nat := 3764969042409697267942097

theorem tailTrace_7332251 : CollatzResearch.WordTrace tailWord_7332251 prefixEnd_7332251 3764969042409697267942097 := by
  unfold tailWord_7332251
  simp only [CollatzResearch.WordTrace]
  refine ⟨267429164159514350619292607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178286109439676233746195071 267429164159514350619292607)
  ·
    refine ⟨401143746239271525928938911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267429164159514350619292607 401143746239271525928938911)
    ·
      refine ⟨601715619358907288893408367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401143746239271525928938911 601715619358907288893408367)
      ·
        refine ⟨902573429038360933340112551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601715619358907288893408367 902573429038360933340112551)
        ·
          refine ⟨1353860143557541400010168827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902573429038360933340112551 1353860143557541400010168827)
          ·
            refine ⟨2030790215336312100015253241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353860143557541400010168827 2030790215336312100015253241)
            ·
              refine ⟨1523092661502234075011439931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030790215336312100015253241 1523092661502234075011439931)
              ·
                refine ⟨2284638992253351112517159897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523092661502234075011439931 2284638992253351112517159897)
                ·
                  refine ⟨1713479244190013334387869923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2284638992253351112517159897 1713479244190013334387869923)
                  ·
                    refine ⟨2570218866285020001581804885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1713479244190013334387869923 2570218866285020001581804885)
                    ·
                      refine ⟨3764969042409697267942097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2570218866285020001581804885 3764969042409697267942097)
                      ·
                        rfl

theorem cell23_7332251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 11].length) (baseStart_7332251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332251 prefixEnd_7332251 := by exact prefixLift 7332251
  have htrace : WordTrace (prefixWord ++ tailWord_7332251) baseStart_7332251 baseEnd_7332251 := by
    simpa [prefixWord, tailWord_7332251, baseEnd_7332251] using wordTrace_append hprefix tailTrace_7332251
  have hstable : (prefixWord ++ tailWord_7332251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332251).length < 2 ^ (prefixWord ++ tailWord_7332251).sum := by decide
  have hdescent : baseEnd_7332251 < baseStart_7332251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332259 : List Nat := [1, 1, 1, 4, 1, 5, 2, 3, 1, 1, 3]
def baseStart_7332259 : Nat := 118140960795 + 7332259 * 2 ^ 59
def prefixEnd_7332259 : Nat := 4983230072969 + 3 ^ 40 * 7332259 * 2
def baseEnd_7332259 : Nat := 3764973150254933236642061

theorem tailTrace_7332259 : CollatzResearch.WordTrace tailWord_7332259 prefixEnd_7332259 3764973150254933236642061 := by
  unfold tailWord_7332259
  simp only [CollatzResearch.WordTrace]
  refine ⟨267429455943485367985583831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178286303962323578657055887 267429455943485367985583831)
  ·
    refine ⟨401144183915228051978375747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267429455943485367985583831 401144183915228051978375747)
    ·
      refine ⟨601716275872842077967563621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401144183915228051978375747 601716275872842077967563621)
      ·
        refine ⟨112821801726157889618918179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 601716275872842077967563621 112821801726157889618918179)
        ·
          refine ⟨169232702589236834428377269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112821801726157889618918179 169232702589236834428377269)
          ·
            refine ⟨15865565867740953227660369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169232702589236834428377269 15865565867740953227660369)
            ·
              refine ⟨11899174400805714920745277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15865565867740953227660369 11899174400805714920745277)
              ·
                refine ⟨4462190400302143095279479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11899174400805714920745277 4462190400302143095279479)
                ·
                  refine ⟨6693285600453214642919219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462190400302143095279479 6693285600453214642919219)
                  ·
                    refine ⟨10039928400679821964378829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6693285600453214642919219 10039928400679821964378829)
                    ·
                      refine ⟨3764973150254933236642061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10039928400679821964378829 3764973150254933236642061)
                      ·
                        rfl

theorem cell23_7332259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 3, 1, 1, 3].length) (baseStart_7332259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332259 prefixEnd_7332259 := by exact prefixLift 7332259
  have htrace : WordTrace (prefixWord ++ tailWord_7332259) baseStart_7332259 baseEnd_7332259 := by
    simpa [prefixWord, tailWord_7332259, baseEnd_7332259] using wordTrace_append hprefix tailTrace_7332259
  have hstable : (prefixWord ++ tailWord_7332259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332259).length < 2 ^ (prefixWord ++ tailWord_7332259).sum := by decide
  have hdescent : baseEnd_7332259 < baseStart_7332259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332266 : List Nat := [3, 1, 6, 1, 1, 2, 1, 2, 6]
def baseStart_7332266 : Nat := 118140960795 + 7332266 * 2 ^ 59
def prefixEnd_7332266 : Nat := 4983230072969 + 3 ^ 40 * 7332266 * 2
def baseEnd_7332266 : Nat := 418330749402168301028281

theorem tailTrace_7332266 : CollatzResearch.WordTrace tailWord_7332266 prefixEnd_7332266 418330749402168301028281 := by
  unfold tailWord_7332266
  simp only [CollatzResearch.WordTrace]
  refine ⟨66857427813615002045272163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178286474169640005454059101 66857427813615002045272163)
  ·
    refine ⟨100286141720422503067908245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66857427813615002045272163 100286141720422503067908245)
    ·
      refine ⟨4700912893144804831308199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 100286141720422503067908245 4700912893144804831308199)
      ·
        refine ⟨7051369339717207246962299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4700912893144804831308199 7051369339717207246962299)
        ·
          refine ⟨10577054009575810870443449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051369339717207246962299 10577054009575810870443449)
          ·
            refine ⟨7932790507181858152832587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10577054009575810870443449 7932790507181858152832587)
            ·
              refine ⟨11899185760772787229248881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7932790507181858152832587 11899185760772787229248881)
              ·
                refine ⟨8924389320579590421936661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11899185760772787229248881 8924389320579590421936661)
                ·
                  refine ⟨418330749402168301028281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8924389320579590421936661 418330749402168301028281)
                  ·
                    rfl

theorem cell23_7332266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 6].length) (baseStart_7332266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332266 prefixEnd_7332266 := by exact prefixLift 7332266
  have htrace : WordTrace (prefixWord ++ tailWord_7332266) baseStart_7332266 baseEnd_7332266 := by
    simpa [prefixWord, tailWord_7332266, baseEnd_7332266] using wordTrace_append hprefix tailTrace_7332266
  have hstable : (prefixWord ++ tailWord_7332266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332266).length < 2 ^ (prefixWord ++ tailWord_7332266).sum := by decide
  have hdescent : baseEnd_7332266 < baseStart_7332266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332268 : List Nat := [2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 5]
def baseStart_7332268 : Nat := 118140960795 + 7332268 * 2 ^ 59
def prefixEnd_7332268 : Nat := 4983230072969 + 3 ^ 40 * 7332268 * 2
def baseEnd_7332268 : Nat := 3764977771580823701429519

theorem tailTrace_7332268 : CollatzResearch.WordTrace tailWord_7332268 prefixEnd_7332268 3764977771580823701429519 := by
  unfold tailWord_7332268
  simp only [CollatzResearch.WordTrace]
  refine ⟨133714892100226381261330729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178286522800301841681774305 133714892100226381261330729)
  ·
    refine ⟨100286169075169785945998047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133714892100226381261330729 100286169075169785945998047)
    ·
      refine ⟨150429253612754678918997071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100286169075169785945998047 150429253612754678918997071)
      ·
        refine ⟨225643880419132018378495607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150429253612754678918997071 225643880419132018378495607)
        ·
          refine ⟨338465820628698027567743411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225643880419132018378495607 338465820628698027567743411)
          ·
            refine ⟨507698730943047041351615117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338465820628698027567743411 507698730943047041351615117)
            ·
              refine ⟨190387024103642640506855669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507698730943047041351615117 190387024103642640506855669)
              ·
                refine ⟨17848783509716497547517719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190387024103642640506855669 17848783509716497547517719)
                ·
                  refine ⟨26773175264574746321276579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17848783509716497547517719 26773175264574746321276579)
                  ·
                    refine ⟨40159762896862119481914869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26773175264574746321276579 40159762896862119481914869)
                    ·
                      refine ⟨3764977771580823701429519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40159762896862119481914869 3764977771580823701429519)
                      ·
                        rfl

theorem cell23_7332268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 5].length) (baseStart_7332268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332268 prefixEnd_7332268 := by exact prefixLift 7332268
  have htrace : WordTrace (prefixWord ++ tailWord_7332268) baseStart_7332268 baseEnd_7332268 := by
    simpa [prefixWord, tailWord_7332268, baseEnd_7332268] using wordTrace_append hprefix tailTrace_7332268
  have hstable : (prefixWord ++ tailWord_7332268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332268).length < 2 ^ (prefixWord ++ tailWord_7332268).sum := by decide
  have hdescent : baseEnd_7332268 < baseStart_7332268 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332285 : List Nat := [1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 5]
def baseStart_7332285 : Nat := 118140960795 + 7332285 * 2 ^ 59
def prefixEnd_7332285 : Nat := 4983230072969 + 3 ^ 40 * 7332285 * 2
def baseEnd_7332285 : Nat := 3764986500751950134916941

theorem tailTrace_7332285 : CollatzResearch.WordTrace tailWord_7332285 prefixEnd_7332285 3764986500751950134916941 := by
  unfold tailWord_7332285
  simp only [CollatzResearch.WordTrace]
  refine ⟨267430404241391174426030309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178286936160927449617353539 267430404241391174426030309)
  ·
    refine ⟨50143200795260845204880683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267430404241391174426030309 50143200795260845204880683)
    ·
      refine ⟨75214801192891267807321025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50143200795260845204880683 75214801192891267807321025)
      ·
        refine ⟨56411100894668450855490769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75214801192891267807321025 56411100894668450855490769)
        ·
          refine ⟨42308325671001338141618077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56411100894668450855490769 42308325671001338141618077)
          ·
            refine ⟨15865622126625501803106779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42308325671001338141618077 15865622126625501803106779)
            ·
              refine ⟨23798433189938252704660169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15865622126625501803106779 23798433189938252704660169)
              ·
                refine ⟨17848824892453689528495127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23798433189938252704660169 17848824892453689528495127)
                ·
                  refine ⟨26773237338680534292742691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17848824892453689528495127 26773237338680534292742691)
                  ·
                    refine ⟨40159856008020801439114037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26773237338680534292742691 40159856008020801439114037)
                    ·
                      refine ⟨3764986500751950134916941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40159856008020801439114037 3764986500751950134916941)
                      ·
                        rfl

theorem cell23_7332285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_7332285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332285 prefixEnd_7332285 := by exact prefixLift 7332285
  have htrace : WordTrace (prefixWord ++ tailWord_7332285) baseStart_7332285 baseEnd_7332285 := by
    simpa [prefixWord, tailWord_7332285, baseEnd_7332285] using wordTrace_append hprefix tailTrace_7332285
  have hstable : (prefixWord ++ tailWord_7332285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332285).length < 2 ^ (prefixWord ++ tailWord_7332285).sum := by decide
  have hdescent : baseEnd_7332285 < baseStart_7332285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332295 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 4]
def baseStart_7332295 : Nat := 118140960795 + 7332295 * 2 ^ 59
def prefixEnd_7332295 : Nat := 4983230072969 + 3 ^ 40 * 7332295 * 2
def baseEnd_7332295 : Nat := 3764991635558495095791895

theorem tailTrace_7332295 : CollatzResearch.WordTrace tailWord_7332295 prefixEnd_7332295 3764991635558495095791895 := by
  unfold tailWord_7332295
  simp only [CollatzResearch.WordTrace]
  refine ⟨267430768971354946133894339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178287179314236630755929559 267430768971354946133894339)
  ·
    refine ⟨401146153457032419200841509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267430768971354946133894339 401146153457032419200841509)
    ·
      refine ⟨75214903773193578600157783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401146153457032419200841509 75214903773193578600157783)
      ·
        refine ⟨112822355659790367900236675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75214903773193578600157783 112822355659790367900236675)
        ·
          refine ⟨169233533489685551850355013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112822355659790367900236675 169233533489685551850355013)
          ·
            refine ⟨31731287529316040971941565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169233533489685551850355013 31731287529316040971941565)
            ·
              refine ⟨11899232823493515364478087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31731287529316040971941565 11899232823493515364478087)
              ·
                refine ⟨17848849235240273046717131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11899232823493515364478087 17848849235240273046717131)
                ·
                  refine ⟨26773273852860409570075697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17848849235240273046717131 26773273852860409570075697)
                  ·
                    refine ⟨20079955389645307177556773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26773273852860409570075697 20079955389645307177556773)
                    ·
                      refine ⟨3764991635558495095791895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20079955389645307177556773 3764991635558495095791895)
                      ·
                        rfl

theorem cell23_7332295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 1, 2, 4].length) (baseStart_7332295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332295 prefixEnd_7332295 := by exact prefixLift 7332295
  have htrace : WordTrace (prefixWord ++ tailWord_7332295) baseStart_7332295 baseEnd_7332295 := by
    simpa [prefixWord, tailWord_7332295, baseEnd_7332295] using wordTrace_append hprefix tailTrace_7332295
  have hstable : (prefixWord ++ tailWord_7332295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332295).length < 2 ^ (prefixWord ++ tailWord_7332295).sum := by decide
  have hdescent : baseEnd_7332295 < baseStart_7332295 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332332 : List Nat := [2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 3]
def baseStart_7332332 : Nat := 118140960795 + 7332332 * 2 ^ 59
def prefixEnd_7332332 : Nat := 4983230072969 + 3 ^ 40 * 7332332 * 2
def baseEnd_7332332 : Nat := 3765010634342711451029225

theorem tailTrace_7332332 : CollatzResearch.WordTrace tailWord_7332332 prefixEnd_7332332 3765010634342711451029225 := by
  unfold tailWord_7332332
  simp only [CollatzResearch.WordTrace]
  refine ⟨133716059236110450726495625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178288078981480600968660833 133716059236110450726495625)
  ·
    refine ⟨100287044427082838044871719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133716059236110450726495625 100287044427082838044871719)
    ·
      refine ⟨150430566640624257067307579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100287044427082838044871719 150430566640624257067307579)
      ·
        refine ⟨225645849960936385600961369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150430566640624257067307579 225645849960936385600961369)
        ·
          refine ⟨169234387470702289200721027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225645849960936385600961369 169234387470702289200721027)
          ·
            refine ⟨253851581206053433801081541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169234387470702289200721027 253851581206053433801081541)
            ·
              refine ⟨47597171476135018837702789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 253851581206053433801081541 47597171476135018837702789)
              ·
                refine ⟨8924469651775316032069273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47597171476135018837702789 8924469651775316032069273)
                ·
                  refine ⟨6693352238831487024051955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8924469651775316032069273 6693352238831487024051955)
                  ·
                    refine ⟨10040028358247230536077933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6693352238831487024051955 10040028358247230536077933)
                    ·
                      refine ⟨3765010634342711451029225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10040028358247230536077933 3765010634342711451029225)
                      ·
                        rfl

theorem cell23_7332332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 3].length) (baseStart_7332332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332332 prefixEnd_7332332 := by exact prefixLift 7332332
  have htrace : WordTrace (prefixWord ++ tailWord_7332332) baseStart_7332332 baseEnd_7332332 := by
    simpa [prefixWord, tailWord_7332332, baseEnd_7332332] using wordTrace_append hprefix tailTrace_7332332
  have hstable : (prefixWord ++ tailWord_7332332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332332).length < 2 ^ (prefixWord ++ tailWord_7332332).sum := by decide
  have hdescent : baseEnd_7332332 < baseStart_7332332 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332348 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 1, 8]
def baseStart_7332348 : Nat := 118140960795 + 7332348 * 2 ^ 59
def prefixEnd_7332348 : Nat := 4983230072969 + 3 ^ 40 * 7332348 * 2
def baseEnd_7332348 : Nat := 1255006283344394462809717

theorem tailTrace_7332348 : CollatzResearch.WordTrace tailWord_7332348 prefixEnd_7332348 1255006283344394462809717 := by
  unfold tailWord_7332348
  simp only [CollatzResearch.WordTrace]
  refine ⟨133716351020081468092786849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178288468026775290790382465 133716351020081468092786849)
  ·
    refine ⟨100287263265061101069590137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133716351020081468092786849 100287263265061101069590137)
    ·
      refine ⟨75215447448795825802192603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100287263265061101069590137 75215447448795825802192603)
      ·
        refine ⟨112823171173193738703288905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75215447448795825802192603 112823171173193738703288905)
        ·
          refine ⟨84617378379895304027466679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112823171173193738703288905 84617378379895304027466679)
          ·
            refine ⟨126926067569842956041200019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84617378379895304027466679 126926067569842956041200019)
            ·
              refine ⟨190389101354764434061800029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126926067569842956041200019 190389101354764434061800029)
              ·
                refine ⟨71395913008036662773175011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190389101354764434061800029 71395913008036662773175011)
                ·
                  refine ⟨107093869512054994159762517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71395913008036662773175011 107093869512054994159762517)
                  ·
                    refine ⟨1255006283344394462809717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107093869512054994159762517 1255006283344394462809717)
                    ·
                      rfl

theorem cell23_7332348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 1, 8].length) (baseStart_7332348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332348 prefixEnd_7332348 := by exact prefixLift 7332348
  have htrace : WordTrace (prefixWord ++ tailWord_7332348) baseStart_7332348 baseEnd_7332348 := by
    simpa [prefixWord, tailWord_7332348, baseEnd_7332348] using wordTrace_append hprefix tailTrace_7332348
  have hstable : (prefixWord ++ tailWord_7332348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332348).length < 2 ^ (prefixWord ++ tailWord_7332348).sum := by decide
  have hdescent : baseEnd_7332348 < baseStart_7332348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332359 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 3, 3, 2]
def baseStart_7332359 : Nat := 118140960795 + 7332359 * 2 ^ 59
def prefixEnd_7332359 : Nat := 4983230072969 + 3 ^ 40 * 7332359 * 2
def baseEnd_7332359 : Nat := 3765024498320382845391601

theorem tailTrace_7332359 : CollatzResearch.WordTrace tailWord_7332359 prefixEnd_7332359 3765024498320382845391601 := by
  unfold tailWord_7332359
  simp only [CollatzResearch.WordTrace]
  refine ⟨267433103243123085064224131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178288735495415390042816087 267433103243123085064224131)
  ·
    refine ⟨401149654864684627596336197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267433103243123085064224131 401149654864684627596336197)
    ·
      refine ⟨75215560287128367674313037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401149654864684627596336197 75215560287128367674313037)
      ·
        refine ⟨28205835107673137877867389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75215560287128367674313037 28205835107673137877867389)
        ·
          refine ⟨10577188165377426704200271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28205835107673137877867389 10577188165377426704200271)
          ·
            refine ⟨15865782248066140056300407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10577188165377426704200271 15865782248066140056300407)
            ·
              refine ⟨23798673372099210084450611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15865782248066140056300407 23798673372099210084450611)
              ·
                refine ⟨35698010058148815126675917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23798673372099210084450611 35698010058148815126675917)
                ·
                  refine ⟨13386753771805805672503469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35698010058148815126675917 13386753771805805672503469)
                  ·
                    refine ⟨5020032664427177127188801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13386753771805805672503469 5020032664427177127188801)
                    ·
                      refine ⟨3765024498320382845391601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020032664427177127188801 3765024498320382845391601)
                      ·
                        rfl

theorem cell23_7332359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 3, 2].length) (baseStart_7332359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332359 prefixEnd_7332359 := by exact prefixLift 7332359
  have htrace : WordTrace (prefixWord ++ tailWord_7332359) baseStart_7332359 baseEnd_7332359 := by
    simpa [prefixWord, tailWord_7332359, baseEnd_7332359] using wordTrace_append hprefix tailTrace_7332359
  have hstable : (prefixWord ++ tailWord_7332359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332359).length < 2 ^ (prefixWord ++ tailWord_7332359).sum := by decide
  have hdescent : baseEnd_7332359 < baseStart_7332359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332376 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 1, 3, 2]
def baseStart_7332376 : Nat := 118140960795 + 7332376 * 2 ^ 59
def prefixEnd_7332376 : Nat := 4983230072969 + 3 ^ 40 * 7332376 * 2
def baseEnd_7332376 : Nat := 3765033227491509278879023

theorem tailTrace_7332376 : CollatzResearch.WordTrace tailWord_7332376 prefixEnd_7332376 3765033227491509278879023 := by
  unfold tailWord_7332376
  simp only [CollatzResearch.WordTrace]
  refine ⟨133716861642030748483796491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178289148856040997978395321 133716861642030748483796491)
  ·
    refine ⟨200575292463046122725694737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133716861642030748483796491 200575292463046122725694737)
    ·
      refine ⟨150431469347284592044271053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200575292463046122725694737 150431469347284592044271053)
      ·
        refine ⟨56411801005231722016601645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 150431469347284592044271053 56411801005231722016601645)
        ·
          refine ⟨21154425376961895756225617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56411801005231722016601645 21154425376961895756225617)
          ·
            refine ⟨15865819032721421817169213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21154425376961895756225617 15865819032721421817169213)
            ·
              refine ⟨5949682137270533181438455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15865819032721421817169213 5949682137270533181438455)
              ·
                refine ⟨8924523205905799772157683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5949682137270533181438455 8924523205905799772157683)
                ·
                  refine ⟨13386784808858699658236525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8924523205905799772157683 13386784808858699658236525)
                  ·
                    refine ⟨5020044303322012371838697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13386784808858699658236525 5020044303322012371838697)
                    ·
                      refine ⟨3765033227491509278879023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020044303322012371838697 3765033227491509278879023)
                      ·
                        rfl

theorem cell23_7332376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 1, 3, 2].length) (baseStart_7332376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332376 prefixEnd_7332376 := by exact prefixLift 7332376
  have htrace : WordTrace (prefixWord ++ tailWord_7332376) baseStart_7332376 baseEnd_7332376 := by
    simpa [prefixWord, tailWord_7332376, baseEnd_7332376] using wordTrace_append hprefix tailTrace_7332376
  have hstable : (prefixWord ++ tailWord_7332376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332376).length < 2 ^ (prefixWord ++ tailWord_7332376).sum := by decide
  have hdescent : baseEnd_7332376 < baseStart_7332376 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332385 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 4]
def baseStart_7332385 : Nat := 118140960795 + 7332385 * 2 ^ 59
def prefixEnd_7332385 : Nat := 4983230072969 + 3 ^ 40 * 7332385 * 2
def baseEnd_7332385 : Nat := 3765037848817399743666481

theorem tailTrace_7332385 : CollatzResearch.WordTrace tailWord_7332385 prefixEnd_7332385 3765037848817399743666481 := by
  unfold tailWord_7332385
  simp only [CollatzResearch.WordTrace]
  refine ⟨267434051541028891504670609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178289367694019261003113739 267434051541028891504670609)
  ·
    refine ⟨200575538655771668628502957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267434051541028891504670609 200575538655771668628502957)
    ·
      refine ⟨75215826995914375735688609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 200575538655771668628502957 75215826995914375735688609)
      ·
        refine ⟨56411870246935781801766457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75215826995914375735688609 56411870246935781801766457)
        ·
          refine ⟨42308902685201836351324843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56411870246935781801766457 42308902685201836351324843)
          ·
            refine ⟨63463354027802754526987265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42308902685201836351324843 63463354027802754526987265)
            ·
              refine ⟨47597515520852065895240449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63463354027802754526987265 47597515520852065895240449)
              ·
                refine ⟨35698136640639049421430337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47597515520852065895240449 35698136640639049421430337)
                ·
                  refine ⟨26773602480479287066072753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35698136640639049421430337 26773602480479287066072753)
                  ·
                    refine ⟨20080201860359465299554565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26773602480479287066072753 20080201860359465299554565)
                    ·
                      refine ⟨3765037848817399743666481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20080201860359465299554565 3765037848817399743666481)
                      ·
                        rfl

theorem cell23_7332385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 2, 2, 4].length) (baseStart_7332385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332385 prefixEnd_7332385 := by exact prefixLift 7332385
  have htrace : WordTrace (prefixWord ++ tailWord_7332385) baseStart_7332385 baseEnd_7332385 := by
    simpa [prefixWord, tailWord_7332385, baseEnd_7332385] using wordTrace_append hprefix tailTrace_7332385
  have hstable : (prefixWord ++ tailWord_7332385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332385).length < 2 ^ (prefixWord ++ tailWord_7332385).sum := by decide
  have hdescent : baseEnd_7332385 < baseStart_7332385 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332389 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 2, 2, 2]
def baseStart_7332389 : Nat := 118140960795 + 7332389 * 2 ^ 59
def prefixEnd_7332389 : Nat := 4983230072969 + 3 ^ 40 * 7332389 * 2
def baseEnd_7332389 : Nat := 3765039902740017728016463

theorem tailTrace_7332389 : CollatzResearch.WordTrace tailWord_7332389 prefixEnd_7332389 3765039902740017728016463 := by
  unfold tailWord_7332389
  simp only [CollatzResearch.WordTrace]
  refine ⟨267434197433014400187816221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178289464955342933458544147 267434197433014400187816221)
  ·
    refine ⟨100287824037380400070431083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267434197433014400187816221 100287824037380400070431083)
    ·
      refine ⟨150431736056070600105646625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100287824037380400070431083 150431736056070600105646625)
      ·
        refine ⟨112823802042052950079234969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150431736056070600105646625 112823802042052950079234969)
        ·
          refine ⟨84617851531539712559426227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112823802042052950079234969 84617851531539712559426227)
          ·
            refine ⟨126926777297309568839139341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84617851531539712559426227 126926777297309568839139341)
            ·
              refine ⟨47597541486491088314677253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126926777297309568839139341 47597541486491088314677253)
              ·
                refine ⟨8924539028717079059001985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47597541486491088314677253 8924539028717079059001985)
                ·
                  refine ⟨6693404271537809294251489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8924539028717079059001985 6693404271537809294251489)
                  ·
                    refine ⟨5020053203653356970688617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6693404271537809294251489 5020053203653356970688617)
                    ·
                      refine ⟨3765039902740017728016463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020053203653356970688617 3765039902740017728016463)
                      ·
                        rfl

theorem cell23_7332389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 2, 2].length) (baseStart_7332389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332389 prefixEnd_7332389 := by exact prefixLift 7332389
  have htrace : WordTrace (prefixWord ++ tailWord_7332389) baseStart_7332389 baseEnd_7332389 := by
    simpa [prefixWord, tailWord_7332389, baseEnd_7332389] using wordTrace_append hprefix tailTrace_7332389
  have hstable : (prefixWord ++ tailWord_7332389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332389).length < 2 ^ (prefixWord ++ tailWord_7332389).sum := by decide
  have hdescent : baseEnd_7332389 < baseStart_7332389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332392 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 2, 4, 3]
def baseStart_7332392 : Nat := 118140960795 + 7332392 * 2 ^ 59
def prefixEnd_7332392 : Nat := 4983230072969 + 3 ^ 40 * 7332392 * 2
def baseEnd_7332392 : Nat := 3765041443181981216278949

theorem tailTrace_7332392 : CollatzResearch.WordTrace tailWord_7332392 prefixEnd_7332392 3765041443181981216278949 := by
  unfold tailWord_7332392
  simp only [CollatzResearch.WordTrace]
  refine ⟨133717153426001765850087715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178289537901335687800116953 133717153426001765850087715)
  ·
    refine ⟨200575730139002648775131573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133717153426001765850087715 200575730139002648775131573)
    ·
      refine ⟨18803974700531498322668585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 200575730139002648775131573 18803974700531498322668585)
      ·
        refine ⟨14102981025398623742001439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18803974700531498322668585 14102981025398623742001439)
        ·
          refine ⟨21154471538097935613002159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14102981025398623742001439 21154471538097935613002159)
          ·
            refine ⟨31731707307146903419503239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21154471538097935613002159 31731707307146903419503239)
            ·
              refine ⟨47597560960720355129254859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31731707307146903419503239 47597560960720355129254859)
              ·
                refine ⟨71396341441080532693882289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47597560960720355129254859 71396341441080532693882289)
                ·
                  refine ⟨53547256080810399520411717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 71396341441080532693882289 53547256080810399520411717)
                  ·
                    refine ⟨10040110515151949910077197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53547256080810399520411717 10040110515151949910077197)
                    ·
                      refine ⟨3765041443181981216278949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10040110515151949910077197 3765041443181981216278949)
                      ·
                        rfl

theorem cell23_7332392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_7332392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332392 prefixEnd_7332392 := by exact prefixLift 7332392
  have htrace : WordTrace (prefixWord ++ tailWord_7332392) baseStart_7332392 baseEnd_7332392 := by
    simpa [prefixWord, tailWord_7332392, baseEnd_7332392] using wordTrace_append hprefix tailTrace_7332392
  have hstable : (prefixWord ++ tailWord_7332392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332392).length < 2 ^ (prefixWord ++ tailWord_7332392).sum := by decide
  have hdescent : baseEnd_7332392 < baseStart_7332392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332406 : List Nat := [5, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_7332406 : Nat := 118140960795 + 7332406 * 2 ^ 59
def prefixEnd_7332406 : Nat := 4983230072969 + 3 ^ 40 * 7332406 * 2
def baseEnd_7332406 : Nat := 3765048631911144161503885

theorem tailTrace_7332406 : CollatzResearch.WordTrace tailWord_7332406 prefixEnd_7332406 3765048631911144161503885 := by
  unfold tailWord_7332406
  simp only [CollatzResearch.WordTrace]
  refine ⟨16714676092122050755699067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178289878315968541394123381 16714676092122050755699067)
  ·
    refine ⟨25072014138183076133548601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16714676092122050755699067 25072014138183076133548601)
    ·
      refine ⟨18804010603637307100161451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25072014138183076133548601 18804010603637307100161451)
      ·
        refine ⟨28206015905455960650242177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18804010603637307100161451 28206015905455960650242177)
        ·
          refine ⟨21154511929091970487681633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28206015905455960650242177 21154511929091970487681633)
          ·
            refine ⟨15865883946818977865761225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21154511929091970487681633 15865883946818977865761225)
            ·
              refine ⟨11899412960114233399320919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15865883946818977865761225 11899412960114233399320919)
              ·
                refine ⟨17849119440171350098981379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11899412960114233399320919 17849119440171350098981379)
                ·
                  refine ⟨26773679160257025148472069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17849119440171350098981379 26773679160257025148472069)
                  ·
                    refine ⟨5020064842548192215338513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26773679160257025148472069 5020064842548192215338513)
                    ·
                      refine ⟨3765048631911144161503885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020064842548192215338513 3765048631911144161503885)
                      ·
                        rfl

theorem cell23_7332406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_7332406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332406 prefixEnd_7332406 := by exact prefixLift 7332406
  have htrace : WordTrace (prefixWord ++ tailWord_7332406) baseStart_7332406 baseEnd_7332406 := by
    simpa [prefixWord, tailWord_7332406, baseEnd_7332406] using wordTrace_append hprefix tailTrace_7332406
  have hstable : (prefixWord ++ tailWord_7332406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332406).length < 2 ^ (prefixWord ++ tailWord_7332406).sum := by decide
  have hdescent : baseEnd_7332406 < baseStart_7332406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332429 : List Nat := [1, 6, 1, 1, 2, 1, 1, 5, 5]
def baseStart_7332429 : Nat := 118140960795 + 7332429 * 2 ^ 59
def prefixEnd_7332429 : Nat := 4983230072969 + 3 ^ 40 * 7332429 * 2
def baseEnd_7332429 : Nat := 418340049107355285724031

theorem tailTrace_7332429 : CollatzResearch.WordTrace tailWord_7332429 prefixEnd_7332429 418340049107355285724031 := by
  unfold tailWord_7332429
  simp only [CollatzResearch.WordTrace]
  refine ⟨267435656352869487019272341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178290437568579658012848227 267435656352869487019272341)
  ·
    refine ⟨12536046391540757204028391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 267435656352869487019272341 12536046391540757204028391)
    ·
      refine ⟨18804069587311135806042587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12536046391540757204028391 18804069587311135806042587)
      ·
        refine ⟨28206104380966703709063881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18804069587311135806042587 28206104380966703709063881)
        ·
          refine ⟨21154578285725027781797911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28206104380966703709063881 21154578285725027781797911)
          ·
            refine ⟨31731867428587541672696867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21154578285725027781797911 31731867428587541672696867)
            ·
              refine ⟨47597801142881312509045301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31731867428587541672696867 47597801142881312509045301)
              ·
                refine ⟨4462293857145123047722997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47597801142881312509045301 4462293857145123047722997)
                ·
                  refine ⟨418340049107355285724031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4462293857145123047722997 418340049107355285724031)
                  ·
                    rfl

theorem cell23_7332429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_7332429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332429 prefixEnd_7332429 := by exact prefixLift 7332429
  have htrace : WordTrace (prefixWord ++ tailWord_7332429) baseStart_7332429 baseEnd_7332429 := by
    simpa [prefixWord, tailWord_7332429, baseEnd_7332429] using wordTrace_append hprefix tailTrace_7332429
  have hstable : (prefixWord ++ tailWord_7332429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332429).length < 2 ^ (prefixWord ++ tailWord_7332429).sum := by decide
  have hdescent : baseEnd_7332429 < baseStart_7332429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332462 : List Nat := [4, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_7332462 : Nat := 118140960795 + 7332462 * 2 ^ 59
def prefixEnd_7332462 : Nat := 4983230072969 + 3 ^ 40 * 7332462 * 2
def baseEnd_7332462 : Nat := 3765077386827795942403627

theorem tailTrace_7332462 : CollatzResearch.WordTrace tailWord_7332462 prefixEnd_7332462 3765077386827795942403627 := by
  unfold tailWord_7332462
  simp only [CollatzResearch.WordTrace]
  refine ⟨33429607495218741706902955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178291239974499955770149093 33429607495218741706902955)
  ·
    refine ⟨50144411242828112560354433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33429607495218741706902955 50144411242828112560354433)
    ·
      refine ⟨37608308432121084420265825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50144411242828112560354433 37608308432121084420265825)
      ·
        refine ⟨28206231324090813315199369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37608308432121084420265825 28206231324090813315199369)
        ·
          refine ⟨21154673493068109986399527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28206231324090813315199369 21154673493068109986399527)
          ·
            refine ⟨31732010239602164979599291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21154673493068109986399527 31732010239602164979599291)
            ·
              refine ⟨47598015359403247469398937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31732010239602164979599291 47598015359403247469398937)
              ·
                refine ⟨35698511519552435602049203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47598015359403247469398937 35698511519552435602049203)
                ·
                  refine ⟨53547767279328653403073805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35698511519552435602049203 53547767279328653403073805)
                  ·
                    refine ⟨20080412729748245026152677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53547767279328653403073805 20080412729748245026152677)
                    ·
                      refine ⟨3765077386827795942403627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20080412729748245026152677 3765077386827795942403627)
                      ·
                        rfl

theorem cell23_7332462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_7332462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332462 prefixEnd_7332462 := by exact prefixLift 7332462
  have htrace : WordTrace (prefixWord ++ tailWord_7332462) baseStart_7332462 baseEnd_7332462 := by
    simpa [prefixWord, tailWord_7332462, baseEnd_7332462] using wordTrace_append hprefix tailTrace_7332462
  have hstable : (prefixWord ++ tailWord_7332462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332462).length < 2 ^ (prefixWord ++ tailWord_7332462).sum := by decide
  have hdescent : baseEnd_7332462 < baseStart_7332462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332485 : List Nat := [1, 3, 1, 1, 4, 2, 1, 2, 8]
def baseStart_7332485 : Nat := 118140960795 + 7332485 * 2 ^ 59
def prefixEnd_7332485 : Nat := 4983230072969 + 3 ^ 40 * 7332485 * 2
def baseEnd_7332485 : Nat := 418343244098094372490669

theorem tailTrace_7332485 : CollatzResearch.WordTrace tailWord_7332485 prefixEnd_7332485 418343244098094372490669 := by
  unfold tailWord_7332485
  simp only [CollatzResearch.WordTrace]
  refine ⟨267437698840666608583310909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178291799227111072388873939 267437698840666608583310909)
  ·
    refine ⟨100289137065249978218741591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267437698840666608583310909 100289137065249978218741591)
    ·
      refine ⟨150433705597874967328112387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100289137065249978218741591 150433705597874967328112387)
      ·
        refine ⟨225650558396812450992168581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150433705597874967328112387 225650558396812450992168581)
        ·
          refine ⟨42309479699402334561031609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225650558396812450992168581 42309479699402334561031609)
          ·
            refine ⟨31732109774551750920773707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42309479699402334561031609 31732109774551750920773707)
            ·
              refine ⟨47598164661827626381160561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31732109774551750920773707 47598164661827626381160561)
              ·
                refine ⟨35698623496370719785870421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47598164661827626381160561 35698623496370719785870421)
                ·
                  refine ⟨418343244098094372490669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35698623496370719785870421 418343244098094372490669)
                  ·
                    rfl

theorem cell23_7332485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 8].length) (baseStart_7332485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332485 prefixEnd_7332485 := by exact prefixLift 7332485
  have htrace : WordTrace (prefixWord ++ tailWord_7332485) baseStart_7332485 baseEnd_7332485 := by
    simpa [prefixWord, tailWord_7332485, baseEnd_7332485] using wordTrace_append hprefix tailTrace_7332485
  have hstable : (prefixWord ++ tailWord_7332485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332485).length < 2 ^ (prefixWord ++ tailWord_7332485).sum := by decide
  have hdescent : baseEnd_7332485 < baseStart_7332485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332495 : List Nat := [1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 3]
def baseStart_7332495 : Nat := 118140960795 + 7332495 * 2 ^ 59
def prefixEnd_7332495 : Nat := 4983230072969 + 3 ^ 40 * 7332495 * 2
def baseEnd_7332495 : Nat := 3765094331689394313290975

theorem tailTrace_7332495 : CollatzResearch.WordTrace tailWord_7332495 prefixEnd_7332495 3765094331689394313290975 := by
  unfold tailWord_7332495
  simp only [CollatzResearch.WordTrace]
  refine ⟨267438063570630380291174939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178292042380420253527449959 267438063570630380291174939)
  ·
    refine ⟨401157095355945570436762409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267438063570630380291174939 401157095355945570436762409)
    ·
      refine ⟨300867821516959177827571807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401157095355945570436762409 300867821516959177827571807)
      ·
        refine ⟨451301732275438766741357711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300867821516959177827571807 451301732275438766741357711)
        ·
          refine ⟨676952598413158150112036567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451301732275438766741357711 676952598413158150112036567)
          ·
            refine ⟨1015428897619737225168054851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676952598413158150112036567 1015428897619737225168054851)
            ·
              refine ⟨1523143346429605837752082277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1015428897619737225168054851 1523143346429605837752082277)
              ·
                refine ⟨285589377455551094578515427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1523143346429605837752082277 285589377455551094578515427)
                ·
                  refine ⟨428384066183326641867773141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285589377455551094578515427 428384066183326641867773141)
                  ·
                    refine ⟨10040251551171718168775933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 428384066183326641867773141 10040251551171718168775933)
                    ·
                      refine ⟨3765094331689394313290975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10040251551171718168775933 3765094331689394313290975)
                      ·
                        rfl

theorem cell23_7332495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 7, 3].length) (baseStart_7332495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332495 prefixEnd_7332495 := by exact prefixLift 7332495
  have htrace : WordTrace (prefixWord ++ tailWord_7332495) baseStart_7332495 baseEnd_7332495 := by
    simpa [prefixWord, tailWord_7332495, baseEnd_7332495] using wordTrace_append hprefix tailTrace_7332495
  have hstable : (prefixWord ++ tailWord_7332495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332495).length < 2 ^ (prefixWord ++ tailWord_7332495).sum := by decide
  have hdescent : baseEnd_7332495 < baseStart_7332495 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332556 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 2, 3, 2]
def baseStart_7332556 : Nat := 118140960795 + 7332556 * 2 ^ 59
def prefixEnd_7332556 : Nat := 4983230072969 + 3 ^ 40 * 7332556 * 2
def baseEnd_7332556 : Nat := 3765125654009318574628195

theorem tailTrace_7332556 : CollatzResearch.WordTrace tailWord_7332556 prefixEnd_7332556 3765125654009318574628195 := by
  unfold tailWord_7332556
  simp only [CollatzResearch.WordTrace]
  refine ⟨133720144211704693854572761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178293525615606258472763681 133720144211704693854572761)
  ·
    refine ⟨100290108158778520390929571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133720144211704693854572761 100290108158778520390929571)
    ·
      refine ⟨150435162238167780586394357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100290108158778520390929571 150435162238167780586394357)
      ·
        refine ⟨14103296459828229429974471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 150435162238167780586394357 14103296459828229429974471)
        ·
          refine ⟨21154944689742344144961707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14103296459828229429974471 21154944689742344144961707)
          ·
            refine ⟨31732417034613516217442561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21154944689742344144961707 31732417034613516217442561)
            ·
              refine ⟨23799312775960137163081921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31732417034613516217442561 23799312775960137163081921)
              ·
                refine ⟨17849484581970102872311441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23799312775960137163081921 17849484581970102872311441)
                ·
                  refine ⟨13387113436477577154233581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17849484581970102872311441 13387113436477577154233581)
                  ·
                    refine ⟨5020167538679091432837593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13387113436477577154233581 5020167538679091432837593)
                    ·
                      refine ⟨3765125654009318574628195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020167538679091432837593 3765125654009318574628195)
                      ·
                        rfl

theorem cell23_7332556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_7332556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332556 prefixEnd_7332556 := by exact prefixLift 7332556
  have htrace : WordTrace (prefixWord ++ tailWord_7332556) baseStart_7332556 baseEnd_7332556 := by
    simpa [prefixWord, tailWord_7332556, baseEnd_7332556] using wordTrace_append hprefix tailTrace_7332556
  have hstable : (prefixWord ++ tailWord_7332556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332556).length < 2 ^ (prefixWord ++ tailWord_7332556).sum := by decide
  have hdescent : baseEnd_7332556 < baseStart_7332556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332557 : List Nat := [1, 6, 2, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7332557 : Nat := 118140960795 + 7332557 * 2 ^ 59
def prefixEnd_7332557 : Nat := 4983230072969 + 3 ^ 40 * 7332557 * 2
def baseEnd_7332557 : Nat := 1255042055829991023571897

theorem tailTrace_7332557 : CollatzResearch.WordTrace tailWord_7332557 prefixEnd_7332557 1255042055829991023571897 := by
  unfold tailWord_7332557
  simp only [CollatzResearch.WordTrace]
  refine ⟨267440324896405764879931925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178293549930937176586621283 267440324896405764879931925)
  ·
    refine ⟨12536265229519020228746809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 267440324896405764879931925 12536265229519020228746809)
    ·
      refine ⟨9402198922139265171560107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12536265229519020228746809 9402198922139265171560107)
      ·
        refine ⟨14103298383208897757340161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9402198922139265171560107 14103298383208897757340161)
        ·
          refine ⟨10577473787406673318005121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14103298383208897757340161 10577473787406673318005121)
          ·
            refine ⟨7933105340555004988503841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10577473787406673318005121 7933105340555004988503841)
            ·
              refine ⟨5949829005416253741377881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7933105340555004988503841 5949829005416253741377881)
              ·
                refine ⟨4462371754062190306033411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5949829005416253741377881 4462371754062190306033411)
                ·
                  refine ⟨6693557631093285459050117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462371754062190306033411 6693557631093285459050117)
                  ·
                    refine ⟨1255042055829991023571897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6693557631093285459050117 1255042055829991023571897)
                    ·
                      rfl

theorem cell23_7332557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7332557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332557 prefixEnd_7332557 := by exact prefixLift 7332557
  have htrace : WordTrace (prefixWord ++ tailWord_7332557) baseStart_7332557 baseEnd_7332557 := by
    simpa [prefixWord, tailWord_7332557, baseEnd_7332557] using wordTrace_append hprefix tailTrace_7332557
  have hstable : (prefixWord ++ tailWord_7332557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332557).length < 2 ^ (prefixWord ++ tailWord_7332557).sum := by decide
  have hdescent : baseEnd_7332557 < baseStart_7332557 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332579 : List Nat := [1, 1, 1, 7, 1, 2, 2, 1, 1, 6]
def baseStart_7332579 : Nat := 118140960795 + 7332579 * 2 ^ 59
def prefixEnd_7332579 : Nat := 4983230072969 + 3 ^ 40 * 7332579 * 2
def baseEnd_7332579 : Nat := 1255045821354790661546863

theorem tailTrace_7332579 : CollatzResearch.WordTrace tailWord_7332579 prefixEnd_7332579 1255045821354790661546863 := by
  unfold tailWord_7332579
  simp only [CollatzResearch.WordTrace]
  refine ⟨267441127302326062637232791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178294084868217375091488527 267441127302326062637232791)
  ·
    refine ⟨401161690953489093955849187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267441127302326062637232791 401161690953489093955849187)
    ·
      refine ⟨601742536430233640933773781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401161690953489093955849187 601742536430233640933773781)
      ·
        refine ⟨14103340697583600959385323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 601742536430233640933773781 14103340697583600959385323)
        ·
          refine ⟨21155011046375401439077985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14103340697583600959385323 21155011046375401439077985)
          ·
            refine ⟨15866258284781551079308489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21155011046375401439077985 15866258284781551079308489)
            ·
              refine ⟨11899693713586163309481367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15866258284781551079308489 11899693713586163309481367)
              ·
                refine ⟨17849540570379244964222051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11899693713586163309481367 17849540570379244964222051)
                ·
                  refine ⟨26774310855568867446333077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17849540570379244964222051 26774310855568867446333077)
                  ·
                    refine ⟨1255045821354790661546863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26774310855568867446333077 1255045821354790661546863)
                    ·
                      rfl

theorem cell23_7332579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 6].length) (baseStart_7332579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332579 prefixEnd_7332579 := by exact prefixLift 7332579
  have htrace : WordTrace (prefixWord ++ tailWord_7332579) baseStart_7332579 baseEnd_7332579 := by
    simpa [prefixWord, tailWord_7332579, baseEnd_7332579] using wordTrace_append hprefix tailTrace_7332579
  have hstable : (prefixWord ++ tailWord_7332579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332579).length < 2 ^ (prefixWord ++ tailWord_7332579).sum := by decide
  have hdescent : baseEnd_7332579 < baseStart_7332579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332589 : List Nat := [1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_7332589 : Nat := 118140960795 + 7332589 * 2 ^ 59
def prefixEnd_7332589 : Nat := 4983230072969 + 3 ^ 40 * 7332589 * 2
def baseEnd_7332589 : Nat := 3765142598870916945515543

theorem tailTrace_7332589 : CollatzResearch.WordTrace tailWord_7332589 prefixEnd_7332589 3765142598870916945515543 := by
  unfold tailWord_7332589
  simp only [CollatzResearch.WordTrace]
  refine ⟨267441492032289834345096821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178294328021526556230064547 267441492032289834345096821)
  ·
    refine ⟨25072639878027171969852827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 267441492032289834345096821 25072639878027171969852827)
    ·
      refine ⟨37608959817040757954779241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25072639878027171969852827 37608959817040757954779241)
      ·
        refine ⟨28206719862780568466084431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37608959817040757954779241 28206719862780568466084431)
        ·
          refine ⟨42310079794170852699126647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28206719862780568466084431 42310079794170852699126647)
          ·
            refine ⟨63465119691256279048689971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42310079794170852699126647 63465119691256279048689971)
            ·
              refine ⟨95197679536884418573034957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63465119691256279048689971 95197679536884418573034957)
              ·
                refine ⟨35699129826331656964888109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95197679536884418573034957 35699129826331656964888109)
                ·
                  refine ⟨13387173684874371361833041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35699129826331656964888109 13387173684874371361833041)
                  ·
                    refine ⟨10040380263655778521374781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13387173684874371361833041 10040380263655778521374781)
                    ·
                      refine ⟨3765142598870916945515543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10040380263655778521374781 3765142598870916945515543)
                      ·
                        rfl

theorem cell23_7332589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_7332589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332589 prefixEnd_7332589 := by exact prefixLift 7332589
  have htrace : WordTrace (prefixWord ++ tailWord_7332589) baseStart_7332589 baseEnd_7332589 := by
    simpa [prefixWord, tailWord_7332589, baseEnd_7332589] using wordTrace_append hprefix tailTrace_7332589
  have hstable : (prefixWord ++ tailWord_7332589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332589).length < 2 ^ (prefixWord ++ tailWord_7332589).sum := by decide
  have hdescent : baseEnd_7332589 < baseStart_7332589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332592 : List Nat := [2, 1, 1, 1, 3, 1, 7, 7]
def baseStart_7332592 : Nat := 118140960795 + 7332592 * 2 ^ 59
def prefixEnd_7332592 : Nat := 4983230072969 + 3 ^ 40 * 7332592 * 2
def baseEnd_7332592 : Nat := 139449782937514090139927

theorem tailTrace_7332592 : CollatzResearch.WordTrace tailWord_7332592 prefixEnd_7332592 139449782937514090139927 := by
  unfold tailWord_7332592
  simp only [CollatzResearch.WordTrace]
  refine ⟨133720800725639482928728015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178294400967519310571637353 133720800725639482928728015)
  ·
    refine ⟨200581201088459224393092023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133720800725639482928728015 200581201088459224393092023)
    ·
      refine ⟨300871801632688836589638035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200581201088459224393092023 300871801632688836589638035)
      ·
        refine ⟨451307702449033254884457053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300871801632688836589638035 451307702449033254884457053)
        ·
          refine ⟨169240388418387470581671395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451307702449033254884457053 169240388418387470581671395)
          ·
            refine ⟨253860582627581205872507093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169240388418387470581671395 253860582627581205872507093)
            ·
              refine ⟨5949857405333934512636885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 253860582627581205872507093 5949857405333934512636885)
              ·
                refine ⟨139449782937514090139927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5949857405333934512636885 139449782937514090139927)
                ·
                  rfl

theorem cell23_7332592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 7, 7].length) (baseStart_7332592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332592 prefixEnd_7332592 := by exact prefixLift 7332592
  have htrace : WordTrace (prefixWord ++ tailWord_7332592) baseStart_7332592 baseEnd_7332592 := by
    simpa [prefixWord, tailWord_7332592, baseEnd_7332592] using wordTrace_append hprefix tailTrace_7332592
  have hstable : (prefixWord ++ tailWord_7332592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332592).length < 2 ^ (prefixWord ++ tailWord_7332592).sum := by decide
  have hdescent : baseEnd_7332592 < baseStart_7332592 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332636 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 1, 3, 3]
def baseStart_7332636 : Nat := 118140960795 + 7332636 * 2 ^ 59
def prefixEnd_7332636 : Nat := 4983230072969 + 3 ^ 40 * 7332636 * 2
def baseEnd_7332636 : Nat := 3765166732461678261627827

theorem tailTrace_7332636 : CollatzResearch.WordTrace tailWord_7332636 prefixEnd_7332636 3765166732461678261627827 := by
  unfold tailWord_7332636
  simp only [CollatzResearch.WordTrace]
  refine ⟨133721603131559780686028881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178295470842079707581371841 133721603131559780686028881)
  ·
    refine ⟨100291202348669835514521661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133721603131559780686028881 100291202348669835514521661)
    ·
      refine ⟨37609200880751188317945623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100291202348669835514521661 37609200880751188317945623)
      ·
        refine ⟨56413801321126782476918435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37609200880751188317945623 56413801321126782476918435)
        ·
          refine ⟨84620701981690173715377653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56413801321126782476918435 84620701981690173715377653)
          ·
            refine ⟨7933190810783453785816655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 84620701981690173715377653 7933190810783453785816655)
            ·
              refine ⟨11899786216175180678724983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7933190810783453785816655 11899786216175180678724983)
              ·
                refine ⟨17849679324262771018087475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11899786216175180678724983 17849679324262771018087475)
                ·
                  refine ⟨26774518986394156527131213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17849679324262771018087475 26774518986394156527131213)
                  ·
                    refine ⟨10040444619897808697674205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26774518986394156527131213 10040444619897808697674205)
                    ·
                      refine ⟨3765166732461678261627827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10040444619897808697674205 3765166732461678261627827)
                      ·
                        rfl

theorem cell23_7332636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 1, 3, 3].length) (baseStart_7332636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332636 prefixEnd_7332636 := by exact prefixLift 7332636
  have htrace : WordTrace (prefixWord ++ tailWord_7332636) baseStart_7332636 baseEnd_7332636 := by
    simpa [prefixWord, tailWord_7332636, baseEnd_7332636] using wordTrace_append hprefix tailTrace_7332636
  have hstable : (prefixWord ++ tailWord_7332636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332636).length < 2 ^ (prefixWord ++ tailWord_7332636).sum := by decide
  have hdescent : baseEnd_7332636 < baseStart_7332636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332672 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4]
def baseStart_7332672 : Nat := 118140960795 + 7332672 * 2 ^ 59
def prefixEnd_7332672 : Nat := 4983230072969 + 3 ^ 40 * 7332672 * 2
def baseEnd_7332672 : Nat := 3765185217765240120777661

theorem tailTrace_7332672 : CollatzResearch.WordTrace tailWord_7332672 prefixEnd_7332672 3765185217765240120777661 := by
  unfold tailWord_7332672
  simp only [CollatzResearch.WordTrace]
  refine ⟨133722259645494569760184135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178296346193992759680245513 133722259645494569760184135)
  ·
    refine ⟨200583389468241854640276203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133722259645494569760184135 200583389468241854640276203)
    ·
      refine ⟨300875084202362781960414305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200583389468241854640276203 300875084202362781960414305)
      ·
        refine ⟨225656313151772086470310729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300875084202362781960414305 225656313151772086470310729)
        ·
          refine ⟨169242234863829064852733047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225656313151772086470310729 169242234863829064852733047)
          ·
            refine ⟨253863352295743597279099571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169242234863829064852733047 253863352295743597279099571)
            ·
              refine ⟨380795028443615395918649357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253863352295743597279099571 380795028443615395918649357)
              ·
                refine ⟨142798135666355773469493509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 380795028443615395918649357 142798135666355773469493509)
                ·
                  refine ⟨26774650437441707525530033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142798135666355773469493509 26774650437441707525530033)
                  ·
                    refine ⟨20080987828081280644147525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26774650437441707525530033 20080987828081280644147525)
                    ·
                      refine ⟨3765185217765240120777661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20080987828081280644147525 3765185217765240120777661)
                      ·
                        rfl

theorem cell23_7332672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 4].length) (baseStart_7332672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332672 prefixEnd_7332672 := by exact prefixLift 7332672
  have htrace : WordTrace (prefixWord ++ tailWord_7332672) baseStart_7332672 baseEnd_7332672 := by
    simpa [prefixWord, tailWord_7332672, baseEnd_7332672] using wordTrace_append hprefix tailTrace_7332672
  have hstable : (prefixWord ++ tailWord_7332672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332672).length < 2 ^ (prefixWord ++ tailWord_7332672).sum := by decide
  have hdescent : baseEnd_7332672 < baseStart_7332672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332682 : List Nat := [3, 1, 2, 1, 1, 1, 2, 5, 7]
def baseStart_7332682 : Nat := 118140960795 + 7332682 * 2 ^ 59
def prefixEnd_7332682 : Nat := 4983230072969 + 3 ^ 40 * 7332682 * 2
def baseEnd_7332682 : Nat := 418354483619087231294735

theorem tailTrace_7332682 : CollatzResearch.WordTrace tailWord_7332682 prefixEnd_7332682 418354483619087231294735 := by
  unfold tailWord_7332682
  simp only [CollatzResearch.WordTrace]
  refine ⟨66861221005238227807058075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178296589347301940818821533 66861221005238227807058075)
  ·
    refine ⟨100291831507857341710587113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66861221005238227807058075 100291831507857341710587113)
    ·
      refine ⟨75218873630893006282940335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100291831507857341710587113 75218873630893006282940335)
      ·
        refine ⟨112828310446339509424410503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75218873630893006282940335 112828310446339509424410503)
        ·
          refine ⟨169242465669509264136615755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112828310446339509424410503 169242465669509264136615755)
          ·
            refine ⟨253863698504263896204923633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169242465669509264136615755 253863698504263896204923633)
            ·
              refine ⟨190397773878197922153692725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253863698504263896204923633 190397773878197922153692725)
              ·
                refine ⟨17849791301081055201908693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 190397773878197922153692725 17849791301081055201908693)
                ·
                  refine ⟨418354483619087231294735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17849791301081055201908693 418354483619087231294735)
                  ·
                    rfl

theorem cell23_7332682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 5, 7].length) (baseStart_7332682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332682 prefixEnd_7332682 := by exact prefixLift 7332682
  have htrace : WordTrace (prefixWord ++ tailWord_7332682) baseStart_7332682 baseEnd_7332682 := by
    simpa [prefixWord, tailWord_7332682, baseEnd_7332682] using wordTrace_append hprefix tailTrace_7332682
  have hstable : (prefixWord ++ tailWord_7332682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332682).length < 2 ^ (prefixWord ++ tailWord_7332682).sum := by decide
  have hdescent : baseEnd_7332682 < baseStart_7332682 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332693 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 2, 2, 2]
def baseStart_7332693 : Nat := 118140960795 + 7332693 * 2 ^ 59
def prefixEnd_7332693 : Nat := 4983230072969 + 3 ^ 40 * 7332693 * 2
def baseEnd_7332693 : Nat := 3765196000858984538615065

theorem tailTrace_7332693 : CollatzResearch.WordTrace tailWord_7332693 prefixEnd_7332693 3765196000858984538615065 := by
  unfold tailWord_7332693
  simp only [CollatzResearch.WordTrace]
  refine ⟨267445285223913060106882733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178296856815942040071255155 267445285223913060106882733)
  ·
    refine ⟨100291981958967397540081025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267445285223913060106882733 100291981958967397540081025)
    ·
      refine ⟨75218986469225548155060769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100291981958967397540081025 75218986469225548155060769)
      ·
        refine ⟨56414239851919161116295577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75218986469225548155060769 56414239851919161116295577)
        ·
          refine ⟨42310679888939370837221683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56414239851919161116295577 42310679888939370837221683)
          ·
            refine ⟨63466019833409056255832525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42310679888939370837221683 63466019833409056255832525)
            ·
              refine ⟨23799757437528396095937197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63466019833409056255832525 23799757437528396095937197)
              ·
                refine ⟨8924909039073148535976449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23799757437528396095937197 8924909039073148535976449)
                ·
                  refine ⟨6693681779304861401982337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8924909039073148535976449 6693681779304861401982337)
                  ·
                    refine ⟨5020261334478646051486753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6693681779304861401982337 5020261334478646051486753)
                    ·
                      refine ⟨3765196000858984538615065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020261334478646051486753 3765196000858984538615065)
                      ·
                        rfl

theorem cell23_7332693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 2, 2].length) (baseStart_7332693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332693 prefixEnd_7332693 := by exact prefixLift 7332693
  have htrace : WordTrace (prefixWord ++ tailWord_7332693) baseStart_7332693 baseEnd_7332693 := by
    simpa [prefixWord, tailWord_7332693, baseEnd_7332693] using wordTrace_append hprefix tailTrace_7332693
  have hstable : (prefixWord ++ tailWord_7332693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332693).length < 2 ^ (prefixWord ++ tailWord_7332693).sum := by decide
  have hdescent : baseEnd_7332693 < baseStart_7332693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332719 : List Nat := [1, 1, 2, 1, 3, 1, 1, 2, 4, 5, 2]
def baseStart_7332719 : Nat := 118140960795 + 7332719 * 2 ^ 59
def prefixEnd_7332719 : Nat := 4983230072969 + 3 ^ 40 * 7332719 * 2
def baseEnd_7332719 : Nat := 3765209351356001436889945

theorem tailTrace_7332719 : CollatzResearch.WordTrace tailWord_7332719 prefixEnd_7332719 3765209351356001436889945 := by
  unfold tailWord_7332719
  simp only [CollatzResearch.WordTrace]
  refine ⟨267446233521818866547329211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178297489014545911031552807 267446233521818866547329211)
  ·
    refine ⟨401169350282728299820993817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267446233521818866547329211 401169350282728299820993817)
    ·
      refine ⟨300877012712046224865745363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401169350282728299820993817 300877012712046224865745363)
      ·
        refine ⟨451315519068069337298618045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300877012712046224865745363 451315519068069337298618045)
        ·
          refine ⟨169243319650526001486981767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451315519068069337298618045 169243319650526001486981767)
          ·
            refine ⟨253864979475789002230472651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169243319650526001486981767 253864979475789002230472651)
            ·
              refine ⟨380797469213683503345708977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253864979475789002230472651 380797469213683503345708977)
              ·
                refine ⟨285598101910262627509281733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380797469213683503345708977 285598101910262627509281733)
                ·
                  refine ⟨53549644108174242657990325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 285598101910262627509281733 53549644108174242657990325)
                  ·
                    refine ⟨5020279135141335249186593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 53549644108174242657990325 5020279135141335249186593)
                    ·
                      refine ⟨3765209351356001436889945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020279135141335249186593 3765209351356001436889945)
                      ·
                        rfl

theorem cell23_7332719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 5, 2].length) (baseStart_7332719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332719 prefixEnd_7332719 := by exact prefixLift 7332719
  have htrace : WordTrace (prefixWord ++ tailWord_7332719) baseStart_7332719 baseEnd_7332719 := by
    simpa [prefixWord, tailWord_7332719, baseEnd_7332719] using wordTrace_append hprefix tailTrace_7332719
  have hstable : (prefixWord ++ tailWord_7332719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332719).length < 2 ^ (prefixWord ++ tailWord_7332719).sum := by decide
  have hdescent : baseEnd_7332719 < baseStart_7332719 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332729 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 2, 5]
def baseStart_7332729 : Nat := 118140960795 + 7332729 * 2 ^ 59
def prefixEnd_7332729 : Nat := 4983230072969 + 3 ^ 40 * 7332729 * 2
def baseEnd_7332729 : Nat := 1255071495387515465921633

theorem tailTrace_7332729 : CollatzResearch.WordTrace tailWord_7332729 prefixEnd_7332729 1255071495387515465921633 := by
  unfold tailWord_7332729
  simp only [CollatzResearch.WordTrace]
  refine ⟨267446598251782638255193241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178297732167855092170128827 267446598251782638255193241)
  ·
    refine ⟨200584948688836978691394931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267446598251782638255193241 200584948688836978691394931)
    ·
      refine ⟨300877423033255468037092397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200584948688836978691394931 300877423033255468037092397)
      ·
        refine ⟨112829033637470800513909649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300877423033255468037092397 112829033637470800513909649)
        ·
          refine ⟨84621775228103100385432237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112829033637470800513909649 84621775228103100385432237)
          ·
            refine ⟨31733165710538662644537089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84621775228103100385432237 31733165710538662644537089)
            ·
              refine ⟨23799874282903996983402817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31733165710538662644537089 23799874282903996983402817)
              ·
                refine ⟨17849905712177997737552113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23799874282903996983402817 17849905712177997737552113)
                ·
                  refine ⟨13387429284133498303164085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17849905712177997737552113 13387429284133498303164085)
                  ·
                    refine ⟨1255071495387515465921633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13387429284133498303164085 1255071495387515465921633)
                    ·
                      rfl

theorem cell23_7332729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 2, 5].length) (baseStart_7332729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332729 prefixEnd_7332729 := by exact prefixLift 7332729
  have htrace : WordTrace (prefixWord ++ tailWord_7332729) baseStart_7332729 baseEnd_7332729 := by
    simpa [prefixWord, tailWord_7332729, baseEnd_7332729] using wordTrace_append hprefix tailTrace_7332729
  have hstable : (prefixWord ++ tailWord_7332729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332729).length < 2 ^ (prefixWord ++ tailWord_7332729).sum := by decide
  have hdescent : baseEnd_7332729 < baseStart_7332729 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332752 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 5]
def baseStart_7332752 : Nat := 118140960795 + 7332752 * 2 ^ 59
def prefixEnd_7332752 : Nat := 4983230072969 + 3 ^ 40 * 7332752 * 2
def baseEnd_7332752 : Nat := 3765226296217599807777293

theorem tailTrace_7332752 : CollatzResearch.WordTrace tailWord_7332752 prefixEnd_7332752 3765226296217599807777293 := by
  unfold tailWord_7332752
  simp only [CollatzResearch.WordTrace]
  refine ⟨133723718565349656591640255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178298291420466208788853673 133723718565349656591640255)
  ·
    refine ⟨200585577848024484887460383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133723718565349656591640255 200585577848024484887460383)
    ·
      refine ⟨300878366772036727331190575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200585577848024484887460383 300878366772036727331190575)
      ·
        refine ⟨451317550158055090996785863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300878366772036727331190575 451317550158055090996785863)
        ·
          refine ⟨676976325237082636495178795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451317550158055090996785863 676976325237082636495178795)
          ·
            refine ⟨1015464487855623954742768193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 676976325237082636495178795 1015464487855623954742768193)
            ·
              refine ⟨761598365891717966057076145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1015464487855623954742768193 761598365891717966057076145)
              ·
                refine ⟨571198774418788474542807109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 761598365891717966057076145 571198774418788474542807109)
                ·
                  refine ⟨107099770203522838976776333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 571198774418788474542807109 107099770203522838976776333)
                  ·
                    refine ⟨40162413826321064616291125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107099770203522838976776333 40162413826321064616291125)
                    ·
                      refine ⟨3765226296217599807777293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40162413826321064616291125 3765226296217599807777293)
                      ·
                        rfl

theorem cell23_7332752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 5].length) (baseStart_7332752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332752 prefixEnd_7332752 := by exact prefixLift 7332752
  have htrace : WordTrace (prefixWord ++ tailWord_7332752) baseStart_7332752 baseEnd_7332752 := by
    simpa [prefixWord, tailWord_7332752, baseEnd_7332752] using wordTrace_append hprefix tailTrace_7332752
  have hstable : (prefixWord ++ tailWord_7332752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332752).length < 2 ^ (prefixWord ++ tailWord_7332752).sum := by decide
  have hdescent : baseEnd_7332752 < baseStart_7332752 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332789 : List Nat := [1, 3, 3, 2, 1, 1, 3, 1, 8]
def baseStart_7332789 : Nat := 118140960795 + 7332789 * 2 ^ 59
def prefixEnd_7332789 : Nat := 4983230072969 + 3 ^ 40 * 7332789 * 2
def baseEnd_7332789 : Nat := 418360588333535129223847

theorem tailTrace_7332789 : CollatzResearch.WordTrace tailWord_7332789 prefixEnd_7332789 418360588333535129223847 := by
  unfold tailWord_7332789
  simp only [CollatzResearch.WordTrace]
  refine ⟨267448786631565268502377421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178299191087710179001584947 267448786631565268502377421)
  ·
    refine ⟨100293294986836975688391533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267448786631565268502377421 100293294986836975688391533)
    ·
      refine ⟨37609985620063865883146825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100293294986836975688391533 37609985620063865883146825)
      ·
        refine ⟨28207489215047899412360119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37609985620063865883146825 28207489215047899412360119)
        ·
          refine ⟨42311233822571849118540179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28207489215047899412360119 42311233822571849118540179)
          ·
            refine ⟨63466850733857773677810269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42311233822571849118540179 63466850733857773677810269)
            ·
              refine ⟨23800069025196665129178851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63466850733857773677810269 23800069025196665129178851)
              ·
                refine ⟨35700103537794997693768277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23800069025196665129178851 35700103537794997693768277)
                ·
                  refine ⟨418360588333535129223847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 35700103537794997693768277 418360588333535129223847)
                  ·
                    rfl

theorem cell23_7332789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 1, 8].length) (baseStart_7332789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332789 prefixEnd_7332789 := by exact prefixLift 7332789
  have htrace : WordTrace (prefixWord ++ tailWord_7332789) baseStart_7332789 baseEnd_7332789 := by
    simpa [prefixWord, tailWord_7332789, baseEnd_7332789] using wordTrace_append hprefix tailTrace_7332789
  have hstable : (prefixWord ++ tailWord_7332789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332789).length < 2 ^ (prefixWord ++ tailWord_7332789).sum := by decide
  have hdescent : baseEnd_7332789 < baseStart_7332789 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332793 : List Nat := [1, 2, 1, 4, 2, 2, 2, 4, 1, 4]
def baseStart_7332793 : Nat := 118140960795 + 7332793 * 2 ^ 59
def prefixEnd_7332793 : Nat := 4983230072969 + 3 ^ 40 * 7332793 * 2
def baseEnd_7332793 : Nat := 1255082449641478049121535

theorem tailTrace_7332793 : CollatzResearch.WordTrace tailWord_7332793 prefixEnd_7332793 1255082449641478049121535 := by
  unfold tailWord_7332793
  simp only [CollatzResearch.WordTrace]
  refine ⟨267448932523550777185523033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178299288349033851457015355 267448932523550777185523033)
  ·
    refine ⟨200586699392663082889142275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267448932523550777185523033 200586699392663082889142275)
    ·
      refine ⟨300880049088994624333713413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200586699392663082889142275 300880049088994624333713413)
      ·
        refine ⟨56415009204186492062571265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300880049088994624333713413 56415009204186492062571265)
        ·
          refine ⟨42311256903139869046928449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56415009204186492062571265 42311256903139869046928449)
          ·
            refine ⟨31733442677354901785196337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42311256903139869046928449 31733442677354901785196337)
            ·
              refine ⟨23800082008016176338897253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31733442677354901785196337 23800082008016176338897253)
              ·
                refine ⟨4462515376503033063543235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23800082008016176338897253 4462515376503033063543235)
                ·
                  refine ⟨6693773064754549595314853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462515376503033063543235 6693773064754549595314853)
                  ·
                    refine ⟨1255082449641478049121535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6693773064754549595314853 1255082449641478049121535)
                    ·
                      rfl

theorem cell23_7332793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 4, 1, 4].length) (baseStart_7332793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332793 prefixEnd_7332793 := by exact prefixLift 7332793
  have htrace : WordTrace (prefixWord ++ tailWord_7332793) baseStart_7332793 baseEnd_7332793 := by
    simpa [prefixWord, tailWord_7332793, baseEnd_7332793] using wordTrace_append hprefix tailTrace_7332793
  have hstable : (prefixWord ++ tailWord_7332793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332793).length < 2 ^ (prefixWord ++ tailWord_7332793).sum := by decide
  have hdescent : baseEnd_7332793 < baseStart_7332793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332859 : List Nat := [1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 3]
def baseStart_7332859 : Nat := 118140960795 + 7332859 * 2 ^ 59
def prefixEnd_7332859 : Nat := 4983230072969 + 3 ^ 40 * 7332859 * 2
def baseEnd_7332859 : Nat := 3765281238647630889139301

theorem tailTrace_7332859 : CollatzResearch.WordTrace tailWord_7332859 prefixEnd_7332859 3765281238647630889139301 := by
  unfold tailWord_7332859
  simp only [CollatzResearch.WordTrace]
  refine ⟨267451339741311670457425631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178300893160874446971617087 267451339741311670457425631)
  ·
    refine ⟨401177009611967505686138447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267451339741311670457425631 401177009611967505686138447)
    ·
      refine ⟨601765514417951258529207671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401177009611967505686138447 601765514417951258529207671)
      ·
        refine ⟨902648271626926887793811507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601765514417951258529207671 902648271626926887793811507)
        ·
          refine ⟨1353972407440390331690717261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902648271626926887793811507 1353972407440390331690717261)
          ·
            refine ⟨507739652790146374384018973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1353972407440390331690717261 507739652790146374384018973)
            ·
              refine ⟨190402369796304890394007115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 507739652790146374384018973 190402369796304890394007115)
              ·
                refine ⟨285603554694457335591010673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190402369796304890394007115 285603554694457335591010673)
                ·
                  refine ⟨214202666020843001693258005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 285603554694457335591010673 214202666020843001693258005)
                  ·
                    refine ⟨10040749969727015704371469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 214202666020843001693258005 10040749969727015704371469)
                    ·
                      refine ⟨3765281238647630889139301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10040749969727015704371469 3765281238647630889139301)
                      ·
                        rfl

theorem cell23_7332859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 6, 3].length) (baseStart_7332859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332859 prefixEnd_7332859 := by exact prefixLift 7332859
  have htrace : WordTrace (prefixWord ++ tailWord_7332859) baseStart_7332859 baseEnd_7332859 := by
    simpa [prefixWord, tailWord_7332859, baseEnd_7332859] using wordTrace_append hprefix tailTrace_7332859
  have hstable : (prefixWord ++ tailWord_7332859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332859).length < 2 ^ (prefixWord ++ tailWord_7332859).sum := by decide
  have hdescent : baseEnd_7332859 < baseStart_7332859 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332869 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 6]
def baseStart_7332869 : Nat := 118140960795 + 7332869 * 2 ^ 59
def prefixEnd_7332869 : Nat := 4983230072969 + 3 ^ 40 * 7332869 * 2
def baseEnd_7332869 : Nat := 3765286373454175850014255

theorem tailTrace_7332869 : CollatzResearch.WordTrace tailWord_7332869 prefixEnd_7332869 3765286373454175850014255 := by
  unfold tailWord_7332869
  simp only [CollatzResearch.WordTrace]
  refine ⟨267451704471275442165289661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178301136314183628110193107 267451704471275442165289661)
  ·
    refine ⟨100294389176728290811983623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267451704471275442165289661 100294389176728290811983623)
    ·
      refine ⟨150441583765092436217975435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100294389176728290811983623 150441583765092436217975435)
      ·
        refine ⟨225662375647638654326963153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150441583765092436217975435 225662375647638654326963153)
        ·
          refine ⟨169246781735728990745222365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225662375647638654326963153 169246781735728990745222365)
          ·
            refine ⟨63467543150898371529458387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169246781735728990745222365 63467543150898371529458387)
            ·
              refine ⟨95201314726347557294187581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63467543150898371529458387 95201314726347557294187581)
              ·
                refine ⟨35700493022380333985320343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95201314726347557294187581 35700493022380333985320343)
                ·
                  refine ⟨53550739533570500977980515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35700493022380333985320343 53550739533570500977980515)
                  ·
                    refine ⟨80326109300355751466970773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53550739533570500977980515 80326109300355751466970773)
                    ·
                      refine ⟨3765286373454175850014255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80326109300355751466970773 3765286373454175850014255)
                      ·
                        rfl

theorem cell23_7332869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 1, 6].length) (baseStart_7332869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332869 prefixEnd_7332869 := by exact prefixLift 7332869
  have htrace : WordTrace (prefixWord ++ tailWord_7332869) baseStart_7332869 baseEnd_7332869 := by
    simpa [prefixWord, tailWord_7332869, baseEnd_7332869] using wordTrace_append hprefix tailTrace_7332869
  have hstable : (prefixWord ++ tailWord_7332869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332869).length < 2 ^ (prefixWord ++ tailWord_7332869).sum := by decide
  have hdescent : baseEnd_7332869 < baseStart_7332869 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332873 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 3, 2, 2]
def baseStart_7332873 : Nat := 118140960795 + 7332873 * 2 ^ 59
def prefixEnd_7332873 : Nat := 4983230072969 + 3 ^ 40 * 7332873 * 2
def baseEnd_7332873 : Nat := 3765288427376793834364237

theorem tailTrace_7332873 : CollatzResearch.WordTrace tailWord_7332873 prefixEnd_7332873 3765288427376793834364237 := by
  unfold tailWord_7332873
  simp only [CollatzResearch.WordTrace]
  refine ⟨267451850363260950848435273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178301233575507300565623515 267451850363260950848435273)
  ·
    refine ⟨200588887772445713136326455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267451850363260950848435273 200588887772445713136326455)
    ·
      refine ⟨300883331658668569704489683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200588887772445713136326455 300883331658668569704489683)
      ·
        refine ⟨451324997488002854556734525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300883331658668569704489683 451324997488002854556734525)
        ·
          refine ⟨169246874058001070458775447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451324997488002854556734525 169246874058001070458775447)
          ·
            refine ⟨253870311087001605688163171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169246874058001070458775447 253870311087001605688163171)
            ·
              refine ⟨380805466630502408532244757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253870311087001605688163171 380805466630502408532244757)
              ·
                refine ⟨17850256248304800399948973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 380805466630502408532244757 17850256248304800399948973)
                ·
                  refine ⟨6693846093114300149980865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17850256248304800399948973 6693846093114300149980865)
                  ·
                    refine ⟨5020384569835725112485649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6693846093114300149980865 5020384569835725112485649)
                    ·
                      refine ⟨3765288427376793834364237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020384569835725112485649 3765288427376793834364237)
                      ·
                        rfl

theorem cell23_7332873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 2, 2].length) (baseStart_7332873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332873 prefixEnd_7332873 := by exact prefixLift 7332873
  have htrace : WordTrace (prefixWord ++ tailWord_7332873) baseStart_7332873 baseEnd_7332873 := by
    simpa [prefixWord, tailWord_7332873, baseEnd_7332873] using wordTrace_append hprefix tailTrace_7332873
  have hstable : (prefixWord ++ tailWord_7332873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332873).length < 2 ^ (prefixWord ++ tailWord_7332873).sum := by decide
  have hdescent : baseEnd_7332873 < baseStart_7332873 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332896 : List Nat := [2, 1, 1, 7, 1, 11]
def baseStart_7332896 : Nat := 118140960795 + 7332896 * 2 ^ 59
def prefixEnd_7332896 : Nat := 4983230072969 + 3 ^ 40 * 7332896 * 2
def baseEnd_7332896 : Nat := 15495062705480852857517

theorem tailTrace_7332896 : CollatzResearch.WordTrace tailWord_7332896 prefixEnd_7332896 15495062705480852857517 := by
  unfold tailWord_7332896
  simp only [CollatzResearch.WordTrace]
  refine ⟨133726344621088812888261271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178301792828118417184348361 133726344621088812888261271)
  ·
    refine ⟨200589516931633219332391907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133726344621088812888261271 200589516931633219332391907)
    ·
      refine ⟨300884275397449828998587861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200589516931633219332391907 300884275397449828998587861)
      ·
        refine ⟨7051975204627730367154403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 300884275397449828998587861 7051975204627730367154403)
        ·
          refine ⟨10577962806941595550731605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7051975204627730367154403 10577962806941595550731605)
          ·
            refine ⟨15495062705480852857517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10577962806941595550731605 15495062705480852857517)
            ·
              rfl

theorem cell23_7332896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 11].length) (baseStart_7332896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332896 prefixEnd_7332896 := by exact prefixLift 7332896
  have htrace : WordTrace (prefixWord ++ tailWord_7332896) baseStart_7332896 baseEnd_7332896 := by
    simpa [prefixWord, tailWord_7332896, baseEnd_7332896] using wordTrace_append hprefix tailTrace_7332896
  have hstable : (prefixWord ++ tailWord_7332896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332896).length < 2 ^ (prefixWord ++ tailWord_7332896).sum := by decide
  have hdescent : baseEnd_7332896 < baseStart_7332896 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332900 : List Nat := [2, 3, 1, 4, 1, 2, 2, 2, 2, 4]
def baseStart_7332900 : Nat := 118140960795 + 7332900 * 2 ^ 59
def prefixEnd_7332900 : Nat := 4983230072969 + 3 ^ 40 * 7332900 * 2
def baseEnd_7332900 : Nat := 1255100763784821742908871

theorem tailTrace_7332900 : CollatzResearch.WordTrace tailWord_7332900 prefixEnd_7332900 1255100763784821742908871 := by
  unfold tailWord_7332900
  simp only [CollatzResearch.WordTrace]
  refine ⟨133726417567081567229834077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178301890089442089639778769 133726417567081567229834077)
  ·
    refine ⟨50147406587655587711187779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133726417567081567229834077 50147406587655587711187779)
    ·
      refine ⟨75221109881483381566781669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50147406587655587711187779 75221109881483381566781669)
      ·
        refine ⟨14103958102778134043771563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 75221109881483381566781669 14103958102778134043771563)
        ·
          refine ⟨21155937154167201065657345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14103958102778134043771563 21155937154167201065657345)
          ·
            refine ⟨15866952865625400799243009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21155937154167201065657345 15866952865625400799243009)
            ·
              refine ⟨11900214649219050599432257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15866952865625400799243009 11900214649219050599432257)
              ·
                refine ⟨8925160986914287949574193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11900214649219050599432257 8925160986914287949574193)
                ·
                  refine ⟨6693870740185715962180645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8925160986914287949574193 6693870740185715962180645)
                  ·
                    refine ⟨1255100763784821742908871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6693870740185715962180645 1255100763784821742908871)
                    ·
                      rfl

theorem cell23_7332900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_7332900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332900 prefixEnd_7332900 := by exact prefixLift 7332900
  have htrace : WordTrace (prefixWord ++ tailWord_7332900) baseStart_7332900 baseEnd_7332900 := by
    simpa [prefixWord, tailWord_7332900, baseEnd_7332900] using wordTrace_append hprefix tailTrace_7332900
  have hstable : (prefixWord ++ tailWord_7332900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332900).length < 2 ^ (prefixWord ++ tailWord_7332900).sum := by decide
  have hdescent : baseEnd_7332900 < baseStart_7332900 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332919 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_7332919 : Nat := 118140960795 + 7332919 * 2 ^ 59
def prefixEnd_7332919 : Nat := 4983230072969 + 3 ^ 40 * 7332919 * 2
def baseEnd_7332919 : Nat := 3765312047486900654389025

theorem tailTrace_7332919 : CollatzResearch.WordTrace tailWord_7332919 prefixEnd_7332919 3765312047486900654389025 := by
  unfold tailWord_7332919
  simp only [CollatzResearch.WordTrace]
  refine ⟨267453528121094300704609811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178302352080729533803073207 267453528121094300704609811)
  ·
    refine ⟨401180292181641451056914717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267453528121094300704609811 401180292181641451056914717)
    ·
      refine ⟨150442609568115544146343019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401180292181641451056914717 150442609568115544146343019)
      ·
        refine ⟨225663914352173316219514529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150442609568115544146343019 225663914352173316219514529)
        ·
          refine ⟨169247935764129987164635897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225663914352173316219514529 169247935764129987164635897)
          ·
            refine ⟨126935951823097490373476923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169247935764129987164635897 126935951823097490373476923)
            ·
              refine ⟨190403927734646235560215385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126935951823097490373476923 190403927734646235560215385)
              ·
                refine ⟨142802945800984676670161539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190403927734646235560215385 142802945800984676670161539)
                ·
                  refine ⟨214204418701477015005242309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142802945800984676670161539 214204418701477015005242309)
                  ·
                    refine ⟨40163328506526940313482933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 214204418701477015005242309 40163328506526940313482933)
                    ·
                      refine ⟨3765312047486900654389025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40163328506526940313482933 3765312047486900654389025)
                      ·
                        rfl

theorem cell23_7332919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_7332919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332919 prefixEnd_7332919 := by exact prefixLift 7332919
  have htrace : WordTrace (prefixWord ++ tailWord_7332919) baseStart_7332919 baseEnd_7332919 := by
    simpa [prefixWord, tailWord_7332919, baseEnd_7332919] using wordTrace_append hprefix tailTrace_7332919
  have hstable : (prefixWord ++ tailWord_7332919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332919).length < 2 ^ (prefixWord ++ tailWord_7332919).sum := by decide
  have hdescent : baseEnd_7332919 < baseStart_7332919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332933 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 3, 3, 2]
def baseStart_7332933 : Nat := 118140960795 + 7332933 * 2 ^ 59
def prefixEnd_7332933 : Nat := 4983230072969 + 3 ^ 40 * 7332933 * 2
def baseEnd_7332933 : Nat := 3765319236216063599613961

theorem tailTrace_7332933 : CollatzResearch.WordTrace tailWord_7332933 prefixEnd_7332933 3765319236216063599613961 := by
  unfold tailWord_7332933
  simp only [CollatzResearch.WordTrace]
  refine ⟨267454038743043581095619453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178302692495362387397079635 267454038743043581095619453)
  ·
    refine ⟨100295264528641342910857295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267454038743043581095619453 100295264528641342910857295)
    ·
      refine ⟨150442896792962014366285943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100295264528641342910857295 150442896792962014366285943)
      ·
        refine ⟨225664345189443021549428915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150442896792962014366285943 225664345189443021549428915)
        ·
          refine ⟨338496517784164532324143373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225664345189443021549428915 338496517784164532324143373)
          ·
            refine ⟨126936194169061699621553765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 338496517784164532324143373 126936194169061699621553765)
            ·
              refine ⟨23800536406699068679041331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 126936194169061699621553765 23800536406699068679041331)
              ·
                refine ⟨35700804610048603018561997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23800536406699068679041331 35700804610048603018561997)
                ·
                  refine ⟨13387801728768226131960749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35700804610048603018561997 13387801728768226131960749)
                  ·
                    refine ⟨5020425648288084799485281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13387801728768226131960749 5020425648288084799485281)
                    ·
                      refine ⟨3765319236216063599613961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020425648288084799485281 3765319236216063599613961)
                      ·
                        rfl

theorem cell23_7332933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 3, 2].length) (baseStart_7332933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332933 prefixEnd_7332933 := by exact prefixLift 7332933
  have htrace : WordTrace (prefixWord ++ tailWord_7332933) baseStart_7332933 baseEnd_7332933 := by
    simpa [prefixWord, tailWord_7332933, baseEnd_7332933] using wordTrace_append hprefix tailTrace_7332933
  have hstable : (prefixWord ++ tailWord_7332933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332933).length < 2 ^ (prefixWord ++ tailWord_7332933).sum := by decide
  have hdescent : baseEnd_7332933 < baseStart_7332933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332939 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 6, 6]
def baseStart_7332939 : Nat := 118140960795 + 7332939 * 2 ^ 59
def prefixEnd_7332939 : Nat := 4983230072969 + 3 ^ 40 * 7332939 * 2
def baseEnd_7332939 : Nat := 1255107439033330192046311

theorem tailTrace_7332939 : CollatzResearch.WordTrace tailWord_7332939 prefixEnd_7332939 1255107439033330192046311 := by
  unfold tailWord_7332939
  simp only [CollatzResearch.WordTrace]
  refine ⟨267454257581021844120337871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178302838387347896080225247 267454257581021844120337871)
  ·
    refine ⟨401181386371532766180506807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267454257581021844120337871 401181386371532766180506807)
    ·
      refine ⟨601772079557299149270760211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401181386371532766180506807 601772079557299149270760211)
      ·
        refine ⟨902658119335948723906140317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601772079557299149270760211 902658119335948723906140317)
        ·
          refine ⟨338496794750980771464802619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 902658119335948723906140317 338496794750980771464802619)
          ·
            refine ⟨507745192126471157197203929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338496794750980771464802619 507745192126471157197203929)
            ·
              refine ⟨380808894094853367897902947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507745192126471157197203929 380808894094853367897902947)
              ·
                refine ⟨571213341142280051846854421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380808894094853367897902947 571213341142280051846854421)
                ·
                  refine ⟨26775625366044377430321301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 571213341142280051846854421 26775625366044377430321301)
                  ·
                    refine ⟨1255107439033330192046311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26775625366044377430321301 1255107439033330192046311)
                    ·
                      rfl

theorem cell23_7332939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 6].length) (baseStart_7332939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332939 prefixEnd_7332939 := by exact prefixLift 7332939
  have htrace : WordTrace (prefixWord ++ tailWord_7332939) baseStart_7332939 baseEnd_7332939 := by
    simpa [prefixWord, tailWord_7332939, baseEnd_7332939] using wordTrace_append hprefix tailTrace_7332939
  have hstable : (prefixWord ++ tailWord_7332939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332939).length < 2 ^ (prefixWord ++ tailWord_7332939).sum := by decide
  have hdescent : baseEnd_7332939 < baseStart_7332939 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332956 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 4, 6]
def baseStart_7332956 : Nat := 118140960795 + 7332956 * 2 ^ 59
def prefixEnd_7332956 : Nat := 4983230072969 + 3 ^ 40 * 7332956 * 2
def baseEnd_7332956 : Nat := 1255110348757039003208785

theorem tailTrace_7332956 : CollatzResearch.WordTrace tailWord_7332956 prefixEnd_7332956 1255110348757039003208785 := by
  unfold tailWord_7332956
  simp only [CollatzResearch.WordTrace]
  refine ⟨133727438810980128011853361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178303251747973504015804481 133727438810980128011853361)
  ·
    refine ⟨100295579108235096008890021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133727438810980128011853361 100295579108235096008890021)
    ·
      refine ⟨18805421082794080501666879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100295579108235096008890021 18805421082794080501666879)
      ·
        refine ⟨28208131624191120752500319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18805421082794080501666879 28208131624191120752500319)
        ·
          refine ⟨42312197436286681128750479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28208131624191120752500319 42312197436286681128750479)
          ·
            refine ⟨63468296154430021693125719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42312197436286681128750479 63468296154430021693125719)
            ·
              refine ⟨95202444231645032539688579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63468296154430021693125719 95202444231645032539688579)
              ·
                refine ⟨142803666347467548809532869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95202444231645032539688579 142803666347467548809532869)
                ·
                  refine ⟨26775687440150165401787413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142803666347467548809532869 26775687440150165401787413)
                  ·
                    refine ⟨1255110348757039003208785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26775687440150165401787413 1255110348757039003208785)
                    ·
                      rfl

theorem cell23_7332956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_7332956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332956 prefixEnd_7332956 := by exact prefixLift 7332956
  have htrace : WordTrace (prefixWord ++ tailWord_7332956) baseStart_7332956 baseEnd_7332956 := by
    simpa [prefixWord, tailWord_7332956, baseEnd_7332956] using wordTrace_append hprefix tailTrace_7332956
  have hstable : (prefixWord ++ tailWord_7332956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332956).length < 2 ^ (prefixWord ++ tailWord_7332956).sum := by decide
  have hdescent : baseEnd_7332956 < baseStart_7332956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332957 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 3]
def baseStart_7332957 : Nat := 118140960795 + 7332957 * 2 ^ 59
def prefixEnd_7332957 : Nat := 4983230072969 + 3 ^ 40 * 7332957 * 2
def baseEnd_7332957 : Nat := 3765331559751771505713851

theorem tailTrace_7332957 : CollatzResearch.WordTrace tailWord_7332957 prefixEnd_7332957 3765331559751771505713851 := by
  unfold tailWord_7332957
  simp only [CollatzResearch.WordTrace]
  refine ⟨267454914094956633194493125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178303276063304422129662083 267454914094956633194493125)
  ·
    refine ⟨50147796392804368723967461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267454914094956633194493125 50147796392804368723967461)
    ·
      refine ⟨9402711823650819135743899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50147796392804368723967461 9402711823650819135743899)
      ·
        refine ⟨14104067735476228703615849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9402711823650819135743899 14104067735476228703615849)
        ·
          refine ⟨10578050801607171527711887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14104067735476228703615849 10578050801607171527711887)
          ·
            refine ⟨15867076202410757291567831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10578050801607171527711887 15867076202410757291567831)
            ·
              refine ⟨23800614303616135937351747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15867076202410757291567831 23800614303616135937351747)
              ·
                refine ⟨35700921455424203906027621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23800614303616135937351747 35700921455424203906027621)
                ·
                  refine ⟨6693922772892038232380179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35700921455424203906027621 6693922772892038232380179)
                  ·
                    refine ⟨10040884159338057348570269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6693922772892038232380179 10040884159338057348570269)
                    ·
                      refine ⟨3765331559751771505713851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10040884159338057348570269 3765331559751771505713851)
                      ·
                        rfl

theorem cell23_7332957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_7332957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332957 prefixEnd_7332957 := by exact prefixLift 7332957
  have htrace : WordTrace (prefixWord ++ tailWord_7332957) baseStart_7332957 baseEnd_7332957 := by
    simpa [prefixWord, tailWord_7332957, baseEnd_7332957] using wordTrace_append hprefix tailTrace_7332957
  have hstable : (prefixWord ++ tailWord_7332957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332957).length < 2 ^ (prefixWord ++ tailWord_7332957).sum := by decide
  have hdescent : baseEnd_7332957 < baseStart_7332957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332976 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 4]
def baseStart_7332976 : Nat := 118140960795 + 7332976 * 2 ^ 59
def prefixEnd_7332976 : Nat := 4983230072969 + 3 ^ 40 * 7332976 * 2
def baseEnd_7332976 : Nat := 3765341315884206931376263

theorem tailTrace_7332976 : CollatzResearch.WordTrace tailWord_7332976 prefixEnd_7332976 3765341315884206931376263 := by
  unfold tailWord_7332976
  simp only [CollatzResearch.WordTrace]
  refine ⟨133727803540943899719717391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178303738054591866292956521 133727803540943899719717391)
  ·
    refine ⟨200591705311415849579576087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133727803540943899719717391 200591705311415849579576087)
    ·
      refine ⟨300887557967123774369364131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200591705311415849579576087 300887557967123774369364131)
      ·
        refine ⟨451331336950685661554046197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300887557967123774369364131 451331336950685661554046197)
        ·
          refine ⟨42312312839126780770691831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 451331336950685661554046197 42312312839126780770691831)
          ·
            refine ⟨63468469258690171156037747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42312312839126780770691831 63468469258690171156037747)
            ·
              refine ⟨95202703888035256734056621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63468469258690171156037747 95202703888035256734056621)
              ·
                refine ⟨35701013958013221275271233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95202703888035256734056621 35701013958013221275271233)
                ·
                  refine ⟨26775760468509915956453425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35701013958013221275271233 26775760468509915956453425)
                  ·
                    refine ⟨20081820351382436967340069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26775760468509915956453425 20081820351382436967340069)
                    ·
                      refine ⟨3765341315884206931376263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20081820351382436967340069 3765341315884206931376263)
                      ·
                        rfl

theorem cell23_7332976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_7332976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332976 prefixEnd_7332976 := by exact prefixLift 7332976
  have htrace : WordTrace (prefixWord ++ tailWord_7332976) baseStart_7332976 baseEnd_7332976 := by
    simpa [prefixWord, tailWord_7332976, baseEnd_7332976] using wordTrace_append hprefix tailTrace_7332976
  have hstable : (prefixWord ++ tailWord_7332976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332976).length < 2 ^ (prefixWord ++ tailWord_7332976).sum := by decide
  have hdescent : baseEnd_7332976 < baseStart_7332976 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7332979 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 9]
def baseStart_7332979 : Nat := 118140960795 + 7332979 * 2 ^ 59
def prefixEnd_7332979 : Nat := 4983230072969 + 3 ^ 40 * 7332979 * 2
def baseEnd_7332979 : Nat := 3765342856326170419638749

theorem tailTrace_7332979 : CollatzResearch.WordTrace tailWord_7332979 prefixEnd_7332979 3765342856326170419638749 := by
  unfold tailWord_7332979
  simp only [CollatzResearch.WordTrace]
  refine ⟨267455716500876930951793991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178303811000584620634529327 267455716500876930951793991)
  ·
    refine ⟨401183574751315396427690987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267455716500876930951793991 401183574751315396427690987)
    ·
      refine ⟨601775362126973094641536481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401183574751315396427690987 601775362126973094641536481)
      ·
        refine ⟨451331521595229820981152361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601775362126973094641536481 451331521595229820981152361)
        ·
          refine ⟨338498641196422365735864271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451331521595229820981152361 338498641196422365735864271)
          ·
            refine ⟨507747961794633548603796407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338498641196422365735864271 507747961794633548603796407)
            ·
              refine ⟨761621942691950322905694611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507747961794633548603796407 761621942691950322905694611)
              ·
                refine ⟨1142432914037925484358541917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 761621942691950322905694611 1142432914037925484358541917)
                ·
                  refine ⟨428412342764222056634453219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142432914037925484358541917 428412342764222056634453219)
                  ·
                    refine ⟨642618514146333084951679829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 428412342764222056634453219 642618514146333084951679829)
                    ·
                      refine ⟨3765342856326170419638749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 642618514146333084951679829 3765342856326170419638749)
                      ·
                        rfl

theorem cell23_7332979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_7332979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7332979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7332979 prefixEnd_7332979 := by exact prefixLift 7332979
  have htrace : WordTrace (prefixWord ++ tailWord_7332979) baseStart_7332979 baseEnd_7332979 := by
    simpa [prefixWord, tailWord_7332979, baseEnd_7332979] using wordTrace_append hprefix tailTrace_7332979
  have hstable : (prefixWord ++ tailWord_7332979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7332979).length < 2 ^ (prefixWord ++ tailWord_7332979).sum := by decide
  have hdescent : baseEnd_7332979 < baseStart_7332979 := by decide
  rcases family_descends (prefixWord ++ tailWord_7332979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333031 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 2, 2, 2]
def baseStart_7333031 : Nat := 118140960795 + 7333031 * 2 ^ 59
def prefixEnd_7333031 : Nat := 4983230072969 + 3 ^ 40 * 7333031 * 2
def baseEnd_7333031 : Nat := 3765369557320204216188511

theorem tailTrace_7333031 : CollatzResearch.WordTrace tailWord_7333031 prefixEnd_7333031 3765369557320204216188511 := by
  unfold tailWord_7333031
  simp only [CollatzResearch.WordTrace]
  refine ⟨267457613096688543832686947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178305075397792362555124631 267457613096688543832686947)
  ·
    refine ⟨401186419645032815749030421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267457613096688543832686947 401186419645032815749030421)
    ·
      refine ⟨18805613420860913238235801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 401186419645032815749030421 18805613420860913238235801)
      ·
        refine ⟨14104210065645684928676851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18805613420860913238235801 14104210065645684928676851)
        ·
          refine ⟨21156315098468527393015277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14104210065645684928676851 21156315098468527393015277)
          ·
            refine ⟨7933618161925697772380729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21156315098468527393015277 7933618161925697772380729)
            ·
              refine ⟨5950213621444273329285547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7933618161925697772380729 5950213621444273329285547)
              ·
                refine ⟨8925320432166409993928321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5950213621444273329285547 8925320432166409993928321)
                ·
                  refine ⟨6693990324124807495446241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8925320432166409993928321 6693990324124807495446241)
                  ·
                    refine ⟨5020492743093605621584681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6693990324124807495446241 5020492743093605621584681)
                    ·
                      refine ⟨3765369557320204216188511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020492743093605621584681 3765369557320204216188511)
                      ·
                        rfl

theorem cell23_7333031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_7333031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333031 prefixEnd_7333031 := by exact prefixLift 7333031
  have htrace : WordTrace (prefixWord ++ tailWord_7333031) baseStart_7333031 baseEnd_7333031 := by
    simpa [prefixWord, tailWord_7333031, baseEnd_7333031] using wordTrace_append hprefix tailTrace_7333031
  have hstable : (prefixWord ++ tailWord_7333031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333031).length < 2 ^ (prefixWord ++ tailWord_7333031).sum := by decide
  have hdescent : baseEnd_7333031 < baseStart_7333031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333036 : List Nat := [2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 4]
def baseStart_7333036 : Nat := 118140960795 + 7333036 * 2 ^ 59
def prefixEnd_7333036 : Nat := 4983230072969 + 3 ^ 40 * 7333036 * 2
def baseEnd_7333036 : Nat := 3765372124723476696625987

theorem tailTrace_7333036 : CollatzResearch.WordTrace tailWord_7333036 prefixEnd_7333036 3765372124723476696625987 := by
  unfold tailWord_7333036
  simp only [CollatzResearch.WordTrace]
  refine ⟨133728897730835214843309481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178305196974446953124412641 133728897730835214843309481)
  ·
    refine ⟨100296673298126411132482111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133728897730835214843309481 100296673298126411132482111)
    ·
      refine ⟨150445009947189616698723167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100296673298126411132482111 150445009947189616698723167)
      ·
        refine ⟨225667514920784425048084751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150445009947189616698723167 225667514920784425048084751)
        ·
          refine ⟨338501272381176637572127127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225667514920784425048084751 338501272381176637572127127)
          ·
            refine ⟨507751908571764956358190691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338501272381176637572127127 507751908571764956358190691)
            ·
              refine ⟨761627862857647434537286037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 507751908571764956358190691 761627862857647434537286037)
              ·
                refine ⟨35701306071452223493935283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 761627862857647434537286037 35701306071452223493935283)
                ·
                  refine ⟨53551959107178335240902925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35701306071452223493935283 53551959107178335240902925)
                  ·
                    refine ⟨20081984665191875715338597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 53551959107178335240902925 20081984665191875715338597)
                    ·
                      refine ⟨3765372124723476696625987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20081984665191875715338597 3765372124723476696625987)
                      ·
                        rfl

theorem cell23_7333036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 4].length) (baseStart_7333036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333036 prefixEnd_7333036 := by exact prefixLift 7333036
  have htrace : WordTrace (prefixWord ++ tailWord_7333036) baseStart_7333036 baseEnd_7333036 := by
    simpa [prefixWord, tailWord_7333036, baseEnd_7333036] using wordTrace_append hprefix tailTrace_7333036
  have hstable : (prefixWord ++ tailWord_7333036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333036).length < 2 ^ (prefixWord ++ tailWord_7333036).sum := by decide
  have hdescent : baseEnd_7333036 < baseStart_7333036 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333053 : List Nat := [1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 4]
def baseStart_7333053 : Nat := 118140960795 + 7333053 * 2 ^ 59
def prefixEnd_7333053 : Nat := 4983230072969 + 3 ^ 40 * 7333053 * 2
def baseEnd_7333053 : Nat := 3765380853894603130113409

theorem tailTrace_7333053 : CollatzResearch.WordTrace tailWord_7333053 prefixEnd_7333053 3765380853894603130113409 := by
  unfold tailWord_7333053
  simp only [CollatzResearch.WordTrace]
  refine ⟨267458415502608841589987813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178305610335072561059991875 267458415502608841589987813)
  ·
    refine ⟨50148452906739157798122715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267458415502608841589987813 50148452906739157798122715)
    ·
      refine ⟨75222679360108736697184073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50148452906739157798122715 75222679360108736697184073)
      ·
        refine ⟨56417009520081552522888055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75222679360108736697184073 56417009520081552522888055)
        ·
          refine ⟨84625514280122328784332083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56417009520081552522888055 84625514280122328784332083)
          ·
            refine ⟨126938271420183493176498125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84625514280122328784332083 126938271420183493176498125)
            ·
              refine ⟨47601851782568809941186797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126938271420183493176498125 47601851782568809941186797)
              ·
                refine ⟨17850694418463303727945049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47601851782568809941186797 17850694418463303727945049)
                ·
                  refine ⟨13388020813847477795958787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17850694418463303727945049 13388020813847477795958787)
                  ·
                    refine ⟨20082031220771216693938181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13388020813847477795958787 20082031220771216693938181)
                    ·
                      refine ⟨3765380853894603130113409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20082031220771216693938181 3765380853894603130113409)
                      ·
                        rfl

theorem cell23_7333053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_7333053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333053 prefixEnd_7333053 := by exact prefixLift 7333053
  have htrace : WordTrace (prefixWord ++ tailWord_7333053) baseStart_7333053 baseEnd_7333053 := by
    simpa [prefixWord, tailWord_7333053, baseEnd_7333053] using wordTrace_append hprefix tailTrace_7333053
  have hstable : (prefixWord ++ tailWord_7333053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333053).length < 2 ^ (prefixWord ++ tailWord_7333053).sum := by decide
  have hdescent : baseEnd_7333053 < baseStart_7333053 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333130 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2]
def baseStart_7333130 : Nat := 118140960795 + 7333130 * 2 ^ 59
def prefixEnd_7333130 : Nat := 4983230072969 + 3 ^ 40 * 7333130 * 2
def baseEnd_7333130 : Nat := 3765420391904999328850555

theorem tailTrace_7333130 : CollatzResearch.WordTrace tailWord_7333130 prefixEnd_7333130 3765420391904999328850555 := by
  unfold tailWord_7333130
  simp only [CollatzResearch.WordTrace]
  refine ⟨66865305980832470935135211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178307482615553255827027229 66865305980832470935135211)
  ·
    refine ⟨100297958971248706402702817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66865305980832470935135211 100297958971248706402702817)
    ·
      refine ⟨75223469228436529802027113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100297958971248706402702817 75223469228436529802027113)
      ·
        refine ⟨56417601921327397351520335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75223469228436529802027113 56417601921327397351520335)
        ·
          refine ⟨84626402881991096027280503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56417601921327397351520335 84626402881991096027280503)
          ·
            refine ⟨126939604322986644040920755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84626402881991096027280503 126939604322986644040920755)
            ·
              refine ⟨190409406484479966061381133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126939604322986644040920755 190409406484479966061381133)
              ·
                refine ⟨71403527431679987273017925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190409406484479966061381133 71403527431679987273017925)
                ·
                  refine ⟨13388161393439997613690861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71403527431679987273017925 13388161393439997613690861)
                  ·
                    refine ⟨5020560522539999105134073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13388161393439997613690861 5020560522539999105134073)
                    ·
                      refine ⟨3765420391904999328850555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020560522539999105134073 3765420391904999328850555)
                      ·
                        rfl

theorem cell23_7333130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_7333130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333130 prefixEnd_7333130 := by exact prefixLift 7333130
  have htrace : WordTrace (prefixWord ++ tailWord_7333130) baseStart_7333130 baseEnd_7333130 := by
    simpa [prefixWord, tailWord_7333130, baseEnd_7333130] using wordTrace_append hprefix tailTrace_7333130
  have hstable : (prefixWord ++ tailWord_7333130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333130).length < 2 ^ (prefixWord ++ tailWord_7333130).sum := by decide
  have hdescent : baseEnd_7333130 < baseStart_7333130 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333137 : List Nat := [1, 2, 2, 1, 1, 4, 1, 6, 1, 1, 3]
def baseStart_7333137 : Nat := 118140960795 + 7333137 * 2 ^ 59
def prefixEnd_7333137 : Nat := 4983230072969 + 3 ^ 40 * 7333137 * 2
def baseEnd_7333137 : Nat := 3765423986269580801463023

theorem tailTrace_7333137 : CollatzResearch.WordTrace tailWord_7333137 prefixEnd_7333137 3765423986269580801463023 := by
  unfold tailWord_7333137
  simp only [CollatzResearch.WordTrace]
  refine ⟨267461479234304523936045665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178307652822869682624030443 267461479234304523936045665)
  ·
    refine ⟨200596109425728392952034249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267461479234304523936045665 200596109425728392952034249)
    ·
      refine ⟨150447082069296294714025687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200596109425728392952034249 150447082069296294714025687)
      ·
        refine ⟨225670623103944442071038531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150447082069296294714025687 225670623103944442071038531)
        ·
          refine ⟨338505934655916663106557797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225670623103944442071038531 338505934655916663106557797)
          ·
            refine ⟨63469862747984374332479587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338505934655916663106557797 63469862747984374332479587)
            ·
              refine ⟨95204794121976561498719381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63469862747984374332479587 95204794121976561498719381)
              ·
                refine ⟨4462724724467651320252471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 95204794121976561498719381 4462724724467651320252471)
                ·
                  refine ⟨6694087086701476980378707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462724724467651320252471 6694087086701476980378707)
                  ·
                    refine ⟨10041130630052215470568061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6694087086701476980378707 10041130630052215470568061)
                    ·
                      refine ⟨3765423986269580801463023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10041130630052215470568061 3765423986269580801463023)
                      ·
                        rfl

theorem cell23_7333137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 6, 1, 1, 3].length) (baseStart_7333137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333137 prefixEnd_7333137 := by exact prefixLift 7333137
  have htrace : WordTrace (prefixWord ++ tailWord_7333137) baseStart_7333137 baseEnd_7333137 := by
    simpa [prefixWord, tailWord_7333137, baseEnd_7333137] using wordTrace_append hprefix tailTrace_7333137
  have hstable : (prefixWord ++ tailWord_7333137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333137).length < 2 ^ (prefixWord ++ tailWord_7333137).sum := by decide
  have hdescent : baseEnd_7333137 < baseStart_7333137 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333170 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 4, 4]
def baseStart_7333170 : Nat := 118140960795 + 7333170 * 2 ^ 59
def prefixEnd_7333170 : Nat := 4983230072969 + 3 ^ 40 * 7333170 * 2
def baseEnd_7333170 : Nat := 1255146977043726390783457

theorem tailTrace_7333170 : CollatzResearch.WordTrace tailWord_7333170 prefixEnd_7333170 1255146977043726390783457 := by
  unfold tailWord_7333170
  simp only [CollatzResearch.WordTrace]
  refine ⟨66865670710796242642999241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178308455228789980381331309 66865670710796242642999241)
  ·
    refine ⟨50149253033097181982249431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66865670710796242642999241 50149253033097181982249431)
    ·
      refine ⟨75223879549645772973374147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50149253033097181982249431 75223879549645772973374147)
      ·
        refine ⟨112835819324468659460061221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75223879549645772973374147 112835819324468659460061221)
        ·
          refine ⟨21156716123337873648761479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112835819324468659460061221 21156716123337873648761479)
          ·
            refine ⟨31735074185006810473142219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21156716123337873648761479 31735074185006810473142219)
            ·
              refine ⟨47602611277510215709713329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31735074185006810473142219 47602611277510215709713329)
              ·
                refine ⟨35701958458132661782284997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47602611277510215709713329 35701958458132661782284997)
                ·
                  refine ⟨6694117210899874084178437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35701958458132661782284997 6694117210899874084178437)
                  ·
                    refine ⟨1255146977043726390783457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6694117210899874084178437 1255146977043726390783457)
                    ·
                      rfl

theorem cell23_7333170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_7333170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333170 prefixEnd_7333170 := by exact prefixLift 7333170
  have htrace : WordTrace (prefixWord ++ tailWord_7333170) baseStart_7333170 baseEnd_7333170 := by
    simpa [prefixWord, tailWord_7333170, baseEnd_7333170] using wordTrace_append hprefix tailTrace_7333170
  have hstable : (prefixWord ++ tailWord_7333170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333170).length < 2 ^ (prefixWord ++ tailWord_7333170).sum := by decide
  have hdescent : baseEnd_7333170 < baseStart_7333170 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333180 : List Nat := [2, 2, 2, 2, 1, 4, 2, 1, 1, 1, 5]
def baseStart_7333180 : Nat := 118140960795 + 7333180 * 2 ^ 59
def prefixEnd_7333180 : Nat := 4983230072969 + 3 ^ 40 * 7333180 * 2
def baseEnd_7333180 : Nat := 3765446065937724133225325

theorem tailTrace_7333180 : CollatzResearch.WordTrace tailWord_7333180 prefixEnd_7333180 3765446065937724133225325 := by
  unfold tailWord_7333180
  simp only [CollatzResearch.WordTrace]
  refine ⟨133731523786574371139930497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178308698382099161519907329 133731523786574371139930497)
  ·
    refine ⟨100298642839930778354947873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133731523786574371139930497 100298642839930778354947873)
    ·
      refine ⟨75223982129948083766210905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100298642839930778354947873 75223982129948083766210905)
      ·
        refine ⟨56417986597461062824658179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75223982129948083766210905 56417986597461062824658179)
        ·
          refine ⟨84626979896191594236987269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56417986597461062824658179 84626979896191594236987269)
          ·
            refine ⟨15867558730535923919435113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 84626979896191594236987269 15867558730535923919435113)
            ·
              refine ⟨11900669047901942939576335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15867558730535923919435113 11900669047901942939576335)
              ·
                refine ⟨17851003571852914409364503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11900669047901942939576335 17851003571852914409364503)
                ·
                  refine ⟨26776505357779371614046755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17851003571852914409364503 26776505357779371614046755)
                  ·
                    refine ⟨40164758036669057421070133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26776505357779371614046755 40164758036669057421070133)
                    ·
                      refine ⟨3765446065937724133225325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40164758036669057421070133 3765446065937724133225325)
                      ·
                        rfl

theorem cell23_7333180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_7333180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333180 prefixEnd_7333180 := by exact prefixLift 7333180
  have htrace : WordTrace (prefixWord ++ tailWord_7333180) baseStart_7333180 baseEnd_7333180 := by
    simpa [prefixWord, tailWord_7333180, baseEnd_7333180] using wordTrace_append hprefix tailTrace_7333180
  have hstable : (prefixWord ++ tailWord_7333180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333180).length < 2 ^ (prefixWord ++ tailWord_7333180).sum := by decide
  have hdescent : baseEnd_7333180 < baseStart_7333180 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333183 : List Nat := [1, 1, 2, 2, 4, 4, 9]
def baseStart_7333183 : Nat := 118140960795 + 7333183 * 2 ^ 59
def prefixEnd_7333183 : Nat := 4983230072969 + 3 ^ 40 * 7333183 * 2
def baseEnd_7333183 : Nat := 46487007486168982981331

theorem tailTrace_7333183 : CollatzResearch.WordTrace tailWord_7333183 prefixEnd_7333183 46487007486168982981331 := by
  unfold tailWord_7333183
  simp only [CollatzResearch.WordTrace]
  refine ⟨267463156992137873792220203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178308771328091915861480135 267463156992137873792220203)
  ·
    refine ⟨401194735488206810688330305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267463156992137873792220203 401194735488206810688330305)
    ·
      refine ⟨300896051616155108016247729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401194735488206810688330305 300896051616155108016247729)
      ·
        refine ⟨225672038712116331012185797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300896051616155108016247729 225672038712116331012185797)
        ·
          refine ⟨42313507258521812064784837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225672038712116331012185797 42313507258521812064784837)
          ·
            refine ⟨7933782610972839762147157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42313507258521812064784837 7933782610972839762147157)
            ·
              refine ⟨46487007486168982981331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7933782610972839762147157 46487007486168982981331)
              ·
                rfl

theorem cell23_7333183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 9].length) (baseStart_7333183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333183 prefixEnd_7333183 := by exact prefixLift 7333183
  have htrace : WordTrace (prefixWord ++ tailWord_7333183) baseStart_7333183 baseEnd_7333183 := by
    simpa [prefixWord, tailWord_7333183, baseEnd_7333183] using wordTrace_append hprefix tailTrace_7333183
  have hstable : (prefixWord ++ tailWord_7333183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333183).length < 2 ^ (prefixWord ++ tailWord_7333183).sum := by decide
  have hdescent : baseEnd_7333183 < baseStart_7333183 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333188 : List Nat := [2, 3, 4, 1, 1, 2, 3, 2, 1, 1, 3]
def baseStart_7333188 : Nat := 118140960795 + 7333188 * 2 ^ 59
def prefixEnd_7333188 : Nat := 4983230072969 + 3 ^ 40 * 7333188 * 2
def baseEnd_7333188 : Nat := 3765450173782960101925289

theorem tailTrace_7333188 : CollatzResearch.WordTrace tailWord_7333188 prefixEnd_7333188 3765450173782960101925289 := by
  unfold tailWord_7333188
  simp only [CollatzResearch.WordTrace]
  refine ⟨133731669678559879823076109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178308892904746506430768145 133731669678559879823076109)
  ·
    refine ⟨50149376129459954933653541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133731669678559879823076109 50149376129459954933653541)
    ·
      refine ⟨9403008024273741550060039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 50149376129459954933653541 9403008024273741550060039)
      ·
        refine ⟨14104512036410612325090059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9403008024273741550060039 14104512036410612325090059)
        ·
          refine ⟨21156768054615918487635089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14104512036410612325090059 21156768054615918487635089)
          ·
            refine ⟨15867576040961938865726317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21156768054615918487635089 15867576040961938865726317)
            ·
              refine ⟨5950341015360727074647369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15867576040961938865726317 5950341015360727074647369)
              ·
                refine ⟨4462755761520545305985527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5950341015360727074647369 4462755761520545305985527)
                ·
                  refine ⟨6694133642280817958978291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462755761520545305985527 6694133642280817958978291)
                  ·
                    refine ⟨10041200463421226938467437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6694133642280817958978291 10041200463421226938467437)
                    ·
                      refine ⟨3765450173782960101925289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10041200463421226938467437 3765450173782960101925289)
                      ·
                        rfl

theorem cell23_7333188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 2, 1, 1, 3].length) (baseStart_7333188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333188 prefixEnd_7333188 := by exact prefixLift 7333188
  have htrace : WordTrace (prefixWord ++ tailWord_7333188) baseStart_7333188 baseEnd_7333188 := by
    simpa [prefixWord, tailWord_7333188, baseEnd_7333188] using wordTrace_append hprefix tailTrace_7333188
  have hstable : (prefixWord ++ tailWord_7333188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333188).length < 2 ^ (prefixWord ++ tailWord_7333188).sum := by decide
  have hdescent : baseEnd_7333188 < baseStart_7333188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333194 : List Nat := [3, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2]
def baseStart_7333194 : Nat := 118140960795 + 7333194 * 2 ^ 59
def prefixEnd_7333194 : Nat := 4983230072969 + 3 ^ 40 * 7333194 * 2
def baseEnd_7333194 : Nat := 3765453254666887078450261

theorem tailTrace_7333194 : CollatzResearch.WordTrace tailWord_7333194 prefixEnd_7333194 3765453254666887078450261 := by
  unfold tailWord_7333194
  simp only [CollatzResearch.WordTrace]
  refine ⟨66865889548774505667717659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178309038796732015113913757 66865889548774505667717659)
  ·
    refine ⟨100298834323161758501576489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66865889548774505667717659 100298834323161758501576489)
    ·
      refine ⟨75224125742371318876182367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100298834323161758501576489 75224125742371318876182367)
      ·
        refine ⟨112836188613556978314273551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75224125742371318876182367 112836188613556978314273551)
        ·
          refine ⟨169254282920335467471410327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112836188613556978314273551 169254282920335467471410327)
          ·
            refine ⟨253881424380503201207115491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169254282920335467471410327 253881424380503201207115491)
            ·
              refine ⟨380822136570754801810673237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253881424380503201207115491 380822136570754801810673237)
              ·
                refine ⟨4462759412938532833718827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 380822136570754801810673237 4462759412938532833718827)
                ·
                  refine ⟨6694139119407799250578241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462759412938532833718827 6694139119407799250578241)
                  ·
                    refine ⟨5020604339555849437933681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6694139119407799250578241 5020604339555849437933681)
                    ·
                      refine ⟨3765453254666887078450261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020604339555849437933681 3765453254666887078450261)
                      ·
                        rfl

theorem cell23_7333194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_7333194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333194 prefixEnd_7333194 := by exact prefixLift 7333194
  have htrace : WordTrace (prefixWord ++ tailWord_7333194) baseStart_7333194 baseEnd_7333194 := by
    simpa [prefixWord, tailWord_7333194, baseEnd_7333194] using wordTrace_append hprefix tailTrace_7333194
  have hstable : (prefixWord ++ tailWord_7333194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333194).length < 2 ^ (prefixWord ++ tailWord_7333194).sum := by decide
  have hdescent : baseEnd_7333194 < baseStart_7333194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333243 : List Nat := [1, 1, 1, 1, 1, 6, 2, 2, 2, 6]
def baseStart_7333243 : Nat := 118140960795 + 7333243 * 2 ^ 59
def prefixEnd_7333243 : Nat := 4983230072969 + 3 ^ 40 * 7333243 * 2
def baseEnd_7333243 : Nat := 1255159471739652462245845

theorem tailTrace_7333243 : CollatzResearch.WordTrace tailWord_7333243 prefixEnd_7333243 1255159471739652462245845 := by
  unfold tailWord_7333243
  simp only [CollatzResearch.WordTrace]
  refine ⟨267465345371920504039404383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178310230247947002692936255 267465345371920504039404383)
  ·
    refine ⟨401198018057880756059106575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267465345371920504039404383 401198018057880756059106575)
    ·
      refine ⟨601797027086821134088659863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401198018057880756059106575 601797027086821134088659863)
      ·
        refine ⟨902695540630231701132989795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601797027086821134088659863 902695540630231701132989795)
        ·
          refine ⟨1354043310945347551699484693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 902695540630231701132989795 1354043310945347551699484693)
          ·
            refine ⟨63470780200563166485913345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1354043310945347551699484693 63470780200563166485913345)
            ·
              refine ⟨47603085150422374864435009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63470780200563166485913345 47603085150422374864435009)
              ·
                refine ⟨35702313862816781148326257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47603085150422374864435009 35702313862816781148326257)
                ·
                  refine ⟨26776735397112585861244693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35702313862816781148326257 26776735397112585861244693)
                  ·
                    refine ⟨1255159471739652462245845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26776735397112585861244693 1255159471739652462245845)
                    ·
                      rfl

theorem cell23_7333243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 6].length) (baseStart_7333243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333243 prefixEnd_7333243 := by exact prefixLift 7333243
  have htrace : WordTrace (prefixWord ++ tailWord_7333243) baseStart_7333243 baseEnd_7333243 := by
    simpa [prefixWord, tailWord_7333243, baseEnd_7333243] using wordTrace_append hprefix tailTrace_7333243
  have hstable : (prefixWord ++ tailWord_7333243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333243).length < 2 ^ (prefixWord ++ tailWord_7333243).sum := by decide
  have hdescent : baseEnd_7333243 < baseStart_7333243 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333253 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 5]
def baseStart_7333253 : Nat := 118140960795 + 7333253 * 2 ^ 59
def prefixEnd_7333253 : Nat := 4983230072969 + 3 ^ 40 * 7333253 * 2
def baseEnd_7333253 : Nat := 3765483550025502347612489

theorem tailTrace_7333253 : CollatzResearch.WordTrace tailWord_7333253 prefixEnd_7333253 3765483550025502347612489 := by
  unfold tailWord_7333253
  simp only [CollatzResearch.WordTrace]
  refine ⟨267465710101884275747268413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178310473401256183831512275 267465710101884275747268413)
  ·
    refine ⟨100299641288206603405225655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267465710101884275747268413 100299641288206603405225655)
    ·
      refine ⟨150449461932309905107838483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100299641288206603405225655 150449461932309905107838483)
      ·
        refine ⟨225674192898464857661757725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150449461932309905107838483 225674192898464857661757725)
        ·
          refine ⟨84627822336924321623159147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225674192898464857661757725 84627822336924321623159147)
          ·
            refine ⟨126941733505386482434738721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84627822336924321623159147 126941733505386482434738721)
            ·
              refine ⟨95206300129039861826054041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126941733505386482434738721 95206300129039861826054041)
              ·
                refine ⟨71404725096779896369540531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95206300129039861826054041 71404725096779896369540531)
                ·
                  refine ⟨107107087645169844554310797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71404725096779896369540531 107107087645169844554310797)
                  ·
                    refine ⟨40165157866938691707866549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 107107087645169844554310797 40165157866938691707866549)
                    ·
                      refine ⟨3765483550025502347612489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40165157866938691707866549 3765483550025502347612489)
                      ·
                        rfl

theorem cell23_7333253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 3, 5].length) (baseStart_7333253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333253 prefixEnd_7333253 := by exact prefixLift 7333253
  have htrace : WordTrace (prefixWord ++ tailWord_7333253) baseStart_7333253 baseEnd_7333253 := by
    simpa [prefixWord, tailWord_7333253, baseEnd_7333253] using wordTrace_append hprefix tailTrace_7333253
  have hstable : (prefixWord ++ tailWord_7333253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333253).length < 2 ^ (prefixWord ++ tailWord_7333253).sum := by decide
  have hdescent : baseEnd_7333253 < baseStart_7333253 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333273 : List Nat := [1, 2, 1, 2, 1, 5, 1, 1, 9]
def baseStart_7333273 : Nat := 118140960795 + 7333273 * 2 ^ 59
def prefixEnd_7333273 : Nat := 4983230072969 + 3 ^ 40 * 7333273 * 2
def baseEnd_7333273 : Nat := 418388202182065807706933

theorem tailTrace_7333273 : CollatzResearch.WordTrace tailWord_7333273 prefixEnd_7333273 418388202182065807706933 := by
  unfold tailWord_7333273
  simp only [CollatzResearch.WordTrace]
  refine ⟨267466439561811819162996473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178310959707874546108664315 267466439561811819162996473)
  ·
    refine ⟨200599829671358864372247355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267466439561811819162996473 200599829671358864372247355)
    ·
      refine ⟨300899744507038296558371033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200599829671358864372247355 300899744507038296558371033)
      ·
        refine ⟨225674808380278722418778275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300899744507038296558371033 225674808380278722418778275)
        ·
          refine ⟨338512212570418083628167413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225674808380278722418778275 338512212570418083628167413)
          ·
            refine ⟨31735519928476695340140695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 338512212570418083628167413 31735519928476695340140695)
            ·
              refine ⟨47603279892715043010211043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31735519928476695340140695 47603279892715043010211043)
              ·
                refine ⟨71404919839072564515316565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47603279892715043010211043 71404919839072564515316565)
                ·
                  refine ⟨418388202182065807706933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 71404919839072564515316565 418388202182065807706933)
                  ·
                    rfl

theorem cell23_7333273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 1, 9].length) (baseStart_7333273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333273 prefixEnd_7333273 := by exact prefixLift 7333273
  have htrace : WordTrace (prefixWord ++ tailWord_7333273) baseStart_7333273 baseEnd_7333273 := by
    simpa [prefixWord, tailWord_7333273, baseEnd_7333273] using wordTrace_append hprefix tailTrace_7333273
  have hstable : (prefixWord ++ tailWord_7333273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333273).length < 2 ^ (prefixWord ++ tailWord_7333273).sum := by decide
  have hdescent : baseEnd_7333273 < baseStart_7333273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333301 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 2, 2, 2]
def baseStart_7333301 : Nat := 118140960795 + 7333301 * 2 ^ 59
def prefixEnd_7333301 : Nat := 4983230072969 + 3 ^ 40 * 7333301 * 2
def baseEnd_7333301 : Nat := 3765508197096918159812269

theorem tailTrace_7333301 : CollatzResearch.WordTrace tailWord_7333301 prefixEnd_7333301 3765508197096918159812269 := by
  unfold tailWord_7333301
  simp only [CollatzResearch.WordTrace]
  refine ⟨267467460805710379945015757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178311640537140253296677171 267467460805710379945015757)
  ·
    refine ⟨100300297802141392479380909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267467460805710379945015757 100300297802141392479380909)
    ·
      refine ⟨37612611675803022179767841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100300297802141392479380909 37612611675803022179767841)
      ·
        refine ⟨28209458756852266634825881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37612611675803022179767841 28209458756852266634825881)
        ·
          refine ⟨21157094067639199976119411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28209458756852266634825881 21157094067639199976119411)
          ·
            refine ⟨31735641101458799964179117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21157094067639199976119411 31735641101458799964179117)
            ·
              refine ⟨11900865413047049986567169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31735641101458799964179117 11900865413047049986567169)
              ·
                refine ⟨8925649059785287489925377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11900865413047049986567169 8925649059785287489925377)
                ·
                  refine ⟨6694236794838965617444033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8925649059785287489925377 6694236794838965617444033)
                  ·
                    refine ⟨5020677596129224213083025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6694236794838965617444033 5020677596129224213083025)
                    ·
                      refine ⟨3765508197096918159812269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020677596129224213083025 3765508197096918159812269)
                      ·
                        rfl

theorem cell23_7333301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 2, 2].length) (baseStart_7333301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333301 prefixEnd_7333301 := by exact prefixLift 7333301
  have htrace : WordTrace (prefixWord ++ tailWord_7333301) baseStart_7333301 baseEnd_7333301 := by
    simpa [prefixWord, tailWord_7333301, baseEnd_7333301] using wordTrace_append hprefix tailTrace_7333301
  have hstable : (prefixWord ++ tailWord_7333301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333301).length < 2 ^ (prefixWord ++ tailWord_7333301).sum := by decide
  have hdescent : baseEnd_7333301 < baseStart_7333301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333457 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 4, 4]
def baseStart_7333457 : Nat := 118140960795 + 7333457 * 2 ^ 59
def prefixEnd_7333457 : Nat := 4983230072969 + 3 ^ 40 * 7333457 * 2
def baseEnd_7333457 : Nat := 1255196100026339849820517

theorem tailTrace_7333457 : CollatzResearch.WordTrace tailWord_7333457 prefixEnd_7333457 1255196100026339849820517 := by
  unfold tailWord_7333457
  simp only [CollatzResearch.WordTrace]
  refine ⟨267473150593145218587694625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178315433728763479058463083 267473150593145218587694625)
  ·
    refine ⟨200604862944858913940770969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267473150593145218587694625 200604862944858913940770969)
    ·
      refine ⟨150453647208644185455578227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200604862944858913940770969 150453647208644185455578227)
      ·
        refine ⟨225680470812966278183367341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150453647208644185455578227 225680470812966278183367341)
        ·
          refine ⟨84630176554862354318762753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225680470812966278183367341 84630176554862354318762753)
          ·
            refine ⟨63472632416146765739072065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84630176554862354318762753 63472632416146765739072065)
            ·
              refine ⟨47604474312110074304304049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63472632416146765739072065 47604474312110074304304049)
              ·
                refine ⟨35703355734082555728228037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 47604474312110074304304049 35703355734082555728228037)
                ·
                  refine ⟨6694379200140479199042757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35703355734082555728228037 6694379200140479199042757)
                  ·
                    refine ⟨1255196100026339849820517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6694379200140479199042757 1255196100026339849820517)
                    ·
                      rfl

theorem cell23_7333457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 4, 4].length) (baseStart_7333457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333457 prefixEnd_7333457 := by exact prefixLift 7333457
  have htrace : WordTrace (prefixWord ++ tailWord_7333457) baseStart_7333457 baseEnd_7333457 := by
    simpa [prefixWord, tailWord_7333457, baseEnd_7333457] using wordTrace_append hprefix tailTrace_7333457
  have hstable : (prefixWord ++ tailWord_7333457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333457).length < 2 ^ (prefixWord ++ tailWord_7333457).sum := by decide
  have hdescent : baseEnd_7333457 < baseStart_7333457 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333458 : List Nat := [3, 2, 2, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_7333458 : Nat := 118140960795 + 7333458 * 2 ^ 59
def prefixEnd_7333458 : Nat := 4983230072969 + 3 ^ 40 * 7333458 * 2
def baseEnd_7333458 : Nat := 3765588813559674045549047

theorem tailTrace_7333458 : CollatzResearch.WordTrace tailWord_7333458 prefixEnd_7333458 3765588813559674045549047 := by
  unfold tailWord_7333458
  simp only [CollatzResearch.WordTrace]
  refine ⟨66868296766535398939620257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178315458044094397172320685 66868296766535398939620257)
  ·
    refine ⟨50151222574901549204715193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66868296766535398939620257 50151222574901549204715193)
    ·
      refine ⟨37613416931176161903536395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50151222574901549204715193 37613416931176161903536395)
      ·
        refine ⟨56420125396764242855304593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37613416931176161903536395 56420125396764242855304593)
        ·
          refine ⟨42315094047573182141478445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56420125396764242855304593 42315094047573182141478445)
          ·
            refine ⟨15868160267839943303054417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42315094047573182141478445 15868160267839943303054417)
            ·
              refine ⟨11901120200879957477290813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15868160267839943303054417 11901120200879957477290813)
              ·
                refine ⟨4462920075329984053984055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11901120200879957477290813 4462920075329984053984055)
                ·
                  refine ⟨6694380112994976080976083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462920075329984053984055 6694380112994976080976083)
                  ·
                    refine ⟨10041570169492464121464125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6694380112994976080976083 10041570169492464121464125)
                    ·
                      refine ⟨3765588813559674045549047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10041570169492464121464125 3765588813559674045549047)
                      ·
                        rfl

theorem cell23_7333458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_7333458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333458 prefixEnd_7333458 := by exact prefixLift 7333458
  have htrace : WordTrace (prefixWord ++ tailWord_7333458) baseStart_7333458 baseEnd_7333458 := by
    simpa [prefixWord, tailWord_7333458, baseEnd_7333458] using wordTrace_append hprefix tailTrace_7333458
  have hstable : (prefixWord ++ tailWord_7333458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333458).length < 2 ^ (prefixWord ++ tailWord_7333458).sum := by decide
  have hdescent : baseEnd_7333458 < baseStart_7333458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333464 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 7, 2, 2]
def baseStart_7333464 : Nat := 118140960795 + 7333464 * 2 ^ 59
def prefixEnd_7333464 : Nat := 4983230072969 + 3 ^ 40 * 7333464 * 2
def baseEnd_7333464 : Nat := 3765591894443601022074019

theorem tailTrace_7333464 : CollatzResearch.WordTrace tailWord_7333464 prefixEnd_7333464 3765591894443601022074019 := by
  unfold tailWord_7333464
  simp only [CollatzResearch.WordTrace]
  refine ⟨133736702952059929391599723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178315603936079905855466297 133736702952059929391599723)
  ·
    refine ⟨200605054428089894087399585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133736702952059929391599723 200605054428089894087399585)
    ·
      refine ⟨150453790821067420565549689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200605054428089894087399585 150453790821067420565549689)
      ·
        refine ⟨112840343115800565424162267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150453790821067420565549689 112840343115800565424162267)
        ·
          refine ⟨169260514673700848136243401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112840343115800565424162267 169260514673700848136243401)
          ·
            refine ⟨126945386005275636102182551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 169260514673700848136243401 126945386005275636102182551)
            ·
              refine ⟨190418079007913454153273827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 126945386005275636102182551 190418079007913454153273827)
              ·
                refine ⟨285627118511870181229910741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 190418079007913454153273827 285627118511870181229910741)
                ·
                  refine ⟨6694385590121957372576033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 285627118511870181229910741 6694385590121957372576033)
                  ·
                    refine ⟨5020789192591468029432025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6694385590121957372576033 5020789192591468029432025)
                    ·
                      refine ⟨3765591894443601022074019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020789192591468029432025 3765591894443601022074019)
                      ·
                        rfl

theorem cell23_7333464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 7, 2, 2].length) (baseStart_7333464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333464 prefixEnd_7333464 := by exact prefixLift 7333464
  have htrace : WordTrace (prefixWord ++ tailWord_7333464) baseStart_7333464 baseEnd_7333464 := by
    simpa [prefixWord, tailWord_7333464, baseEnd_7333464] using wordTrace_append hprefix tailTrace_7333464
  have hstable : (prefixWord ++ tailWord_7333464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333464).length < 2 ^ (prefixWord ++ tailWord_7333464).sum := by decide
  have hdescent : baseEnd_7333464 < baseStart_7333464 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333494 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6]
def baseStart_7333494 : Nat := 118140960795 + 7333494 * 2 ^ 59
def prefixEnd_7333494 : Nat := 4983230072969 + 3 ^ 40 * 7333494 * 2
def baseEnd_7333494 : Nat := 3765607298863235904698881

theorem tailTrace_7333494 : CollatzResearch.WordTrace tailWord_7333494 prefixEnd_7333494 3765607298863235904698881 := by
  unfold tailWord_7333494
  simp only [CollatzResearch.WordTrace]
  refine ⟨16717156255875698369174471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 178316333396007449271194357 16717156255875698369174471)
  ·
    refine ⟨25075734383813547553761707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16717156255875698369174471 25075734383813547553761707)
    ·
      refine ⟨37613601575720321330642561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25075734383813547553761707 37613601575720321330642561)
      ·
        refine ⟨28210201181790240997981921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37613601575720321330642561 28210201181790240997981921)
        ·
          refine ⟨21157650886342680748486441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28210201181790240997981921 21157650886342680748486441)
          ·
            refine ⟨15868238164757010561364831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21157650886342680748486441 15868238164757010561364831)
            ·
              refine ⟨23802357247135515842047247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15868238164757010561364831 23802357247135515842047247)
              ·
                refine ⟨35703535870703273763070871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23802357247135515842047247 35703535870703273763070871)
                ·
                  refine ⟨53555303806054910644606307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35703535870703273763070871 53555303806054910644606307)
                  ·
                    refine ⟨80332955709082365966909461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53555303806054910644606307 80332955709082365966909461)
                    ·
                      refine ⟨3765607298863235904698881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80332955709082365966909461 3765607298863235904698881)
                      ·
                        rfl

theorem cell23_7333494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_7333494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333494 prefixEnd_7333494 := by exact prefixLift 7333494
  have htrace : WordTrace (prefixWord ++ tailWord_7333494) baseStart_7333494 baseEnd_7333494 := by
    simpa [prefixWord, tailWord_7333494, baseEnd_7333494] using wordTrace_append hprefix tailTrace_7333494
  have hstable : (prefixWord ++ tailWord_7333494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333494).length < 2 ^ (prefixWord ++ tailWord_7333494).sum := by decide
  have hdescent : baseEnd_7333494 < baseStart_7333494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333501 : List Nat := [1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 3]
def baseStart_7333501 : Nat := 118140960795 + 7333501 * 2 ^ 59
def prefixEnd_7333501 : Nat := 4983230072969 + 3 ^ 40 * 7333501 * 2
def baseEnd_7333501 : Nat := 3765610893227817377311349

theorem tailTrace_7333501 : CollatzResearch.WordTrace tailWord_7333501 prefixEnd_7333501 3765610893227817377311349 := by
  unfold tailWord_7333501
  simp only [CollatzResearch.WordTrace]
  refine ⟨267474755404985814102296357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178316503603323876068197571 267474755404985814102296357)
  ·
    refine ⟨50151516638434840144180567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 267474755404985814102296357 50151516638434840144180567)
    ·
      refine ⟨75227274957652260216270851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50151516638434840144180567 75227274957652260216270851)
      ·
        refine ⟨112840912436478390324406277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75227274957652260216270851 112840912436478390324406277)
        ·
          refine ⟨21157671081839698185826177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 112840912436478390324406277 21157671081839698185826177)
          ·
            refine ⟨15868253311379773639369633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21157671081839698185826177 15868253311379773639369633)
            ·
              refine ⟨11901189983534830229527225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15868253311379773639369633 11901189983534830229527225)
              ·
                refine ⟨8925892487651122672145419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11901189983534830229527225 8925892487651122672145419)
                ·
                  refine ⟨13388838731476684008218129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8925892487651122672145419 13388838731476684008218129)
                  ·
                    refine ⟨10041629048607513006163597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13388838731476684008218129 10041629048607513006163597)
                    ·
                      refine ⟨3765610893227817377311349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10041629048607513006163597 3765610893227817377311349)
                      ·
                        rfl

theorem cell23_7333501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 2, 3].length) (baseStart_7333501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333501 prefixEnd_7333501 := by exact prefixLift 7333501
  have htrace : WordTrace (prefixWord ++ tailWord_7333501) baseStart_7333501 baseEnd_7333501 := by
    simpa [prefixWord, tailWord_7333501, baseEnd_7333501] using wordTrace_append hprefix tailTrace_7333501
  have hstable : (prefixWord ++ tailWord_7333501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333501).length < 2 ^ (prefixWord ++ tailWord_7333501).sum := by decide
  have hdescent : baseEnd_7333501 < baseStart_7333501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333520 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 8]
def baseStart_7333520 : Nat := 118140960795 + 7333520 * 2 ^ 59
def prefixEnd_7333520 : Nat := 4983230072969 + 3 ^ 40 * 7333520 * 2
def baseEnd_7333520 : Nat := 3765620649360252802973761

theorem tailTrace_7333520 : CollatzResearch.WordTrace tailWord_7333520 prefixEnd_7333520 3765620649360252802973761 := by
  unfold tailWord_7333520
  simp only [CollatzResearch.WordTrace]
  refine ⟨133737724195958490173619007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178316965594611320231492009 133737724195958490173619007)
  ·
    refine ⟨200606586293937735260428511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133737724195958490173619007 200606586293937735260428511)
    ·
      refine ⟨300909879440906602890642767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200606586293937735260428511 300909879440906602890642767)
      ·
        refine ⟨451364819161359904335964151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300909879440906602890642767 451364819161359904335964151)
        ·
          refine ⟨677047228742039856503946227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451364819161359904335964151 677047228742039856503946227)
          ·
            refine ⟨1015570843113059784755919341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677047228742039856503946227 1015570843113059784755919341)
            ·
              refine ⟨380839066167397419283469753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1015570843113059784755919341 380839066167397419283469753)
              ·
                refine ⟨285629299625548064462602315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 380839066167397419283469753 285629299625548064462602315)
                ·
                  refine ⟨428443949438322096693903473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 285629299625548064462602315 428443949438322096693903473)
                  ·
                    refine ⟨321332962078741572520427605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 428443949438322096693903473 321332962078741572520427605)
                    ·
                      refine ⟨3765620649360252802973761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 321332962078741572520427605 3765620649360252802973761)
                      ·
                        rfl

theorem cell23_7333520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_7333520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333520 prefixEnd_7333520 := by exact prefixLift 7333520
  have htrace : WordTrace (prefixWord ++ tailWord_7333520) baseStart_7333520 baseEnd_7333520 := by
    simpa [prefixWord, tailWord_7333520, baseEnd_7333520] using wordTrace_append hprefix tailTrace_7333520
  have hstable : (prefixWord ++ tailWord_7333520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333520).length < 2 ^ (prefixWord ++ tailWord_7333520).sum := by decide
  have hdescent : baseEnd_7333520 < baseStart_7333520 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333532 : List Nat := [2, 2, 3, 2, 3, 1, 3, 2, 1, 2, 2]
def baseStart_7333532 : Nat := 118140960795 + 7333532 * 2 ^ 59
def prefixEnd_7333532 : Nat := 4983230072969 + 3 ^ 40 * 7333532 * 2
def baseEnd_7333532 : Nat := 3765626811128106756023707

theorem tailTrace_7333532 : CollatzResearch.WordTrace tailWord_7333532 prefixEnd_7333532 3765626811128106756023707 := by
  unfold tailWord_7333532
  simp only [CollatzResearch.WordTrace]
  refine ⟨133737943033936753198337425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178317257378582337597783233 133737943033936753198337425)
  ·
    refine ⟨100303457275452564898753069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133737943033936753198337425 100303457275452564898753069)
    ·
      refine ⟨37613796478294711837032401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100303457275452564898753069 37613796478294711837032401)
      ·
        refine ⟨28210347358721033877774301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37613796478294711837032401 28210347358721033877774301)
        ·
          refine ⟨10578880259520387704165363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28210347358721033877774301 10578880259520387704165363)
          ·
            refine ⟨15868320389280581556248045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10578880259520387704165363 15868320389280581556248045)
            ·
              refine ⟨5950620145980218083593017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15868320389280581556248045 5950620145980218083593017)
              ·
                refine ⟨4462965109485163562694763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5950620145980218083593017 4462965109485163562694763)
                ·
                  refine ⟨6694447664227745344042145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4462965109485163562694763 6694447664227745344042145)
                  ·
                    refine ⟨5020835748170809008031609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6694447664227745344042145 5020835748170809008031609)
                    ·
                      refine ⟨3765626811128106756023707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020835748170809008031609 3765626811128106756023707)
                      ·
                        rfl

theorem cell23_7333532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 3, 2, 1, 2, 2].length) (baseStart_7333532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333532 prefixEnd_7333532 := by exact prefixLift 7333532
  have htrace : WordTrace (prefixWord ++ tailWord_7333532) baseStart_7333532 baseEnd_7333532 := by
    simpa [prefixWord, tailWord_7333532, baseEnd_7333532] using wordTrace_append hprefix tailTrace_7333532
  have hstable : (prefixWord ++ tailWord_7333532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333532).length < 2 ^ (prefixWord ++ tailWord_7333532).sum := by decide
  have hdescent : baseEnd_7333532 < baseStart_7333532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333604 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 2, 3, 3]
def baseStart_7333604 : Nat := 118140960795 + 7333604 * 2 ^ 59
def prefixEnd_7333604 : Nat := 4983230072969 + 3 ^ 40 * 7333604 * 2
def baseEnd_7333604 : Nat := 3765663781735230474323375

theorem tailTrace_7333604 : CollatzResearch.WordTrace tailWord_7333604 prefixEnd_7333604 3765663781735230474323375 := by
  unfold tailWord_7333604
  simp only [CollatzResearch.WordTrace]
  refine ⟨133739256061806331346647933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178319008082408441795530577 133739256061806331346647933)
  ·
    refine ⟨50152221023177374254992975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133739256061806331346647933 50152221023177374254992975)
    ·
      refine ⟨75228331534766061382489463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50152221023177374254992975 75228331534766061382489463)
      ·
        refine ⟨112842497302149092073734195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75228331534766061382489463 112842497302149092073734195)
        ·
          refine ⟨169263745953223638110601293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112842497302149092073734195 169263745953223638110601293)
          ·
            refine ⟨63473904732458864291475485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169263745953223638110601293 63473904732458864291475485)
            ·
              refine ⟨23802714274672074109303307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63473904732458864291475485 23802714274672074109303307)
              ·
                refine ⟨35704071412008111163954961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23802714274672074109303307 35704071412008111163954961)
                ·
                  refine ⟨26778053559006083372966221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35704071412008111163954961 26778053559006083372966221)
                  ·
                    refine ⟨10041770084627281264862333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26778053559006083372966221 10041770084627281264862333)
                    ·
                      refine ⟨3765663781735230474323375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10041770084627281264862333 3765663781735230474323375)
                      ·
                        rfl

theorem cell23_7333604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 2, 3, 3].length) (baseStart_7333604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333604 prefixEnd_7333604 := by exact prefixLift 7333604
  have htrace : WordTrace (prefixWord ++ tailWord_7333604) baseStart_7333604 baseEnd_7333604 := by
    simpa [prefixWord, tailWord_7333604, baseEnd_7333604] using wordTrace_append hprefix tailTrace_7333604
  have hstable : (prefixWord ++ tailWord_7333604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333604).length < 2 ^ (prefixWord ++ tailWord_7333604).sum := by decide
  have hdescent : baseEnd_7333604 < baseStart_7333604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333644 : List Nat := [2, 2, 1, 2, 2, 1, 2, 4, 2, 1, 4]
def baseStart_7333644 : Nat := 118140960795 + 7333644 * 2 ^ 59
def prefixEnd_7333644 : Nat := 4983230072969 + 3 ^ 40 * 7333644 * 2
def baseEnd_7333644 : Nat := 3765684320961410317823191

theorem tailTrace_7333644 : CollatzResearch.WordTrace tailWord_7333644 prefixEnd_7333644 3765684320961410317823191 := by
  unfold tailWord_7333644
  simp only [CollatzResearch.WordTrace]
  refine ⟨133739985521733874762375993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178319980695645166349834657 133739985521733874762375993)
  ·
    refine ⟨100304989141300406071781995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133739985521733874762375993 100304989141300406071781995)
    ·
      refine ⟨150457483711950609107672993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100304989141300406071781995 150457483711950609107672993)
      ·
        refine ⟨112843112783962956830754745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150457483711950609107672993 112843112783962956830754745)
        ·
          refine ⟨84632334587972217623066059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112843112783962956830754745 84632334587972217623066059)
          ·
            refine ⟨126948501881958326434599089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84632334587972217623066059 126948501881958326434599089)
            ·
              refine ⟨95211376411468744825949317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126948501881958326434599089 95211376411468744825949317)
              ·
                refine ⟨17852133077150389654865497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 95211376411468744825949317 17852133077150389654865497)
                ·
                  refine ⟨13389099807862792241149123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17852133077150389654865497 13389099807862792241149123)
                  ·
                    refine ⟨20083649711794188361723685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13389099807862792241149123 20083649711794188361723685)
                    ·
                      refine ⟨3765684320961410317823191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20083649711794188361723685 3765684320961410317823191)
                      ·
                        rfl

theorem cell23_7333644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 4, 2, 1, 4].length) (baseStart_7333644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333644 prefixEnd_7333644 := by exact prefixLift 7333644
  have htrace : WordTrace (prefixWord ++ tailWord_7333644) baseStart_7333644 baseEnd_7333644 := by
    simpa [prefixWord, tailWord_7333644, baseEnd_7333644] using wordTrace_append hprefix tailTrace_7333644
  have hstable : (prefixWord ++ tailWord_7333644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333644).length < 2 ^ (prefixWord ++ tailWord_7333644).sum := by decide
  have hdescent : baseEnd_7333644 < baseStart_7333644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333664 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 3]
def baseStart_7333664 : Nat := 118140960795 + 7333664 * 2 ^ 59
def prefixEnd_7333664 : Nat := 4983230072969 + 3 ^ 40 * 7333664 * 2
def baseEnd_7333664 : Nat := 3765694590574500239573099

theorem tailTrace_7333664 : CollatzResearch.WordTrace tailWord_7333664 prefixEnd_7333664 3765694590574500239573099 := by
  unfold tailWord_7333664
  simp only [CollatzResearch.WordTrace]
  refine ⟨133740350251697646470240023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178320467002263528626986697 133740350251697646470240023)
  ·
    refine ⟨200610525377546469705360035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133740350251697646470240023 200610525377546469705360035)
    ·
      refine ⟨300915788066319704558040053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200610525377546469705360035 300915788066319704558040053)
      ·
        refine ⟨28210855131217472302316255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 300915788066319704558040053 28210855131217472302316255)
        ·
          refine ⟨42316282696826208453474383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28210855131217472302316255 42316282696826208453474383)
          ·
            refine ⟨63474424045239312680211575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42316282696826208453474383 63474424045239312680211575)
            ·
              refine ⟨95211636067858969020317363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63474424045239312680211575 95211636067858969020317363)
              ·
                refine ⟨142817454101788453530476045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95211636067858969020317363 142817454101788453530476045)
                ·
                  refine ⟨53556545288170670073928517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142817454101788453530476045 53556545288170670073928517)
                  ·
                    refine ⟨10041852241532000638861597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 53556545288170670073928517 10041852241532000638861597)
                    ·
                      refine ⟨3765694590574500239573099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10041852241532000638861597 3765694590574500239573099)
                      ·
                        rfl

theorem cell23_7333664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_7333664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333664 prefixEnd_7333664 := by exact prefixLift 7333664
  have htrace : WordTrace (prefixWord ++ tailWord_7333664) baseStart_7333664 baseEnd_7333664 := by
    simpa [prefixWord, tailWord_7333664, baseEnd_7333664] using wordTrace_append hprefix tailTrace_7333664
  have hstable : (prefixWord ++ tailWord_7333664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333664).length < 2 ^ (prefixWord ++ tailWord_7333664).sum := by decide
  have hdescent : baseEnd_7333664 < baseStart_7333664 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333687 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 8]
def baseStart_7333687 : Nat := 118140960795 + 7333687 * 2 ^ 59
def prefixEnd_7333687 : Nat := 4983230072969 + 3 ^ 40 * 7333687 * 2
def baseEnd_7333687 : Nat := 3765706400629553649585493

theorem tailTrace_7333687 : CollatzResearch.WordTrace tailWord_7333687 prefixEnd_7333687 3765706400629553649585493 := by
  unfold tailWord_7333687
  simp only [CollatzResearch.WordTrace]
  refine ⟨267481539382311967868567315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178321026254874645245711543 267481539382311967868567315)
  ·
    refine ⟨401222309073467951802850973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267481539382311967868567315 401222309073467951802850973)
    ·
      refine ⟨150458365902550481926069115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401222309073467951802850973 150458365902550481926069115)
      ·
        refine ⟨225687548853825722889103673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150458365902550481926069115 225687548853825722889103673)
        ·
          refine ⟨169265661640369292166827755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225687548853825722889103673 169265661640369292166827755)
          ·
            refine ⟨253898492460553938250241633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169265661640369292166827755 253898492460553938250241633)
            ·
              refine ⟨190423869345415453687681225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253898492460553938250241633 190423869345415453687681225)
              ·
                refine ⟨142817902009061590265760919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190423869345415453687681225 142817902009061590265760919)
                ·
                  refine ⟨214226853013592385398641379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142817902009061590265760919 214226853013592385398641379)
                  ·
                    refine ⟨321340279520388578097962069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 214226853013592385398641379 321340279520388578097962069)
                    ·
                      refine ⟨3765706400629553649585493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 321340279520388578097962069 3765706400629553649585493)
                      ·
                        rfl

theorem cell23_7333687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 8].length) (baseStart_7333687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333687 prefixEnd_7333687 := by exact prefixLift 7333687
  have htrace : WordTrace (prefixWord ++ tailWord_7333687) baseStart_7333687 baseEnd_7333687 := by
    simpa [prefixWord, tailWord_7333687, baseEnd_7333687] using wordTrace_append hprefix tailTrace_7333687
  have hstable : (prefixWord ++ tailWord_7333687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333687).length < 2 ^ (prefixWord ++ tailWord_7333687).sum := by decide
  have hdescent : baseEnd_7333687 < baseStart_7333687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333688 : List Nat := [2, 1, 2, 1, 3, 3, 3, 3, 1, 4]
def baseStart_7333688 : Nat := 118140960795 + 7333688 * 2 ^ 59
def prefixEnd_7333688 : Nat := 4983230072969 + 3 ^ 40 * 7333688 * 2
def baseEnd_7333688 : Nat := 1255235638036736048557663

theorem tailTrace_7333688 : CollatzResearch.WordTrace tailWord_7333688 prefixEnd_7333688 1255235638036736048557663 := by
  unfold tailWord_7333688
  simp only [CollatzResearch.WordTrace]
  refine ⟨133740787927654172519676859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178321050570205563359569145 133740787927654172519676859)
  ·
    refine ⟨200611181891481258779515289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 133740787927654172519676859 200611181891481258779515289)
    ·
      refine ⟨150458386418610944084636467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200611181891481258779515289 150458386418610944084636467)
      ·
        refine ⟨225687579627916416126954701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150458386418610944084636467 225687579627916416126954701)
        ·
          refine ⟨84632842360468656047608013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225687579627916416126954701 84632842360468656047608013)
          ·
            refine ⟨31737315885175746017853005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 84632842360468656047608013 31737315885175746017853005)
            ·
              refine ⟨11901493456940904756694877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31737315885175746017853005 11901493456940904756694877)
              ·
                refine ⟨4463060046352839283760579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11901493456940904756694877 4463060046352839283760579)
                ·
                  refine ⟨6694590069529258925640869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463060046352839283760579 6694590069529258925640869)
                  ·
                    refine ⟨1255235638036736048557663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6694590069529258925640869 1255235638036736048557663)
                    ·
                      rfl

theorem cell23_7333688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 3, 1, 4].length) (baseStart_7333688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333688 prefixEnd_7333688 := by exact prefixLift 7333688
  have htrace : WordTrace (prefixWord ++ tailWord_7333688) baseStart_7333688 baseEnd_7333688 := by
    simpa [prefixWord, tailWord_7333688, baseEnd_7333688] using wordTrace_append hprefix tailTrace_7333688
  have hstable : (prefixWord ++ tailWord_7333688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333688).length < 2 ^ (prefixWord ++ tailWord_7333688).sum := by decide
  have hdescent : baseEnd_7333688 < baseStart_7333688 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333721 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 4, 3, 2]
def baseStart_7333721 : Nat := 118140960795 + 7333721 * 2 ^ 59
def prefixEnd_7333721 : Nat := 4983230072969 + 3 ^ 40 * 7333721 * 2
def baseEnd_7333721 : Nat := 3765723858971806516560337

theorem tailTrace_7333721 : CollatzResearch.WordTrace tailWord_7333721 prefixEnd_7333721 3765723858971806516560337 := by
  unfold tailWord_7333721
  simp only [CollatzResearch.WordTrace]
  refine ⟨267482779464188791675305017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178321852976125861116870011 267482779464188791675305017)
  ·
    refine ⟨200612084598141593756478763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267482779464188791675305017 200612084598141593756478763)
    ·
      refine ⟨300918126897212390634718145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200612084598141593756478763 300918126897212390634718145)
      ·
        refine ⟨225688595172909292976038609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300918126897212390634718145 225688595172909292976038609)
        ·
          refine ⟨169266446379681969732028957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225688595172909292976038609 169266446379681969732028957)
          ·
            refine ⟨63474917392380738649510859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169266446379681969732028957 63474917392380738649510859)
            ·
              refine ⟨95212376088571107974266289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63474917392380738649510859 95212376088571107974266289)
              ·
                refine ⟨71409282066428330980699717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95212376088571107974266289 71409282066428330980699717)
                ·
                  refine ⟨13389240387455312058881197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71409282066428330980699717 13389240387455312058881197)
                  ·
                    refine ⟨5020965145295742022080449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13389240387455312058881197 5020965145295742022080449)
                    ·
                      refine ⟨3765723858971806516560337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5020965145295742022080449 3765723858971806516560337)
                      ·
                        rfl

theorem cell23_7333721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 3, 2].length) (baseStart_7333721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333721 prefixEnd_7333721 := by exact prefixLift 7333721
  have htrace : WordTrace (prefixWord ++ tailWord_7333721) baseStart_7333721 baseEnd_7333721 := by
    simpa [prefixWord, tailWord_7333721, baseEnd_7333721] using wordTrace_append hprefix tailTrace_7333721
  have hstable : (prefixWord ++ tailWord_7333721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333721).length < 2 ^ (prefixWord ++ tailWord_7333721).sum := by decide
  have hdescent : baseEnd_7333721 < baseStart_7333721 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333731 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 3, 5]
def baseStart_7333731 : Nat := 118140960795 + 7333731 * 2 ^ 59
def prefixEnd_7333731 : Nat := 4983230072969 + 3 ^ 40 * 7333731 * 2
def baseEnd_7333731 : Nat := 1255242997926117159145097

theorem tailTrace_7333731 : CollatzResearch.WordTrace tailWord_7333731 prefixEnd_7333731 1255242997926117159145097 := by
  unfold tailWord_7333731
  simp only [CollatzResearch.WordTrace]
  refine ⟨267483144194152563383169047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178322096129435042255446031 267483144194152563383169047)
  ·
    refine ⟨401224716291228845074753571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267483144194152563383169047 401224716291228845074753571)
    ·
      refine ⟨601837074436843267612130357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401224716291228845074753571 601837074436843267612130357)
      ·
        refine ⟨56422225728454056338637221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 601837074436843267612130357 56422225728454056338637221)
        ·
          refine ⟨10579167324085135563494479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 56422225728454056338637221 10579167324085135563494479)
          ·
            refine ⟨15868750986127703345241719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10579167324085135563494479 15868750986127703345241719)
            ·
              refine ⟨23803126479191555017862579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15868750986127703345241719 23803126479191555017862579)
              ·
                refine ⟨35704689718787332526793869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23803126479191555017862579 35704689718787332526793869)
                ·
                  refine ⟨13389258644545249697547701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35704689718787332526793869 13389258644545249697547701)
                  ·
                    refine ⟨1255242997926117159145097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13389258644545249697547701 1255242997926117159145097)
                    ·
                      rfl

theorem cell23_7333731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 3, 5].length) (baseStart_7333731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333731 prefixEnd_7333731 := by exact prefixLift 7333731
  have htrace : WordTrace (prefixWord ++ tailWord_7333731) baseStart_7333731 baseEnd_7333731 := by
    simpa [prefixWord, tailWord_7333731, baseEnd_7333731] using wordTrace_append hprefix tailTrace_7333731
  have hstable : (prefixWord ++ tailWord_7333731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333731).length < 2 ^ (prefixWord ++ tailWord_7333731).sum := by decide
  have hdescent : baseEnd_7333731 < baseStart_7333731 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333764 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 3, 1, 6]
def baseStart_7333764 : Nat := 118140960795 + 7333764 * 2 ^ 59
def prefixEnd_7333764 : Nat := 4983230072969 + 3 ^ 40 * 7333764 * 2
def baseEnd_7333764 : Nat := 3765745938639949848322639

theorem tailTrace_7333764 : CollatzResearch.WordTrace tailWord_7333764 prefixEnd_7333764 3765745938639949848322639 := by
  unfold tailWord_7333764
  simp only [CollatzResearch.WordTrace]
  refine ⟨133742173901516505009560173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178322898535355340012746897 133742173901516505009560173)
  ·
    refine ⟨50153315213068689378585065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133742173901516505009560173 50153315213068689378585065)
    ·
      refine ⟨37614986409801517033938799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50153315213068689378585065 37614986409801517033938799)
      ·
        refine ⟨56422479614702275550908199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37614986409801517033938799 56422479614702275550908199)
        ·
          refine ⟨84633719422053413326362299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56422479614702275550908199 84633719422053413326362299)
          ·
            refine ⟨126950579133080119989543449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84633719422053413326362299 126950579133080119989543449)
            ·
              refine ⟨95212934349810089992157587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126950579133080119989543449 95212934349810089992157587)
              ·
                refine ⟨142819401524715134988236381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95212934349810089992157587 142819401524715134988236381)
                ·
                  refine ⟨53557275571768175620588643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 142819401524715134988236381 53557275571768175620588643)
                  ·
                    refine ⟨80335913357652263430882965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 53557275571768175620588643 80335913357652263430882965)
                    ·
                      refine ⟨3765745938639949848322639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 80335913357652263430882965 3765745938639949848322639)
                      ·
                        rfl

theorem cell23_7333764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_7333764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333764 prefixEnd_7333764 := by exact prefixLift 7333764
  have htrace : WordTrace (prefixWord ++ tailWord_7333764) baseStart_7333764 baseEnd_7333764 := by
    simpa [prefixWord, tailWord_7333764, baseEnd_7333764] using wordTrace_append hprefix tailTrace_7333764
  have hstable : (prefixWord ++ tailWord_7333764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333764).length < 2 ^ (prefixWord ++ tailWord_7333764).sum := by decide
  have hdescent : baseEnd_7333764 < baseStart_7333764 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333778 : List Nat := [3, 2, 3, 2, 1, 2, 2, 1, 1, 6]
def baseStart_7333778 : Nat := 118140960795 + 7333778 * 2 ^ 59
def prefixEnd_7333778 : Nat := 4983230072969 + 3 ^ 40 * 7333778 * 2
def baseEnd_7333778 : Nat := 1255251042456370931182525

theorem tailTrace_7333778 : CollatzResearch.WordTrace tailWord_7333778 prefixEnd_7333778 1255251042456370931182525 := by
  unfold tailWord_7333778
  simp only [CollatzResearch.WordTrace]
  refine ⟨66871214606245572602532497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178323238949988193606753325 66871214606245572602532497)
  ·
    refine ⟨50153410954684179451899373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66871214606245572602532497 50153410954684179451899373)
    ·
      refine ⟨18807529108006567294462265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 50153410954684179451899373 18807529108006567294462265)
      ·
        refine ⟨14105646831004925470846699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18807529108006567294462265 14105646831004925470846699)
        ·
          refine ⟨21158470246507388206270049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14105646831004925470846699 21158470246507388206270049)
          ·
            refine ⟨15868852684880541154702537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21158470246507388206270049 15868852684880541154702537)
            ·
              refine ⟨11901639513660405866026903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15868852684880541154702537 11901639513660405866026903)
              ·
                refine ⟨17852459270490608799040355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11901639513660405866026903 17852459270490608799040355)
                ·
                  refine ⟨26778688905735913198560533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17852459270490608799040355 26778688905735913198560533)
                  ·
                    refine ⟨1255251042456370931182525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26778688905735913198560533 1255251042456370931182525)
                    ·
                      rfl

theorem cell23_7333778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_7333778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333778 prefixEnd_7333778 := by exact prefixLift 7333778
  have htrace : WordTrace (prefixWord ++ tailWord_7333778) baseStart_7333778 baseEnd_7333778 := by
    simpa [prefixWord, tailWord_7333778, baseEnd_7333778] using wordTrace_append hprefix tailTrace_7333778
  have hstable : (prefixWord ++ tailWord_7333778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333778).length < 2 ^ (prefixWord ++ tailWord_7333778).sum := by decide
  have hdescent : baseEnd_7333778 < baseStart_7333778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333781 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 4]
def baseStart_7333781 : Nat := 118140960795 + 7333781 * 2 ^ 59
def prefixEnd_7333781 : Nat := 4983230072969 + 3 ^ 40 * 7333781 * 2
def baseEnd_7333781 : Nat := 3765754667811076281810061

theorem tailTrace_7333781 : CollatzResearch.WordTrace tailWord_7333781 prefixEnd_7333781 3765754667811076281810061 := by
  unfold tailWord_7333781
  simp only [CollatzResearch.WordTrace]
  refine ⟨267484967843971421922489197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178323311895980947948326131 267484967843971421922489197)
  ·
    refine ⟨100306862941489283220933449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267484967843971421922489197 100306862941489283220933449)
    ·
      refine ⟨75230147206116962415700087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100306862941489283220933449 75230147206116962415700087)
      ·
        refine ⟨112845220809175443623550131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75230147206116962415700087 112845220809175443623550131)
        ·
          refine ⟨169267831213763165435325197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112845220809175443623550131 169267831213763165435325197)
          ·
            refine ⟨63475436705161187038246949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 169267831213763165435325197 63475436705161187038246949)
            ·
              refine ⟨11901644382217722569671303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 63475436705161187038246949 11901644382217722569671303)
              ·
                refine ⟨17852466573326583854506955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11901644382217722569671303 17852466573326583854506955)
                ·
                  refine ⟨26778699859989875781760433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17852466573326583854506955 26778699859989875781760433)
                  ·
                    refine ⟨20084024894992406836320325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26778699859989875781760433 20084024894992406836320325)
                    ·
                      refine ⟨3765754667811076281810061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20084024894992406836320325 3765754667811076281810061)
                      ·
                        rfl

theorem cell23_7333781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 1, 2, 4].length) (baseStart_7333781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333781 prefixEnd_7333781 := by exact prefixLift 7333781
  have htrace : WordTrace (prefixWord ++ tailWord_7333781) baseStart_7333781 baseEnd_7333781 := by
    simpa [prefixWord, tailWord_7333781, baseEnd_7333781] using wordTrace_append hprefix tailTrace_7333781
  have hstable : (prefixWord ++ tailWord_7333781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333781).length < 2 ^ (prefixWord ++ tailWord_7333781).sum := by decide
  have hdescent : baseEnd_7333781 < baseStart_7333781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333788 : List Nat := [2, 2, 3, 3, 1, 1, 2, 1, 3, 2, 3]
def baseStart_7333788 : Nat := 118140960795 + 7333788 * 2 ^ 59
def prefixEnd_7333788 : Nat := 4983230072969 + 3 ^ 40 * 7333788 * 2
def baseEnd_7333788 : Nat := 3765758262175657754422529

theorem tailTrace_7333788 : CollatzResearch.WordTrace tailWord_7333788 prefixEnd_7333788 3765758262175657754422529 := by
  unfold tailWord_7333788
  simp only [CollatzResearch.WordTrace]
  refine ⟨133742611577473031058997009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178323482103297374745329345 133742611577473031058997009)
  ·
    refine ⟨100306958683104773294247757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133742611577473031058997009 100306958683104773294247757)
    ·
      refine ⟨37615109506164289985342909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100306958683104773294247757 37615109506164289985342909)
      ·
        refine ⟨14105666064811608744503591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 37615109506164289985342909 14105666064811608744503591)
        ·
          refine ⟨21158499097217413116755387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14105666064811608744503591 21158499097217413116755387)
          ·
            refine ⟨31737748645826119675133081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21158499097217413116755387 31737748645826119675133081)
            ·
              refine ⟨23803311484369589756349811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31737748645826119675133081 23803311484369589756349811)
              ·
                refine ⟨35704967226554384634524717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23803311484369589756349811 35704967226554384634524717)
                ·
                  refine ⟨13389362709957894237946769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35704967226554384634524717 13389362709957894237946769)
                  ·
                    refine ⟨10042022032468420678460077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13389362709957894237946769 10042022032468420678460077)
                    ·
                      refine ⟨3765758262175657754422529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10042022032468420678460077 3765758262175657754422529)
                      ·
                        rfl

theorem cell23_7333788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_7333788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333788 prefixEnd_7333788 := by exact prefixLift 7333788
  have htrace : WordTrace (prefixWord ++ tailWord_7333788) baseStart_7333788 baseEnd_7333788 := by
    simpa [prefixWord, tailWord_7333788, baseEnd_7333788] using wordTrace_append hprefix tailTrace_7333788
  have hstable : (prefixWord ++ tailWord_7333788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333788).length < 2 ^ (prefixWord ++ tailWord_7333788).sum := by decide
  have hdescent : baseEnd_7333788 < baseStart_7333788 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333818 : List Nat := [3, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3]
def baseStart_7333818 : Nat := 118140960795 + 7333818 * 2 ^ 59
def prefixEnd_7333818 : Nat := 4983230072969 + 3 ^ 40 * 7333818 * 2
def baseEnd_7333818 : Nat := 3765773666595292637047391

theorem tailTrace_7333818 : CollatzResearch.WordTrace tailWord_7333818 prefixEnd_7333818 3765773666595292637047391 := by
  unfold tailWord_7333818
  simp only [CollatzResearch.WordTrace]
  refine ⟨66871579336209344310396527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178324211563224918161057405 66871579336209344310396527)
  ·
    refine ⟨100307369004314016465594791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66871579336209344310396527 100307369004314016465594791)
    ·
      refine ⟨150461053506471024698392187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100307369004314016465594791 150461053506471024698392187)
      ·
        refine ⟨225691580259706537047588281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150461053506471024698392187 225691580259706537047588281)
        ·
          refine ⟨169268685194779902785691211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225691580259706537047588281 169268685194779902785691211)
          ·
            refine ⟨253903027792169854178536817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169268685194779902785691211 253903027792169854178536817)
            ·
              refine ⟨190427270844127390633902613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253903027792169854178536817 190427270844127390633902613)
              ·
                refine ⟨8926278320818471435964185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 190427270844127390633902613 8926278320818471435964185)
                ·
                  refine ⟨6694708740613853576973139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8926278320818471435964185 6694708740613853576973139)
                  ·
                    refine ⟨10042063110920780365459709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6694708740613853576973139 10042063110920780365459709)
                    ·
                      refine ⟨3765773666595292637047391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10042063110920780365459709 3765773666595292637047391)
                      ·
                        rfl

theorem cell23_7333818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3].length) (baseStart_7333818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333818 prefixEnd_7333818 := by exact prefixLift 7333818
  have htrace : WordTrace (prefixWord ++ tailWord_7333818) baseStart_7333818 baseEnd_7333818 := by
    simpa [prefixWord, tailWord_7333818, baseEnd_7333818] using wordTrace_append hprefix tailTrace_7333818
  have hstable : (prefixWord ++ tailWord_7333818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333818).length < 2 ^ (prefixWord ++ tailWord_7333818).sum := by decide
  have hdescent : baseEnd_7333818 < baseStart_7333818 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333835 : List Nat := [1, 1, 1, 1, 3, 4, 5, 1, 2, 1, 3]
def baseStart_7333835 : Nat := 118140960795 + 7333835 * 2 ^ 59
def prefixEnd_7333835 : Nat := 4983230072969 + 3 ^ 40 * 7333835 * 2
def baseEnd_7333835 : Nat := 3765782395766419070534813

theorem tailTrace_7333835 : CollatzResearch.WordTrace tailWord_7333835 prefixEnd_7333835 3765782395766419070534813 := by
  unfold tailWord_7333835
  simp only [CollatzResearch.WordTrace]
  refine ⟨267486937385775789144954959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178324624923850526096636639 267486937385775789144954959)
  ·
    refine ⟨401230406078663683717432439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267486937385775789144954959 401230406078663683717432439)
    ·
      refine ⟨601845609117995525576148659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401230406078663683717432439 601845609117995525576148659)
      ·
        refine ⟨902768413676993288364222989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601845609117995525576148659 902768413676993288364222989)
        ·
          refine ⟨338538155128872483136583621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 902768413676993288364222989 338538155128872483136583621)
          ·
            refine ⟨63475904086663590588109429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 338538155128872483136583621 63475904086663590588109429)
            ·
              refine ⟨5950866008124711617635259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 63475904086663590588109429 5950866008124711617635259)
              ·
                refine ⟨8926299012187067426452889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5950866008124711617635259 8926299012187067426452889)
                ·
                  refine ⟨6694724259140300569839667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8926299012187067426452889 6694724259140300569839667)
                  ·
                    refine ⟨10042086388710450854759501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6694724259140300569839667 10042086388710450854759501)
                    ·
                      refine ⟨3765782395766419070534813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10042086388710450854759501 3765782395766419070534813)
                      ·
                        rfl

theorem cell23_7333835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 5, 1, 2, 1, 3].length) (baseStart_7333835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333835 prefixEnd_7333835 := by exact prefixLift 7333835
  have htrace : WordTrace (prefixWord ++ tailWord_7333835) baseStart_7333835 baseEnd_7333835 := by
    simpa [prefixWord, tailWord_7333835, baseEnd_7333835] using wordTrace_append hprefix tailTrace_7333835
  have hstable : (prefixWord ++ tailWord_7333835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333835).length < 2 ^ (prefixWord ++ tailWord_7333835).sum := by decide
  have hdescent : baseEnd_7333835 < baseStart_7333835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333845 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 1, 3, 2]
def baseStart_7333845 : Nat := 118140960795 + 7333845 * 2 ^ 59
def prefixEnd_7333845 : Nat := 4983230072969 + 3 ^ 40 * 7333845 * 2
def baseEnd_7333845 : Nat := 3765787530572964031409767

theorem tailTrace_7333845 : CollatzResearch.WordTrace tailWord_7333845 prefixEnd_7333845 3765787530572964031409767 := by
  unfold tailWord_7333845
  simp only [CollatzResearch.WordTrace]
  refine ⟨267487302115739560852818989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178324868077159707235212659 267487302115739560852818989)
  ·
    refine ⟨100307738293402335319807121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267487302115739560852818989 100307738293402335319807121)
    ·
      refine ⟨75230803720051751489855341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100307738293402335319807121 75230803720051751489855341)
      ·
        refine ⟨28211551395019406808695753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 75230803720051751489855341 28211551395019406808695753)
        ·
          refine ⟨21158663546264555106521815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28211551395019406808695753 21158663546264555106521815)
          ·
            refine ⟨31737995319396832659782723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21158663546264555106521815 31737995319396832659782723)
            ·
              refine ⟨47606992979095248989674085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31737995319396832659782723 47606992979095248989674085)
              ·
                refine ⟨8926311183580359185563891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 47606992979095248989674085 8926311183580359185563891)
                ·
                  refine ⟨13389466775370538778345837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8926311183580359185563891 13389466775370538778345837)
                  ·
                    refine ⟨5021050040763952041879689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13389466775370538778345837 5021050040763952041879689)
                    ·
                      refine ⟨3765787530572964031409767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021050040763952041879689 3765787530572964031409767)
                      ·
                        rfl

theorem cell23_7333845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 3, 2].length) (baseStart_7333845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333845 prefixEnd_7333845 := by exact prefixLift 7333845
  have htrace : WordTrace (prefixWord ++ tailWord_7333845) baseStart_7333845 baseEnd_7333845 := by
    simpa [prefixWord, tailWord_7333845, baseEnd_7333845] using wordTrace_append hprefix tailTrace_7333845
  have hstable : (prefixWord ++ tailWord_7333845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333845).length < 2 ^ (prefixWord ++ tailWord_7333845).sum := by decide
  have hdescent : baseEnd_7333845 < baseStart_7333845 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333881 : List Nat := [1, 2, 1, 3, 1, 4, 3, 1, 7]
def baseStart_7333881 : Nat := 118140960795 + 7333881 * 2 ^ 59
def prefixEnd_7333881 : Nat := 4983230072969 + 3 ^ 40 * 7333881 * 2
def baseEnd_7333881 : Nat := 418422890652947321173289

theorem tailTrace_7333881 : CollatzResearch.WordTrace tailWord_7333881 prefixEnd_7333881 418422890652947321173289 := by
  unfold tailWord_7333881
  simp only [CollatzResearch.WordTrace]
  refine ⟨267488615143609139001129497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178325743429072759334086331 267488615143609139001129497)
  ·
    refine ⟨200616461357706854250847123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267488615143609139001129497 200616461357706854250847123)
    ·
      refine ⟨300924692036560281376270685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200616461357706854250847123 300924692036560281376270685)
      ·
        refine ⟨112846759513710105516101507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 300924692036560281376270685 112846759513710105516101507)
        ·
          refine ⟨169270139270565158274152261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112846759513710105516101507 169270139270565158274152261)
          ·
            refine ⟨31738151113230967176403549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 169270139270565158274152261 31738151113230967176403549)
            ·
              refine ⟨11901806667461612691151331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31738151113230967176403549 11901806667461612691151331)
              ·
                refine ⟨17852710001192419036726997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11901806667461612691151331 17852710001192419036726997)
                ·
                  refine ⟨418422890652947321173289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17852710001192419036726997 418422890652947321173289)
                  ·
                    rfl

theorem cell23_7333881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 3, 1, 7].length) (baseStart_7333881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333881 prefixEnd_7333881 := by exact prefixLift 7333881
  have htrace : WordTrace (prefixWord ++ tailWord_7333881) baseStart_7333881 baseEnd_7333881 := by
    simpa [prefixWord, tailWord_7333881, baseEnd_7333881] using wordTrace_append hprefix tailTrace_7333881
  have hstable : (prefixWord ++ tailWord_7333881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333881).length < 2 ^ (prefixWord ++ tailWord_7333881).sum := by decide
  have hdescent : baseEnd_7333881 < baseStart_7333881 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333891 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 3]
def baseStart_7333891 : Nat := 118140960795 + 7333891 * 2 ^ 59
def prefixEnd_7333891 : Nat := 4983230072969 + 3 ^ 40 * 7333891 * 2
def baseEnd_7333891 : Nat := 3765811150683070851434555

theorem tailTrace_7333891 : CollatzResearch.WordTrace tailWord_7333891 prefixEnd_7333891 3765811150683070851434555 := by
  unfold tailWord_7333891
  simp only [CollatzResearch.WordTrace]
  refine ⟨267488979873572910708993527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178325986582381940472662351 267488979873572910708993527)
  ·
    refine ⟨401233469810359366063490291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267488979873572910708993527 401233469810359366063490291)
    ·
      refine ⟨601850204715539049095235437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401233469810359366063490291 601850204715539049095235437)
      ·
        refine ⟨225693826768327143410713289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 601850204715539049095235437 225693826768327143410713289)
        ·
          refine ⟨169270370076245357558034967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 225693826768327143410713289 169270370076245357558034967)
          ·
            refine ⟨253905555114368036337052451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169270370076245357558034967 253905555114368036337052451)
            ·
              refine ⟨380858332671552054505578677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253905555114368036337052451 380858332671552054505578677)
              ·
                refine ⟨35705468687958005109898001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 380858332671552054505578677 35705468687958005109898001)
                ·
                  refine ⟨26779101515968503832423501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35705468687958005109898001 26779101515968503832423501)
                  ·
                    refine ⟨10042163068488188937158813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26779101515968503832423501 10042163068488188937158813)
                    ·
                      refine ⟨3765811150683070851434555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10042163068488188937158813 3765811150683070851434555)
                      ·
                        rfl

theorem cell23_7333891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 3, 3].length) (baseStart_7333891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333891 prefixEnd_7333891 := by exact prefixLift 7333891
  have htrace : WordTrace (prefixWord ++ tailWord_7333891) baseStart_7333891 baseEnd_7333891 := by
    simpa [prefixWord, tailWord_7333891, baseEnd_7333891] using wordTrace_append hprefix tailTrace_7333891
  have hstable : (prefixWord ++ tailWord_7333891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333891).length < 2 ^ (prefixWord ++ tailWord_7333891).sum := by decide
  have hdescent : baseEnd_7333891 < baseStart_7333891 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333931 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 4]
def baseStart_7333931 : Nat := 118140960795 + 7333931 * 2 ^ 59
def prefixEnd_7333931 : Nat := 4983230072969 + 3 ^ 40 * 7333931 * 2
def baseEnd_7333931 : Nat := 3765831689909250694934371

theorem tailTrace_7333931 : CollatzResearch.WordTrace tailWord_7333931 prefixEnd_7333931 3765831689909250694934371 := by
  unfold tailWord_7333931
  simp only [CollatzResearch.WordTrace]
  refine ⟨267490438793427997540449647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178326959195618665026966431 267490438793427997540449647)
  ·
    refine ⟨401235658190141996310674471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267490438793427997540449647 401235658190141996310674471)
    ·
      refine ⟨601853487285212994466011707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401235658190141996310674471 601853487285212994466011707)
      ·
        refine ⟨902780230927819491699017561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601853487285212994466011707 902780230927819491699017561)
        ·
          refine ⟨677085173195864618774263171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 902780230927819491699017561 677085173195864618774263171)
          ·
            refine ⟨1015627759793796928161394757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 677085173195864618774263171 1015627759793796928161394757)
            ·
              refine ⟨190430204961336924030261517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1015627759793796928161394757 190430204961336924030261517)
              ·
                refine ⟨71411326860501346511348069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 190430204961336924030261517 71411326860501346511348069)
                ·
                  refine ⟨13389623786344002470877763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 71411326860501346511348069 13389623786344002470877763)
                  ·
                    refine ⟨20084435679516003706316645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13389623786344002470877763 20084435679516003706316645)
                    ·
                      refine ⟨3765831689909250694934371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20084435679516003706316645 3765831689909250694934371)
                      ·
                        rfl

theorem cell23_7333931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 4, 1, 4].length) (baseStart_7333931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333931 prefixEnd_7333931 := by exact prefixLift 7333931
  have htrace : WordTrace (prefixWord ++ tailWord_7333931) baseStart_7333931 baseEnd_7333931 := by
    simpa [prefixWord, tailWord_7333931, baseEnd_7333931] using wordTrace_append hprefix tailTrace_7333931
  have hstable : (prefixWord ++ tailWord_7333931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333931).length < 2 ^ (prefixWord ++ tailWord_7333931).sum := by decide
  have hdescent : baseEnd_7333931 < baseStart_7333931 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333965 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 1, 6, 2]
def baseStart_7333965 : Nat := 118140960795 + 7333965 * 2 ^ 59
def prefixEnd_7333965 : Nat := 4983230072969 + 3 ^ 40 * 7333965 * 2
def baseEnd_7333965 : Nat := 3765849148251503561909215

theorem tailTrace_7333965 : CollatzResearch.WordTrace tailWord_7333965 prefixEnd_7333965 3765849148251503561909215 := by
  unfold tailWord_7333965
  simp only [CollatzResearch.WordTrace]
  refine ⟨267491678875304821347187349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178327785916869880898124899 267491678875304821347187349)
  ·
    refine ⟨12538672447279913500649407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 267491678875304821347187349 12538672447279913500649407)
    ·
      refine ⟨18808008670919870250974111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12538672447279913500649407 18808008670919870250974111)
      ·
        refine ⟨28212013006379805376461167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18808008670919870250974111 28212013006379805376461167)
        ·
          refine ⟨42318019509569708064691751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28212013006379805376461167 42318019509569708064691751)
          ·
            refine ⟨63477029264354562097037627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42318019509569708064691751 63477029264354562097037627)
            ·
              refine ⟨95215543896531843145556441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63477029264354562097037627 95215543896531843145556441)
              ·
                refine ⟨71411657922398882359167331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 95215543896531843145556441 71411657922398882359167331)
                ·
                  refine ⟨107117486883598323538750997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71411657922398882359167331 107117486883598323538750997)
                  ·
                    refine ⟨5021132197668671415878953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 107117486883598323538750997 5021132197668671415878953)
                    ·
                      refine ⟨3765849148251503561909215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021132197668671415878953 3765849148251503561909215)
                      ·
                        rfl

theorem cell23_7333965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 6, 2].length) (baseStart_7333965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333965 prefixEnd_7333965 := by exact prefixLift 7333965
  have htrace : WordTrace (prefixWord ++ tailWord_7333965) baseStart_7333965 baseEnd_7333965 := by
    simpa [prefixWord, tailWord_7333965, baseEnd_7333965] using wordTrace_append hprefix tailTrace_7333965
  have hstable : (prefixWord ++ tailWord_7333965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333965).length < 2 ^ (prefixWord ++ tailWord_7333965).sum := by decide
  have hdescent : baseEnd_7333965 < baseStart_7333965 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333975 : List Nat := [1, 1, 3, 2, 2, 1, 3, 5, 1, 4]
def baseStart_7333975 : Nat := 118140960795 + 7333975 * 2 ^ 59
def prefixEnd_7333975 : Nat := 4983230072969 + 3 ^ 40 * 7333975 * 2
def baseEnd_7333975 : Nat := 1255284761019349507594723

theorem tailTrace_7333975 : CollatzResearch.WordTrace tailWord_7333975 prefixEnd_7333975 1255284761019349507594723 := by
  unfold tailWord_7333975
  simp only [CollatzResearch.WordTrace]
  refine ⟨267492043605268593055051379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178328029070179062036700919 267492043605268593055051379)
  ·
    refine ⟨401238065407902889582577069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267492043605268593055051379 401238065407902889582577069)
    ·
      refine ⟨150464274527963583593466401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 401238065407902889582577069 150464274527963583593466401)
      ·
        refine ⟨112848205895972687695099801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150464274527963583593466401 112848205895972687695099801)
        ·
          refine ⟨84636154421979515771324851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112848205895972687695099801 84636154421979515771324851)
          ·
            refine ⟨126954231632969273656987277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84636154421979515771324851 126954231632969273656987277)
            ·
              refine ⟨47607836862363477621370229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 126954231632969273656987277 47607836862363477621370229)
              ·
                refine ⟨4463234705846576027003459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 47607836862363477621370229 4463234705846576027003459)
                ·
                  refine ⟨6694852058769864040505189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463234705846576027003459 6694852058769864040505189)
                  ·
                    refine ⟨1255284761019349507594723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6694852058769864040505189 1255284761019349507594723)
                    ·
                      rfl

theorem cell23_7333975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 5, 1, 4].length) (baseStart_7333975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333975 prefixEnd_7333975 := by exact prefixLift 7333975
  have htrace : WordTrace (prefixWord ++ tailWord_7333975) baseStart_7333975 baseEnd_7333975 := by
    simpa [prefixWord, tailWord_7333975, baseEnd_7333975] using wordTrace_append hprefix tailTrace_7333975
  have hstable : (prefixWord ++ tailWord_7333975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333975).length < 2 ^ (prefixWord ++ tailWord_7333975).sum := by decide
  have hdescent : baseEnd_7333975 < baseStart_7333975 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333988 : List Nat := [2, 3, 1, 1, 2, 1, 5, 2, 6]
def baseStart_7333988 : Nat := 118140960795 + 7333988 * 2 ^ 59
def prefixEnd_7333988 : Nat := 4983230072969 + 3 ^ 40 * 7333988 * 2
def baseEnd_7333988 : Nat := 418428995367395219102401

theorem tailTrace_7333988 : CollatzResearch.WordTrace tailWord_7333988 prefixEnd_7333988 418428995367395219102401 := by
  unfold tailWord_7333988
  simp only [CollatzResearch.WordTrace]
  refine ⟨133746258877110748137637309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178328345169480997516849745 133746258877110748137637309)
  ·
    refine ⟨50154847078916530551613991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 133746258877110748137637309 50154847078916530551613991)
    ·
      refine ⟨75232270618374795827420987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50154847078916530551613991 75232270618374795827420987)
      ·
        refine ⟨112848405927562193741131481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75232270618374795827420987 112848405927562193741131481)
        ·
          refine ⟨84636304445671645305848611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112848405927562193741131481 84636304445671645305848611)
          ·
            refine ⟨126954456668507467958772917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84636304445671645305848611 126954456668507467958772917)
            ·
              refine ⟨11901980312672575121134961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 126954456668507467958772917 11901980312672575121134961)
              ·
                refine ⟨8926485234504431340851221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11901980312672575121134961 8926485234504431340851221)
                ·
                  refine ⟨418428995367395219102401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8926485234504431340851221 418428995367395219102401)
                  ·
                    rfl

theorem cell23_7333988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_7333988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333988 prefixEnd_7333988 := by exact prefixLift 7333988
  have htrace : WordTrace (prefixWord ++ tailWord_7333988) baseStart_7333988 baseEnd_7333988 := by
    simpa [prefixWord, tailWord_7333988, baseEnd_7333988] using wordTrace_append hprefix tailTrace_7333988
  have hstable : (prefixWord ++ tailWord_7333988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333988).length < 2 ^ (prefixWord ++ tailWord_7333988).sum := by decide
  have hdescent : baseEnd_7333988 < baseStart_7333988 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7333991 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 8]
def baseStart_7333991 : Nat := 118140960795 + 7333991 * 2 ^ 59
def prefixEnd_7333991 : Nat := 4983230072969 + 3 ^ 40 * 7333991 * 2
def baseEnd_7333991 : Nat := 3765862498748520460184095

theorem tailTrace_7333991 : CollatzResearch.WordTrace tailWord_7333991 prefixEnd_7333991 3765862498748520460184095 := by
  unfold tailWord_7333991
  simp only [CollatzResearch.WordTrace]
  refine ⟨267492627173210627787633827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178328418115473751858422551 267492627173210627787633827)
  ·
    refine ⟨401238940759815941681450741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267492627173210627787633827 401238940759815941681450741)
    ·
      refine ⟨37616150696232744532636007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 401238940759815941681450741 37616150696232744532636007)
      ·
        refine ⟨56424226044349116798954011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37616150696232744532636007 56424226044349116798954011)
        ·
          refine ⟨84636339066523675198431017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56424226044349116798954011 84636339066523675198431017)
          ·
            refine ⟨63477254299892756398823263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84636339066523675198431017 63477254299892756398823263)
            ·
              refine ⟨95215881449839134598234895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63477254299892756398823263 95215881449839134598234895)
              ·
                refine ⟨142823822174758701897352343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 95215881449839134598234895 142823822174758701897352343)
                ·
                  refine ⟨214235733262138052846028515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 142823822174758701897352343 214235733262138052846028515)
                  ·
                    refine ⟨321353599893207079269042773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 214235733262138052846028515 321353599893207079269042773)
                    ·
                      refine ⟨3765862498748520460184095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 321353599893207079269042773 3765862498748520460184095)
                      ·
                        rfl

theorem cell23_7333991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 1, 8].length) (baseStart_7333991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7333991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7333991 prefixEnd_7333991 := by exact prefixLift 7333991
  have htrace : WordTrace (prefixWord ++ tailWord_7333991) baseStart_7333991 baseEnd_7333991 := by
    simpa [prefixWord, tailWord_7333991, baseEnd_7333991] using wordTrace_append hprefix tailTrace_7333991
  have hstable : (prefixWord ++ tailWord_7333991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7333991).length < 2 ^ (prefixWord ++ tailWord_7333991).sum := by decide
  have hdescent : baseEnd_7333991 < baseStart_7333991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7333991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334025 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 2, 3, 2]
def baseStart_7334025 : Nat := 118140960795 + 7334025 * 2 ^ 59
def prefixEnd_7334025 : Nat := 4983230072969 + 3 ^ 40 * 7334025 * 2
def baseEnd_7334025 : Nat := 3765879957090773327158939

theorem tailTrace_7334025 : CollatzResearch.WordTrace tailWord_7334025 prefixEnd_7334025 3765879957090773327158939 := by
  unfold tailWord_7334025
  simp only [CollatzResearch.WordTrace]
  refine ⟨267493867255087451594371529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178329244836724967729581019 267493867255087451594371529)
  ·
    refine ⟨200620400441315588695778647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267493867255087451594371529 200620400441315588695778647)
    ·
      refine ⟨300930600661973383043667971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200620400441315588695778647 300930600661973383043667971)
      ·
        refine ⟨451395900992960074565501957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300930600661973383043667971 451395900992960074565501957)
        ·
          refine ⟨84636731436180013981031617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 451395900992960074565501957 84636731436180013981031617)
          ·
            refine ⟨63477548577135010485773713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84636731436180013981031617 63477548577135010485773713)
            ·
              refine ⟨47608161432851257864330285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 63477548577135010485773713 47608161432851257864330285)
              ·
                refine ⟨17853060537319221699123857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 47608161432851257864330285 17853060537319221699123857)
                ·
                  refine ⟨13389795402989416274342893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17853060537319221699123857 13389795402989416274342893)
                  ·
                    refine ⟨5021173276121031102878585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13389795402989416274342893 5021173276121031102878585)
                    ·
                      refine ⟨3765879957090773327158939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021173276121031102878585 3765879957090773327158939)
                      ·
                        rfl

theorem cell23_7334025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 3, 2].length) (baseStart_7334025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334025 prefixEnd_7334025 := by exact prefixLift 7334025
  have htrace : WordTrace (prefixWord ++ tailWord_7334025) baseStart_7334025 baseEnd_7334025 := by
    simpa [prefixWord, tailWord_7334025, baseEnd_7334025] using wordTrace_append hprefix tailTrace_7334025
  have hstable : (prefixWord ++ tailWord_7334025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334025).length < 2 ^ (prefixWord ++ tailWord_7334025).sum := by decide
  have hdescent : baseEnd_7334025 < baseStart_7334025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334069 : List Nat := [1, 3, 3, 4, 1, 2, 1, 2, 1, 5]
def baseStart_7334069 : Nat := 118140960795 + 7334069 * 2 ^ 59
def prefixEnd_7334069 : Nat := 4983230072969 + 3 ^ 40 * 7334069 * 2
def baseEnd_7334069 : Nat := 1255300850079857051669579

theorem tailTrace_7334069 : CollatzResearch.WordTrace tailWord_7334069 prefixEnd_7334069 1255300850079857051669579 := by
  unfold tailWord_7334069
  simp only [CollatzResearch.WordTrace]
  refine ⟨267495472066928047108973261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178330314711285364739315507 267495472066928047108973261)
  ·
    refine ⟨100310802025098017665864973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267495472066928047108973261 100310802025098017665864973)
    ·
      refine ⟨37616550759411756624699365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100310802025098017665864973 37616550759411756624699365)
      ·
        refine ⟨7053103267389704367131131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 37616550759411756624699365 7053103267389704367131131)
        ·
          refine ⟨10579654901084556550696697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053103267389704367131131 10579654901084556550696697)
          ·
            refine ⟨7934741175813417413022523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10579654901084556550696697 7934741175813417413022523)
            ·
              refine ⟨11902111763720126119533785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7934741175813417413022523 11902111763720126119533785)
              ·
                refine ⟨8926583822790094589650339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11902111763720126119533785 8926583822790094589650339)
                ·
                  refine ⟨13389875734185141884475509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8926583822790094589650339 13389875734185141884475509)
                  ·
                    refine ⟨1255300850079857051669579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13389875734185141884475509 1255300850079857051669579)
                    ·
                      rfl

theorem cell23_7334069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_7334069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334069 prefixEnd_7334069 := by exact prefixLift 7334069
  have htrace : WordTrace (prefixWord ++ tailWord_7334069) baseStart_7334069 baseEnd_7334069 := by
    simpa [prefixWord, tailWord_7334069, baseEnd_7334069] using wordTrace_append hprefix tailTrace_7334069
  have hstable : (prefixWord ++ tailWord_7334069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334069).length < 2 ^ (prefixWord ++ tailWord_7334069).sum := by decide
  have hdescent : baseEnd_7334069 < baseStart_7334069 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334082 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_7334082 : Nat := 118140960795 + 7334082 * 2 ^ 59
def prefixEnd_7334082 : Nat := 4983230072969 + 3 ^ 40 * 7334082 * 2
def baseEnd_7334082 : Nat := 1255303075162693201382059

theorem tailTrace_7334082 : CollatzResearch.WordTrace tailWord_7334082 prefixEnd_7334082 1255303075162693201382059 := by
  unfold tailWord_7334082
  simp only [CollatzResearch.WordTrace]
  refine ⟨66873986553970237582299125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178330630810587300219464333 66873986553970237582299125)
  ·
    refine ⟨6269436239434709773340543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 66873986553970237582299125 6269436239434709773340543)
    ·
      refine ⟨9404154359152064660010815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6269436239434709773340543 9404154359152064660010815)
      ·
        refine ⟨14106231538728096990016223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9404154359152064660010815 14106231538728096990016223)
        ·
          refine ⟨21159347308092145485024335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14106231538728096990016223 21159347308092145485024335)
          ·
            refine ⟨31739020962138218227536503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21159347308092145485024335 31739020962138218227536503)
            ·
              refine ⟨47608531443207327341304755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31739020962138218227536503 47608531443207327341304755)
              ·
                refine ⟨71412797164810991011957133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47608531443207327341304755 71412797164810991011957133)
                ·
                  refine ⟨26779798936804121629483925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71412797164810991011957133 26779798936804121629483925)
                  ·
                    refine ⟨1255303075162693201382059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26779798936804121629483925 1255303075162693201382059)
                    ·
                      rfl

theorem cell23_7334082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_7334082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334082 prefixEnd_7334082 := by exact prefixLift 7334082
  have htrace : WordTrace (prefixWord ++ tailWord_7334082) baseStart_7334082 baseEnd_7334082 := by
    simpa [prefixWord, tailWord_7334082, baseEnd_7334082] using wordTrace_append hprefix tailTrace_7334082
  have hstable : (prefixWord ++ tailWord_7334082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334082).length < 2 ^ (prefixWord ++ tailWord_7334082).sum := by decide
  have hdescent : baseEnd_7334082 < baseStart_7334082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334105 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 3]
def baseStart_7334105 : Nat := 118140960795 + 7334105 * 2 ^ 59
def prefixEnd_7334105 : Nat := 4983230072969 + 3 ^ 40 * 7334105 * 2
def baseEnd_7334105 : Nat := 3765921035543133014158571

theorem tailTrace_7334105 : CollatzResearch.WordTrace tailWord_7334105 prefixEnd_7334105 3765921035543133014158571 := by
  unfold tailWord_7334105
  simp only [CollatzResearch.WordTrace]
  refine ⟨267496785094797625257283769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178331190063198416838189179 267496785094797625257283769)
  ·
    refine ⟨200622588821098218942962827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267496785094797625257283769 200622588821098218942962827)
    ·
      refine ⟨300933883231647328414444241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200622588821098218942962827 300933883231647328414444241)
      ·
        refine ⟨225700412423735496310833181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300933883231647328414444241 225700412423735496310833181)
        ·
          refine ⟨84637654658900811116562443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 225700412423735496310833181 84637654658900811116562443)
          ·
            refine ⟨126956481988351216674843665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84637654658900811116562443 126956481988351216674843665)
            ·
              refine ⟨95217361491263412506132749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 126956481988351216674843665 95217361491263412506132749)
              ·
                refine ⟨35706510559223779689799781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 95217361491263412506132749 35706510559223779689799781)
                ·
                  refine ⟨6694970729854458691837459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 35706510559223779689799781 6694970729854458691837459)
                  ·
                    refine ⟨10042456094781688037756189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6694970729854458691837459 10042456094781688037756189)
                    ·
                      refine ⟨3765921035543133014158571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10042456094781688037756189 3765921035543133014158571)
                      ·
                        rfl

theorem cell23_7334105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 1, 3].length) (baseStart_7334105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334105 prefixEnd_7334105 := by exact prefixLift 7334105
  have htrace : WordTrace (prefixWord ++ tailWord_7334105) baseStart_7334105 baseEnd_7334105 := by
    simpa [prefixWord, tailWord_7334105, baseEnd_7334105] using wordTrace_append hprefix tailTrace_7334105
  have hstable : (prefixWord ++ tailWord_7334105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334105).length < 2 ^ (prefixWord ++ tailWord_7334105).sum := by decide
  have hdescent : baseEnd_7334105 < baseStart_7334105 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334106 : List Nat := [3, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2]
def baseStart_7334106 : Nat := 118140960795 + 7334106 * 2 ^ 59
def prefixEnd_7334106 : Nat := 4983230072969 + 3 ^ 40 * 7334106 * 2
def baseEnd_7334106 : Nat := 3765921549023787510246067

theorem tailTrace_7334106 : CollatzResearch.WordTrace tailWord_7334106 prefixEnd_7334106 3765921549023787510246067 := by
  unfold tailWord_7334106
  simp only [CollatzResearch.WordTrace]
  refine ⟨66874205391948500607017543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178331214378529334952046781 66874205391948500607017543)
  ·
    refine ⟨100311308087922750910526315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66874205391948500607017543 100311308087922750910526315)
    ·
      refine ⟨150466962131884126365789473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100311308087922750910526315 150466962131884126365789473)
      ·
        refine ⟨112850221598913094774342105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 150466962131884126365789473 112850221598913094774342105)
        ·
          refine ⟨84637666199184821080756579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112850221598913094774342105 84637666199184821080756579)
          ·
            refine ⟨126956499298777231621134869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 84637666199184821080756579 126956499298777231621134869)
            ·
              refine ⟨5951085904630182732240697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 126956499298777231621134869 5951085904630182732240697)
              ·
                refine ⟨4463314428472637049180523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5951085904630182732240697 4463314428472637049180523)
                ·
                  refine ⟨6694971642708955573770785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463314428472637049180523 6694971642708955573770785)
                  ·
                    refine ⟨5021228732031716680328089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6694971642708955573770785 5021228732031716680328089)
                    ·
                      refine ⟨3765921549023787510246067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021228732031716680328089 3765921549023787510246067)
                      ·
                        rfl

theorem cell23_7334106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 2, 1, 2, 2].length) (baseStart_7334106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334106 prefixEnd_7334106 := by exact prefixLift 7334106
  have htrace : WordTrace (prefixWord ++ tailWord_7334106) baseStart_7334106 baseEnd_7334106 := by
    simpa [prefixWord, tailWord_7334106, baseEnd_7334106] using wordTrace_append hprefix tailTrace_7334106
  have hstable : (prefixWord ++ tailWord_7334106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334106).length < 2 ^ (prefixWord ++ tailWord_7334106).sum := by decide
  have hdescent : baseEnd_7334106 < baseStart_7334106 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334122 : List Nat := [3, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3]
def baseStart_7334122 : Nat := 118140960795 + 7334122 * 2 ^ 59
def prefixEnd_7334122 : Nat := 4983230072969 + 3 ^ 40 * 7334122 * 2
def baseEnd_7334122 : Nat := 3765929764714259447645993

theorem tailTrace_7334122 : CollatzResearch.WordTrace tailWord_7334122 prefixEnd_7334122 3765929764714259447645993 := by
  unfold tailWord_7334122
  simp only [CollatzResearch.WordTrace]
  refine ⟨66874351283934009290163155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178331603423824024773768413 66874351283934009290163155)
  ·
    refine ⟨100311526925901013935244733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66874351283934009290163155 100311526925901013935244733)
    ·
      refine ⟨37616822597212880225716775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100311526925901013935244733 37616822597212880225716775)
      ·
        refine ⟨56425233895819320338575163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37616822597212880225716775 56425233895819320338575163)
        ·
          refine ⟨84637850843728980507862745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 56425233895819320338575163 84637850843728980507862745)
          ·
            refine ⟨63478388132796735380897059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84637850843728980507862745 63478388132796735380897059)
            ·
              refine ⟨95217582199195103071345589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 63478388132796735380897059 95217582199195103071345589)
              ·
                refine ⟨8926648331174540912938649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 95217582199195103071345589 8926648331174540912938649)
                ·
                  refine ⟨6694986248380905684703987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8926648331174540912938649 6694986248380905684703987)
                  ·
                    refine ⟨10042479372571358527055981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6694986248380905684703987 10042479372571358527055981)
                    ·
                      refine ⟨3765929764714259447645993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10042479372571358527055981 3765929764714259447645993)
                      ·
                        rfl

theorem cell23_7334122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 5, 2, 1, 3].length) (baseStart_7334122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334122 prefixEnd_7334122 := by exact prefixLift 7334122
  have htrace : WordTrace (prefixWord ++ tailWord_7334122) baseStart_7334122 baseEnd_7334122 := by
    simpa [prefixWord, tailWord_7334122, baseEnd_7334122] using wordTrace_append hprefix tailTrace_7334122
  have hstable : (prefixWord ++ tailWord_7334122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334122).length < 2 ^ (prefixWord ++ tailWord_7334122).sum := by decide
  have hdescent : baseEnd_7334122 < baseStart_7334122 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334175 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 4]
def baseStart_7334175 : Nat := 118140960795 + 7334175 * 2 ^ 59
def prefixEnd_7334175 : Nat := 4983230072969 + 3 ^ 40 * 7334175 * 2
def baseEnd_7334175 : Nat := 3765956979188947740283249

theorem tailTrace_7334175 : CollatzResearch.WordTrace tailWord_7334175 prefixEnd_7334175 3765956979188947740283249 := by
  unfold tailWord_7334175
  simp only [CollatzResearch.WordTrace]
  refine ⟨267499338204544027212331979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178332892136362684808221319 267499338204544027212331979)
  ·
    refine ⟨401249007306816040818497969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267499338204544027212331979 401249007306816040818497969)
    ·
      refine ⟨300936755480112030613873477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 401249007306816040818497969 300936755480112030613873477)
      ·
        refine ⟨56425641652521005740101277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 300936755480112030613873477 56425641652521005740101277)
        ·
          refine ⟨21159615619695377152537979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 56425641652521005740101277 21159615619695377152537979)
          ·
            refine ⟨31739423429543065728806969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21159615619695377152537979 31739423429543065728806969)
            ·
              refine ⟨23804567572157299296605227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31739423429543065728806969 23804567572157299296605227)
              ·
                refine ⟨35706851358235948944907841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23804567572157299296605227 35706851358235948944907841)
                ·
                  refine ⟨26780138518676961708680881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 35706851358235948944907841 26780138518676961708680881)
                  ·
                    refine ⟨20085103889007721281510661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26780138518676961708680881 20085103889007721281510661)
                    ·
                      refine ⟨3765956979188947740283249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20085103889007721281510661 3765956979188947740283249)
                      ·
                        rfl

theorem cell23_7334175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_7334175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334175 prefixEnd_7334175 := by exact prefixLift 7334175
  have htrace : WordTrace (prefixWord ++ tailWord_7334175) baseStart_7334175 baseEnd_7334175 := by
    simpa [prefixWord, tailWord_7334175, baseEnd_7334175] using wordTrace_append hprefix tailTrace_7334175
  have hstable : (prefixWord ++ tailWord_7334175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334175).length < 2 ^ (prefixWord ++ tailWord_7334175).sum := by decide
  have hdescent : baseEnd_7334175 < baseStart_7334175 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334202 : List Nat := [3, 1, 1, 1, 4, 2, 3, 3, 5]
def baseStart_7334202 : Nat := 118140960795 + 7334202 * 2 ^ 59
def prefixEnd_7334202 : Nat := 4983230072969 + 3 ^ 40 * 7334202 * 2
def baseEnd_7334202 : Nat := 418441204796291014960625

theorem tailTrace_7334202 : CollatzResearch.WordTrace tailWord_7334202 prefixEnd_7334202 418441204796291014960625 := by
  unfold tailWord_7334202
  simp only [CollatzResearch.WordTrace]
  refine ⟨66875080743861552705891215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178333548650297473882376573 66875080743861552705891215)
  ·
    refine ⟨100312621115792329058836823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66875080743861552705891215 100312621115792329058836823)
    ·
      refine ⟨150468931673688493588255235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 100312621115792329058836823 150468931673688493588255235)
      ·
        refine ⟨225703397510532740382382853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150468931673688493588255235 225703397510532740382382853)
        ·
          refine ⟨42319387033224888821696785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225703397510532740382382853 42319387033224888821696785)
          ·
            refine ⟨31739540274918666616272589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 42319387033224888821696785 31739540274918666616272589)
            ·
              refine ⟨11902327603094499981102221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31739540274918666616272589 11902327603094499981102221)
              ·
                refine ⟨4463372851160437492913333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11902327603094499981102221 4463372851160437492913333)
                ·
                  refine ⟨418441204796291014960625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4463372851160437492913333 418441204796291014960625)
                  ·
                    rfl

theorem cell23_7334202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 3, 3, 5].length) (baseStart_7334202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334202 prefixEnd_7334202 := by exact prefixLift 7334202
  have htrace : WordTrace (prefixWord ++ tailWord_7334202) baseStart_7334202 baseEnd_7334202 := by
    simpa [prefixWord, tailWord_7334202, baseEnd_7334202] using wordTrace_append hprefix tailTrace_7334202
  have hstable : (prefixWord ++ tailWord_7334202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334202).length < 2 ^ (prefixWord ++ tailWord_7334202).sum := by decide
  have hdescent : baseEnd_7334202 < baseStart_7334202 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334215 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 2, 5]
def baseStart_7334215 : Nat := 118140960795 + 7334215 * 2 ^ 59
def prefixEnd_7334215 : Nat := 4983230072969 + 3 ^ 40 * 7334215 * 2
def baseEnd_7334215 : Nat := 1255325839471709194594355

theorem tailTrace_7334215 : CollatzResearch.WordTrace tailWord_7334215 prefixEnd_7334215 1255325839471709194594355 := by
  unfold tailWord_7334215
  simp only [CollatzResearch.WordTrace]
  refine ⟨267500797124399114043788099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178333864749599409362525399 267500797124399114043788099)
  ·
    refine ⟨401251195686598671065682149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267500797124399114043788099 401251195686598671065682149)
    ·
      refine ⟨75234599191237250824815403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401251195686598671065682149 75234599191237250824815403)
      ·
        refine ⟨112851898786855876237223105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75234599191237250824815403 112851898786855876237223105)
        ·
          refine ⟨84638924090141907177917329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 112851898786855876237223105 84638924090141907177917329)
          ·
            refine ⟨63479193067606430383437997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 84638924090141907177917329 63479193067606430383437997)
            ·
              refine ⟨23804697400352411393789249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63479193067606430383437997 23804697400352411393789249)
              ·
                refine ⟨17853523050264308545341937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23804697400352411393789249 17853523050264308545341937)
                ·
                  refine ⟨13390142287698231409006453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17853523050264308545341937 13390142287698231409006453)
                  ·
                    refine ⟨1255325839471709194594355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13390142287698231409006453 1255325839471709194594355)
                    ·
                      rfl

theorem cell23_7334215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_7334215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334215 prefixEnd_7334215 := by exact prefixLift 7334215
  have htrace : WordTrace (prefixWord ++ tailWord_7334215) baseStart_7334215 baseEnd_7334215 := by
    simpa [prefixWord, tailWord_7334215, baseEnd_7334215] using wordTrace_append hprefix tailTrace_7334215
  have hstable : (prefixWord ++ tailWord_7334215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334215).length < 2 ^ (prefixWord ++ tailWord_7334215).sum := by decide
  have hdescent : baseEnd_7334215 < baseStart_7334215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334218 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8]
def baseStart_7334218 : Nat := 118140960795 + 7334218 * 2 ^ 59
def prefixEnd_7334218 : Nat := 4983230072969 + 3 ^ 40 * 7334218 * 2
def baseEnd_7334218 : Nat := 3765979058857091072045551

theorem tailTrace_7334218 : CollatzResearch.WordTrace tailWord_7334218 prefixEnd_7334218 3765979058857091072045551 := by
  unfold tailWord_7334218
  simp only [CollatzResearch.WordTrace]
  refine ⟨66875226635847061389036827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178333937695592163704098205 66875226635847061389036827)
  ·
    refine ⟨100312839953770592083555241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 66875226635847061389036827 100312839953770592083555241)
    ·
      refine ⟨75234629965327944062666431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 100312839953770592083555241 75234629965327944062666431)
      ·
        refine ⟨112851944947991916093999647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75234629965327944062666431 112851944947991916093999647)
        ·
          refine ⟨169277917421987874140999471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112851944947991916093999647 169277917421987874140999471)
          ·
            refine ⟨253916876132981811211499207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169277917421987874140999471 253916876132981811211499207)
            ·
              refine ⟨380875314199472716817248811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 253916876132981811211499207 380875314199472716817248811)
              ·
                refine ⟨571312971299209075225873217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 380875314199472716817248811 571312971299209075225873217)
                ·
                  refine ⟨428484728474406806419404913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 571312971299209075225873217 428484728474406806419404913)
                  ·
                    refine ⟨321363546355805104814553685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 428484728474406806419404913 321363546355805104814553685)
                    ·
                      refine ⟨3765979058857091072045551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 321363546355805104814553685 3765979058857091072045551)
                      ·
                        rfl

theorem cell23_7334218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_7334218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334218 prefixEnd_7334218 := by exact prefixLift 7334218
  have htrace : WordTrace (prefixWord ++ tailWord_7334218) baseStart_7334218 baseEnd_7334218 := by
    simpa [prefixWord, tailWord_7334218, baseEnd_7334218] using wordTrace_append hprefix tailTrace_7334218
  have hstable : (prefixWord ++ tailWord_7334218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334218).length < 2 ^ (prefixWord ++ tailWord_7334218).sum := by decide
  have hdescent : baseEnd_7334218 < baseStart_7334218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334225 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 5]
def baseStart_7334225 : Nat := 118140960795 + 7334225 * 2 ^ 59
def prefixEnd_7334225 : Nat := 4983230072969 + 3 ^ 40 * 7334225 * 2
def baseEnd_7334225 : Nat := 3765982653221672544658019

theorem tailTrace_7334225 : CollatzResearch.WordTrace tailWord_7334225 prefixEnd_7334225 3765982653221672544658019 := by
  unfold tailWord_7334225
  simp only [CollatzResearch.WordTrace]
  refine ⟨267501161854362885751652129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178334107902908590501101419 267501161854362885751652129)
  ·
    refine ⟨200625871390772164313739097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267501161854362885751652129 200625871390772164313739097)
    ·
      refine ⟨150469403543079123235304323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 200625871390772164313739097 150469403543079123235304323)
      ·
        refine ⟨225704105314618684852956485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 150469403543079123235304323 225704105314618684852956485)
        ·
          refine ⟨42319519746491003409929341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 225704105314618684852956485 42319519746491003409929341)
          ·
            refine ⟨15869819904934126278723503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 42319519746491003409929341 15869819904934126278723503)
            ·
              refine ⟨23804729857401189418085255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15869819904934126278723503 23804729857401189418085255)
              ·
                refine ⟨35707094786101784127127883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23804729857401189418085255 35707094786101784127127883)
                ·
                  refine ⟨53560642179152676190691825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 35707094786101784127127883 53560642179152676190691825)
                  ·
                    refine ⟨40170481634364507143018869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 53560642179152676190691825 40170481634364507143018869)
                    ·
                      refine ⟨3765982653221672544658019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40170481634364507143018869 3765982653221672544658019)
                      ·
                        rfl

theorem cell23_7334225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 2, 5].length) (baseStart_7334225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334225 prefixEnd_7334225 := by exact prefixLift 7334225
  have htrace : WordTrace (prefixWord ++ tailWord_7334225) baseStart_7334225 baseEnd_7334225 := by
    simpa [prefixWord, tailWord_7334225, baseEnd_7334225] using wordTrace_append hprefix tailTrace_7334225
  have hstable : (prefixWord ++ tailWord_7334225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334225).length < 2 ^ (prefixWord ++ tailWord_7334225).sum := by decide
  have hdescent : baseEnd_7334225 < baseStart_7334225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334279 : List Nat := [1, 1, 4, 2, 2, 1, 3, 4, 1, 4]
def baseStart_7334279 : Nat := 118140960795 + 7334279 * 2 ^ 59
def prefixEnd_7334279 : Nat := 4983230072969 + 3 ^ 40 * 7334279 * 2
def baseEnd_7334279 : Nat := 1255336793725671777794257

theorem tailTrace_7334279 : CollatzResearch.WordTrace tailWord_7334279 prefixEnd_7334279 1255336793725671777794257 := by
  unfold tailWord_7334279
  simp only [CollatzResearch.WordTrace]
  refine ⟨267503131396167252974117891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178335420930778168649411927 267503131396167252974117891)
  ·
    refine ⟨401254697094250879461176837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267503131396167252974117891 401254697094250879461176837)
    ·
      refine ⟨75235255705172039898970657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 401254697094250879461176837 75235255705172039898970657)
      ·
        refine ⟨56426441778879029924227993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 75235255705172039898970657 56426441778879029924227993)
        ·
          refine ⟨42319831334159272443170995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56426441778879029924227993 42319831334159272443170995)
          ·
            refine ⟨63479747001238908664756493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 42319831334159272443170995 63479747001238908664756493)
            ·
              refine ⟨23804905125464590749283685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63479747001238908664756493 23804905125464590749283685)
              ·
                refine ⟨4463419711024610765490691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23804905125464590749283685 4463419711024610765490691)
                ·
                  refine ⟨6695129566536916148236037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4463419711024610765490691 6695129566536916148236037)
                  ·
                    refine ⟨1255336793725671777794257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6695129566536916148236037 1255336793725671777794257)
                    ·
                      rfl

theorem cell23_7334279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_7334279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334279 prefixEnd_7334279 := by exact prefixLift 7334279
  have htrace : WordTrace (prefixWord ++ tailWord_7334279) baseStart_7334279 baseEnd_7334279 := by
    simpa [prefixWord, tailWord_7334279, baseEnd_7334279] using wordTrace_append hprefix tailTrace_7334279
  have hstable : (prefixWord ++ tailWord_7334279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334279).length < 2 ^ (prefixWord ++ tailWord_7334279).sum := by decide
  have hdescent : baseEnd_7334279 < baseStart_7334279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334322 : List Nat := [3, 2, 1, 1, 1, 1, 5, 3, 1, 5]
def baseStart_7334322 : Nat := 118140960795 + 7334322 * 2 ^ 59
def prefixEnd_7334322 : Nat := 4983230072969 + 3 ^ 40 * 7334322 * 2
def baseEnd_7334322 : Nat := 1255344153615052888381691

theorem tailTrace_7334322 : CollatzResearch.WordTrace tailWord_7334322 prefixEnd_7334322 1255344153615052888381691 := by
  unfold tailWord_7334322
  simp only [CollatzResearch.WordTrace]
  refine ⟨66876174933752867829483305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 178336466490007647545288813 66876174933752867829483305)
  ·
    refine ⟨50157131200314650872112479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 66876174933752867829483305 50157131200314650872112479)
    ·
      refine ⟨75235696800471976308168719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 50157131200314650872112479 75235696800471976308168719)
      ·
        refine ⟨112853545200707964462253079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 75235696800471976308168719 112853545200707964462253079)
        ·
          refine ⟨169280317801061946693379619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 112853545200707964462253079 169280317801061946693379619)
          ·
            refine ⟨253920476701592920040069429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169280317801061946693379619 253920476701592920040069429)
            ·
              refine ⟨23805044690774336253756509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 253920476701592920040069429 23805044690774336253756509)
              ·
                refine ⟨8926891759040376095158691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23805044690774336253756509 8926891759040376095158691)
                ·
                  refine ⟨13390337638560564142738037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8926891759040376095158691 13390337638560564142738037)
                  ·
                    refine ⟨1255344153615052888381691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13390337638560564142738037 1255344153615052888381691)
                    ·
                      rfl

theorem cell23_7334322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_7334322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334322 prefixEnd_7334322 := by exact prefixLift 7334322
  have htrace : WordTrace (prefixWord ++ tailWord_7334322) baseStart_7334322 baseEnd_7334322 := by
    simpa [prefixWord, tailWord_7334322, baseEnd_7334322] using wordTrace_append hprefix tailTrace_7334322
  have hstable : (prefixWord ++ tailWord_7334322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334322).length < 2 ^ (prefixWord ++ tailWord_7334322).sum := by decide
  have hdescent : baseEnd_7334322 < baseStart_7334322 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334345 : List Nat := [1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 5]
def baseStart_7334345 : Nat := 118140960795 + 7334345 * 2 ^ 59
def prefixEnd_7334345 : Nat := 4983230072969 + 3 ^ 40 * 7334345 * 2
def baseEnd_7334345 : Nat := 3766044270900212075157467

theorem tailTrace_7334345 : CollatzResearch.WordTrace tailWord_7334345 prefixEnd_7334345 3766044270900212075157467 := by
  unfold tailWord_7334345
  simp only [CollatzResearch.WordTrace]
  refine ⟨267505538613928146246020489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178337025742618764164013659 267505538613928146246020489)
  ·
    refine ⟨200629153960446109684515367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267505538613928146246020489 200629153960446109684515367)
    ·
      refine ⟨300943730940669164526773051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200629153960446109684515367 300943730940669164526773051)
      ·
        refine ⟨451415596411003746790159577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 300943730940669164526773051 451415596411003746790159577)
        ·
          refine ⟨338561697308252810092619683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 451415596411003746790159577 338561697308252810092619683)
          ·
            refine ⟨507842545962379215138929525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338561697308252810092619683 507842545962379215138929525)
            ·
              refine ⟨47610238683973051419274643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 507842545962379215138929525 47610238683973051419274643)
              ·
                refine ⟨71415358025959577128911965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 47610238683973051419274643 71415358025959577128911965)
                ·
                  refine ⟨26780759259734841423341987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 71415358025959577128911965 26780759259734841423341987)
                  ·
                    refine ⟨40171138889602262135012981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26780759259734841423341987 40171138889602262135012981)
                    ·
                      refine ⟨3766044270900212075157467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 40171138889602262135012981 3766044270900212075157467)
                      ·
                        rfl

theorem cell23_7334345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 1, 3, 1, 5].length) (baseStart_7334345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334345 prefixEnd_7334345 := by exact prefixLift 7334345
  have htrace : WordTrace (prefixWord ++ tailWord_7334345) baseStart_7334345 baseEnd_7334345 := by
    simpa [prefixWord, tailWord_7334345, baseEnd_7334345] using wordTrace_append hprefix tailTrace_7334345
  have hstable : (prefixWord ++ tailWord_7334345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334345).length < 2 ^ (prefixWord ++ tailWord_7334345).sum := by decide
  have hdescent : baseEnd_7334345 < baseStart_7334345 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334382 : List Nat := [4, 1, 2, 1, 2, 4, 9]
def baseStart_7334382 : Nat := 118140960795 + 7334382 * 2 ^ 59
def prefixEnd_7334382 : Nat := 4983230072969 + 3 ^ 40 * 7334382 * 2
def baseEnd_7334382 : Nat := 46494608267708992967837

theorem tailTrace_7334382 : CollatzResearch.WordTrace tailWord_7334382 prefixEnd_7334382 46494608267708992967837 := by
  unfold tailWord_7334382
  simp only [CollatzResearch.WordTrace]
  refine ⟨33438361014349262695639675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178337925409862734376744933 33438361014349262695639675)
  ·
    refine ⟨50157541521523894043459513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 33438361014349262695639675 50157541521523894043459513)
    ·
      refine ⟨37618156141142920532594635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 50157541521523894043459513 37618156141142920532594635)
      ·
        refine ⟨56427234211714380798891953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 37618156141142920532594635 56427234211714380798891953)
        ·
          refine ⟨42320425658785785599168965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 56427234211714380798891953 42320425658785785599168965)
          ·
            refine ⟨7935079811022334799844181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 42320425658785785599168965 7935079811022334799844181)
            ·
              refine ⟨46494608267708992967837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7935079811022334799844181 46494608267708992967837)
              ·
                rfl

theorem cell23_7334382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 9].length) (baseStart_7334382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334382 prefixEnd_7334382 := by exact prefixLift 7334382
  have htrace : WordTrace (prefixWord ++ tailWord_7334382) baseStart_7334382 baseEnd_7334382 := by
    simpa [prefixWord, tailWord_7334382, baseEnd_7334382] using wordTrace_append hprefix tailTrace_7334382
  have hstable : (prefixWord ++ tailWord_7334382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334382).length < 2 ^ (prefixWord ++ tailWord_7334382).sum := by decide
  have hdescent : baseEnd_7334382 < baseStart_7334382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334413 : List Nat := [1, 7, 1, 1, 1, 2, 1, 1, 3, 2, 3]
def baseStart_7334413 : Nat := 118140960795 + 7334413 * 2 ^ 59
def prefixEnd_7334413 : Nat := 4983230072969 + 3 ^ 40 * 7334413 * 2
def baseEnd_7334413 : Nat := 3766079187584717809107155

theorem tailTrace_7334413 : CollatzResearch.WordTrace tailWord_7334413 prefixEnd_7334413 3766079187584717809107155 := by
  unfold tailWord_7334413
  simp only [CollatzResearch.WordTrace]
  refine ⟨267508018777681793859495893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178338679185121195906330595 267508018777681793859495893)
  ·
    refine ⟨6269719190101917043581935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 267508018777681793859495893 6269719190101917043581935)
    ·
      refine ⟨9404578785152875565372903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6269719190101917043581935 9404578785152875565372903)
      ·
        refine ⟨14106868177729313348059355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9404578785152875565372903 14106868177729313348059355)
        ·
          refine ⟨21160302266593970022089033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14106868177729313348059355 21160302266593970022089033)
          ·
            refine ⟨15870226699945477516566775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21160302266593970022089033 15870226699945477516566775)
            ·
              refine ⟨23805340049918216274850163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15870226699945477516566775 23805340049918216274850163)
              ·
                refine ⟨35708010074877324412275245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23805340049918216274850163 35708010074877324412275245)
                ·
                  refine ⟨13390503778078996654603217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35708010074877324412275245 13390503778078996654603217)
                  ·
                    refine ⟨10042877833559247490952413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13390503778078996654603217 10042877833559247490952413)
                    ·
                      refine ⟨3766079187584717809107155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10042877833559247490952413 3766079187584717809107155)
                      ·
                        rfl

theorem cell23_7334413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_7334413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334413 prefixEnd_7334413 := by exact prefixLift 7334413
  have htrace : WordTrace (prefixWord ++ tailWord_7334413) baseStart_7334413 baseEnd_7334413 := by
    simpa [prefixWord, tailWord_7334413, baseEnd_7334413] using wordTrace_append hprefix tailTrace_7334413
  have hstable : (prefixWord ++ tailWord_7334413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334413).length < 2 ^ (prefixWord ++ tailWord_7334413).sum := by decide
  have hdescent : baseEnd_7334413 < baseStart_7334413 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334419 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 3, 3, 2]
def baseStart_7334419 : Nat := 118140960795 + 7334419 * 2 ^ 59
def prefixEnd_7334419 : Nat := 4983230072969 + 3 ^ 40 * 7334419 * 2
def baseEnd_7334419 : Nat := 3766082268468644785632127

theorem tailTrace_7334419 : CollatzResearch.WordTrace tailWord_7334419 prefixEnd_7334419 3766082268468644785632127 := by
  unfold tailWord_7334419
  simp only [CollatzResearch.WordTrace]
  refine ⟨267508237615660056884214311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178338825077106704589476207 267508237615660056884214311)
  ·
    refine ⟨401262356423490085326321467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267508237615660056884214311 401262356423490085326321467)
    ·
      refine ⟨601893534635235127989482201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401262356423490085326321467 601893534635235127989482201)
      ·
        refine ⟨451420150976426345992111651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601893534635235127989482201 451420150976426345992111651)
        ·
          refine ⟨677130226464639518988167477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 451420150976426345992111651 677130226464639518988167477)
          ·
            refine ⟨63480958731059954905140701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 677130226464639518988167477 63480958731059954905140701)
            ·
              refine ⟨23805359524147483089427763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 63480958731059954905140701 23805359524147483089427763)
              ·
                refine ⟨35708039286221224634141645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23805359524147483089427763 35708039286221224634141645)
                ·
                  refine ⟨13390514732332959237803117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 35708039286221224634141645 13390514732332959237803117)
                  ·
                    refine ⟨5021443024624859714176169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13390514732332959237803117 5021443024624859714176169)
                    ·
                      refine ⟨3766082268468644785632127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021443024624859714176169 3766082268468644785632127)
                      ·
                        rfl

theorem cell23_7334419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 3, 2].length) (baseStart_7334419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334419 prefixEnd_7334419 := by exact prefixLift 7334419
  have htrace : WordTrace (prefixWord ++ tailWord_7334419) baseStart_7334419 baseEnd_7334419 := by
    simpa [prefixWord, tailWord_7334419, baseEnd_7334419] using wordTrace_append hprefix tailTrace_7334419
  have hstable : (prefixWord ++ tailWord_7334419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334419).length < 2 ^ (prefixWord ++ tailWord_7334419).sum := by decide
  have hdescent : baseEnd_7334419 < baseStart_7334419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334425 : List Nat := [1, 2, 1, 2, 1, 1, 2, 4, 1, 8]
def baseStart_7334425 : Nat := 118140960795 + 7334425 * 2 ^ 59
def prefixEnd_7334425 : Nat := 4983230072969 + 3 ^ 40 * 7334425 * 2
def baseEnd_7334425 : Nat := 1255361783117523920719033

theorem tailTrace_7334425 : CollatzResearch.WordTrace tailWord_7334425 prefixEnd_7334425 1255361783117523920719033 := by
  unfold tailWord_7334425
  simp only [CollatzResearch.WordTrace]
  refine ⟨267508456453638319908932729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178338970969092213272621819 267508456453638319908932729)
  ·
    refine ⟨200631342340228739931699547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 267508456453638319908932729 200631342340228739931699547)
    ·
      refine ⟨300947013510343109897549321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 200631342340228739931699547 300947013510343109897549321)
      ·
        refine ⟨225710260132757332423161991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 300947013510343109897549321 225710260132757332423161991)
        ·
          refine ⟨338565390199135998634742987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 225710260132757332423161991 338565390199135998634742987)
          ·
            refine ⟨507848085298703997952114481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 338565390199135998634742987 507848085298703997952114481)
            ·
              refine ⟨380886063974027998464085861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 507848085298703997952114481 380886063974027998464085861)
              ·
                refine ⟨71416136995130249712016099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 380886063974027998464085861 71416136995130249712016099)
                ·
                  refine ⟨107124205492695374568024149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 71416136995130249712016099 107124205492695374568024149)
                  ·
                    refine ⟨1255361783117523920719033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 107124205492695374568024149 1255361783117523920719033)
                    ·
                      rfl

theorem cell23_7334425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 4, 1, 8].length) (baseStart_7334425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334425 prefixEnd_7334425 := by exact prefixLift 7334425
  have htrace : WordTrace (prefixWord ++ tailWord_7334425) baseStart_7334425 baseEnd_7334425 := by
    simpa [prefixWord, tailWord_7334425, baseEnd_7334425] using wordTrace_append hprefix tailTrace_7334425
  have hstable : (prefixWord ++ tailWord_7334425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334425).length < 2 ^ (prefixWord ++ tailWord_7334425).sum := by decide
  have hdescent : baseEnd_7334425 < baseStart_7334425 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334494 : List Nat := [4, 4, 1, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_7334494 : Nat := 118140960795 + 7334494 * 2 ^ 59
def prefixEnd_7334494 : Nat := 4983230072969 + 3 ^ 40 * 7334494 * 2
def baseEnd_7334494 : Nat := 3766120779517731992194283

theorem tailTrace_7334494 : CollatzResearch.WordTrace tailWord_7334494 prefixEnd_7334494 3766120779517731992194283 := by
  unfold tailWord_7334494
  simp only [CollatzResearch.WordTrace]
  refine ⟨33438871636298543086649317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 178340648726925563128796357 33438871636298543086649317)
  ·
    refine ⟨6269788431805976828746747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 33438871636298543086649317 6269788431805976828746747)
    ·
      refine ⟨9404682647708965243120121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6269788431805976828746747 9404682647708965243120121)
      ·
        refine ⟨7053511985781723932340091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9404682647708965243120121 7053511985781723932340091)
        ·
          refine ⟨10580267978672585898510137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7053511985781723932340091 10580267978672585898510137)
          ·
            refine ⟨7935200984004439423882603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10580267978672585898510137 7935200984004439423882603)
            ·
              refine ⟨11902801476006659135823905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7935200984004439423882603 11902801476006659135823905)
              ·
                refine ⟨8927101107004994351867929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11902801476006659135823905 8927101107004994351867929)
                ·
                  refine ⟨6695325830253745763900947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8927101107004994351867929 6695325830253745763900947)
                  ·
                    refine ⟨10042988745380618645851421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6695325830253745763900947 10042988745380618645851421)
                    ·
                      refine ⟨3766120779517731992194283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10042988745380618645851421 3766120779517731992194283)
                      ·
                        rfl

theorem cell23_7334494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_7334494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334494 prefixEnd_7334494 := by exact prefixLift 7334494
  have htrace : WordTrace (prefixWord ++ tailWord_7334494) baseStart_7334494 baseEnd_7334494 := by
    simpa [prefixWord, tailWord_7334494, baseEnd_7334494] using wordTrace_append hprefix tailTrace_7334494
  have hstable : (prefixWord ++ tailWord_7334494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334494).length < 2 ^ (prefixWord ++ tailWord_7334494).sum := by decide
  have hdescent : baseEnd_7334494 < baseStart_7334494 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334517 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 2, 2, 2]
def baseStart_7334517 : Nat := 118140960795 + 7334517 * 2 ^ 59
def prefixEnd_7334517 : Nat := 4983230072969 + 3 ^ 40 * 7334517 * 2
def baseEnd_7334517 : Nat := 3766132589572785402206677

theorem tailTrace_7334517 : CollatzResearch.WordTrace tailWord_7334517 prefixEnd_7334517 3766132589572785402206677 := by
  unfold tailWord_7334517
  simp only [CollatzResearch.WordTrace]
  refine ⟨267511811969305019621281805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178341207979536679747521203 267511811969305019621281805)
  ·
    refine ⟨100316929488489382357980677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 267511811969305019621281805 100316929488489382357980677)
    ·
      refine ⟨18809424279091759192121377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 100316929488489382357980677 18809424279091759192121377)
      ·
        refine ⟨14107068209318819394091033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18809424279091759192121377 14107068209318819394091033)
        ·
          refine ⟨10580301156989114545568275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14107068209318819394091033 10580301156989114545568275)
          ·
            refine ⟨15870451735483671818352413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10580301156989114545568275 15870451735483671818352413)
            ·
              refine ⟨5951419400806376931882155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15870451735483671818352413 5951419400806376931882155)
              ·
                refine ⟨8927129101209565397823233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5951419400806376931882155 8927129101209565397823233)
                ·
                  refine ⟨6695346825907174048367425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8927129101209565397823233 6695346825907174048367425)
                  ·
                    refine ⟨5021510119430380536275569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6695346825907174048367425 5021510119430380536275569)
                    ·
                      refine ⟨3766132589572785402206677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021510119430380536275569 3766132589572785402206677)
                      ·
                        rfl

theorem cell23_7334517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_7334517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334517 prefixEnd_7334517 := by exact prefixLift 7334517
  have htrace : WordTrace (prefixWord ++ tailWord_7334517) baseStart_7334517 baseEnd_7334517 := by
    simpa [prefixWord, tailWord_7334517, baseEnd_7334517] using wordTrace_append hprefix tailTrace_7334517
  have hstable : (prefixWord ++ tailWord_7334517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334517).length < 2 ^ (prefixWord ++ tailWord_7334517).sum := by decide
  have hdescent : baseEnd_7334517 < baseStart_7334517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334539 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 4, 4, 2]
def baseStart_7334539 : Nat := 118140960795 + 7334539 * 2 ^ 59
def prefixEnd_7334539 : Nat := 4983230072969 + 3 ^ 40 * 7334539 * 2
def baseEnd_7334539 : Nat := 3766143886147184316131575

theorem tailTrace_7334539 : CollatzResearch.WordTrace tailWord_7334539 prefixEnd_7334539 3766143886147184316131575 := by
  unfold tailWord_7334539
  simp only [CollatzResearch.WordTrace]
  refine ⟨267512614375225317378582671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178341742916816878252388447 267512614375225317378582671)
  ·
    refine ⟨401268921562837976067874007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267512614375225317378582671 401268921562837976067874007)
    ·
      refine ⟨601903382344256964101811011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401268921562837976067874007 601903382344256964101811011)
      ·
        refine ⟨902855073516385446152716517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 601903382344256964101811011 902855073516385446152716517)
        ·
          refine ⟨169285326284322271153634347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 902855073516385446152716517 169285326284322271153634347)
          ·
            refine ⟨253927989426483406730451521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 169285326284322271153634347 253927989426483406730451521)
            ·
              refine ⟨190445992069862555047838641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 253927989426483406730451521 190445992069862555047838641)
              ·
                refine ⟨142834494052396916285878981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 190445992069862555047838641 142834494052396916285878981)
                ·
                  refine ⟨26781467634824421803602309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 142834494052396916285878981 26781467634824421803602309)
                  ·
                    refine ⟨5021525181529579088175433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26781467634824421803602309 5021525181529579088175433)
                    ·
                      refine ⟨3766143886147184316131575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5021525181529579088175433 3766143886147184316131575)
                      ·
                        rfl

theorem cell23_7334539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 4, 2].length) (baseStart_7334539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334539 prefixEnd_7334539 := by exact prefixLift 7334539
  have htrace : WordTrace (prefixWord ++ tailWord_7334539) baseStart_7334539 baseEnd_7334539 := by
    simpa [prefixWord, tailWord_7334539, baseEnd_7334539] using wordTrace_append hprefix tailTrace_7334539
  have hstable : (prefixWord ++ tailWord_7334539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334539).length < 2 ^ (prefixWord ++ tailWord_7334539).sum := by decide
  have hdescent : baseEnd_7334539 < baseStart_7334539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334556 : List Nat := [2, 2, 3, 2, 2, 2, 1, 2, 2, 1, 4]
def baseStart_7334556 : Nat := 118140960795 + 7334556 * 2 ^ 59
def prefixEnd_7334556 : Nat := 4983230072969 + 3 ^ 40 * 7334556 * 2
def baseEnd_7334556 : Nat := 3766152615318310749618997

theorem tailTrace_7334556 : CollatzResearch.WordTrace tailWord_7334556 prefixEnd_7334556 3766152615318310749618997 := by
  unfold tailWord_7334556
  simp only [CollatzResearch.WordTrace]
  refine ⟨133756617208081864640975761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 178342156277442486187967681 133756617208081864640975761)
  ·
    refine ⟨100317462906061398480731821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 133756617208081864640975761 100317462906061398480731821)
    ·
      refine ⟨37619048589773024430274433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 100317462906061398480731821 37619048589773024430274433)
      ·
        refine ⟨28214286442329768322705825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 37619048589773024430274433 28214286442329768322705825)
        ·
          refine ⟨21160714831747326242029369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28214286442329768322705825 21160714831747326242029369)
          ·
            refine ⟨15870536123810494681522027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21160714831747326242029369 15870536123810494681522027)
            ·
              refine ⟨23805804185715742022283041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15870536123810494681522027 23805804185715742022283041)
              ·
                refine ⟨17854353139286806516712281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23805804185715742022283041 17854353139286806516712281)
                ·
                  refine ⟨13390764854465104887534211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17854353139286806516712281 13390764854465104887534211)
                  ·
                    refine ⟨20086147281697657331301317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13390764854465104887534211 20086147281697657331301317)
                    ·
                      refine ⟨3766152615318310749618997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 20086147281697657331301317 3766152615318310749618997)
                      ·
                        rfl

theorem cell23_7334556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_7334556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334556 prefixEnd_7334556 := by exact prefixLift 7334556
  have htrace : WordTrace (prefixWord ++ tailWord_7334556) baseStart_7334556 baseEnd_7334556 := by
    simpa [prefixWord, tailWord_7334556, baseEnd_7334556] using wordTrace_append hprefix tailTrace_7334556
  have hstable : (prefixWord ++ tailWord_7334556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334556).length < 2 ^ (prefixWord ++ tailWord_7334556).sum := by decide
  have hdescent : baseEnd_7334556 < baseStart_7334556 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7334579 : List Nat := [1, 1, 1, 2, 3, 5, 1, 3, 6]
def baseStart_7334579 : Nat := 118140960795 + 7334579 * 2 ^ 59
def prefixEnd_7334579 : Nat := 4983230072969 + 3 ^ 40 * 7334579 * 2
def baseEnd_7334579 : Nat := 418462713930373795514599

theorem tailTrace_7334579 : CollatzResearch.WordTrace tailWord_7334579 prefixEnd_7334579 418462713930373795514599 := by
  unfold tailWord_7334579
  simp only [CollatzResearch.WordTrace]
  refine ⟨267514073295080404210038791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 178342715530053602806692527 267514073295080404210038791)
  ·
    refine ⟨401271109942620606315058187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 267514073295080404210038791 401271109942620606315058187)
    ·
      refine ⟨601906664913930909472587281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 401271109942620606315058187 601906664913930909472587281)
      ·
        refine ⟨451429998685448182104440461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 601906664913930909472587281 451429998685448182104440461)
        ·
          refine ⟨169286249507043068289165173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 451429998685448182104440461 169286249507043068289165173)
          ·
            refine ⟨15870585891285287652109235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 169286249507043068289165173 15870585891285287652109235)
            ·
              refine ⟨23805878836927931478163853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15870585891285287652109235 23805878836927931478163853)
              ·
                refine ⟨8927204563847974304311445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23805878836927931478163853 8927204563847974304311445)
                ·
                  refine ⟨418462713930373795514599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8927204563847974304311445 418462713930373795514599)
                  ·
                    rfl

theorem cell23_7334579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 6].length) (baseStart_7334579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7334579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7334579 prefixEnd_7334579 := by exact prefixLift 7334579
  have htrace : WordTrace (prefixWord ++ tailWord_7334579) baseStart_7334579 baseEnd_7334579 := by
    simpa [prefixWord, tailWord_7334579, baseEnd_7334579] using wordTrace_append hprefix tailTrace_7334579
  have hstable : (prefixWord ++ tailWord_7334579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7334579).length < 2 ^ (prefixWord ++ tailWord_7334579).sum := by decide
  have hdescent : baseEnd_7334579 < baseStart_7334579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7334579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
