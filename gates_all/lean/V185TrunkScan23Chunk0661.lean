import V185TrunkScan23Chunk0660

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3907790 : List Nat := [4, 1, 1, 1, 4, 3, 1, 1, 1, 6]
def baseStart_3907790 : Nat := 118140960795 + 3907790 * 2 ^ 59
def prefixEnd_3907790 : Nat := 4983230072969 + 3 ^ 40 * 3907790 * 2
def baseEnd_3907790 : Nat := 668858188944456995784469

theorem tailTrace_3907790 : CollatzResearch.WordTrace tailWord_3907790 prefixEnd_3907790 668858188944456995784469 := by
  unfold tailWord_3907790
  simp only [CollatzResearch.WordTrace]
  refine ⟨17816101314093962780361103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95019207008501134828592549 17816101314093962780361103)
  ·
    refine ⟨26724151971140944170541655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17816101314093962780361103 26724151971140944170541655)
    ·
      refine ⟨40086227956711416255812483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26724151971140944170541655 40086227956711416255812483)
      ·
        refine ⟨60129341935067124383718725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40086227956711416255812483 60129341935067124383718725)
        ·
          refine ⟨11274251612825085821947261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60129341935067124383718725 11274251612825085821947261)
          ·
            refine ⟨4227844354809407183230223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11274251612825085821947261 4227844354809407183230223)
            ·
              refine ⟨6341766532214110774845335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4227844354809407183230223 6341766532214110774845335)
              ·
                refine ⟨9512649798321166162268003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341766532214110774845335 9512649798321166162268003)
                ·
                  refine ⟨14268974697481749243402005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9512649798321166162268003 14268974697481749243402005)
                  ·
                    refine ⟨668858188944456995784469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14268974697481749243402005 668858188944456995784469)
                    ·
                      rfl

theorem cell23_3907790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 3, 1, 1, 1, 6].length) (baseStart_3907790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907790 prefixEnd_3907790 := by exact prefixLift 3907790
  have htrace : WordTrace (prefixWord ++ tailWord_3907790) baseStart_3907790 baseEnd_3907790 := by
    simpa [prefixWord, tailWord_3907790, baseEnd_3907790] using wordTrace_append hprefix tailTrace_3907790
  have hstable : (prefixWord ++ tailWord_3907790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907790).length < 2 ^ (prefixWord ++ tailWord_3907790).sum := by decide
  have hdescent : baseEnd_3907790 < baseStart_3907790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907793 : List Nat := [1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_3907793 : Nat := 118140960795 + 3907793 * 2 ^ 59
def prefixEnd_3907793 : Nat := 4983230072969 + 3 ^ 40 * 3907793 * 2
def baseEnd_3907793 : Nat := 2006576107275334475615893

theorem tailTrace_3907793 : CollatzResearch.WordTrace tailWord_3907793 prefixEnd_3907793 2006576107275334475615893 := by
  unfold tailWord_3907793
  simp only [CollatzResearch.WordTrace]
  refine ⟨142528919931740833755248033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95019279954493889170165355 142528919931740833755248033)
  ·
    refine ⟨106896689948805625316436025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142528919931740833755248033 106896689948805625316436025)
    ·
      refine ⟨80172517461604218987327019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106896689948805625316436025 80172517461604218987327019)
      ·
        refine ⟨120258776192406328480990529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80172517461604218987327019 120258776192406328480990529)
        ·
          refine ⟨90194082144304746360742897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120258776192406328480990529 90194082144304746360742897)
          ·
            refine ⟨67645561608228559770557173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90194082144304746360742897 67645561608228559770557173)
            ·
              refine ⟨6341771400771427478489735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67645561608228559770557173 6341771400771427478489735)
              ·
                refine ⟨9512657101157141217734603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6341771400771427478489735 9512657101157141217734603)
                ·
                  refine ⟨14268985651735711826601905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9512657101157141217734603 14268985651735711826601905)
                  ·
                    refine ⟨10701739238801783869951429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14268985651735711826601905 10701739238801783869951429)
                    ·
                      refine ⟨2006576107275334475615893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10701739238801783869951429 2006576107275334475615893)
                      ·
                        rfl

theorem cell23_3907793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_3907793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907793 prefixEnd_3907793 := by exact prefixLift 3907793
  have htrace : WordTrace (prefixWord ++ tailWord_3907793) baseStart_3907793 baseEnd_3907793 := by
    simpa [prefixWord, tailWord_3907793, baseEnd_3907793] using wordTrace_append hprefix tailTrace_3907793
  have hstable : (prefixWord ++ tailWord_3907793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907793).length < 2 ^ (prefixWord ++ tailWord_3907793).sum := by decide
  have hdescent : baseEnd_3907793 < baseStart_3907793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907797 : List Nat := [1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_3907797 : Nat := 118140960795 + 3907797 * 2 ^ 59
def prefixEnd_3907797 : Nat := 4983230072969 + 3 ^ 40 * 3907797 * 2
def baseEnd_3907797 : Nat := 2006578161197952459965875

theorem tailTrace_3907797 : CollatzResearch.WordTrace tailWord_3907797 prefixEnd_3907797 2006578161197952459965875 := by
  unfold tailWord_3907797
  simp only [CollatzResearch.WordTrace]
  refine ⟨142529065823726342438393645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95019377215817561625595763 142529065823726342438393645)
  ·
    refine ⟨53448399683897378414397617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142529065823726342438393645 53448399683897378414397617)
    ·
      refine ⟨40086299762923033810798213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53448399683897378414397617 40086299762923033810798213)
      ·
        refine ⟨7516181205548068839524665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40086299762923033810798213 7516181205548068839524665)
        ·
          refine ⟨5637135904161051629643499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7516181205548068839524665 5637135904161051629643499)
          ·
            refine ⟨8455703856241577444465249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637135904161051629643499 8455703856241577444465249)
            ·
              refine ⟨6341777892181183083348937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8455703856241577444465249 6341777892181183083348937)
              ·
                refine ⟨4756333419135887312511703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6341777892181183083348937 4756333419135887312511703)
                ·
                  refine ⟨7134500128703830968767555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756333419135887312511703 7134500128703830968767555)
                  ·
                    refine ⟨10701750193055746453151333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7134500128703830968767555 10701750193055746453151333)
                    ·
                      refine ⟨2006578161197952459965875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10701750193055746453151333 2006578161197952459965875)
                      ·
                        rfl

theorem cell23_3907797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_3907797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907797 prefixEnd_3907797 := by exact prefixLift 3907797
  have htrace : WordTrace (prefixWord ++ tailWord_3907797) baseStart_3907797 baseEnd_3907797 := by
    simpa [prefixWord, tailWord_3907797, baseEnd_3907797] using wordTrace_append hprefix tailTrace_3907797
  have hstable : (prefixWord ++ tailWord_3907797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907797).length < 2 ^ (prefixWord ++ tailWord_3907797).sum := by decide
  have hdescent : baseEnd_3907797 < baseStart_3907797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907800 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 1, 2, 3]
def baseStart_3907800 : Nat := 118140960795 + 3907800 * 2 ^ 59
def prefixEnd_3907800 : Nat := 4983230072969 + 3 ^ 40 * 3907800 * 2
def baseEnd_3907800 : Nat := 2006579701639915948228361

theorem tailTrace_3907800 : CollatzResearch.WordTrace tailWord_3907800 prefixEnd_3907800 2006579701639915948228361 := by
  unfold tailWord_3907800
  simp only [CollatzResearch.WordTrace]
  refine ⟨71264587621357736975376427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95019450161810315967168569 71264587621357736975376427)
  ·
    refine ⟨106896881432036605463064641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71264587621357736975376427 106896881432036605463064641)
    ·
      refine ⟨80172661074027454097298481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106896881432036605463064641 80172661074027454097298481)
      ·
        refine ⟨60129495805520590572973861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80172661074027454097298481 60129495805520590572973861)
        ·
          refine ⟨11274280463535110732432599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60129495805520590572973861 11274280463535110732432599)
          ·
            refine ⟨16911420695302666098648899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11274280463535110732432599 16911420695302666098648899)
            ·
              refine ⟨25367131042953999147973349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16911420695302666098648899 25367131042953999147973349)
              ·
                refine ⟨4756337070553874840245003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25367131042953999147973349 4756337070553874840245003)
                ·
                  refine ⟨7134505605830812260367505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756337070553874840245003 7134505605830812260367505)
                  ·
                    refine ⟨5350879204373109195275629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7134505605830812260367505 5350879204373109195275629)
                    ·
                      refine ⟨2006579701639915948228361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5350879204373109195275629 2006579701639915948228361)
                      ·
                        rfl

theorem cell23_3907800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_3907800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907800 prefixEnd_3907800 := by exact prefixLift 3907800
  have htrace : WordTrace (prefixWord ++ tailWord_3907800) baseStart_3907800 baseEnd_3907800 := by
    simpa [prefixWord, tailWord_3907800, baseEnd_3907800] using wordTrace_append hprefix tailTrace_3907800
  have hstable : (prefixWord ++ tailWord_3907800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907800).length < 2 ^ (prefixWord ++ tailWord_3907800).sum := by decide
  have hdescent : baseEnd_3907800 < baseStart_3907800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907856 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_3907856 : Nat := 118140960795 + 3907856 * 2 ^ 59
def prefixEnd_3907856 : Nat := 4983230072969 + 3 ^ 40 * 3907856 * 2
def baseEnd_3907856 : Nat := 2006608456556567729128103

theorem tailTrace_3907856 : CollatzResearch.WordTrace tailWord_3907856 prefixEnd_3907856 2006608456556567729128103 := by
  unfold tailWord_3907856
  simp only [CollatzResearch.WordTrace]
  refine ⟨71265608865256297757395711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95020811820341730343194281 71265608865256297757395711)
  ·
    refine ⟨106898413297884446636093567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71265608865256297757395711 106898413297884446636093567)
    ·
      refine ⟨160347619946826669954140351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106898413297884446636093567 160347619946826669954140351)
      ·
        refine ⟨240521429920240004931210527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160347619946826669954140351 240521429920240004931210527)
        ·
          refine ⟨360782144880360007396815791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240521429920240004931210527 360782144880360007396815791)
          ·
            refine ⟨541173217320540011095223687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360782144880360007396815791 541173217320540011095223687)
            ·
              refine ⟨811759825980810016642835531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541173217320540011095223687 811759825980810016642835531)
              ·
                refine ⟨1217639738971215024964253297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 811759825980810016642835531 1217639738971215024964253297)
                ·
                  refine ⟨913229804228411268723189973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1217639738971215024964253297 913229804228411268723189973)
                  ·
                    refine ⟨21403823536603389110699765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 913229804228411268723189973 21403823536603389110699765)
                    ·
                      refine ⟨2006608456556567729128103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21403823536603389110699765 2006608456556567729128103)
                      ·
                        rfl

theorem cell23_3907856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_3907856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907856 prefixEnd_3907856 := by exact prefixLift 3907856
  have htrace : WordTrace (prefixWord ++ tailWord_3907856) baseStart_3907856 baseEnd_3907856 := by
    simpa [prefixWord, tailWord_3907856, baseEnd_3907856] using wordTrace_append hprefix tailTrace_3907856
  have hstable : (prefixWord ++ tailWord_3907856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907856).length < 2 ^ (prefixWord ++ tailWord_3907856).sum := by decide
  have hdescent : baseEnd_3907856 < baseStart_3907856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907857 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 1, 3, 2]
def baseStart_3907857 : Nat := 118140960795 + 3907857 * 2 ^ 59
def prefixEnd_3907857 : Nat := 4983230072969 + 3 ^ 40 * 3907857 * 2
def baseEnd_3907857 : Nat := 2006608970037222225215599

theorem tailTrace_3907857 : CollatzResearch.WordTrace tailWord_3907857 prefixEnd_3907857 2006608970037222225215599 := by
  unfold tailWord_3907857
  simp only [CollatzResearch.WordTrace]
  refine ⟨142531254203508972685577825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95020836135672648457051883 142531254203508972685577825)
  ·
    refine ⟨106898440652631729514183369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142531254203508972685577825 106898440652631729514183369)
    ·
      refine ⟨80173830489473797135637527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106898440652631729514183369 80173830489473797135637527)
      ·
        refine ⟨120260745734210695703456291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80173830489473797135637527 120260745734210695703456291)
        ·
          refine ⟨180391118601316043555184437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120260745734210695703456291 180391118601316043555184437)
          ·
            refine ⟨16911667368873379083298541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180391118601316043555184437 16911667368873379083298541)
            ·
              refine ⟨6341875263327517156236953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16911667368873379083298541 6341875263327517156236953)
              ·
                refine ⟨4756406447495637867177715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6341875263327517156236953 4756406447495637867177715)
                ·
                  refine ⟨7134609671243456800766573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756406447495637867177715 7134609671243456800766573)
                  ·
                    refine ⟨2675478626716296300287465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7134609671243456800766573 2675478626716296300287465)
                    ·
                      refine ⟨2006608970037222225215599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675478626716296300287465 2006608970037222225215599)
                      ·
                        rfl

theorem cell23_3907857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 3, 2].length) (baseStart_3907857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907857 prefixEnd_3907857 := by exact prefixLift 3907857
  have htrace : WordTrace (prefixWord ++ tailWord_3907857) baseStart_3907857 baseEnd_3907857 := by
    simpa [prefixWord, tailWord_3907857, baseEnd_3907857] using wordTrace_append hprefix tailTrace_3907857
  have hstable : (prefixWord ++ tailWord_3907857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907857).length < 2 ^ (prefixWord ++ tailWord_3907857).sum := by decide
  have hdescent : baseEnd_3907857 < baseStart_3907857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907873 : List Nat := [1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_3907873 : Nat := 118140960795 + 3907873 * 2 ^ 59
def prefixEnd_3907873 : Nat := 4983230072969 + 3 ^ 40 * 3907873 * 2
def baseEnd_3907873 : Nat := 2006617185727694162615525

theorem tailTrace_3907873 : CollatzResearch.WordTrace tailWord_3907873 prefixEnd_3907873 2006617185727694162615525 := by
  unfold tailWord_3907873
  simp only [CollatzResearch.WordTrace]
  refine ⟨142531837771451007418160273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95021225180967338278773515 142531837771451007418160273)
  ·
    refine ⟨106898878328588255563620205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142531837771451007418160273 106898878328588255563620205)
    ·
      refine ⟨40087079373220595836357577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106898878328588255563620205 40087079373220595836357577)
      ·
        refine ⟨30065309529915446877268183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40087079373220595836357577 30065309529915446877268183)
        ·
          refine ⟨45097964294873170315902275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30065309529915446877268183 45097964294873170315902275)
          ·
            refine ⟨67646946442309755473853413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45097964294873170315902275 67646946442309755473853413)
            ·
              refine ⟨12683802457933079151347515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67646946442309755473853413 12683802457933079151347515)
              ·
                refine ⟨19025703686899618727021273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12683802457933079151347515 19025703686899618727021273)
                ·
                  refine ⟨14269277765174714045265955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19025703686899618727021273 14269277765174714045265955)
                  ·
                    refine ⟨21403916647762071067898933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14269277765174714045265955 21403916647762071067898933)
                    ·
                      refine ⟨2006617185727694162615525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21403916647762071067898933 2006617185727694162615525)
                      ·
                        rfl

theorem cell23_3907873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_3907873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907873 prefixEnd_3907873 := by exact prefixLift 3907873
  have htrace : WordTrace (prefixWord ++ tailWord_3907873) baseStart_3907873 baseEnd_3907873 := by
    simpa [prefixWord, tailWord_3907873, baseEnd_3907873] using wordTrace_append hprefix tailTrace_3907873
  have hstable : (prefixWord ++ tailWord_3907873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907873).length < 2 ^ (prefixWord ++ tailWord_3907873).sum := by decide
  have hdescent : baseEnd_3907873 < baseStart_3907873 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907887 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 2, 2, 2]
def baseStart_3907887 : Nat := 118140960795 + 3907887 * 2 ^ 59
def prefixEnd_3907887 : Nat := 4983230072969 + 3 ^ 40 * 3907887 * 2
def baseEnd_3907887 : Nat := 2006624374456857107840461

theorem tailTrace_3907887 : CollatzResearch.WordTrace tailWord_3907887 prefixEnd_3907887 2006624374456857107840461 := by
  unfold tailWord_3907887
  simp only [CollatzResearch.WordTrace]
  refine ⟨142532348393400287809169915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95021565595600191872779943 142532348393400287809169915)
  ·
    refine ⟨213798522590100431713754873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142532348393400287809169915 213798522590100431713754873)
    ·
      refine ⟨160348891942575323785316155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213798522590100431713754873 160348891942575323785316155)
      ·
        refine ⟨240523337913862985677974233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160348891942575323785316155 240523337913862985677974233)
        ·
          refine ⟨180392503435397239258480675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240523337913862985677974233 180392503435397239258480675)
          ·
            refine ⟨270588755153095858887721013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180392503435397239258480675 270588755153095858887721013)
            ·
              refine ⟨25367695795602736770723845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 270588755153095858887721013 25367695795602736770723845)
              ·
                refine ⟨4756442961675513144510721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25367695795602736770723845 4756442961675513144510721)
                ·
                  refine ⟨3567332221256634858383041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4756442961675513144510721 3567332221256634858383041)
                  ·
                    refine ⟨2675499165942476143787281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3567332221256634858383041 2675499165942476143787281)
                    ·
                      refine ⟨2006624374456857107840461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675499165942476143787281 2006624374456857107840461)
                      ·
                        rfl

theorem cell23_3907887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 2, 2].length) (baseStart_3907887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907887 prefixEnd_3907887 := by exact prefixLift 3907887
  have htrace : WordTrace (prefixWord ++ tailWord_3907887) baseStart_3907887 baseEnd_3907887 := by
    simpa [prefixWord, tailWord_3907887, baseEnd_3907887] using wordTrace_append hprefix tailTrace_3907887
  have hstable : (prefixWord ++ tailWord_3907887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907887).length < 2 ^ (prefixWord ++ tailWord_3907887).sum := by decide
  have hdescent : baseEnd_3907887 < baseStart_3907887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907893 : List Nat := [1, 3, 3, 1, 2, 1, 2, 3, 7]
def baseStart_3907893 : Nat := 118140960795 + 3907893 * 2 ^ 59
def prefixEnd_3907893 : Nat := 4983230072969 + 3 ^ 40 * 3907893 * 2
def baseEnd_3907893 : Nat := 222958606148976009373937

theorem tailTrace_3907893 : CollatzResearch.WordTrace tailWord_3907893 prefixEnd_3907893 222958606148976009373937 := by
  unfold tailWord_3907893
  simp only [CollatzResearch.WordTrace]
  refine ⟨142532567231378550833888333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95021711487585700555925555 142532567231378550833888333)
  ·
    refine ⟨53449712711766956562708125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142532567231378550833888333 53449712711766956562708125)
    ·
      refine ⟨20043642266912608711015547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53449712711766956562708125 20043642266912608711015547)
      ·
        refine ⟨30065463400368913066523321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20043642266912608711015547 30065463400368913066523321)
        ·
          refine ⟨22549097550276684799892491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30065463400368913066523321 22549097550276684799892491)
          ·
            refine ⟨33823646325415027199838737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22549097550276684799892491 33823646325415027199838737)
            ·
              refine ⟨25367734744061270399879053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33823646325415027199838737 25367734744061270399879053)
              ·
                refine ⟨9512900529022976399954645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25367734744061270399879053 9512900529022976399954645)
                ·
                  refine ⟨222958606148976009373937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9512900529022976399954645 222958606148976009373937)
                  ·
                    rfl

theorem cell23_3907893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_3907893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907893 prefixEnd_3907893 := by exact prefixLift 3907893
  have htrace : WordTrace (prefixWord ++ tailWord_3907893) baseStart_3907893 baseEnd_3907893 := by
    simpa [prefixWord, tailWord_3907893, baseEnd_3907893] using wordTrace_append hprefix tailTrace_3907893
  have hstable : (prefixWord ++ tailWord_3907893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907893).length < 2 ^ (prefixWord ++ tailWord_3907893).sum := by decide
  have hdescent : baseEnd_3907893 < baseStart_3907893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907923 : List Nat := [1, 1, 1, 2, 1, 1, 4, 5, 2, 5]
def baseStart_3907923 : Nat := 118140960795 + 3907923 * 2 ^ 59
def prefixEnd_3907923 : Nat := 4983230072969 + 3 ^ 40 * 3907923 * 2
def baseEnd_3907923 : Nat := 668880953253472988996765

theorem tailTrace_3907923 : CollatzResearch.WordTrace tailWord_3907923 prefixEnd_3907923 668880953253472988996765 := by
  unfold tailWord_3907923
  simp only [CollatzResearch.WordTrace]
  refine ⟨142533661421269865957480423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95022440947513243971653615 142533661421269865957480423)
  ·
    refine ⟨213800492131904798936220635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142533661421269865957480423 213800492131904798936220635)
    ·
      refine ⟨320700738197857198404330953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213800492131904798936220635 320700738197857198404330953)
      ·
        refine ⟨240525553648392898803248215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320700738197857198404330953 240525553648392898803248215)
        ·
          refine ⟨360788330472589348204872323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240525553648392898803248215 360788330472589348204872323)
          ·
            refine ⟨541182495708884022307308485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360788330472589348204872323 541182495708884022307308485)
            ·
              refine ⟨101471717945415754182620341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 541182495708884022307308485 101471717945415754182620341)
              ·
                refine ⟨9512973557382726954620657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101471717945415754182620341 9512973557382726954620657)
                ·
                  refine ⟨7134730168037045215965493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9512973557382726954620657 7134730168037045215965493)
                  ·
                    refine ⟨668880953253472988996765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7134730168037045215965493 668880953253472988996765)
                    ·
                      rfl

theorem cell23_3907923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 5].length) (baseStart_3907923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907923 prefixEnd_3907923 := by exact prefixLift 3907923
  have htrace : WordTrace (prefixWord ++ tailWord_3907923) baseStart_3907923 baseEnd_3907923 := by
    simpa [prefixWord, tailWord_3907923, baseEnd_3907923] using wordTrace_append hprefix tailTrace_3907923
  have hstable : (prefixWord ++ tailWord_3907923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907923).length < 2 ^ (prefixWord ++ tailWord_3907923).sum := by decide
  have hdescent : baseEnd_3907923 < baseStart_3907923 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907973 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_3907973 : Nat := 118140960795 + 3907973 * 2 ^ 59
def prefixEnd_3907973 : Nat := 4983230072969 + 3 ^ 40 * 3907973 * 2
def baseEnd_3907973 : Nat := 2006668533793143771365065

theorem tailTrace_3907973 : CollatzResearch.WordTrace tailWord_3907973 prefixEnd_3907973 2006668533793143771365065 := by
  unfold tailWord_3907973
  simp only [CollatzResearch.WordTrace]
  refine ⟨142535485071088724496800573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95023656714059149664533715 142535485071088724496800573)
  ·
    refine ⟨53450806901658271686300215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142535485071088724496800573 53450806901658271686300215)
    ·
      refine ⟨80176210352487407529450323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53450806901658271686300215 80176210352487407529450323)
      ·
        refine ⟨120264315528731111294175485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80176210352487407529450323 120264315528731111294175485)
        ·
          refine ⟨45099118323274166735315807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120264315528731111294175485 45099118323274166735315807)
          ·
            refine ⟨67648677484911250102973711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45099118323274166735315807 67648677484911250102973711)
            ·
              refine ⟨101473016227366875154460567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67648677484911250102973711 101473016227366875154460567)
              ·
                refine ⟨152209524341050312731690851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101473016227366875154460567 152209524341050312731690851)
                ·
                  refine ⟨228314286511575469097536277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152209524341050312731690851 228314286511575469097536277)
                  ·
                    refine ⟨10702232180230100113947013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 228314286511575469097536277 10702232180230100113947013)
                    ·
                      refine ⟨2006668533793143771365065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10702232180230100113947013 2006668533793143771365065)
                      ·
                        rfl

theorem cell23_3907973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_3907973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907973 prefixEnd_3907973 := by exact prefixLift 3907973
  have htrace : WordTrace (prefixWord ++ tailWord_3907973) baseStart_3907973 baseEnd_3907973 := by
    simpa [prefixWord, tailWord_3907973, baseEnd_3907973] using wordTrace_append hprefix tailTrace_3907973
  have hstable : (prefixWord ++ tailWord_3907973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907973).length < 2 ^ (prefixWord ++ tailWord_3907973).sum := by decide
  have hdescent : baseEnd_3907973 < baseStart_3907973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3907980 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 1, 4, 3]
def baseStart_3907980 : Nat := 118140960795 + 3907980 * 2 ^ 59
def prefixEnd_3907980 : Nat := 4983230072969 + 3 ^ 40 * 3907980 * 2
def baseEnd_3907980 : Nat := 2006672128157725243977533

theorem tailTrace_3907980 : CollatzResearch.WordTrace tailWord_3907980 prefixEnd_3907980 2006672128157725243977533 := by
  unfold tailWord_3907980
  simp only [CollatzResearch.WordTrace]
  refine ⟨71267870191031682346152697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95023826921375576461536929 71267870191031682346152697)
  ·
    refine ⟨53450902643273761759614523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71267870191031682346152697 53450902643273761759614523)
    ·
      refine ⟨80176353964910642639421785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53450902643273761759614523 80176353964910642639421785)
      ·
        refine ⟨60132265473682981979566339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80176353964910642639421785 60132265473682981979566339)
        ·
          refine ⟨90198398210524472969349509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60132265473682981979566339 90198398210524472969349509)
          ·
            refine ⟨16912199664473338681753033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90198398210524472969349509 16912199664473338681753033)
            ·
              refine ⟨12684149748355004011314775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16912199664473338681753033 12684149748355004011314775)
              ·
                refine ⟨19026224622532506016972163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12684149748355004011314775 19026224622532506016972163)
                ·
                  refine ⟨28539336933798759025458245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19026224622532506016972163 28539336933798759025458245)
                  ·
                    refine ⟨5351125675087267317273421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28539336933798759025458245 5351125675087267317273421)
                    ·
                      refine ⟨2006672128157725243977533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5351125675087267317273421 2006672128157725243977533)
                      ·
                        rfl

theorem cell23_3907980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 4, 3].length) (baseStart_3907980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3907980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3907980 prefixEnd_3907980 := by exact prefixLift 3907980
  have htrace : WordTrace (prefixWord ++ tailWord_3907980) baseStart_3907980 baseEnd_3907980 := by
    simpa [prefixWord, tailWord_3907980, baseEnd_3907980] using wordTrace_append hprefix tailTrace_3907980
  have hstable : (prefixWord ++ tailWord_3907980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3907980).length < 2 ^ (prefixWord ++ tailWord_3907980).sum := by decide
  have hdescent : baseEnd_3907980 < baseStart_3907980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3907980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908017 : List Nat := [1, 2, 2, 4, 1, 2, 4, 1, 6]
def baseStart_3908017 : Nat := 118140960795 + 3908017 * 2 ^ 59
def prefixEnd_3908017 : Nat := 4983230072969 + 3 ^ 40 * 3908017 * 2
def baseEnd_3908017 : Nat := 222965680771326844357207

theorem tailTrace_3908017 : CollatzResearch.WordTrace tailWord_3908017 prefixEnd_3908017 222965680771326844357207 := by
  unfold tailWord_3908017
  simp only [CollatzResearch.WordTrace]
  refine ⟨142537089882929320011402305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95024726588619546674268203 142537089882929320011402305)
  ·
    refine ⟨106902817412196990008551729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142537089882929320011402305 106902817412196990008551729)
    ·
      refine ⟨80177113059147742506413797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106902817412196990008551729 80177113059147742506413797)
      ·
        refine ⟨15033208698590201719952587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80177113059147742506413797 15033208698590201719952587)
        ·
          refine ⟨22549813047885302579928881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15033208698590201719952587 22549813047885302579928881)
          ·
            refine ⟨16912359785913976934946661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22549813047885302579928881 16912359785913976934946661)
            ·
              refine ⟨3171067459858870675302499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16912359785913976934946661 3171067459858870675302499)
              ·
                refine ⟨4756601189788306012953749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171067459858870675302499 4756601189788306012953749)
                ·
                  refine ⟨222965680771326844357207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4756601189788306012953749 222965680771326844357207)
                  ·
                    rfl

theorem cell23_3908017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 6].length) (baseStart_3908017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908017 prefixEnd_3908017 := by exact prefixLift 3908017
  have htrace : WordTrace (prefixWord ++ tailWord_3908017) baseStart_3908017 baseEnd_3908017 := by
    simpa [prefixWord, tailWord_3908017, baseEnd_3908017] using wordTrace_append hprefix tailTrace_3908017
  have hstable : (prefixWord ++ tailWord_3908017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908017).length < 2 ^ (prefixWord ++ tailWord_3908017).sum := by decide
  have hdescent : baseEnd_3908017 < baseStart_3908017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908061 : List Nat := [1, 4, 3, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_3908061 : Nat := 118140960795 + 3908061 * 2 ^ 59
def prefixEnd_3908061 : Nat := 4983230072969 + 3 ^ 40 * 3908061 * 2
def baseEnd_3908061 : Nat := 2006713720090739427064661

theorem tailTrace_3908061 : CollatzResearch.WordTrace tailWord_3908061 prefixEnd_3908061 2006713720090739427064661 := by
  unfold tailWord_3908061
  simp only [CollatzResearch.WordTrace]
  refine ⟨142538694694769915526004037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95025796463179943684002691 142538694694769915526004037)
  ·
    refine ⟨26726005255269359161125757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142538694694769915526004037 26726005255269359161125757)
    ·
      refine ⟨10022251970726009685422159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26726005255269359161125757 10022251970726009685422159)
      ·
        refine ⟨15033377956089014528133239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10022251970726009685422159 15033377956089014528133239)
        ·
          refine ⟨22550066934133521792199859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15033377956089014528133239 22550066934133521792199859)
          ·
            refine ⟨33825100401200282688299789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22550066934133521792199859 33825100401200282688299789)
            ·
              refine ⟨12684412650450106008112421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33825100401200282688299789 12684412650450106008112421)
              ·
                refine ⟨2378327371959394876521079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12684412650450106008112421 2378327371959394876521079)
                ·
                  refine ⟨3567491057939092314781619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378327371959394876521079 3567491057939092314781619)
                  ·
                    refine ⟨5351236586908638472172429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3567491057939092314781619 5351236586908638472172429)
                    ·
                      refine ⟨2006713720090739427064661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5351236586908638472172429 2006713720090739427064661)
                      ·
                        rfl

theorem cell23_3908061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_3908061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908061 prefixEnd_3908061 := by exact prefixLift 3908061
  have htrace : WordTrace (prefixWord ++ tailWord_3908061) baseStart_3908061 baseEnd_3908061 := by
    simpa [prefixWord, tailWord_3908061, baseEnd_3908061] using wordTrace_append hprefix tailTrace_3908061
  have hstable : (prefixWord ++ tailWord_3908061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908061).length < 2 ^ (prefixWord ++ tailWord_3908061).sum := by decide
  have hdescent : baseEnd_3908061 < baseStart_3908061 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908073 : List Nat := [1, 2, 1, 1, 1, 2, 1, 14]
def baseStart_3908073 : Nat := 118140960795 + 3908073 * 2 ^ 59
def prefixEnd_3908073 : Nat := 4983230072969 + 3 ^ 40 * 3908073 * 2
def baseEnd_3908073 : Nat := 74322958587355310374615

theorem tailTrace_3908073 : CollatzResearch.WordTrace tailWord_3908073 prefixEnd_3908073 74322958587355310374615 := by
  unfold tailWord_3908073
  simp only [CollatzResearch.WordTrace]
  refine ⟨142539132370726441575440873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95026088247150961050293915 142539132370726441575440873)
  ·
    refine ⟨106904349278044831181580655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142539132370726441575440873 106904349278044831181580655)
    ·
      refine ⟨160356523917067246772370983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106904349278044831181580655 160356523917067246772370983)
      ·
        refine ⟨240534785875600870158556475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160356523917067246772370983 240534785875600870158556475)
        ·
          refine ⟨360802178813401305237834713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240534785875600870158556475 360802178813401305237834713)
          ·
            refine ⟨270601634110050978928376035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 360802178813401305237834713 270601634110050978928376035)
            ·
              refine ⟨405902451165076468392564053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270601634110050978928376035 405902451165076468392564053)
              ·
                refine ⟨74322958587355310374615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 405902451165076468392564053 74322958587355310374615)
                ·
                  rfl

theorem cell23_3908073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 14].length) (baseStart_3908073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908073 prefixEnd_3908073 := by exact prefixLift 3908073
  have htrace : WordTrace (prefixWord ++ tailWord_3908073) baseStart_3908073 baseEnd_3908073 := by
    simpa [prefixWord, tailWord_3908073, baseEnd_3908073] using wordTrace_append hprefix tailTrace_3908073
  have hstable : (prefixWord ++ tailWord_3908073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908073).length < 2 ^ (prefixWord ++ tailWord_3908073).sum := by decide
  have hdescent : baseEnd_3908073 < baseStart_3908073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908077 : List Nat := [1, 5, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_3908077 : Nat := 118140960795 + 3908077 * 2 ^ 59
def prefixEnd_3908077 : Nat := 4983230072969 + 3 ^ 40 * 3908077 * 2
def baseEnd_3908077 : Nat := 668907311927070454821529

theorem tailTrace_3908077 : CollatzResearch.WordTrace tailWord_3908077 prefixEnd_3908077 668907311927070454821529 := by
  unfold tailWord_3908077
  simp only [CollatzResearch.WordTrace]
  refine ⟨142539278262711950258586485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95026185508474633505724323 142539278262711950258586485)
  ·
    refine ⟨13363057337129245336742483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142539278262711950258586485 13363057337129245336742483)
    ·
      refine ⟨20044586005693868005113725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13363057337129245336742483 20044586005693868005113725)
      ·
        refine ⟨7516719752135200501917647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20044586005693868005113725 7516719752135200501917647)
        ·
          refine ⟨11275079628202800752876471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7516719752135200501917647 11275079628202800752876471)
          ·
            refine ⟨16912619442304201129314707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11275079628202800752876471 16912619442304201129314707)
            ·
              refine ⟨25368929163456301693972061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16912619442304201129314707 25368929163456301693972061)
              ·
                refine ⟨9513348436296113135239523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25368929163456301693972061 9513348436296113135239523)
                ·
                  refine ⟨14270022654444169702859285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9513348436296113135239523 14270022654444169702859285)
                  ·
                    refine ⟨668907311927070454821529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14270022654444169702859285 668907311927070454821529)
                    ·
                      rfl

theorem cell23_3908077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_3908077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908077 prefixEnd_3908077 := by exact prefixLift 3908077
  have htrace : WordTrace (prefixWord ++ tailWord_3908077) baseStart_3908077 baseEnd_3908077 := by
    simpa [prefixWord, tailWord_3908077, baseEnd_3908077] using wordTrace_append hprefix tailTrace_3908077
  have hstable : (prefixWord ++ tailWord_3908077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908077).length < 2 ^ (prefixWord ++ tailWord_3908077).sum := by decide
  have hdescent : baseEnd_3908077 < baseStart_3908077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908097 : List Nat := [1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_3908097 : Nat := 118140960795 + 3908097 * 2 ^ 59
def prefixEnd_3908097 : Nat := 4983230072969 + 3 ^ 40 * 3908097 * 2
def baseEnd_3908097 : Nat := 2006732205394301286214495

theorem tailTrace_3908097 : CollatzResearch.WordTrace tailWord_3908097 prefixEnd_3908097 2006732205394301286214495 := by
  unfold tailWord_3908097
  simp only [CollatzResearch.WordTrace]
  refine ⟨142540007722639493674314545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95026671815092995782876363 142540007722639493674314545)
  ·
    refine ⟨106905005791979620255735909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142540007722639493674314545 106905005791979620255735909)
    ·
      refine ⟨20044688585996178797950483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106905005791979620255735909 20044688585996178797950483)
      ·
        refine ⟨30067032878994268196925725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20044688585996178797950483 30067032878994268196925725)
        ·
          refine ⟨11275137329622850573847147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30067032878994268196925725 11275137329622850573847147)
          ·
            refine ⟨16912705994434275860770721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11275137329622850573847147 16912705994434275860770721)
            ·
              refine ⟨12684529495825706895578041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16912705994434275860770721 12684529495825706895578041)
              ·
                refine ⟨9513397121869280171683531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12684529495825706895578041 9513397121869280171683531)
                ·
                  refine ⟨14270095682803920257525297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9513397121869280171683531 14270095682803920257525297)
                  ·
                    refine ⟨10702571762102940193143973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14270095682803920257525297 10702571762102940193143973)
                    ·
                      refine ⟨2006732205394301286214495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10702571762102940193143973 2006732205394301286214495)
                      ·
                        rfl

theorem cell23_3908097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_3908097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908097 prefixEnd_3908097 := by exact prefixLift 3908097
  have htrace : WordTrace (prefixWord ++ tailWord_3908097) baseStart_3908097 baseEnd_3908097 := by
    simpa [prefixWord, tailWord_3908097, baseEnd_3908097] using wordTrace_append hprefix tailTrace_3908097
  have hstable : (prefixWord ++ tailWord_3908097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908097).length < 2 ^ (prefixWord ++ tailWord_3908097).sum := by decide
  have hdescent : baseEnd_3908097 < baseStart_3908097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908098 : List Nat := [3, 4, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_3908098 : Nat := 118140960795 + 3908098 * 2 ^ 59
def prefixEnd_3908098 : Nat := 4983230072969 + 3 ^ 40 * 3908098 * 2
def baseEnd_3908098 : Nat := 668910906291651927433997

theorem tailTrace_3908098 : CollatzResearch.WordTrace tailWord_3908098 prefixEnd_3908098 668910906291651927433997 := by
  unfold tailWord_3908098
  simp only [CollatzResearch.WordTrace]
  refine ⟨35635011048908967711275237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95026696130423913896733965 35635011048908967711275237)
  ·
    refine ⟨6681564571670431445864107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35635011048908967711275237 6681564571670431445864107)
    ·
      refine ⟨10022346857505647168796161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6681564571670431445864107 10022346857505647168796161)
      ·
        refine ⟨7516760143129235376597121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10022346857505647168796161 7516760143129235376597121)
        ·
          refine ⟨5637570107346926532447841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7516760143129235376597121 5637570107346926532447841)
          ·
            refine ⟨4228177580510194899335881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5637570107346926532447841 4228177580510194899335881)
            ·
              refine ⟨3171133185382646174501911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4228177580510194899335881 3171133185382646174501911)
              ·
                refine ⟨4756699778073969261752867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171133185382646174501911 4756699778073969261752867)
                ·
                  refine ⟨7135049667110953892629301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756699778073969261752867 7135049667110953892629301)
                  ·
                    refine ⟨668910906291651927433997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7135049667110953892629301 668910906291651927433997)
                    ·
                      rfl

theorem cell23_3908098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_3908098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908098 prefixEnd_3908098 := by exact prefixLift 3908098
  have htrace : WordTrace (prefixWord ++ tailWord_3908098) baseStart_3908098 baseEnd_3908098 := by
    simpa [prefixWord, tailWord_3908098, baseEnd_3908098] using wordTrace_append hprefix tailTrace_3908098
  have hstable : (prefixWord ++ tailWord_3908098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908098).length < 2 ^ (prefixWord ++ tailWord_3908098).sum := by decide
  have hdescent : baseEnd_3908098 < baseStart_3908098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908101 : List Nat := [1, 3, 1, 1, 2, 2, 3, 5, 1, 2, 2]
def baseStart_3908101 : Nat := 118140960795 + 3908101 * 2 ^ 59
def prefixEnd_3908101 : Nat := 4983230072969 + 3 ^ 40 * 3908101 * 2
def baseEnd_3908101 : Nat := 2006734259316919270564477

theorem tailTrace_3908101 : CollatzResearch.WordTrace tailWord_3908101 prefixEnd_3908101 2006734259316919270564477 := by
  unfold tailWord_3908101
  simp only [CollatzResearch.WordTrace]
  refine ⟨142540153614625002357460157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95026769076416668238306771 142540153614625002357460157)
  ·
    refine ⟨53452557605484375884047559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142540153614625002357460157 53452557605484375884047559)
    ·
      refine ⟨80178836408226563826071339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53452557605484375884047559 80178836408226563826071339)
      ·
        refine ⟨120268254612339845739107009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80178836408226563826071339 120268254612339845739107009)
        ·
          refine ⟨90201190959254884304330257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120268254612339845739107009 90201190959254884304330257)
          ·
            refine ⟨67650893219441163228247693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90201190959254884304330257 67650893219441163228247693)
            ·
              refine ⟨25369084957290436210592885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67650893219441163228247693 25369084957290436210592885)
              ·
                refine ⟨2378351714745978394743083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 25369084957290436210592885 2378351714745978394743083)
                ·
                  refine ⟨3567527572118967592114625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378351714745978394743083 3567527572118967592114625)
                  ·
                    refine ⟨2675645679089225694085969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3567527572118967592114625 2675645679089225694085969)
                    ·
                      refine ⟨2006734259316919270564477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675645679089225694085969 2006734259316919270564477)
                      ·
                        rfl

theorem cell23_3908101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 5, 1, 2, 2].length) (baseStart_3908101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908101 prefixEnd_3908101 := by exact prefixLift 3908101
  have htrace : WordTrace (prefixWord ++ tailWord_3908101) baseStart_3908101 baseEnd_3908101 := by
    simpa [prefixWord, tailWord_3908101, baseEnd_3908101] using wordTrace_append hprefix tailTrace_3908101
  have hstable : (prefixWord ++ tailWord_3908101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908101).length < 2 ^ (prefixWord ++ tailWord_3908101).sum := by decide
  have hdescent : baseEnd_3908101 < baseStart_3908101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908140 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_3908140 : Nat := 118140960795 + 3908140 * 2 ^ 59
def prefixEnd_3908140 : Nat := 4983230072969 + 3 ^ 40 * 3908140 * 2
def baseEnd_3908140 : Nat := 2006754285062444617976797

theorem tailTrace_3908140 : CollatzResearch.WordTrace tailWord_3908140 prefixEnd_3908140 2006754285062444617976797 := by
  unfold tailWord_3908140
  simp only [CollatzResearch.WordTrace]
  refine ⟨71270788030741856009064937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95027717374322474678753249 71270788030741856009064937)
  ·
    refine ⟨53453091023056392006798703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71270788030741856009064937 53453091023056392006798703)
    ·
      refine ⟨80179636534584588010198055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53453091023056392006798703 80179636534584588010198055)
      ·
        refine ⟨120269454801876882015297083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80179636534584588010198055 120269454801876882015297083)
        ·
          refine ⟨180404182202815323022945625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120269454801876882015297083 180404182202815323022945625)
          ·
            refine ⟨135303136652111492267209219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180404182202815323022945625 135303136652111492267209219)
            ·
              refine ⟨202954704978167238400813829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135303136652111492267209219 202954704978167238400813829)
              ·
                refine ⟨38054007183406357200152593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 202954704978167238400813829 38054007183406357200152593)
                ·
                  refine ⟨28540505387554767900114445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38054007183406357200152593 28540505387554767900114445)
                  ·
                    refine ⟨10702689520333037962542917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28540505387554767900114445 10702689520333037962542917)
                    ·
                      refine ⟨2006754285062444617976797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10702689520333037962542917 2006754285062444617976797)
                      ·
                        rfl

theorem cell23_3908140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_3908140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908140 prefixEnd_3908140 := by exact prefixLift 3908140
  have htrace : WordTrace (prefixWord ++ tailWord_3908140) baseStart_3908140 baseEnd_3908140 := by
    simpa [prefixWord, tailWord_3908140, baseEnd_3908140] using wordTrace_append hprefix tailTrace_3908140
  have hstable : (prefixWord ++ tailWord_3908140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908140).length < 2 ^ (prefixWord ++ tailWord_3908140).sum := by decide
  have hdescent : baseEnd_3908140 < baseStart_3908140 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908141 : List Nat := [1, 5, 4, 1, 1, 1, 1, 9]
def baseStart_3908141 : Nat := 118140960795 + 3908141 * 2 ^ 59
def prefixEnd_3908141 : Nat := 4983230072969 + 3 ^ 40 * 3908141 * 2
def baseEnd_3908141 : Nat := 74324251797892559780159

theorem tailTrace_3908141 : CollatzResearch.WordTrace tailWord_3908141 prefixEnd_3908141 74324251797892559780159 := by
  unfold tailWord_3908141
  simp only [CollatzResearch.WordTrace]
  refine ⟨142541612534480089188916277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95027741689653392792610851 142541612534480089188916277)
  ·
    refine ⟨13363276175107508361460901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142541612534480089188916277 13363276175107508361460901)
    ·
      refine ⟨2505614282832657817773919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 13363276175107508361460901 2505614282832657817773919)
      ·
        refine ⟨3758421424248986726660879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2505614282832657817773919 3758421424248986726660879)
        ·
          refine ⟨5637632136373480089991319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758421424248986726660879 5637632136373480089991319)
          ·
            refine ⟨8456448204560220134986979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5637632136373480089991319 8456448204560220134986979)
            ·
              refine ⟨12684672306840330202480469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456448204560220134986979 12684672306840330202480469)
              ·
                refine ⟨74324251797892559780159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12684672306840330202480469 74324251797892559780159)
                ·
                  rfl

theorem cell23_3908141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 9].length) (baseStart_3908141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908141 prefixEnd_3908141 := by exact prefixLift 3908141
  have htrace : WordTrace (prefixWord ++ tailWord_3908141) baseStart_3908141 baseEnd_3908141 := by
    simpa [prefixWord, tailWord_3908141, baseEnd_3908141] using wordTrace_append hprefix tailTrace_3908141
  have hstable : (prefixWord ++ tailWord_3908141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908141).length < 2 ^ (prefixWord ++ tailWord_3908141).sum := by decide
  have hdescent : baseEnd_3908141 < baseStart_3908141 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908144 : List Nat := [2, 1, 1, 1, 2, 3, 3, 4, 1, 3, 2]
def baseStart_3908144 : Nat := 118140960795 + 3908144 * 2 ^ 59
def prefixEnd_3908144 : Nat := 4983230072969 + 3 ^ 40 * 3908144 * 2
def baseEnd_3908144 : Nat := 2006756338985062602326779

theorem tailTrace_3908144 : CollatzResearch.WordTrace tailWord_3908144 prefixEnd_3908144 2006756338985062602326779 := by
  unfold tailWord_3908144
  simp only [CollatzResearch.WordTrace]
  refine ⟨71270860976734610350637743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95027814635646147134183657 71270860976734610350637743)
  ·
    refine ⟨106906291465101915525956615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71270860976734610350637743 106906291465101915525956615)
    ·
      refine ⟨160359437197652873288934923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106906291465101915525956615 160359437197652873288934923)
      ·
        refine ⟨240539155796479309933402385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160359437197652873288934923 240539155796479309933402385)
        ·
          refine ⟨180404366847359482450051789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240539155796479309933402385 180404366847359482450051789)
          ·
            refine ⟨67651637567759805918769421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180404366847359482450051789 67651637567759805918769421)
            ·
              refine ⟨25369364087909927219538533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67651637567759805918769421 25369364087909927219538533)
              ·
                refine ⟨4756755766483111353663475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25369364087909927219538533 4756755766483111353663475)
                ·
                  refine ⟨7135133649724667030495213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756755766483111353663475 7135133649724667030495213)
                  ·
                    refine ⟨2675675118646750136435705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7135133649724667030495213 2675675118646750136435705)
                    ·
                      refine ⟨2006756338985062602326779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675675118646750136435705 2006756338985062602326779)
                      ·
                        rfl

theorem cell23_3908144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 4, 1, 3, 2].length) (baseStart_3908144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908144 prefixEnd_3908144 := by exact prefixLift 3908144
  have htrace : WordTrace (prefixWord ++ tailWord_3908144) baseStart_3908144 baseEnd_3908144 := by
    simpa [prefixWord, tailWord_3908144, baseEnd_3908144] using wordTrace_append hprefix tailTrace_3908144
  have hstable : (prefixWord ++ tailWord_3908144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908144).length < 2 ^ (prefixWord ++ tailWord_3908144).sum := by decide
  have hdescent : baseEnd_3908144 < baseStart_3908144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908160 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_3908160 : Nat := 118140960795 + 3908160 * 2 ^ 59
def prefixEnd_3908160 : Nat := 4983230072969 + 3 ^ 40 * 3908160 * 2
def baseEnd_3908160 : Nat := 2006764554675534539726705

theorem tailTrace_3908160 : CollatzResearch.WordTrace tailWord_3908160 prefixEnd_3908160 2006764554675534539726705 := by
  unfold tailWord_3908160
  simp only [CollatzResearch.WordTrace]
  refine ⟨71271152760705627716928967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95028203680940836955905289 71271152760705627716928967)
  ·
    refine ⟨106906729141058441575393451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71271152760705627716928967 106906729141058441575393451)
    ·
      refine ⟨160360093711587662363090177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106906729141058441575393451 160360093711587662363090177)
      ·
        refine ⟨120270070283690746772317633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160360093711587662363090177 120270070283690746772317633)
        ·
          refine ⟨90202552712768060079238225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120270070283690746772317633 90202552712768060079238225)
          ·
            refine ⟨67651914534576045059428669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90202552712768060079238225 67651914534576045059428669)
            ·
              refine ⟨25369467950466016897285751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67651914534576045059428669 25369467950466016897285751)
              ·
                refine ⟨38054201925699025345928627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25369467950466016897285751 38054201925699025345928627)
                ·
                  refine ⟨57081302888548538018892941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38054201925699025345928627 57081302888548538018892941)
                  ·
                    refine ⟨21405488583205701757084853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57081302888548538018892941 21405488583205701757084853)
                    ·
                      refine ⟨2006764554675534539726705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21405488583205701757084853 2006764554675534539726705)
                      ·
                        rfl

theorem cell23_3908160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_3908160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908160 prefixEnd_3908160 := by exact prefixLift 3908160
  have htrace : WordTrace (prefixWord ++ tailWord_3908160) baseStart_3908160 baseEnd_3908160 := by
    simpa [prefixWord, tailWord_3908160, baseEnd_3908160] using wordTrace_append hprefix tailTrace_3908160
  have hstable : (prefixWord ++ tailWord_3908160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908160).length < 2 ^ (prefixWord ++ tailWord_3908160).sum := by decide
  have hdescent : baseEnd_3908160 < baseStart_3908160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908161 : List Nat := [1, 2, 5, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_3908161 : Nat := 118140960795 + 3908161 * 2 ^ 59
def prefixEnd_3908161 : Nat := 4983230072969 + 3 ^ 40 * 3908161 * 2
def baseEnd_3908161 : Nat := 2006765068156189035814201

theorem tailTrace_3908161 : CollatzResearch.WordTrace tailWord_3908161 prefixEnd_3908161 2006765068156189035814201 := by
  unfold tailWord_3908161
  simp only [CollatzResearch.WordTrace]
  refine ⟨142542341994407632604644337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95028227996271755069762891 142542341994407632604644337)
  ·
    refine ⟨106906756495805724453483253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142542341994407632604644337 106906756495805724453483253)
    ·
      refine ⟨10022508421481786667514055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 106906756495805724453483253 10022508421481786667514055)
      ·
        refine ⟨15033762632222680001271083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10022508421481786667514055 15033762632222680001271083)
        ·
          refine ⟨22550643948334020001906625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15033762632222680001271083 22550643948334020001906625)
          ·
            refine ⟨16912982961250515001429969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22550643948334020001906625 16912982961250515001429969)
            ·
              refine ⟨12684737220937886251072477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16912982961250515001429969 12684737220937886251072477)
              ·
                refine ⟨4756776457851707344152179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12684737220937886251072477 4756776457851707344152179)
                ·
                  refine ⟨7135164686777561016228269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4756776457851707344152179 7135164686777561016228269)
                  ·
                    refine ⟨2675686757541585381085601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7135164686777561016228269 2675686757541585381085601)
                    ·
                      refine ⟨2006765068156189035814201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675686757541585381085601 2006765068156189035814201)
                      ·
                        rfl

theorem cell23_3908161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_3908161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908161 prefixEnd_3908161 := by exact prefixLift 3908161
  have htrace : WordTrace (prefixWord ++ tailWord_3908161) baseStart_3908161 baseEnd_3908161 := by
    simpa [prefixWord, tailWord_3908161, baseEnd_3908161] using wordTrace_append hprefix tailTrace_3908161
  have hstable : (prefixWord ++ tailWord_3908161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908161).length < 2 ^ (prefixWord ++ tailWord_3908161).sum := by decide
  have hdescent : baseEnd_3908161 < baseStart_3908161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908227 : List Nat := [1, 1, 1, 3, 3, 1, 4, 2, 2, 5]
def baseStart_3908227 : Nat := 118140960795 + 3908227 * 2 ^ 59
def prefixEnd_3908227 : Nat := 4983230072969 + 3 ^ 40 * 3908227 * 2
def baseEnd_3908227 : Nat := 668932985959795259196299

theorem tailTrace_3908227 : CollatzResearch.WordTrace tailWord_3908227 prefixEnd_3908227 668932985959795259196299 := by
  unfold tailWord_3908227
  simp only [CollatzResearch.WordTrace]
  refine ⟨142544749212168525876546935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95029832808112350584364623 142544749212168525876546935)
  ·
    refine ⟨213817123818252788814820403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142544749212168525876546935 213817123818252788814820403)
    ·
      refine ⟨320725685727379183222230605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213817123818252788814820403 320725685727379183222230605)
      ·
        refine ⟨120272132147767193708336477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320725685727379183222230605 120272132147767193708336477)
        ·
          refine ⟨45102049555412697640626179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120272132147767193708336477 45102049555412697640626179)
          ·
            refine ⟨67653074333119046460939269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45102049555412697640626179 67653074333119046460939269)
            ·
              refine ⟨12684951437459821211426113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67653074333119046460939269 12684951437459821211426113)
              ·
                refine ⟨9513713578094865908569585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12684951437459821211426113 9513713578094865908569585)
                ·
                  refine ⟨7135285183571149431427189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9513713578094865908569585 7135285183571149431427189)
                  ·
                    refine ⟨668932985959795259196299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7135285183571149431427189 668932985959795259196299)
                    ·
                      rfl

theorem cell23_3908227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 5].length) (baseStart_3908227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908227 prefixEnd_3908227 := by exact prefixLift 3908227
  have htrace : WordTrace (prefixWord ++ tailWord_3908227) baseStart_3908227 baseEnd_3908227 := by
    simpa [prefixWord, tailWord_3908227, baseEnd_3908227] using wordTrace_append hprefix tailTrace_3908227
  have hstable : (prefixWord ++ tailWord_3908227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908227).length < 2 ^ (prefixWord ++ tailWord_3908227).sum := by decide
  have hdescent : baseEnd_3908227 < baseStart_3908227 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908240 : List Nat := [2, 1, 1, 1, 1, 1, 3, 1, 4, 8]
def baseStart_3908240 : Nat := 118140960795 + 3908240 * 2 ^ 59
def prefixEnd_3908240 : Nat := 4983230072969 + 3 ^ 40 * 3908240 * 2
def baseEnd_3908240 : Nat := 668935211042631408908779

theorem tailTrace_3908240 : CollatzResearch.WordTrace tailWord_3908240 prefixEnd_3908240 668935211042631408908779 := by
  unfold tailWord_3908240
  simp only [CollatzResearch.WordTrace]
  refine ⟨71272611680560714548385087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95030148907414286064513449 71272611680560714548385087)
  ·
    refine ⟨106908917520841071822577631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71272611680560714548385087 106908917520841071822577631)
    ·
      refine ⟨160363376281261607733866447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106908917520841071822577631 160363376281261607733866447)
      ·
        refine ⟨240545064421892411600799671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160363376281261607733866447 240545064421892411600799671)
        ·
          refine ⟨360817596632838617401199507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240545064421892411600799671 360817596632838617401199507)
          ·
            refine ⟨541226394949257926101799261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360817596632838617401199507 541226394949257926101799261)
            ·
              refine ⟨202959898105971722288174723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 541226394949257926101799261 202959898105971722288174723)
              ·
                refine ⟨304439847158957583432262085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 202959898105971722288174723 304439847158957583432262085)
                ·
                  refine ⟨57082471342304546893549141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 304439847158957583432262085 57082471342304546893549141)
                  ·
                    refine ⟨668935211042631408908779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57082471342304546893549141 668935211042631408908779)
                    ·
                      rfl

theorem cell23_3908240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_3908240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908240 prefixEnd_3908240 := by exact prefixLift 3908240
  have htrace : WordTrace (prefixWord ++ tailWord_3908240) baseStart_3908240 baseEnd_3908240 := by
    simpa [prefixWord, tailWord_3908240, baseEnd_3908240] using wordTrace_append hprefix tailTrace_3908240
  have hstable : (prefixWord ++ tailWord_3908240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908240).length < 2 ^ (prefixWord ++ tailWord_3908240).sum := by decide
  have hdescent : baseEnd_3908240 < baseStart_3908240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908247 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_3908247 : Nat := 118140960795 + 3908247 * 2 ^ 59
def prefixEnd_3908247 : Nat := 4983230072969 + 3 ^ 40 * 3908247 * 2
def baseEnd_3908247 : Nat := 2006809227492475699338805

theorem tailTrace_3908247 : CollatzResearch.WordTrace tailWord_3908247 prefixEnd_3908247 2006809227492475699338805 := by
  unfold tailWord_3908247
  simp only [CollatzResearch.WordTrace]
  refine ⟨142545478672096069292274995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95030319114730712861516663 142545478672096069292274995)
  ·
    refine ⟨213818218008144103938412493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142545478672096069292274995 213818218008144103938412493)
    ·
      refine ⟨80181831753054038976904685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213818218008144103938412493 80181831753054038976904685)
      ·
        refine ⟨30068186907395264616339257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80181831753054038976904685 30068186907395264616339257)
        ·
          refine ⟨22551140180546448462254443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30068186907395264616339257 22551140180546448462254443)
          ·
            refine ⟨33826710270819672693381665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22551140180546448462254443 33826710270819672693381665)
            ·
              refine ⟨25370032703114754520036249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33826710270819672693381665 25370032703114754520036249)
              ·
                refine ⟨19027524527336065890027187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25370032703114754520036249 19027524527336065890027187)
                ·
                  refine ⟨28541286791004098835040781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19027524527336065890027187 28541286791004098835040781)
                  ·
                    refine ⟨10702982546626537063140293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28541286791004098835040781 10702982546626537063140293)
                    ·
                      refine ⟨2006809227492475699338805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10702982546626537063140293 2006809227492475699338805)
                      ·
                        rfl

theorem cell23_3908247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_3908247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908247 prefixEnd_3908247 := by exact prefixLift 3908247
  have htrace : WordTrace (prefixWord ++ tailWord_3908247) baseStart_3908247 baseEnd_3908247 := by
    simpa [prefixWord, tailWord_3908247, baseEnd_3908247] using wordTrace_append hprefix tailTrace_3908247
  have hstable : (prefixWord ++ tailWord_3908247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908247).length < 2 ^ (prefixWord ++ tailWord_3908247).sum := by decide
  have hdescent : baseEnd_3908247 < baseStart_3908247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908284 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 4, 2, 3]
def baseStart_3908284 : Nat := 118140960795 + 3908284 * 2 ^ 59
def prefixEnd_3908284 : Nat := 4983230072969 + 3 ^ 40 * 3908284 * 2
def baseEnd_3908284 : Nat := 2006828226276692054576135

theorem tailTrace_3908284 : CollatzResearch.WordTrace tailWord_3908284 prefixEnd_3908284 2006828226276692054576135 := by
  unfold tailWord_3908284
  simp only [CollatzResearch.WordTrace]
  refine ⟨71273414086481012305685953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95031218781974683074247937 71273414086481012305685953)
  ·
    refine ⟨53455060564860759229264465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71273414086481012305685953 53455060564860759229264465)
    ·
      refine ⟨40091295423645569421948349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53455060564860759229264465 40091295423645569421948349)
      ·
        refine ⟨15034235783867088533230631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40091295423645569421948349 15034235783867088533230631)
        ·
          refine ⟨22551353675800632799845947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15034235783867088533230631 22551353675800632799845947)
          ·
            refine ⟨33827030513700949199768921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22551353675800632799845947 33827030513700949199768921)
            ·
              refine ⟨25370272885275711899826691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33827030513700949199768921 25370272885275711899826691)
              ·
                refine ⟨38055409327913567849740037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25370272885275711899826691 38055409327913567849740037)
                ·
                  refine ⟨7135389248983793971826257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38055409327913567849740037 7135389248983793971826257)
                  ·
                    refine ⟨5351541936737845478869693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7135389248983793971826257 5351541936737845478869693)
                    ·
                      refine ⟨2006828226276692054576135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5351541936737845478869693 2006828226276692054576135)
                      ·
                        rfl

theorem cell23_3908284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_3908284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908284 prefixEnd_3908284 := by exact prefixLift 3908284
  have htrace : WordTrace (prefixWord ++ tailWord_3908284) baseStart_3908284 baseEnd_3908284 := by
    simpa [prefixWord, tailWord_3908284, baseEnd_3908284] using wordTrace_append hprefix tailTrace_3908284
  have hstable : (prefixWord ++ tailWord_3908284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908284).length < 2 ^ (prefixWord ++ tailWord_3908284).sum := by decide
  have hdescent : baseEnd_3908284 < baseStart_3908284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908287 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 8]
def baseStart_3908287 : Nat := 118140960795 + 3908287 * 2 ^ 59
def prefixEnd_3908287 : Nat := 4983230072969 + 3 ^ 40 * 3908287 * 2
def baseEnd_3908287 : Nat := 222981085190961726982069

theorem tailTrace_3908287 : CollatzResearch.WordTrace tailWord_3908287 prefixEnd_3908287 222981085190961726982069 := by
  unfold tailWord_3908287
  simp only [CollatzResearch.WordTrace]
  refine ⟨142546937591951156123731115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95031291727967437415820743 142546937591951156123731115)
  ·
    refine ⟨213820406387926734185596673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142546937591951156123731115 213820406387926734185596673)
    ·
      refine ⟨160365304790945050639197505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213820406387926734185596673 160365304790945050639197505)
      ·
        refine ⟨120273978593208787979398129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160365304790945050639197505 120273978593208787979398129)
        ·
          refine ⟨90205483944906590984548597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120273978593208787979398129 90205483944906590984548597)
          ·
            refine ⟨8456764119834992904801431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90205483944906590984548597 8456764119834992904801431)
            ·
              refine ⟨12685146179752489357202147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8456764119834992904801431 12685146179752489357202147)
              ·
                refine ⟨19027719269628734035803221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12685146179752489357202147 19027719269628734035803221)
                ·
                  refine ⟨222981085190961726982069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19027719269628734035803221 222981085190961726982069)
                  ·
                    rfl

theorem cell23_3908287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 8].length) (baseStart_3908287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908287 prefixEnd_3908287 := by exact prefixLift 3908287
  have htrace : WordTrace (prefixWord ++ tailWord_3908287) baseStart_3908287 baseEnd_3908287 := by
    simpa [prefixWord, tailWord_3908287, baseEnd_3908287] using wordTrace_append hprefix tailTrace_3908287
  have hstable : (prefixWord ++ tailWord_3908287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908287).length < 2 ^ (prefixWord ++ tailWord_3908287).sum := by decide
  have hdescent : baseEnd_3908287 < baseStart_3908287 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908348 : List Nat := [2, 2, 2, 1, 3, 4, 1, 1, 3, 1, 3]
def baseStart_3908348 : Nat := 118140960795 + 3908348 * 2 ^ 59
def prefixEnd_3908348 : Nat := 4983230072969 + 3 ^ 40 * 3908348 * 2
def baseEnd_3908348 : Nat := 2006861089038579804175841

theorem tailTrace_3908348 : CollatzResearch.WordTrace tailWord_3908348 prefixEnd_3908348 2006861089038579804175841 := by
  unfold tailWord_3908348
  simp only [CollatzResearch.WordTrace]
  refine ⟨71274581222365081770850849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95032774963153442361134465 71274581222365081770850849)
  ·
    refine ⟨53455935916773811328138137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71274581222365081770850849 53455935916773811328138137)
    ·
      refine ⟨40091951937580358496103603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53455935916773811328138137 40091951937580358496103603)
      ·
        refine ⟨60137927906370537744155405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40091951937580358496103603 60137927906370537744155405)
        ·
          refine ⟨22551722964888951654058277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60137927906370537744155405 22551722964888951654058277)
          ·
            refine ⟨4228448055916678435135927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22551722964888951654058277 4228448055916678435135927)
            ·
              refine ⟨6342672083875017652703891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4228448055916678435135927 6342672083875017652703891)
              ·
                refine ⟨9514008125812526479055837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6342672083875017652703891 9514008125812526479055837)
                ·
                  refine ⟨3567753047179697429645939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9514008125812526479055837 3567753047179697429645939)
                  ·
                    refine ⟨5351629570769546144468909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3567753047179697429645939 5351629570769546144468909)
                    ·
                      refine ⟨2006861089038579804175841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5351629570769546144468909 2006861089038579804175841)
                      ·
                        rfl

theorem cell23_3908348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 3, 1, 3].length) (baseStart_3908348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908348 prefixEnd_3908348 := by exact prefixLift 3908348
  have htrace : WordTrace (prefixWord ++ tailWord_3908348) baseStart_3908348 baseEnd_3908348 := by
    simpa [prefixWord, tailWord_3908348, baseEnd_3908348] using wordTrace_append hprefix tailTrace_3908348
  have hstable : (prefixWord ++ tailWord_3908348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908348).length < 2 ^ (prefixWord ++ tailWord_3908348).sum := by decide
  have hdescent : baseEnd_3908348 < baseStart_3908348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908367 : List Nat := [1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_3908367 : Nat := 118140960795 + 3908367 * 2 ^ 59
def prefixEnd_3908367 : Nat := 4983230072969 + 3 ^ 40 * 3908367 * 2
def baseEnd_3908367 : Nat := 2006870845171015229838253

theorem tailTrace_3908367 : CollatzResearch.WordTrace tailWord_3908367 prefixEnd_3908367 2006870845171015229838253 := by
  unfold tailWord_3908367
  simp only [CollatzResearch.WordTrace]
  refine ⟨142549855431661329786643355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95033236954440886524428903 142549855431661329786643355)
  ·
    refine ⟨213824783147491994679965033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142549855431661329786643355 213824783147491994679965033)
    ·
      refine ⟨160368587360618996009973775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213824783147491994679965033 160368587360618996009973775)
      ·
        refine ⟨240552881040928494014960663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160368587360618996009973775 240552881040928494014960663)
        ·
          refine ⟨360829321561392741022440995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240552881040928494014960663 360829321561392741022440995)
          ·
            refine ⟨541243982342089111533661493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360829321561392741022440995 541243982342089111533661493)
            ·
              refine ⟨50741623344570854206280765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 541243982342089111533661493 50741623344570854206280765)
              ·
                refine ⟨19028108754214070327355287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50741623344570854206280765 19028108754214070327355287)
                ·
                  refine ⟨28542163131321105491032931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19028108754214070327355287 28542163131321105491032931)
                  ·
                    refine ⟨42813244696981658236549397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28542163131321105491032931 42813244696981658236549397)
                    ·
                      refine ⟨2006870845171015229838253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42813244696981658236549397 2006870845171015229838253)
                      ·
                        rfl

theorem cell23_3908367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_3908367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908367 prefixEnd_3908367 := by exact prefixLift 3908367
  have htrace : WordTrace (prefixWord ++ tailWord_3908367) baseStart_3908367 baseEnd_3908367 := by
    simpa [prefixWord, tailWord_3908367, baseEnd_3908367] using wordTrace_append hprefix tailTrace_3908367
  have hstable : (prefixWord ++ tailWord_3908367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908367).length < 2 ^ (prefixWord ++ tailWord_3908367).sum := by decide
  have hdescent : baseEnd_3908367 < baseStart_3908367 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908371 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 5, 2, 2]
def baseStart_3908371 : Nat := 118140960795 + 3908371 * 2 ^ 59
def prefixEnd_3908371 : Nat := 4983230072969 + 3 ^ 40 * 3908371 * 2
def baseEnd_3908371 : Nat := 2006872899093633214188235

theorem tailTrace_3908371 : CollatzResearch.WordTrace tailWord_3908371 prefixEnd_3908371 2006872899093633214188235 := by
  unfold tailWord_3908371
  simp only [CollatzResearch.WordTrace]
  refine ⟨142550001323646838469788967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95033334215764558979859311 142550001323646838469788967)
  ·
    refine ⟨213825001985470257704683451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142550001323646838469788967 213825001985470257704683451)
    ·
      refine ⟨320737502978205386557025177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213825001985470257704683451 320737502978205386557025177)
      ·
        refine ⟨240553127233654039917768883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320737502978205386557025177 240553127233654039917768883)
        ·
          refine ⟨360829690850481059876653325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240553127233654039917768883 360829690850481059876653325)
          ·
            refine ⟨135311134068930397453744997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 360829690850481059876653325 135311134068930397453744997)
            ·
              refine ⟨25370837637924449522577187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135311134068930397453744997 25370837637924449522577187)
              ·
                refine ⟨38056256456886674283865781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25370837637924449522577187 38056256456886674283865781)
                ·
                  refine ⟨3567774042833125714112417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38056256456886674283865781 3567774042833125714112417)
                  ·
                    refine ⟨2675830532124844285584313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3567774042833125714112417 2675830532124844285584313)
                    ·
                      refine ⟨2006872899093633214188235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675830532124844285584313 2006872899093633214188235)
                      ·
                        rfl

theorem cell23_3908371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 2, 2].length) (baseStart_3908371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908371 prefixEnd_3908371 := by exact prefixLift 3908371
  have htrace : WordTrace (prefixWord ++ tailWord_3908371) baseStart_3908371 baseEnd_3908371 := by
    simpa [prefixWord, tailWord_3908371, baseEnd_3908371] using wordTrace_append hprefix tailTrace_3908371
  have hstable : (prefixWord ++ tailWord_3908371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908371).length < 2 ^ (prefixWord ++ tailWord_3908371).sum := by decide
  have hdescent : baseEnd_3908371 < baseStart_3908371 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908384 : List Nat := [2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_3908384 : Nat := 118140960795 + 3908384 * 2 ^ 59
def prefixEnd_3908384 : Nat := 4983230072969 + 3 ^ 40 * 3908384 * 2
def baseEnd_3908384 : Nat := 2006879574342141663325675

theorem tailTrace_3908384 : CollatzResearch.WordTrace tailWord_3908384 prefixEnd_3908384 2006879574342141663325675 := by
  unfold tailWord_3908384
  simp only [CollatzResearch.WordTrace]
  refine ⟨71275237736299870845006103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95033650315066494460008137 71275237736299870845006103)
  ·
    refine ⟨106912856604449806267509155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71275237736299870845006103 106912856604449806267509155)
    ·
      refine ⟨160369284906674709401263733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106912856604449806267509155 160369284906674709401263733)
      ·
        refine ⟨15034620460000754006368475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160369284906674709401263733 15034620460000754006368475)
        ·
          refine ⟨22551930690001131009552713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15034620460000754006368475 22551930690001131009552713)
          ·
            refine ⟨16913948017500848257164535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22551930690001131009552713 16913948017500848257164535)
            ·
              refine ⟨25370922026251272385746803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16913948017500848257164535 25370922026251272385746803)
              ·
                refine ⟨38056383039376908578620205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25370922026251272385746803 38056383039376908578620205)
                ·
                  refine ⟨14271143639766340716982577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38056383039376908578620205 14271143639766340716982577)
                  ·
                    refine ⟨10703357729824755537736933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14271143639766340716982577 10703357729824755537736933)
                    ·
                      refine ⟨2006879574342141663325675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10703357729824755537736933 2006879574342141663325675)
                      ·
                        rfl

theorem cell23_3908384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_3908384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908384 prefixEnd_3908384 := by exact prefixLift 3908384
  have htrace : WordTrace (prefixWord ++ tailWord_3908384) baseStart_3908384 baseEnd_3908384 := by
    simpa [prefixWord, tailWord_3908384, baseEnd_3908384] using wordTrace_append hprefix tailTrace_3908384
  have hstable : (prefixWord ++ tailWord_3908384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908384).length < 2 ^ (prefixWord ++ tailWord_3908384).sum := by decide
  have hdescent : baseEnd_3908384 < baseStart_3908384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908394 : List Nat := [3, 1, 4, 3, 12]
def baseStart_3908394 : Nat := 118140960795 + 3908394 * 2 ^ 59
def prefixEnd_3908394 : Nat := 4983230072969 + 3 ^ 40 * 3908394 * 2
def baseEnd_3908394 : Nat := 2752928270437155863101

theorem tailTrace_3908394 : CollatzResearch.WordTrace tailWord_3908394 prefixEnd_3908394 2752928270437155863101 := by
  unfold tailWord_3908394
  simp only [CollatzResearch.WordTrace]
  refine ⟨35637710050640878349469059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95033893468375675598584157 35637710050640878349469059)
  ·
    refine ⟨53456565075961317524203589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35637710050640878349469059 53456565075961317524203589)
    ·
      refine ⟨10023105951742747035788173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53456565075961317524203589 10023105951742747035788173)
      ·
        refine ⟨3758664731903530138420565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10023105951742747035788173 3758664731903530138420565)
        ·
          refine ⟨2752928270437155863101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3758664731903530138420565 2752928270437155863101)
          ·
            rfl

theorem cell23_3908394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 12].length) (baseStart_3908394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908394 prefixEnd_3908394 := by exact prefixLift 3908394
  have htrace : WordTrace (prefixWord ++ tailWord_3908394) baseStart_3908394 baseEnd_3908394 := by
    simpa [prefixWord, tailWord_3908394, baseEnd_3908394] using wordTrace_append hprefix tailTrace_3908394
  have hstable : (prefixWord ++ tailWord_3908394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908394).length < 2 ^ (prefixWord ++ tailWord_3908394).sum := by decide
  have hdescent : baseEnd_3908394 < baseStart_3908394 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908398 : List Nat := [4, 1, 3, 2, 1, 1, 1, 4, 2, 4]
def baseStart_3908398 : Nat := 118140960795 + 3908398 * 2 ^ 59
def prefixEnd_3908398 : Nat := 4983230072969 + 3 ^ 40 * 3908398 * 2
def baseEnd_3908398 : Nat := 668962254357101536183537

theorem tailTrace_3908398 : CollatzResearch.WordTrace tailWord_3908398 prefixEnd_3908398 668962254357101536183537 := by
  unfold tailWord_3908398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17818873261818627760127731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95033990729699348054014565 17818873261818627760127731)
  ·
    refine ⟨26728309892727941640191597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17818873261818627760127731 26728309892727941640191597)
    ·
      refine ⟨10023116209772978115071849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26728309892727941640191597 10023116209772978115071849)
      ·
        refine ⟨7517337157329733586303887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10023116209772978115071849 7517337157329733586303887)
        ·
          refine ⟨11276005735994600379455831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7517337157329733586303887 11276005735994600379455831)
          ·
            refine ⟨16914008603991900569183747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11276005735994600379455831 16914008603991900569183747)
            ·
              refine ⟨25371012905987850853775621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16914008603991900569183747 25371012905987850853775621)
              ·
                refine ⟨4757064919872722035082929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25371012905987850853775621 4757064919872722035082929)
                ·
                  refine ⟨3567798689904541526312197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4757064919872722035082929 3567798689904541526312197)
                  ·
                    refine ⟨668962254357101536183537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3567798689904541526312197 668962254357101536183537)
                    ·
                      rfl

theorem cell23_3908398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_3908398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908398 prefixEnd_3908398 := by exact prefixLift 3908398
  have htrace : WordTrace (prefixWord ++ tailWord_3908398) baseStart_3908398 baseEnd_3908398 := by
    simpa [prefixWord, tailWord_3908398, baseEnd_3908398] using wordTrace_append hprefix tailTrace_3908398
  have hstable : (prefixWord ++ tailWord_3908398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908398).length < 2 ^ (prefixWord ++ tailWord_3908398).sum := by decide
  have hdescent : baseEnd_3908398 < baseStart_3908398 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908407 : List Nat := [1, 1, 3, 1, 2, 1, 3, 1, 1, 9]
def baseStart_3908407 : Nat := 118140960795 + 3908407 * 2 ^ 59
def prefixEnd_3908407 : Nat := 4983230072969 + 3 ^ 40 * 3908407 * 2
def baseEnd_3908407 : Nat := 668963794799065024446023

theorem tailTrace_3908407 : CollatzResearch.WordTrace tailWord_3908407 prefixEnd_3908407 668963794799065024446023 := by
  unfold tailWord_3908407
  simp only [CollatzResearch.WordTrace]
  refine ⟨142551314351516416618099475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95034209567677611078732983 142551314351516416618099475)
  ·
    refine ⟨213826971527274624927149213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142551314351516416618099475 213826971527274624927149213)
    ·
      refine ⟨80185114322727984347680955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213826971527274624927149213 80185114322727984347680955)
      ·
        refine ⟨120277671484091976521521433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80185114322727984347680955 120277671484091976521521433)
        ·
          refine ⟨90208253613068982391141075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120277671484091976521521433 90208253613068982391141075)
          ·
            refine ⟨135312380419603473586711613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90208253613068982391141075 135312380419603473586711613)
            ·
              refine ⟨50742142657351302595016855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135312380419603473586711613 50742142657351302595016855)
              ·
                refine ⟨76113213986026953892525283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50742142657351302595016855 76113213986026953892525283)
                ·
                  refine ⟨114169820979040430838787925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76113213986026953892525283 114169820979040430838787925)
                  ·
                    refine ⟨668963794799065024446023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 114169820979040430838787925 668963794799065024446023)
                    ·
                      rfl

theorem cell23_3908407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_3908407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908407 prefixEnd_3908407 := by exact prefixLift 3908407
  have htrace : WordTrace (prefixWord ++ tailWord_3908407) baseStart_3908407 baseEnd_3908407 := by
    simpa [prefixWord, tailWord_3908407, baseEnd_3908407] using wordTrace_append hprefix tailTrace_3908407
  have hstable : (prefixWord ++ tailWord_3908407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908407).length < 2 ^ (prefixWord ++ tailWord_3908407).sum := by decide
  have hdescent : baseEnd_3908407 < baseStart_3908407 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908434 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_3908434 : Nat := 118140960795 + 3908434 * 2 ^ 59
def prefixEnd_3908434 : Nat := 4983230072969 + 3 ^ 40 * 3908434 * 2
def baseEnd_3908434 : Nat := 2006905248374866467700445

theorem tailTrace_3908434 : CollatzResearch.WordTrace tailWord_3908434 prefixEnd_3908434 2006905248374866467700445 := by
  unfold tailWord_3908434
  simp only [CollatzResearch.WordTrace]
  refine ⟨35638074780604650057333089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95034866081612400152888237 35638074780604650057333089)
  ·
    refine ⟨26728556085453487542999817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35638074780604650057333089 26728556085453487542999817)
    ·
      refine ⟨20046417064090115657249863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26728556085453487542999817 20046417064090115657249863)
      ·
        refine ⟨30069625596135173485874795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20046417064090115657249863 30069625596135173485874795)
        ·
          refine ⟨45104438394202760228812193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30069625596135173485874795 45104438394202760228812193)
          ·
            refine ⟨33828328795652070171609145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45104438394202760228812193 33828328795652070171609145)
            ·
              refine ⟨25371246596739052628706859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33828328795652070171609145 25371246596739052628706859)
              ·
                refine ⟨38056869895108578943060289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25371246596739052628706859 38056869895108578943060289)
                ·
                  refine ⟨28542652421331434207295217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38056869895108578943060289 28542652421331434207295217)
                  ·
                    refine ⟨21406989315998575655471413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28542652421331434207295217 21406989315998575655471413)
                    ·
                      refine ⟨2006905248374866467700445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21406989315998575655471413 2006905248374866467700445)
                      ·
                        rfl

theorem cell23_3908434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_3908434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908434 prefixEnd_3908434 := by exact prefixLift 3908434
  have htrace : WordTrace (prefixWord ++ tailWord_3908434) baseStart_3908434 baseEnd_3908434 := by
    simpa [prefixWord, tailWord_3908434, baseEnd_3908434] using wordTrace_append hprefix tailTrace_3908434
  have hstable : (prefixWord ++ tailWord_3908434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908434).length < 2 ^ (prefixWord ++ tailWord_3908434).sum := by decide
  have hdescent : baseEnd_3908434 < baseStart_3908434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908448 : List Nat := [2, 1, 1, 3, 3, 1, 3, 3, 1, 3, 2]
def baseStart_3908448 : Nat := 118140960795 + 3908448 * 2 ^ 59
def prefixEnd_3908448 : Nat := 4983230072969 + 3 ^ 40 * 3908448 * 2
def baseEnd_3908448 : Nat := 2006912437104029412925381

theorem tailTrace_3908448 : CollatzResearch.WordTrace tailWord_3908448 prefixEnd_3908448 2006912437104029412925381 := by
  unfold tailWord_3908448
  simp only [CollatzResearch.WordTrace]
  refine ⟨71276404872183940310170999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95035206496245253746894665 71276404872183940310170999)
  ·
    refine ⟨106914607308275910465256499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71276404872183940310170999 106914607308275910465256499)
    ·
      refine ⟨160371910962413865697884749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106914607308275910465256499 160371910962413865697884749)
      ·
        refine ⟨60139466610905199636706781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160371910962413865697884749 60139466610905199636706781)
        ·
          refine ⟨22552299979089449863765043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60139466610905199636706781 22552299979089449863765043)
          ·
            refine ⟨33828449968634174795647565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22552299979089449863765043 33828449968634174795647565)
            ·
              refine ⟨12685668738237815548367837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33828449968634174795647565 12685668738237815548367837)
              ·
                refine ⟨4757125776839180830637939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12685668738237815548367837 4757125776839180830637939)
                ·
                  refine ⟨7135688665258771245956909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757125776839180830637939 7135688665258771245956909)
                  ·
                    refine ⟨2675883249472039217233841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7135688665258771245956909 2675883249472039217233841)
                    ·
                      refine ⟨2006912437104029412925381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675883249472039217233841 2006912437104029412925381)
                      ·
                        rfl

theorem cell23_3908448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 3, 1, 3, 2].length) (baseStart_3908448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908448 prefixEnd_3908448 := by exact prefixLift 3908448
  have htrace : WordTrace (prefixWord ++ tailWord_3908448) baseStart_3908448 baseEnd_3908448 := by
    simpa [prefixWord, tailWord_3908448, baseEnd_3908448] using wordTrace_append hprefix tailTrace_3908448
  have hstable : (prefixWord ++ tailWord_3908448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908448).length < 2 ^ (prefixWord ++ tailWord_3908448).sum := by decide
  have hdescent : baseEnd_3908448 < baseStart_3908448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908455 : List Nat := [1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_3908455 : Nat := 118140960795 + 3908455 * 2 ^ 59
def prefixEnd_3908455 : Nat := 4983230072969 + 3 ^ 40 * 3908455 * 2
def baseEnd_3908455 : Nat := 2006916031468610885537849

theorem tailTrace_3908455 : CollatzResearch.WordTrace tailWord_3908455 prefixEnd_3908455 2006916031468610885537849 := by
  unfold tailWord_3908455
  simp only [CollatzResearch.WordTrace]
  refine ⟨142553065055342520815846819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95035376703561680543897879 142553065055342520815846819)
  ·
    refine ⟨213829597583013781223770229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142553065055342520815846819 213829597583013781223770229)
    ·
      refine ⟨20046524773407541989728459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213829597583013781223770229 20046524773407541989728459)
      ·
        refine ⟨30069787160111312984592689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20046524773407541989728459 30069787160111312984592689)
        ·
          refine ⟨22552340370083484738444517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30069787160111312984592689 22552340370083484738444517)
          ·
            refine ⟨4228563819390653388458347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22552340370083484738444517 4228563819390653388458347)
            ·
              refine ⟨6342845729085980082687521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4228563819390653388458347 6342845729085980082687521)
              ·
                refine ⟨4757134296814485062015641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6342845729085980082687521 4757134296814485062015641)
                ·
                  refine ⟨3567850722610863796511731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4757134296814485062015641 3567850722610863796511731)
                  ·
                    refine ⟨5351776083916295694767597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3567850722610863796511731 5351776083916295694767597)
                    ·
                      refine ⟨2006916031468610885537849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5351776083916295694767597 2006916031468610885537849)
                      ·
                        rfl

theorem cell23_3908455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_3908455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908455 prefixEnd_3908455 := by exact prefixLift 3908455
  have htrace : WordTrace (prefixWord ++ tailWord_3908455) baseStart_3908455 baseEnd_3908455 := by
    simpa [prefixWord, tailWord_3908455, baseEnd_3908455] using wordTrace_append hprefix tailTrace_3908455
  have hstable : (prefixWord ++ tailWord_3908455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908455).length < 2 ^ (prefixWord ++ tailWord_3908455).sum := by decide
  have hdescent : baseEnd_3908455 < baseStart_3908455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908464 : List Nat := [2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 3]
def baseStart_3908464 : Nat := 118140960795 + 3908464 * 2 ^ 59
def prefixEnd_3908464 : Nat := 4983230072969 + 3 ^ 40 * 3908464 * 2
def baseEnd_3908464 : Nat := 2006920652794501350325307

theorem tailTrace_3908464 : CollatzResearch.WordTrace tailWord_3908464 prefixEnd_3908464 2006920652794501350325307 := by
  unfold tailWord_3908464
  simp only [CollatzResearch.WordTrace]
  refine ⟨71276696656154957676462223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95035595541539943568616297 71276696656154957676462223)
  ·
    refine ⟨106915044984232436514693335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71276696656154957676462223 106915044984232436514693335)
    ·
      refine ⟨160372567476348654772040003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106915044984232436514693335 160372567476348654772040003)
      ·
        refine ⟨240558851214522982158060005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160372567476348654772040003 240558851214522982158060005)
        ·
          refine ⟨45104784602723059154636251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240558851214522982158060005 45104784602723059154636251)
          ·
            refine ⟨67657176904084588731954377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45104784602723059154636251 67657176904084588731954377)
            ·
              refine ⟨50742882678063441548965783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67657176904084588731954377 50742882678063441548965783)
              ·
                refine ⟨76114324017095162323448675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50742882678063441548965783 76114324017095162323448675)
                ·
                  refine ⟨114171486025642743485173013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76114324017095162323448675 114171486025642743485173013)
                  ·
                    refine ⟨5351788407452003600867485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114171486025642743485173013 5351788407452003600867485)
                    ·
                      refine ⟨2006920652794501350325307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5351788407452003600867485 2006920652794501350325307)
                      ·
                        rfl

theorem cell23_3908464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_3908464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908464 prefixEnd_3908464 := by exact prefixLift 3908464
  have htrace : WordTrace (prefixWord ++ tailWord_3908464) baseStart_3908464 baseEnd_3908464 := by
    simpa [prefixWord, tailWord_3908464, baseEnd_3908464] using wordTrace_append hprefix tailTrace_3908464
  have hstable : (prefixWord ++ tailWord_3908464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908464).length < 2 ^ (prefixWord ++ tailWord_3908464).sum := by decide
  have hdescent : baseEnd_3908464 < baseStart_3908464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908498 : List Nat := [3, 2, 3, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3908498 : Nat := 118140960795 + 3908498 * 2 ^ 59
def prefixEnd_3908498 : Nat := 4983230072969 + 3 ^ 40 * 3908498 * 2
def baseEnd_3908498 : Nat := 2006938111136754217300151

theorem tailTrace_3908498 : CollatzResearch.WordTrace tailWord_3908498 prefixEnd_3908498 2006938111136754217300151 := by
  unfold tailWord_3908498
  simp only [CollatzResearch.WordTrace]
  refine ⟨35638658348546684789915537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95036422262791159439774765 35638658348546684789915537)
  ·
    refine ⟨26728993761410013592436653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35638658348546684789915537 26728993761410013592436653)
    ·
      refine ⟨10023372660528755097163745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26728993761410013592436653 10023372660528755097163745)
      ·
        refine ⟨7517529495396566322872809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10023372660528755097163745 7517529495396566322872809)
        ·
          refine ⟨5638147121547424742154607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7517529495396566322872809 5638147121547424742154607)
          ·
            refine ⟨8457220682321137113231911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638147121547424742154607 8457220682321137113231911)
            ·
              refine ⟨12685831023481705669847867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457220682321137113231911 12685831023481705669847867)
              ·
                refine ⟨19028746535222558504771801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12685831023481705669847867 19028746535222558504771801)
                ·
                  refine ⟨14271559901416918878578851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19028746535222558504771801 14271559901416918878578851)
                  ·
                    refine ⟨21407339852125378317868277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14271559901416918878578851 21407339852125378317868277)
                    ·
                      refine ⟨2006938111136754217300151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21407339852125378317868277 2006938111136754217300151)
                      ·
                        rfl

theorem cell23_3908498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3908498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908498 prefixEnd_3908498 := by exact prefixLift 3908498
  have htrace : WordTrace (prefixWord ++ tailWord_3908498) baseStart_3908498 baseEnd_3908498 := by
    simpa [prefixWord, tailWord_3908498, baseEnd_3908498] using wordTrace_append hprefix tailTrace_3908498
  have hstable : (prefixWord ++ tailWord_3908498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908498).length < 2 ^ (prefixWord ++ tailWord_3908498).sum := by decide
  have hdescent : baseEnd_3908498 < baseStart_3908498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908521 : List Nat := [1, 2, 1, 1, 1, 1, 6, 1, 2, 5, 2]
def baseStart_3908521 : Nat := 118140960795 + 3908521 * 2 ^ 59
def prefixEnd_3908521 : Nat := 4983230072969 + 3 ^ 40 * 3908521 * 2
def baseEnd_3908521 : Nat := 2006949921191807627312545

theorem tailTrace_3908521 : CollatzResearch.WordTrace tailWord_3908521 prefixEnd_3908521 2006949921191807627312545 := by
  unfold tailWord_3908521
  simp only [CollatzResearch.WordTrace]
  refine ⟨142555472273103414087749417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95036981515402276058499611 142555472273103414087749417)
  ·
    refine ⟨106916604204827560565812063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142555472273103414087749417 106916604204827560565812063)
    ·
      refine ⟨160374906307241340848718095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106916604204827560565812063 160374906307241340848718095)
      ·
        refine ⟨240562359460862011273077143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160374906307241340848718095 240562359460862011273077143)
        ·
          refine ⟨360843539191293016909615715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240562359460862011273077143 360843539191293016909615715)
          ·
            refine ⟨541265308786939525364423573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 360843539191293016909615715 541265308786939525364423573)
            ·
              refine ⟨25371811349387790251457355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 541265308786939525364423573 25371811349387790251457355)
              ·
                refine ⟨38057717024081685377186033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25371811349387790251457355 38057717024081685377186033)
                ·
                  refine ⟨28543287768061264032889525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38057717024081685377186033 28543287768061264032889525)
                  ·
                    refine ⟨2675933228255743503083393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28543287768061264032889525 2675933228255743503083393)
                    ·
                      refine ⟨2006949921191807627312545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675933228255743503083393 2006949921191807627312545)
                      ·
                        rfl

theorem cell23_3908521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 5, 2].length) (baseStart_3908521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908521 prefixEnd_3908521 := by exact prefixLift 3908521
  have htrace : WordTrace (prefixWord ++ tailWord_3908521) baseStart_3908521 baseEnd_3908521 := by
    simpa [prefixWord, tailWord_3908521, baseEnd_3908521] using wordTrace_append hprefix tailTrace_3908521
  have hstable : (prefixWord ++ tailWord_3908521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908521).length < 2 ^ (prefixWord ++ tailWord_3908521).sum := by decide
  have hdescent : baseEnd_3908521 < baseStart_3908521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908524 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_3908524 : Nat := 118140960795 + 3908524 * 2 ^ 59
def prefixEnd_3908524 : Nat := 4983230072969 + 3 ^ 40 * 3908524 * 2
def baseEnd_3908524 : Nat := 2006951461633771115575031

theorem tailTrace_3908524 : CollatzResearch.WordTrace tailWord_3908524 prefixEnd_3908524 2006951461633771115575031 := by
  unfold tailWord_3908524
  simp only [CollatzResearch.WordTrace]
  refine ⟨71277790846046272800054313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95037054461395030400072417 71277790846046272800054313)
  ·
    refine ⟨53458343134534704600040735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71277790846046272800054313 53458343134534704600040735)
    ·
      refine ⟨80187514701802056900061103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53458343134534704600040735 80187514701802056900061103)
      ·
        refine ⟨120281272052703085350091655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80187514701802056900061103 120281272052703085350091655)
        ·
          refine ⟨180421908079054628025137483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120281272052703085350091655 180421908079054628025137483)
          ·
            refine ⟨270632862118581942037706225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180421908079054628025137483 270632862118581942037706225)
            ·
              refine ⟨202974646588936456528279669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270632862118581942037706225 202974646588936456528279669)
              ·
                refine ⟨19028873117712792799526219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 202974646588936456528279669 19028873117712792799526219)
                ·
                  refine ⟨28543309676569189199289329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19028873117712792799526219 28543309676569189199289329)
                  ·
                    refine ⟨21407482257426891899466997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28543309676569189199289329 21407482257426891899466997)
                    ·
                      refine ⟨2006951461633771115575031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21407482257426891899466997 2006951461633771115575031)
                      ·
                        rfl

theorem cell23_3908524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_3908524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908524 prefixEnd_3908524 := by exact prefixLift 3908524
  have htrace : WordTrace (prefixWord ++ tailWord_3908524) baseStart_3908524 baseEnd_3908524 := by
    simpa [prefixWord, tailWord_3908524, baseEnd_3908524] using wordTrace_append hprefix tailTrace_3908524
  have hstable : (prefixWord ++ tailWord_3908524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908524).length < 2 ^ (prefixWord ++ tailWord_3908524).sum := by decide
  have hdescent : baseEnd_3908524 < baseStart_3908524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908529 : List Nat := [1, 2, 2, 4, 3, 2, 2, 1, 2, 2, 2]
def baseStart_3908529 : Nat := 118140960795 + 3908529 * 2 ^ 59
def prefixEnd_3908529 : Nat := 4983230072969 + 3 ^ 40 * 3908529 * 2
def baseEnd_3908529 : Nat := 2006954029037043596012509

theorem tailTrace_3908529 : CollatzResearch.WordTrace tailWord_3908529 prefixEnd_3908529 2006954029037043596012509 := by
  unfold tailWord_3908529
  simp only [CollatzResearch.WordTrace]
  refine ⟨142555764057074431454040641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95037176038049620969360427 142555764057074431454040641)
  ·
    refine ⟨106916823042805823590530481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142555764057074431454040641 106916823042805823590530481)
    ·
      refine ⟨80187617282104367692897861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106916823042805823590530481 80187617282104367692897861)
      ·
        refine ⟨15035178240394568942418349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80187617282104367692897861 15035178240394568942418349)
        ·
          refine ⟨5638191840147963353406881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15035178240394568942418349 5638191840147963353406881)
          ·
            refine ⟨4228643880110972515055161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5638191840147963353406881 4228643880110972515055161)
            ·
              refine ⟨3171482910083229386291371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4228643880110972515055161 3171482910083229386291371)
              ·
                refine ⟨4757224365124844079437057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171482910083229386291371 4757224365124844079437057)
                ·
                  refine ⟨3567918273843633059577793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4757224365124844079437057 3567918273843633059577793)
                  ·
                    refine ⟨2675938705382724794683345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3567918273843633059577793 2675938705382724794683345)
                    ·
                      refine ⟨2006954029037043596012509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2675938705382724794683345 2006954029037043596012509)
                      ·
                        rfl

theorem cell23_3908529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_3908529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908529 prefixEnd_3908529 := by exact prefixLift 3908529
  have htrace : WordTrace (prefixWord ++ tailWord_3908529) baseStart_3908529 baseEnd_3908529 := by
    simpa [prefixWord, tailWord_3908529, baseEnd_3908529] using wordTrace_append hprefix tailTrace_3908529
  have hstable : (prefixWord ++ tailWord_3908529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908529).length < 2 ^ (prefixWord ++ tailWord_3908529).sum := by decide
  have hdescent : baseEnd_3908529 < baseStart_3908529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908551 : List Nat := [1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_3908551 : Nat := 118140960795 + 3908551 * 2 ^ 59
def prefixEnd_3908551 : Nat := 4983230072969 + 3 ^ 40 * 3908551 * 2
def baseEnd_3908551 : Nat := 2006965325611442509937407

theorem tailTrace_3908551 : CollatzResearch.WordTrace tailWord_3908551 prefixEnd_3908551 2006965325611442509937407 := by
  unfold tailWord_3908551
  simp only [CollatzResearch.WordTrace]
  refine ⟨142556566462994729211341507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95037710975329819474227671 142556566462994729211341507)
  ·
    refine ⟨213834849694492093817012261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142556566462994729211341507 213834849694492093817012261)
    ·
      refine ⟨40094034317717267590689799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213834849694492093817012261 40094034317717267590689799)
      ·
        refine ⟨60141051476575901386034699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40094034317717267590689799 60141051476575901386034699)
        ·
          refine ⟨90211577214863852079052049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60141051476575901386034699 90211577214863852079052049)
          ·
            refine ⟨67658682911147889059289037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90211577214863852079052049 67658682911147889059289037)
            ·
              refine ⟨25372006091680458397233389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67658682911147889059289037 25372006091680458397233389)
              ·
                refine ⟨9514502284380171898962521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25372006091680458397233389 9514502284380171898962521)
                ·
                  refine ⟨7135876713285128924221891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9514502284380171898962521 7135876713285128924221891)
                  ·
                    refine ⟨10703815069927693386332837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7135876713285128924221891 10703815069927693386332837)
                    ·
                      refine ⟨2006965325611442509937407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10703815069927693386332837 2006965325611442509937407)
                      ·
                        rfl

theorem cell23_3908551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_3908551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908551 prefixEnd_3908551 := by exact prefixLift 3908551
  have htrace : WordTrace (prefixWord ++ tailWord_3908551) baseStart_3908551 baseEnd_3908551 := by
    simpa [prefixWord, tailWord_3908551, baseEnd_3908551] using wordTrace_append hprefix tailTrace_3908551
  have hstable : (prefixWord ++ tailWord_3908551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908551).length < 2 ^ (prefixWord ++ tailWord_3908551).sum := by decide
  have hdescent : baseEnd_3908551 < baseStart_3908551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908591 : List Nat := [1, 1, 2, 1, 4, 3, 2, 3, 6]
def baseStart_3908591 : Nat := 118140960795 + 3908591 * 2 ^ 59
def prefixEnd_3908591 : Nat := 4983230072969 + 3 ^ 40 * 3908591 * 2
def baseEnd_3908591 : Nat := 222998429426402483715247

theorem tailTrace_3908591 : CollatzResearch.WordTrace tailWord_3908591 prefixEnd_3908591 222998429426402483715247 := by
  unfold tailWord_3908591
  simp only [CollatzResearch.WordTrace]
  refine ⟨142558025382849816042797627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95038683588566544028531751 142558025382849816042797627)
  ·
    refine ⟨213837038074274724064196441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142558025382849816042797627 213837038074274724064196441)
    ·
      refine ⟨160377778555706043048147331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213837038074274724064196441 160377778555706043048147331)
      ·
        refine ⟨240566667833559064572220997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160377778555706043048147331 240566667833559064572220997)
        ·
          refine ⟨45106250218792324607291437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240566667833559064572220997 45106250218792324607291437)
          ·
            refine ⟨16914843832047121727734289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45106250218792324607291437 16914843832047121727734289)
            ·
              refine ⟨12686132874035341295800717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16914843832047121727734289 12686132874035341295800717)
              ·
                refine ⟨4757299827763252985925269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12686132874035341295800717 4757299827763252985925269)
                ·
                  refine ⟨222998429426402483715247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4757299827763252985925269 222998429426402483715247)
                  ·
                    rfl

theorem cell23_3908591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 3, 6].length) (baseStart_3908591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908591 prefixEnd_3908591 := by exact prefixLift 3908591
  have htrace : WordTrace (prefixWord ++ tailWord_3908591) baseStart_3908591 baseEnd_3908591 := by
    simpa [prefixWord, tailWord_3908591, baseEnd_3908591] using wordTrace_append hprefix tailTrace_3908591
  have hstable : (prefixWord ++ tailWord_3908591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908591).length < 2 ^ (prefixWord ++ tailWord_3908591).sum := by decide
  have hdescent : baseEnd_3908591 < baseStart_3908591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908658 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2]
def baseStart_3908658 : Nat := 118140960795 + 3908658 * 2 ^ 59
def prefixEnd_3908658 : Nat := 4983230072969 + 3 ^ 40 * 3908658 * 2
def baseEnd_3908658 : Nat := 2007020268041473591299415

theorem tailTrace_3908658 : CollatzResearch.WordTrace tailWord_3908658 prefixEnd_3908658 2007020268041473591299415 := by
  unfold tailWord_3908658
  simp only [CollatzResearch.WordTrace]
  refine ⟨35640117268401771621371657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95040312715738057656991085 35640117268401771621371657)
  ·
    refine ⟨26730087951301328716028743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35640117268401771621371657 26730087951301328716028743)
    ·
      refine ⟨40095131926951993074043115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26730087951301328716028743 40095131926951993074043115)
      ·
        refine ⟨60142697890427989611064673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40095131926951993074043115 60142697890427989611064673)
        ·
          refine ⟨45107023417820992208298505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60142697890427989611064673 45107023417820992208298505)
          ·
            refine ⟨33830267563365744156223879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45107023417820992208298505 33830267563365744156223879)
            ·
              refine ⟨50745401345048616234335819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33830267563365744156223879 50745401345048616234335819)
              ·
                refine ⟨76118102017572924351503729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50745401345048616234335819 76118102017572924351503729)
                ·
                  refine ⟨57088576513179693263627797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76118102017572924351503729 57088576513179693263627797)
                  ·
                    refine ⟨2676027024055298121732553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 57088576513179693263627797 2676027024055298121732553)
                    ·
                      refine ⟨2007020268041473591299415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2676027024055298121732553 2007020268041473591299415)
                      ·
                        rfl

theorem cell23_3908658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_3908658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908658 prefixEnd_3908658 := by exact prefixLift 3908658
  have htrace : WordTrace (prefixWord ++ tailWord_3908658) baseStart_3908658 baseEnd_3908658 := by
    simpa [prefixWord, tailWord_3908658, baseEnd_3908658] using wordTrace_append hprefix tailTrace_3908658
  have hstable : (prefixWord ++ tailWord_3908658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908658).length < 2 ^ (prefixWord ++ tailWord_3908658).sum := by decide
  have hdescent : baseEnd_3908658 < baseStart_3908658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908661 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_3908661 : Nat := 118140960795 + 3908661 * 2 ^ 59
def prefixEnd_3908661 : Nat := 4983230072969 + 3 ^ 40 * 3908661 * 2
def baseEnd_3908661 : Nat := 2007021808483437079561901

theorem tailTrace_3908661 : CollatzResearch.WordTrace tailWord_3908661 prefixEnd_3908661 2007021808483437079561901 := by
  unfold tailWord_3908661
  simp only [CollatzResearch.WordTrace]
  refine ⟨142560578492596217997845837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95040385661730811998563891 142560578492596217997845837)
  ·
    refine ⟨53460216934723581749192189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142560578492596217997845837 53460216934723581749192189)
    ·
      refine ⟨20047581350521343155947071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53460216934723581749192189 20047581350521343155947071)
      ·
        refine ⟨30071372025782014733920607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20047581350521343155947071 30071372025782014733920607)
        ·
          refine ⟨45107058038673022100880911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30071372025782014733920607 45107058038673022100880911)
          ·
            refine ⟨67660587058009533151321367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45107058038673022100880911 67660587058009533151321367)
            ·
              refine ⟨101490880587014299726982051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67660587058009533151321367 101490880587014299726982051)
              ·
                refine ⟨152236320880521449590473077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101490880587014299726982051 152236320880521449590473077)
                ·
                  refine ⟨14272155082548885899106851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152236320880521449590473077 14272155082548885899106851)
                  ·
                    refine ⟨21408232623823328848660277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14272155082548885899106851 21408232623823328848660277)
                    ·
                      refine ⟨2007021808483437079561901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21408232623823328848660277 2007021808483437079561901)
                      ·
                        rfl

theorem cell23_3908661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_3908661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908661 prefixEnd_3908661 := by exact prefixLift 3908661
  have htrace : WordTrace (prefixWord ++ tailWord_3908661) baseStart_3908661 baseEnd_3908661 := by
    simpa [prefixWord, tailWord_3908661, baseEnd_3908661] using wordTrace_append hprefix tailTrace_3908661
  have hstable : (prefixWord ++ tailWord_3908661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908661).length < 2 ^ (prefixWord ++ tailWord_3908661).sum := by decide
  have hdescent : baseEnd_3908661 < baseStart_3908661 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908668 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 4, 4]
def baseStart_3908668 : Nat := 118140960795 + 3908668 * 2 ^ 59
def prefixEnd_3908668 : Nat := 4983230072969 + 3 ^ 40 * 3908668 * 2
def baseEnd_3908668 : Nat := 669008467616006184058123

theorem tailTrace_3908668 : CollatzResearch.WordTrace tailWord_3908668 prefixEnd_3908668 669008467616006184058123 := by
  unfold tailWord_3908668
  simp only [CollatzResearch.WordTrace]
  refine ⟨71280416901785429096675329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95040555869047238795567105 71280416901785429096675329)
  ·
    refine ⟨53460312676339071822506497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71280416901785429096675329 53460312676339071822506497)
    ·
      refine ⟨40095234507254303866879873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53460312676339071822506497 40095234507254303866879873)
      ·
        refine ⟨30071425880440727900159905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40095234507254303866879873 30071425880440727900159905)
        ·
          refine ⟨22553569410330545925119929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30071425880440727900159905 22553569410330545925119929)
          ·
            refine ⟨16915177057747909443839947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22553569410330545925119929 16915177057747909443839947)
            ·
              refine ⟨25372765586621864165759921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16915177057747909443839947 25372765586621864165759921)
              ·
                refine ⟨19029574189966398124319941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25372765586621864165759921 19029574189966398124319941)
                ·
                  refine ⟨3568045160618699648309989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19029574189966398124319941 3568045160618699648309989)
                  ·
                    refine ⟨669008467616006184058123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3568045160618699648309989 669008467616006184058123)
                    ·
                      rfl

theorem cell23_3908668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 4, 4].length) (baseStart_3908668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908668 prefixEnd_3908668 := by exact prefixLift 3908668
  have htrace : WordTrace (prefixWord ++ tailWord_3908668) baseStart_3908668 baseEnd_3908668 := by
    simpa [prefixWord, tailWord_3908668, baseEnd_3908668] using wordTrace_append hprefix tailTrace_3908668
  have hstable : (prefixWord ++ tailWord_3908668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908668).length < 2 ^ (prefixWord ++ tailWord_3908668).sum := by decide
  have hdescent : baseEnd_3908668 < baseStart_3908668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908669 : List Nat := [1, 4, 1, 3, 1, 4, 1, 3, 1, 1, 3]
def baseStart_3908669 : Nat := 118140960795 + 3908669 * 2 ^ 59
def prefixEnd_3908669 : Nat := 4983230072969 + 3 ^ 40 * 3908669 * 2
def baseEnd_3908669 : Nat := 2007025916328673048261865

theorem tailTrace_3908669 : CollatzResearch.WordTrace tailWord_3908669 prefixEnd_3908669 2007025916328673048261865 := by
  unfold tailWord_3908669
  simp only [CollatzResearch.WordTrace]
  refine ⟨142560870276567235364137061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95040580184378156909424707 142560870276567235364137061)
  ·
    refine ⟨26730163176856356630775699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142560870276567235364137061 26730163176856356630775699)
    ·
      refine ⟨40095244765284534946163549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26730163176856356630775699 40095244765284534946163549)
      ·
        refine ⟨15035716786981700604811331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40095244765284534946163549 15035716786981700604811331)
        ·
          refine ⟨22553575180472550907216997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15035716786981700604811331 22553575180472550907216997)
          ·
            refine ⟨4228795346338603295103187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22553575180472550907216997 4228795346338603295103187)
            ·
              refine ⟨6343193019507904942654781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4228795346338603295103187 6343193019507904942654781)
              ·
                refine ⟨2378697382315464353495543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6343193019507904942654781 2378697382315464353495543)
                ·
                  refine ⟨3568046073473196530243315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2378697382315464353495543 3568046073473196530243315)
                  ·
                    refine ⟨5352069110209794795364973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3568046073473196530243315 5352069110209794795364973)
                    ·
                      refine ⟨2007025916328673048261865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5352069110209794795364973 2007025916328673048261865)
                      ·
                        rfl

theorem cell23_3908669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_3908669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908669 prefixEnd_3908669 := by exact prefixLift 3908669
  have htrace : WordTrace (prefixWord ++ tailWord_3908669) baseStart_3908669 baseEnd_3908669 := by
    simpa [prefixWord, tailWord_3908669, baseEnd_3908669] using wordTrace_append hprefix tailTrace_3908669
  have hstable : (prefixWord ++ tailWord_3908669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908669).length < 2 ^ (prefixWord ++ tailWord_3908669).sum := by decide
  have hdescent : baseEnd_3908669 < baseStart_3908669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908671 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_3908671 : Nat := 118140960795 + 3908671 * 2 ^ 59
def prefixEnd_3908671 : Nat := 4983230072969 + 3 ^ 40 * 3908671 * 2
def baseEnd_3908671 : Nat := 2007026943289982040436855

theorem tailTrace_3908671 : CollatzResearch.WordTrace tailWord_3908671 prefixEnd_3908671 2007026943289982040436855 := by
  unfold tailWord_3908671
  simp only [CollatzResearch.WordTrace]
  refine ⟨142560943222559989705709867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95040628815039993137139911 142560943222559989705709867)
  ·
    refine ⟨213841414833839984558564801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142560943222559989705709867 213841414833839984558564801)
    ·
      refine ⟨160381061125379988418923601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213841414833839984558564801 160381061125379988418923601)
      ·
        refine ⟨120285795844034991314192701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160381061125379988418923601 120285795844034991314192701)
        ·
          refine ⟨45107173441513121742822263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120285795844034991314192701 45107173441513121742822263)
          ·
            refine ⟨67660760162269682614233395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45107173441513121742822263 67660760162269682614233395)
            ·
              refine ⟨101491140243404523921350093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67660760162269682614233395 101491140243404523921350093)
              ·
                refine ⟨38059177591276696470506285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101491140243404523921350093 38059177591276696470506285)
                ·
                  refine ⟨14272191596728761176439857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38059177591276696470506285 14272191596728761176439857)
                  ·
                    refine ⟨10704143697546570882329893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14272191596728761176439857 10704143697546570882329893)
                    ·
                      refine ⟨2007026943289982040436855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10704143697546570882329893 2007026943289982040436855)
                      ·
                        rfl

theorem cell23_3908671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_3908671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908671 prefixEnd_3908671 := by exact prefixLift 3908671
  have htrace : WordTrace (prefixWord ++ tailWord_3908671) baseStart_3908671 baseEnd_3908671 := by
    simpa [prefixWord, tailWord_3908671, baseEnd_3908671] using wordTrace_append hprefix tailTrace_3908671
  have hstable : (prefixWord ++ tailWord_3908671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908671).length < 2 ^ (prefixWord ++ tailWord_3908671).sum := by decide
  have hdescent : baseEnd_3908671 < baseStart_3908671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908685 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3908685 : Nat := 118140960795 + 3908685 * 2 ^ 59
def prefixEnd_3908685 : Nat := 4983230072969 + 3 ^ 40 * 3908685 * 2
def baseEnd_3908685 : Nat := 669011377339714995220597

theorem tailTrace_3908685 : CollatzResearch.WordTrace tailWord_3908685 prefixEnd_3908685 669011377339714995220597 := by
  unfold tailWord_3908685
  simp only [CollatzResearch.WordTrace]
  refine ⟨142561453844509270096719509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95040969229672846731146339 142561453844509270096719509)
  ·
    refine ⟨6682568148961372035783727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142561453844509270096719509 6682568148961372035783727)
    ·
      refine ⟨10023852223442058053675591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6682568148961372035783727 10023852223442058053675591)
      ·
        refine ⟨15035778335163087080513387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10023852223442058053675591 15035778335163087080513387)
        ·
          refine ⟨22553667502744630620770081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15035778335163087080513387 22553667502744630620770081)
          ·
            refine ⟨16915250627058472965577561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22553667502744630620770081 16915250627058472965577561)
            ·
              refine ⟨12686437970293854724183171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16915250627058472965577561 12686437970293854724183171)
              ·
                refine ⟨19029656955440782086274757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12686437970293854724183171 19029656955440782086274757)
                ·
                  refine ⟨3568060679145146641176517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19029656955440782086274757 3568060679145146641176517)
                  ·
                    refine ⟨669011377339714995220597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3568060679145146641176517 669011377339714995220597)
                    ·
                      rfl

theorem cell23_3908685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3908685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908685 prefixEnd_3908685 := by exact prefixLift 3908685
  have htrace : WordTrace (prefixWord ++ tailWord_3908685) baseStart_3908685 baseEnd_3908685 := by
    simpa [prefixWord, tailWord_3908685, baseEnd_3908685] using wordTrace_append hprefix tailTrace_3908685
  have hstable : (prefixWord ++ tailWord_3908685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908685).length < 2 ^ (prefixWord ++ tailWord_3908685).sum := by decide
  have hdescent : baseEnd_3908685 < baseStart_3908685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908692 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 3, 2, 2]
def baseStart_3908692 : Nat := 118140960795 + 3908692 * 2 ^ 59
def prefixEnd_3908692 : Nat := 4983230072969 + 3 ^ 40 * 3908692 * 2
def baseEnd_3908692 : Nat := 2007037726383726458274259

theorem tailTrace_3908692 : CollatzResearch.WordTrace tailWord_3908692 prefixEnd_3908692 2007037726383726458274259 := by
  unfold tailWord_3908692
  simp only [CollatzResearch.WordTrace]
  refine ⟨71280854577741955146112165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95041139436989273528149553 71280854577741955146112165)
  ·
    refine ⟨13365160233326616589896031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71280854577741955146112165 13365160233326616589896031)
    ·
      refine ⟨20047740349989924884844047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13365160233326616589896031 20047740349989924884844047)
      ·
        refine ⟨30071610524984887327266071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20047740349989924884844047 30071610524984887327266071)
        ·
          refine ⟨45107415787477330990899107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30071610524984887327266071 45107415787477330990899107)
          ·
            refine ⟨67661123681215996486348661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45107415787477330990899107 67661123681215996486348661)
            ·
              refine ⟨6343230345113999670595187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67661123681215996486348661 6343230345113999670595187)
              ·
                refine ⟨9514845517670999505892781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6343230345113999670595187 9514845517670999505892781)
                ·
                  refine ⟨3568067069126624814709793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9514845517670999505892781 3568067069126624814709793)
                  ·
                    refine ⟨2676050301844968611032345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3568067069126624814709793 2676050301844968611032345)
                    ·
                      refine ⟨2007037726383726458274259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2676050301844968611032345 2007037726383726458274259)
                      ·
                        rfl

theorem cell23_3908692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_3908692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908692 prefixEnd_3908692 := by exact prefixLift 3908692
  have htrace : WordTrace (prefixWord ++ tailWord_3908692) baseStart_3908692 baseEnd_3908692 := by
    simpa [prefixWord, tailWord_3908692, baseEnd_3908692] using wordTrace_append hprefix tailTrace_3908692
  have hstable : (prefixWord ++ tailWord_3908692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908692).length < 2 ^ (prefixWord ++ tailWord_3908692).sum := by decide
  have hdescent : baseEnd_3908692 < baseStart_3908692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908708 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_3908708 : Nat := 118140960795 + 3908708 * 2 ^ 59
def prefixEnd_3908708 : Nat := 4983230072969 + 3 ^ 40 * 3908708 * 2
def baseEnd_3908708 : Nat := 2007045942074198395674185

theorem tailTrace_3908708 : CollatzResearch.WordTrace tailWord_3908708 prefixEnd_3908708 2007045942074198395674185 := by
  unfold tailWord_3908708
  simp only [CollatzResearch.WordTrace]
  refine ⟨71281146361712972512403389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95041528482283963349871185 71281146361712972512403389)
  ·
    refine ⟨26730429885642364692151271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71281146361712972512403389 26730429885642364692151271)
    ·
      refine ⟨40095644828463547038226907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26730429885642364692151271 40095644828463547038226907)
      ·
        refine ⟨60143467242695320557340361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40095644828463547038226907 60143467242695320557340361)
        ·
          refine ⟨45107600432021490418005271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60143467242695320557340361 45107600432021490418005271)
          ·
            refine ⟨67661400648032235627007907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45107600432021490418005271 67661400648032235627007907)
            ·
              refine ⟨101492100972048353440511861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67661400648032235627007907 101492100972048353440511861)
              ·
                refine ⟨9514884466129533135047987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101492100972048353440511861 9514884466129533135047987)
                ·
                  refine ⟨14272326699194299702571981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9514884466129533135047987 14272326699194299702571981)
                  ·
                    refine ⟨5352122512197862388464493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14272326699194299702571981 5352122512197862388464493)
                    ·
                      refine ⟨2007045942074198395674185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5352122512197862388464493 2007045942074198395674185)
                      ·
                        rfl

theorem cell23_3908708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_3908708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908708 prefixEnd_3908708 := by exact prefixLift 3908708
  have htrace : WordTrace (prefixWord ++ tailWord_3908708) baseStart_3908708 baseEnd_3908708 := by
    simpa [prefixWord, tailWord_3908708, baseEnd_3908708] using wordTrace_append hprefix tailTrace_3908708
  have hstable : (prefixWord ++ tailWord_3908708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908708).length < 2 ^ (prefixWord ++ tailWord_3908708).sum := by decide
  have hdescent : baseEnd_3908708 < baseStart_3908708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908712 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_3908712 : Nat := 118140960795 + 3908712 * 2 ^ 59
def prefixEnd_3908712 : Nat := 4983230072969 + 3 ^ 40 * 3908712 * 2
def baseEnd_3908712 : Nat := 2007047995996816380024167

theorem tailTrace_3908712 : CollatzResearch.WordTrace tailWord_3908712 prefixEnd_3908712 2007047995996816380024167 := by
  unfold tailWord_3908712
  simp only [CollatzResearch.WordTrace]
  refine ⟨71281219307705726853976195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95041625743607635805301593 71281219307705726853976195)
  ·
    refine ⟨106921828961558590280964293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71281219307705726853976195 106921828961558590280964293)
    ·
      refine ⟨20047842930292235677680805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106921828961558590280964293 20047842930292235677680805)
      ·
        refine ⟨3758970549429794189565151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20047842930292235677680805 3758970549429794189565151)
        ·
          refine ⟨5638455824144691284347727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3758970549429794189565151 5638455824144691284347727)
          ·
            refine ⟨8457683736217036926521591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5638455824144691284347727 8457683736217036926521591)
            ·
              refine ⟨12686525604325555389782387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8457683736217036926521591 12686525604325555389782387)
              ·
                refine ⟨19029788406488333084673581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12686525604325555389782387 19029788406488333084673581)
                ·
                  refine ⟨7136170652433124906752593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19029788406488333084673581 7136170652433124906752593)
                  ·
                    refine ⟨5352127989324843680064445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7136170652433124906752593 5352127989324843680064445)
                    ·
                      refine ⟨2007047995996816380024167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5352127989324843680064445 2007047995996816380024167)
                      ·
                        rfl

theorem cell23_3908712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_3908712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908712 prefixEnd_3908712 := by exact prefixLift 3908712
  have htrace : WordTrace (prefixWord ++ tailWord_3908712) baseStart_3908712 baseEnd_3908712 := by
    simpa [prefixWord, tailWord_3908712, baseEnd_3908712] using wordTrace_append hprefix tailTrace_3908712
  have hstable : (prefixWord ++ tailWord_3908712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908712).length < 2 ^ (prefixWord ++ tailWord_3908712).sum := by decide
  have hdescent : baseEnd_3908712 < baseStart_3908712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908721 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_3908721 : Nat := 118140960795 + 3908721 * 2 ^ 59
def prefixEnd_3908721 : Nat := 4983230072969 + 3 ^ 40 * 3908721 * 2
def baseEnd_3908721 : Nat := 2007052617322706844811625

theorem tailTrace_3908721 : CollatzResearch.WordTrace tailWord_3908721 prefixEnd_3908721 2007052617322706844811625 := by
  unfold tailWord_3908721
  simp only [CollatzResearch.WordTrace]
  refine ⟨142562766872378848245030017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95041844581585898830020011 142562766872378848245030017)
  ·
    refine ⟨106922075154284136183772513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142562766872378848245030017 106922075154284136183772513)
    ·
      refine ⟨80191556365713102137829385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106922075154284136183772513 80191556365713102137829385)
      ·
        refine ⟨60143667274284826603372039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80191556365713102137829385 60143667274284826603372039)
        ·
          refine ⟨90215500911427239905058059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60143667274284826603372039 90215500911427239905058059)
          ·
            refine ⟨135323251367140859857587089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90215500911427239905058059 135323251367140859857587089)
            ·
              refine ⟨101492438525355644893190317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135323251367140859857587089 101492438525355644893190317)
              ·
                refine ⟨38059664447008366834946369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101492438525355644893190317 38059664447008366834946369)
                ·
                  refine ⟨28544748335256275126209777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38059664447008366834946369 28544748335256275126209777)
                  ·
                    refine ⟨21408561251442206344657333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28544748335256275126209777 21408561251442206344657333)
                    ·
                      refine ⟨2007052617322706844811625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21408561251442206344657333 2007052617322706844811625)
                      ·
                        rfl

theorem cell23_3908721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_3908721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908721 prefixEnd_3908721 := by exact prefixLift 3908721
  have htrace : WordTrace (prefixWord ++ tailWord_3908721) baseStart_3908721 baseEnd_3908721 := by
    simpa [prefixWord, tailWord_3908721, baseEnd_3908721] using wordTrace_append hprefix tailTrace_3908721
  have hstable : (prefixWord ++ tailWord_3908721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908721).length < 2 ^ (prefixWord ++ tailWord_3908721).sum := by decide
  have hdescent : baseEnd_3908721 < baseStart_3908721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908731 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 4]
def baseStart_3908731 : Nat := 118140960795 + 3908731 * 2 ^ 59
def prefixEnd_3908731 : Nat := 4983230072969 + 3 ^ 40 * 3908731 * 2
def baseEnd_3908731 : Nat := 2007057752129251805686579

theorem tailTrace_3908731 : CollatzResearch.WordTrace tailWord_3908731 prefixEnd_3908731 2007057752129251805686579 := by
  unfold tailWord_3908731
  simp only [CollatzResearch.WordTrace]
  refine ⟨142563131602342619952894047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95042087734895079968596031 142563131602342619952894047)
  ·
    refine ⟨213844697403513929929341071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142563131602342619952894047 213844697403513929929341071)
    ·
      refine ⟨320767046105270894894011607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213844697403513929929341071 320767046105270894894011607)
      ·
        refine ⟨481150569157906342341017411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320767046105270894894011607 481150569157906342341017411)
        ·
          refine ⟨721725853736859513511526117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481150569157906342341017411 721725853736859513511526117)
          ·
            refine ⟨135323597575661158783411147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 721725853736859513511526117 135323597575661158783411147)
            ·
              refine ⟨202985396363491738175116721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135323597575661158783411147 202985396363491738175116721)
              ·
                refine ⟨152239047272618803631337541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 202985396363491738175116721 152239047272618803631337541)
                ·
                  refine ⟨28544821363616025680875789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152239047272618803631337541 28544821363616025680875789)
                  ·
                    refine ⟨10704308011356009630328421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28544821363616025680875789 10704308011356009630328421)
                    ·
                      refine ⟨2007057752129251805686579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10704308011356009630328421 2007057752129251805686579)
                      ·
                        rfl

theorem cell23_3908731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 4].length) (baseStart_3908731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908731 prefixEnd_3908731 := by exact prefixLift 3908731
  have htrace : WordTrace (prefixWord ++ tailWord_3908731) baseStart_3908731 baseEnd_3908731 := by
    simpa [prefixWord, tailWord_3908731, baseEnd_3908731] using wordTrace_append hprefix tailTrace_3908731
  have hstable : (prefixWord ++ tailWord_3908731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908731).length < 2 ^ (prefixWord ++ tailWord_3908731).sum := by decide
  have hdescent : baseEnd_3908731 < baseStart_3908731 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908768 : List Nat := [2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 3]
def baseStart_3908768 : Nat := 118140960795 + 3908768 * 2 ^ 59
def prefixEnd_3908768 : Nat := 4983230072969 + 3 ^ 40 * 3908768 * 2
def baseEnd_3908768 : Nat := 2007076750913468160923909

theorem tailTrace_3908768 : CollatzResearch.WordTrace tailWord_3908768 prefixEnd_3908768 2007076750913468160923909 := by
  unfold tailWord_3908768
  simp only [CollatzResearch.WordTrace]
  refine ⟨71282240551604287635995479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95042987402139050181327305 71282240551604287635995479)
  ·
    refine ⟨106923360827406431453993219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71282240551604287635995479 106923360827406431453993219)
    ·
      refine ⟨160385041241109647180989829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106923360827406431453993219 160385041241109647180989829)
      ·
        refine ⟨30072195232708058846435593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160385041241109647180989829 30072195232708058846435593)
        ·
          refine ⟨22554146424531044134826695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30072195232708058846435593 22554146424531044134826695)
          ·
            refine ⟨33831219636796566202240043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22554146424531044134826695 33831219636796566202240043)
            ·
              refine ⟨50746829455194849303360065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33831219636796566202240043 50746829455194849303360065)
              ·
                refine ⟨38060122091396136977520049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50746829455194849303360065 38060122091396136977520049)
                ·
                  refine ⟨28545091568547102733140037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38060122091396136977520049 28545091568547102733140037)
                  ·
                    refine ⟨5352204669102581762463757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28545091568547102733140037 5352204669102581762463757)
                    ·
                      refine ⟨2007076750913468160923909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5352204669102581762463757 2007076750913468160923909)
                      ·
                        rfl

theorem cell23_3908768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_3908768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908768 prefixEnd_3908768 := by exact prefixLift 3908768
  have htrace : WordTrace (prefixWord ++ tailWord_3908768) baseStart_3908768 baseEnd_3908768 := by
    simpa [prefixWord, tailWord_3908768, baseEnd_3908768] using wordTrace_append hprefix tailTrace_3908768
  have hstable : (prefixWord ++ tailWord_3908768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908768).length < 2 ^ (prefixWord ++ tailWord_3908768).sum := by decide
  have hdescent : baseEnd_3908768 < baseStart_3908768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908818 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_3908818 : Nat := 118140960795 + 3908818 * 2 ^ 59
def prefixEnd_3908818 : Nat := 4983230072969 + 3 ^ 40 * 3908818 * 2
def baseEnd_3908818 : Nat := 669034141648730988432893

theorem tailTrace_3908818 : CollatzResearch.WordTrace tailWord_3908818 prefixEnd_3908818 669034141648730988432893 := by
  unfold tailWord_3908818
  simp only [CollatzResearch.WordTrace]
  refine ⟨35641576188256858452827777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95044203168684955874207405 35641576188256858452827777)
  ·
    refine ⟨26731182141192643839620833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35641576188256858452827777 26731182141192643839620833)
    ·
      refine ⟨20048386605894482879715625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26731182141192643839620833 20048386605894482879715625)
      ·
        refine ⟨15036289954420862159786719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20048386605894482879715625 15036289954420862159786719)
        ·
          refine ⟨22554434931631293239680079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15036289954420862159786719 22554434931631293239680079)
          ·
            refine ⟨33831652397446939859520119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22554434931631293239680079 33831652397446939859520119)
            ·
              refine ⟨50747478596170409789280179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33831652397446939859520119 50747478596170409789280179)
              ·
                refine ⟨76121217894255614683920269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50747478596170409789280179 76121217894255614683920269)
                ·
                  refine ⟨28545456710345855506470101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76121217894255614683920269 28545456710345855506470101)
                  ·
                    refine ⟨669034141648730988432893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28545456710345855506470101 669034141648730988432893)
                    ·
                      rfl

theorem cell23_3908818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_3908818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908818 prefixEnd_3908818 := by exact prefixLift 3908818
  have htrace : WordTrace (prefixWord ++ tailWord_3908818) baseStart_3908818 baseEnd_3908818 := by
    simpa [prefixWord, tailWord_3908818, baseEnd_3908818] using wordTrace_append hprefix tailTrace_3908818
  have hstable : (prefixWord ++ tailWord_3908818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908818).length < 2 ^ (prefixWord ++ tailWord_3908818).sum := by decide
  have hdescent : baseEnd_3908818 < baseStart_3908818 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908839 : List Nat := [1, 1, 5, 3, 2, 2, 1, 3, 5]
def baseStart_3908839 : Nat := 118140960795 + 3908839 * 2 ^ 59
def prefixEnd_3908839 : Nat := 4983230072969 + 3 ^ 40 * 3908839 * 2
def baseEnd_3908839 : Nat := 223012578671104153681787

theorem tailTrace_3908839 : CollatzResearch.WordTrace tailWord_3908839 prefixEnd_3908839 223012578671104153681787 := by
  unfold tailWord_3908839
  simp only [CollatzResearch.WordTrace]
  refine ⟨142567070685951354397825571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95044713790634236265217047 142567070685951354397825571)
  ·
    refine ⟨213850606028927031596738357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142567070685951354397825571 213850606028927031596738357)
    ·
      refine ⟨20048494315211909212194221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213850606028927031596738357 20048494315211909212194221)
      ·
        refine ⟨7518185368204465954572833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20048494315211909212194221 7518185368204465954572833)
        ·
          refine ⟨5638639026153349465929625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7518185368204465954572833 5638639026153349465929625)
          ·
            refine ⟨4228979269615012099447219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5638639026153349465929625 4228979269615012099447219)
            ·
              refine ⟨6343468904422518149170829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4228979269615012099447219 6343468904422518149170829)
              ·
                refine ⟨2378800839158444305939061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6343468904422518149170829 2378800839158444305939061)
                ·
                  refine ⟨223012578671104153681787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2378800839158444305939061 223012578671104153681787)
                  ·
                    rfl

theorem cell23_3908839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 5].length) (baseStart_3908839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908839 prefixEnd_3908839 := by exact prefixLift 3908839
  have htrace : WordTrace (prefixWord ++ tailWord_3908839) baseStart_3908839 baseEnd_3908839 := by
    simpa [prefixWord, tailWord_3908839, baseEnd_3908839] using wordTrace_append hprefix tailTrace_3908839
  have hstable : (prefixWord ++ tailWord_3908839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908839).length < 2 ^ (prefixWord ++ tailWord_3908839).sum := by decide
  have hdescent : baseEnd_3908839 < baseStart_3908839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908909 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3908909 : Nat := 118140960795 + 3908909 * 2 ^ 59
def prefixEnd_3908909 : Nat := 4983230072969 + 3 ^ 40 * 3908909 * 2
def baseEnd_3908909 : Nat := 2007149151685752109260761

theorem tailTrace_3908909 : CollatzResearch.WordTrace tailWord_3908909 prefixEnd_3908909 2007149151685752109260761 := by
  unfold tailWord_3908909
  simp only [CollatzResearch.WordTrace]
  refine ⟨142569623795697756352873781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95046415863798504235249187 142569623795697756352873781)
  ·
    refine ⟨13365902230846664658081917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142569623795697756352873781 13365902230846664658081917)
    ·
      refine ⟨5012213336567499246780719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13365902230846664658081917 5012213336567499246780719)
      ·
        refine ⟨7518320004851248870171079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5012213336567499246780719 7518320004851248870171079)
        ·
          refine ⟨11277480007276873305256619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7518320004851248870171079 11277480007276873305256619)
          ·
            refine ⟨16916220010915309957884929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11277480007276873305256619 16916220010915309957884929)
            ·
              refine ⟨12687165008186482468413697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16916220010915309957884929 12687165008186482468413697)
              ·
                refine ⟨9515373756139861851310273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12687165008186482468413697 9515373756139861851310273)
                ·
                  refine ⟨7136530317104896388482705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9515373756139861851310273 7136530317104896388482705)
                  ·
                    refine ⟨5352397737828672291362029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7136530317104896388482705 5352397737828672291362029)
                    ·
                      refine ⟨2007149151685752109260761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5352397737828672291362029 2007149151685752109260761)
                      ·
                        rfl

theorem cell23_3908909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3908909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908909 prefixEnd_3908909 := by exact prefixLift 3908909
  have htrace : WordTrace (prefixWord ++ tailWord_3908909) baseStart_3908909 baseEnd_3908909 := by
    simpa [prefixWord, tailWord_3908909, baseEnd_3908909] using wordTrace_append hprefix tailTrace_3908909
  have hstable : (prefixWord ++ tailWord_3908909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908909).length < 2 ^ (prefixWord ++ tailWord_3908909).sum := by decide
  have hdescent : baseEnd_3908909 < baseStart_3908909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908922 : List Nat := [3, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3]
def baseStart_3908922 : Nat := 118140960795 + 3908922 * 2 ^ 59
def prefixEnd_3908922 : Nat := 4983230072969 + 3 ^ 40 * 3908922 * 2
def baseEnd_3908922 : Nat := 2007155826934260558398201

theorem tailTrace_3908922 : CollatzResearch.WordTrace tailWord_3908922 prefixEnd_3908922 2007155826934260558398201 := by
  unfold tailWord_3908922
  simp only [CollatzResearch.WordTrace]
  refine ⟨35642524486162664893274255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95046731963100439715398013 35642524486162664893274255)
  ·
    refine ⟨53463786729243997339911383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35642524486162664893274255 53463786729243997339911383)
    ·
      refine ⟨80195680093865996009867075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53463786729243997339911383 80195680093865996009867075)
      ·
        refine ⟨120293520140798994014800613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80195680093865996009867075 120293520140798994014800613)
        ·
          refine ⟨22555035026399811377775115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120293520140798994014800613 22555035026399811377775115)
          ·
            refine ⟨33832552539599717066662673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22555035026399811377775115 33832552539599717066662673)
            ·
              refine ⟨25374414404699787799997005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33832552539599717066662673 25374414404699787799997005)
              ·
                refine ⟨9515405401762420424998877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25374414404699787799997005 9515405401762420424998877)
                ·
                  refine ⟨3568277025660907659374579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9515405401762420424998877 3568277025660907659374579)
                  ·
                    refine ⟨5352415538491361489061869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3568277025660907659374579 5352415538491361489061869)
                    ·
                      refine ⟨2007155826934260558398201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5352415538491361489061869 2007155826934260558398201)
                      ·
                        rfl

theorem cell23_3908922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3].length) (baseStart_3908922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908922 prefixEnd_3908922 := by exact prefixLift 3908922
  have htrace : WordTrace (prefixWord ++ tailWord_3908922) baseStart_3908922 baseEnd_3908922 := by
    simpa [prefixWord, tailWord_3908922, baseEnd_3908922] using wordTrace_append hprefix tailTrace_3908922
  have hstable : (prefixWord ++ tailWord_3908922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908922).length < 2 ^ (prefixWord ++ tailWord_3908922).sum := by decide
  have hdescent : baseEnd_3908922 < baseStart_3908922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908945 : List Nat := [1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_3908945 : Nat := 118140960795 + 3908945 * 2 ^ 59
def prefixEnd_3908945 : Nat := 4983230072969 + 3 ^ 40 * 3908945 * 2
def baseEnd_3908945 : Nat := 2007167636989313968410595

theorem tailTrace_3908945 : CollatzResearch.WordTrace tailWord_3908945 prefixEnd_3908945 2007167636989313968410595 := by
  unfold tailWord_3908945
  simp only [CollatzResearch.WordTrace]
  refine ⟨142570936823567334501184289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95047291215711556334122859 142570936823567334501184289)
  ·
    refine ⟨106928202617675500875888217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142570936823567334501184289 106928202617675500875888217)
    ·
      refine ⟨80196151963256625656916163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106928202617675500875888217 80196151963256625656916163)
      ·
        refine ⟨120294227944884938485374245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80196151963256625656916163 120294227944884938485374245)
        ·
          refine ⟨22555167739665925966007671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120294227944884938485374245 22555167739665925966007671)
          ·
            refine ⟨33832751609498888949011507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22555167739665925966007671 33832751609498888949011507)
            ·
              refine ⟨50749127414248333423517261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33832751609498888949011507 50749127414248333423517261)
              ·
                refine ⟨19030922780343125033818973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50749127414248333423517261 19030922780343125033818973)
                ·
                  refine ⟨7136596042628671887682115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19030922780343125033818973 7136596042628671887682115)
                  ·
                    refine ⟨10704894063943007831523173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7136596042628671887682115 10704894063943007831523173)
                    ·
                      refine ⟨2007167636989313968410595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10704894063943007831523173 2007167636989313968410595)
                      ·
                        rfl

theorem cell23_3908945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_3908945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908945 prefixEnd_3908945 := by exact prefixLift 3908945
  have htrace : WordTrace (prefixWord ++ tailWord_3908945) baseStart_3908945 baseEnd_3908945 := by
    simpa [prefixWord, tailWord_3908945, baseEnd_3908945] using wordTrace_append hprefix tailTrace_3908945
  have hstable : (prefixWord ++ tailWord_3908945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908945).length < 2 ^ (prefixWord ++ tailWord_3908945).sum := by decide
  have hdescent : baseEnd_3908945 < baseStart_3908945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908949 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_3908949 : Nat := 118140960795 + 3908949 * 2 ^ 59
def prefixEnd_3908949 : Nat := 4983230072969 + 3 ^ 40 * 3908949 * 2
def baseEnd_3908949 : Nat := 2007169690911931952760577

theorem tailTrace_3908949 : CollatzResearch.WordTrace tailWord_3908949 prefixEnd_3908949 2007169690911931952760577 := by
  unfold tailWord_3908949
  simp only [CollatzResearch.WordTrace]
  refine ⟨142571082715552843184329901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95047388477035228789553267 142571082715552843184329901)
  ·
    refine ⟨53464156018332316194123713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142571082715552843184329901 53464156018332316194123713)
    ·
      refine ⟨40098117013749237145592785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53464156018332316194123713 40098117013749237145592785)
      ·
        refine ⟨30073587760311927859194589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40098117013749237145592785 30073587760311927859194589)
        ·
          refine ⟨11277595410116972947197971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30073587760311927859194589 11277595410116972947197971)
          ·
            refine ⟨16916393115175459420796957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11277595410116972947197971 16916393115175459420796957)
            ·
              refine ⟨6343647418190797282798859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16916393115175459420796957 6343647418190797282798859)
              ·
                refine ⟨9515471127286195924198289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6343647418190797282798859 9515471127286195924198289)
                ·
                  refine ⟨7136603345464646943148717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9515471127286195924198289 7136603345464646943148717)
                  ·
                    refine ⟨2676226254549242603680769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7136603345464646943148717 2676226254549242603680769)
                    ·
                      refine ⟨2007169690911931952760577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2676226254549242603680769 2007169690911931952760577)
                      ·
                        rfl

theorem cell23_3908949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_3908949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908949 prefixEnd_3908949 := by exact prefixLift 3908949
  have htrace : WordTrace (prefixWord ++ tailWord_3908949) baseStart_3908949 baseEnd_3908949 := by
    simpa [prefixWord, tailWord_3908949, baseEnd_3908949] using wordTrace_append hprefix tailTrace_3908949
  have hstable : (prefixWord ++ tailWord_3908949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908949).length < 2 ^ (prefixWord ++ tailWord_3908949).sum := by decide
  have hdescent : baseEnd_3908949 < baseStart_3908949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908965 : List Nat := [1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_3908965 : Nat := 118140960795 + 3908965 * 2 ^ 59
def prefixEnd_3908965 : Nat := 4983230072969 + 3 ^ 40 * 3908965 * 2
def baseEnd_3908965 : Nat := 2007177906602403890160503

theorem tailTrace_3908965 : CollatzResearch.WordTrace tailWord_3908965 prefixEnd_3908965 2007177906602403890160503 := by
  unfold tailWord_3908965
  simp only [CollatzResearch.WordTrace]
  refine ⟨142571666283494877916912349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95047777522329918611274899 142571666283494877916912349)
  ·
    refine ⟨53464374856310579218842131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142571666283494877916912349 53464374856310579218842131)
    ·
      refine ⟨80196562284465868828263197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53464374856310579218842131 80196562284465868828263197)
      ·
        refine ⟨30073710856674700810598699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80196562284465868828263197 30073710856674700810598699)
        ·
          refine ⟨45110566285012051215898049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30073710856674700810598699 45110566285012051215898049)
          ·
            refine ⟨33832924713759038411923537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45110566285012051215898049 33832924713759038411923537)
            ·
              refine ⟨25374693535319278808942653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33832924713759038411923537 25374693535319278808942653)
              ·
                refine ⟨9515510075744729553353495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25374693535319278808942653 9515510075744729553353495)
                ·
                  refine ⟨14273265113617094330030243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9515510075744729553353495 14273265113617094330030243)
                  ·
                    refine ⟨21409897670425641495045365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14273265113617094330030243 21409897670425641495045365)
                    ·
                      refine ⟨2007177906602403890160503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21409897670425641495045365 2007177906602403890160503)
                      ·
                        rfl

theorem cell23_3908965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_3908965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908965 prefixEnd_3908965 := by exact prefixLift 3908965
  have htrace : WordTrace (prefixWord ++ tailWord_3908965) baseStart_3908965 baseEnd_3908965 := by
    simpa [prefixWord, tailWord_3908965, baseEnd_3908965] using wordTrace_append hprefix tailTrace_3908965
  have hstable : (prefixWord ++ tailWord_3908965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908965).length < 2 ^ (prefixWord ++ tailWord_3908965).sum := by decide
  have hdescent : baseEnd_3908965 < baseStart_3908965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908972 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 4, 4]
def baseStart_3908972 : Nat := 118140960795 + 3908972 * 2 ^ 59
def prefixEnd_3908972 : Nat := 4983230072969 + 3 ^ 40 * 3908972 * 2
def baseEnd_3908972 : Nat := 669060500322328454257657

theorem tailTrace_3908972 : CollatzResearch.WordTrace tailWord_3908972 prefixEnd_3908972 669060500322328454257657 := by
  unfold tailWord_3908972
  simp only [CollatzResearch.WordTrace]
  refine ⟨71285960797234759056208585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95047947729646345408278113 71285960797234759056208585)
  ·
    refine ⟨53464470597926069292156439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71285960797234759056208585 53464470597926069292156439)
    ·
      refine ⟨80196705896889103938234659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53464470597926069292156439 80196705896889103938234659)
      ·
        refine ⟨120295058845333655907351989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80196705896889103938234659 120295058845333655907351989)
        ·
          refine ⟨11277661766750030241314249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120295058845333655907351989 11277661766750030241314249)
          ·
            refine ⟨8458246325062522680985687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11277661766750030241314249 8458246325062522680985687)
            ·
              refine ⟨12687369487593784021478531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458246325062522680985687 12687369487593784021478531)
              ·
                refine ⟨19031054231390676032217797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12687369487593784021478531 19031054231390676032217797)
                ·
                  refine ⟨3568322668385751756040837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19031054231390676032217797 3568322668385751756040837)
                  ·
                    refine ⟨669060500322328454257657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3568322668385751756040837 669060500322328454257657)
                    ·
                      rfl

theorem cell23_3908972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 4].length) (baseStart_3908972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908972 prefixEnd_3908972 := by exact prefixLift 3908972
  have htrace : WordTrace (prefixWord ++ tailWord_3908972) baseStart_3908972 baseEnd_3908972 := by
    simpa [prefixWord, tailWord_3908972, baseEnd_3908972] using wordTrace_append hprefix tailTrace_3908972
  have hstable : (prefixWord ++ tailWord_3908972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908972).length < 2 ^ (prefixWord ++ tailWord_3908972).sum := by decide
  have hdescent : baseEnd_3908972 < baseStart_3908972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908989 : List Nat := [1, 4, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_3908989 : Nat := 118140960795 + 3908989 * 2 ^ 59
def prefixEnd_3908989 : Nat := 4983230072969 + 3 ^ 40 * 3908989 * 2
def baseEnd_3908989 : Nat := 669063410046037265420131

theorem tailTrace_3908989 : CollatzResearch.WordTrace tailWord_3908989 prefixEnd_3908989 669063410046037265420131 := by
  unfold tailWord_3908989
  simp only [CollatzResearch.WordTrace]
  refine ⟨142572541635407930015786021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95048361090271953343857347 142572541635407930015786021)
  ·
    refine ⟨26732351556638986877959879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142572541635407930015786021 26732351556638986877959879)
    ·
      refine ⟨40098527334958480316939819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26732351556638986877959879 40098527334958480316939819)
      ·
        refine ⟨60147791002437720475409729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40098527334958480316939819 60147791002437720475409729)
        ·
          refine ⟨45110843251828290356557297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60147791002437720475409729 45110843251828290356557297)
          ·
            refine ⟨33833132438871217767417973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45110843251828290356557297 33833132438871217767417973)
            ·
              refine ⟨3171856166144176665695435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33833132438871217767417973 3171856166144176665695435)
              ·
                refine ⟨4757784249216264998543153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3171856166144176665695435 4757784249216264998543153)
                ·
                  refine ⟨3568338186912198748907365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4757784249216264998543153 3568338186912198748907365)
                  ·
                    refine ⟨669063410046037265420131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3568338186912198748907365 669063410046037265420131)
                    ·
                      rfl

theorem cell23_3908989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_3908989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908989 prefixEnd_3908989 := by exact prefixLift 3908989
  have htrace : WordTrace (prefixWord ++ tailWord_3908989) baseStart_3908989 baseEnd_3908989 := by
    simpa [prefixWord, tailWord_3908989, baseEnd_3908989] using wordTrace_append hprefix tailTrace_3908989
  have hstable : (prefixWord ++ tailWord_3908989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908989).length < 2 ^ (prefixWord ++ tailWord_3908989).sum := by decide
  have hdescent : baseEnd_3908989 < baseStart_3908989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3908999 : List Nat := [1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_3908999 : Nat := 118140960795 + 3908999 * 2 ^ 59
def prefixEnd_3908999 : Nat := 4983230072969 + 3 ^ 40 * 3908999 * 2
def baseEnd_3908999 : Nat := 2007195364944656757135347

theorem tailTrace_3908999 : CollatzResearch.WordTrace tailWord_3908999 prefixEnd_3908999 2007195364944656757135347 := by
  unfold tailWord_3908999
  simp only [CollatzResearch.WordTrace]
  refine ⟨142572906365371701723650051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95048604243581134482433367 142572906365371701723650051)
  ·
    refine ⟨213859359548057552585475077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142572906365371701723650051 213859359548057552585475077)
    ·
      refine ⟨40098629915260791109776577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 213859359548057552585475077 40098629915260791109776577)
      ·
        refine ⟨30073972436445593332332433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40098629915260791109776577 30073972436445593332332433)
        ·
          refine ⟨22555479327334194999249325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30073972436445593332332433 22555479327334194999249325)
          ·
            refine ⟨8458304747750323124718497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22555479327334194999249325 8458304747750323124718497)
            ·
              refine ⟨6343728560812742343538873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8458304747750323124718497 6343728560812742343538873)
              ·
                refine ⟨4757796420609556757654155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6343728560812742343538873 4757796420609556757654155)
                ·
                  refine ⟨7136694630914335136481233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4757796420609556757654155 7136694630914335136481233)
                  ·
                    refine ⟨5352520973185751352360925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7136694630914335136481233 5352520973185751352360925)
                    ·
                      refine ⟨2007195364944656757135347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5352520973185751352360925 2007195364944656757135347)
                      ·
                        rfl

theorem cell23_3908999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_3908999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3908999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3908999 prefixEnd_3908999 := by exact prefixLift 3908999
  have htrace : WordTrace (prefixWord ++ tailWord_3908999) baseStart_3908999 baseEnd_3908999 := by
    simpa [prefixWord, tailWord_3908999, baseEnd_3908999] using wordTrace_append hprefix tailTrace_3908999
  have hstable : (prefixWord ++ tailWord_3908999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3908999).length < 2 ^ (prefixWord ++ tailWord_3908999).sum := by decide
  have hdescent : baseEnd_3908999 < baseStart_3908999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3908999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909065 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_3909065 : Nat := 118140960795 + 3909065 * 2 ^ 59
def prefixEnd_3909065 : Nat := 4983230072969 + 3 ^ 40 * 3909065 * 2
def baseEnd_3909065 : Nat := 2007229254667853498910043

theorem tailTrace_3909065 : CollatzResearch.WordTrace tailWord_3909065 prefixEnd_3909065 2007229254667853498910043 := by
  unfold tailWord_3909065
  simp only [CollatzResearch.WordTrace]
  refine ⟨142575313583132594995552649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95050209055421729997035099 142575313583132594995552649)
  ·
    refine ⟨106931485187349446246664487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142575313583132594995552649 106931485187349446246664487)
    ·
      refine ⟨160397227781024169369996731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106931485187349446246664487 160397227781024169369996731)
      ·
        refine ⟨240595841671536254054995097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160397227781024169369996731 240595841671536254054995097)
        ·
          refine ⟨180446881253652190541246323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240595841671536254054995097 180446881253652190541246323)
          ·
            refine ⟨270670321880478285811869485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180446881253652190541246323 270670321880478285811869485)
            ·
              refine ⟨101501370705179357179451057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270670321880478285811869485 101501370705179357179451057)
              ·
                refine ⟨76126028028884517884588293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101501370705179357179451057 76126028028884517884588293)
                ·
                  refine ⟨14273630255415847103360305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76126028028884517884588293 14273630255415847103360305)
                  ·
                    refine ⟨10705222691561885327520229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14273630255415847103360305 10705222691561885327520229)
                    ·
                      refine ⟨2007229254667853498910043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10705222691561885327520229 2007229254667853498910043)
                      ·
                        rfl

theorem cell23_3909065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_3909065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909065 prefixEnd_3909065 := by exact prefixLift 3909065
  have htrace : WordTrace (prefixWord ++ tailWord_3909065) baseStart_3909065 baseEnd_3909065 := by
    simpa [prefixWord, tailWord_3909065, baseEnd_3909065] using wordTrace_append hprefix tailTrace_3909065
  have hstable : (prefixWord ++ tailWord_3909065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909065).length < 2 ^ (prefixWord ++ tailWord_3909065).sum := by decide
  have hdescent : baseEnd_3909065 < baseStart_3909065 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909109 : List Nat := [1, 3, 5, 1, 1, 2, 1, 2, 7]
def baseStart_3909109 : Nat := 118140960795 + 3909109 * 2 ^ 59
def prefixEnd_3909109 : Nat := 4983230072969 + 3 ^ 40 * 3909109 * 2
def baseEnd_3909109 : Nat := 223027983090739036306649

theorem tailTrace_3909109 : CollatzResearch.WordTrace tailWord_3909109 prefixEnd_3909109 223027983090739036306649 := by
  unfold tailWord_3909109
  simp only [CollatzResearch.WordTrace]
  refine ⟨142576918394973190510154381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95051278929982127006769587 142576918394973190510154381)
  ·
    refine ⟨53466344398114946441307893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142576918394973190510154381 53466344398114946441307893)
    ·
      refine ⟨5012469787323276228872615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53466344398114946441307893 5012469787323276228872615)
      ·
        refine ⟨7518704680984914343308923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5012469787323276228872615 7518704680984914343308923)
        ·
          refine ⟨11278057021477371514963385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7518704680984914343308923 11278057021477371514963385)
          ·
            refine ⟨8458542766108028636222539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11278057021477371514963385 8458542766108028636222539)
            ·
              refine ⟨12687814149162042954333809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8458542766108028636222539 12687814149162042954333809)
              ·
                refine ⟨9515860611871532215750357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12687814149162042954333809 9515860611871532215750357)
                ·
                  refine ⟨223027983090739036306649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9515860611871532215750357 223027983090739036306649)
                  ·
                    rfl

theorem cell23_3909109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_3909109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909109 prefixEnd_3909109 := by exact prefixLift 3909109
  have htrace : WordTrace (prefixWord ++ tailWord_3909109) baseStart_3909109 baseEnd_3909109 := by
    simpa [prefixWord, tailWord_3909109, baseEnd_3909109] using wordTrace_append hprefix tailTrace_3909109
  have hstable : (prefixWord ++ tailWord_3909109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909109).length < 2 ^ (prefixWord ++ tailWord_3909109).sum := by decide
  have hdescent : baseEnd_3909109 < baseStart_3909109 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909276 : List Nat := [2, 2, 3, 2, 3, 1, 2, 1, 1, 6]
def baseStart_3909276 : Nat := 118140960795 + 3909276 * 2 ^ 59
def prefixEnd_3909276 : Nat := 4983230072969 + 3 ^ 40 * 3909276 * 2
def baseEnd_3909276 : Nat := 669112533028650724457191

theorem tailTrace_3909276 : CollatzResearch.WordTrace tailWord_3909276 prefixEnd_3909276 669112533028650724457191 := by
  unfold tailWord_3909276
  simp only [CollatzResearch.WordTrace]
  refine ⟨71291504692684089015741841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95055339590245452020989121 71291504692684089015741841)
  ·
    refine ⟨53468628519513066761806381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71291504692684089015741841 53468628519513066761806381)
    ·
      refine ⟨20050735694817400035677393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53468628519513066761806381 20050735694817400035677393)
      ·
        refine ⟨15038051771113050026758045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20050735694817400035677393 15038051771113050026758045)
        ·
          refine ⟨5639269414167393760034267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15038051771113050026758045 5639269414167393760034267)
          ·
            refine ⟨8458904121251090640051401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639269414167393760034267 8458904121251090640051401)
            ·
              refine ⟨6344178090938317980038551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8458904121251090640051401 6344178090938317980038551)
              ·
                refine ⟨9516267136407476970057827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6344178090938317980038551 9516267136407476970057827)
                ·
                  refine ⟨14274400704611215455086741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9516267136407476970057827 14274400704611215455086741)
                  ·
                    refine ⟨669112533028650724457191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14274400704611215455086741 669112533028650724457191)
                    ·
                      rfl

theorem cell23_3909276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 1, 6].length) (baseStart_3909276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909276 prefixEnd_3909276 := by exact prefixLift 3909276
  have htrace : WordTrace (prefixWord ++ tailWord_3909276) baseStart_3909276 baseEnd_3909276 := by
    simpa [prefixWord, tailWord_3909276, baseEnd_3909276] using wordTrace_append hprefix tailTrace_3909276
  have hstable : (prefixWord ++ tailWord_3909276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909276).length < 2 ^ (prefixWord ++ tailWord_3909276).sum := by decide
  have hdescent : baseEnd_3909276 < baseStart_3909276 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909299 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 3]
def baseStart_3909299 : Nat := 118140960795 + 3909299 * 2 ^ 59
def prefixEnd_3909299 : Nat := 4983230072969 + 3 ^ 40 * 3909299 * 2
def baseEnd_3909299 : Nat := 2007349409141005583383967

theorem tailTrace_3909299 : CollatzResearch.WordTrace tailWord_3909299 prefixEnd_3909299 2007349409141005583383967 := by
  unfold tailWord_3909299
  simp only [CollatzResearch.WordTrace]
  refine ⟨142583848264284852959570951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95055898842856568639713967 142583848264284852959570951)
  ·
    refine ⟨213875772396427279439356427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142583848264284852959570951 213875772396427279439356427)
    ·
      refine ⟨320813658594640919159034641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213875772396427279439356427 320813658594640919159034641)
      ·
        refine ⟨240610243945980689369275981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320813658594640919159034641 240610243945980689369275981)
        ·
          refine ⟨90228841479742758513478493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240610243945980689369275981 90228841479742758513478493)
          ·
            refine ⟨33835815554903534442554435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90228841479742758513478493 33835815554903534442554435)
            ·
              refine ⟨50753723332355301663831653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33835815554903534442554435 50753723332355301663831653)
              ·
                refine ⟨9516323124816619061968435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50753723332355301663831653 9516323124816619061968435)
                ·
                  refine ⟨14274484687224928592952653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9516323124816619061968435 14274484687224928592952653)
                  ·
                    refine ⟨5352931757709348222357245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14274484687224928592952653 5352931757709348222357245)
                    ·
                      refine ⟨2007349409141005583383967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5352931757709348222357245 2007349409141005583383967)
                      ·
                        rfl

theorem cell23_3909299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_3909299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909299 prefixEnd_3909299 := by exact prefixLift 3909299
  have htrace : WordTrace (prefixWord ++ tailWord_3909299) baseStart_3909299 baseEnd_3909299 := by
    simpa [prefixWord, tailWord_3909299, baseEnd_3909299] using wordTrace_append hprefix tailTrace_3909299
  have hstable : (prefixWord ++ tailWord_3909299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909299).length < 2 ^ (prefixWord ++ tailWord_3909299).sum := by decide
  have hdescent : baseEnd_3909299 < baseStart_3909299 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909303 : List Nat := [1, 1, 3, 1, 5, 1, 4, 1, 1, 2, 3]
def baseStart_3909303 : Nat := 118140960795 + 3909303 * 2 ^ 59
def prefixEnd_3909303 : Nat := 4983230072969 + 3 ^ 40 * 3909303 * 2
def baseEnd_3909303 : Nat := 2007351463063623567733949

theorem tailTrace_3909303 : CollatzResearch.WordTrace tailWord_3909303 prefixEnd_3909303 2007351463063623567733949 := by
  unfold tailWord_3909303
  simp only [CollatzResearch.WordTrace]
  refine ⟨142583994156270361642716563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95055996104180241095144375 142583994156270361642716563)
  ·
    refine ⟨213875991234405542464074845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142583994156270361642716563 213875991234405542464074845)
    ·
      refine ⟨80203496712902078424028067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213875991234405542464074845 80203496712902078424028067)
      ·
        refine ⟨120305245069353117636042101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80203496712902078424028067 120305245069353117636042101)
        ·
          refine ⟨11278616725251854778378947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120305245069353117636042101 11278616725251854778378947)
          ·
            refine ⟨16917925087877782167568421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11278616725251854778378947 16917925087877782167568421)
            ·
              refine ⟨3172110953977084156419079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16917925087877782167568421 3172110953977084156419079)
              ·
                refine ⟨4758166430965626234628619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172110953977084156419079 4758166430965626234628619)
                ·
                  refine ⟨7137249646448439351942929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758166430965626234628619 7137249646448439351942929)
                  ·
                    refine ⟨5352937234836329513957197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7137249646448439351942929 5352937234836329513957197)
                    ·
                      refine ⟨2007351463063623567733949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5352937234836329513957197 2007351463063623567733949)
                      ·
                        rfl

theorem cell23_3909303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 4, 1, 1, 2, 3].length) (baseStart_3909303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909303 prefixEnd_3909303 := by exact prefixLift 3909303
  have htrace : WordTrace (prefixWord ++ tailWord_3909303) baseStart_3909303 baseEnd_3909303 := by
    simpa [prefixWord, tailWord_3909303, baseEnd_3909303] using wordTrace_append hprefix tailTrace_3909303
  have hstable : (prefixWord ++ tailWord_3909303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909303).length < 2 ^ (prefixWord ++ tailWord_3909303).sum := by decide
  have hdescent : baseEnd_3909303 < baseStart_3909303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909340 : List Nat := [2, 2, 5, 1, 3, 1, 2, 7]
def baseStart_3909340 : Nat := 118140960795 + 3909340 * 2 ^ 59
def prefixEnd_3909340 : Nat := 4983230072969 + 3 ^ 40 * 3909340 * 2
def baseEnd_3909340 : Nat := 74347054142512589739677

theorem tailTrace_3909340 : CollatzResearch.WordTrace tailWord_3909340 prefixEnd_3909340 74347054142512589739677 := by
  unfold tailWord_3909340
  simp only [CollatzResearch.WordTrace]
  refine ⟨71292671828568158480906737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95056895771424211307875649 71292671828568158480906737)
  ·
    refine ⟨53469503871426118860680053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71292671828568158480906737 53469503871426118860680053)
    ·
      refine ⟨5012765987946198643188755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53469503871426118860680053 5012765987946198643188755)
      ·
        refine ⟨7519148981919297964783133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5012765987946198643188755 7519148981919297964783133)
        ·
          refine ⟨2819680868219736736793675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7519148981919297964783133 2819680868219736736793675)
          ·
            refine ⟨4229521302329605105190513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819680868219736736793675 4229521302329605105190513)
            ·
              refine ⟨3172140976747203828892885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4229521302329605105190513 3172140976747203828892885)
              ·
                refine ⟨74347054142512589739677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3172140976747203828892885 74347054142512589739677)
                ·
                  rfl

theorem cell23_3909340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 7].length) (baseStart_3909340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909340 prefixEnd_3909340 := by exact prefixLift 3909340
  have htrace : WordTrace (prefixWord ++ tailWord_3909340) baseStart_3909340 baseEnd_3909340 := by
    simpa [prefixWord, tailWord_3909340, baseEnd_3909340] using wordTrace_append hprefix tailTrace_3909340
  have hstable : (prefixWord ++ tailWord_3909340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909340).length < 2 ^ (prefixWord ++ tailWord_3909340).sum := by decide
  have hdescent : baseEnd_3909340 < baseStart_3909340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909343 : List Nat := [1, 1, 2, 3, 2, 2, 4, 2, 1, 3, 2]
def baseStart_3909343 : Nat := 118140960795 + 3909343 * 2 ^ 59
def prefixEnd_3909343 : Nat := 4983230072969 + 3 ^ 40 * 3909343 * 2
def baseEnd_3909343 : Nat := 2007372002289803411233765

theorem tailTrace_3909343 : CollatzResearch.WordTrace tailWord_3909343 prefixEnd_3909343 2007372002289803411233765 := by
  unfold tailWord_3909343
  simp only [CollatzResearch.WordTrace]
  refine ⟨142585453076125448474172683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95056968717416965649448455 142585453076125448474172683)
  ·
    refine ⟨213878179614188172711259025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142585453076125448474172683 213878179614188172711259025)
    ·
      refine ⟨160408634710641129533444269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213878179614188172711259025 160408634710641129533444269)
      ·
        refine ⟨60153238016490423575041601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160408634710641129533444269 60153238016490423575041601)
        ·
          refine ⟨45114928512367817681281201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60153238016490423575041601 45114928512367817681281201)
          ·
            refine ⟨33836196384275863260960901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45114928512367817681281201 33836196384275863260960901)
            ·
              refine ⟨6344286822051724361430169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33836196384275863260960901 6344286822051724361430169)
              ·
                refine ⟨4758215116538793271072627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6344286822051724361430169 4758215116538793271072627)
                ·
                  refine ⟨7137322674808189906608941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758215116538793271072627 7137322674808189906608941)
                  ·
                    refine ⟨2676496003053071214978353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7137322674808189906608941 2676496003053071214978353)
                    ·
                      refine ⟨2007372002289803411233765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2676496003053071214978353 2007372002289803411233765)
                      ·
                        rfl

theorem cell23_3909343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_3909343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909343 prefixEnd_3909343 := by exact prefixLift 3909343
  have htrace : WordTrace (prefixWord ++ tailWord_3909343) baseStart_3909343 baseEnd_3909343 := by
    simpa [prefixWord, tailWord_3909343, baseEnd_3909343] using wordTrace_append hprefix tailTrace_3909343
  have hstable : (prefixWord ++ tailWord_3909343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909343).length < 2 ^ (prefixWord ++ tailWord_3909343).sum := by decide
  have hdescent : baseEnd_3909343 < baseStart_3909343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909351 : List Nat := [1, 1, 5, 4, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3909351 : Nat := 118140960795 + 3909351 * 2 ^ 59
def prefixEnd_3909351 : Nat := 4983230072969 + 3 ^ 40 * 3909351 * 2
def baseEnd_3909351 : Nat := 2007376110135039379933729

theorem tailTrace_3909351 : CollatzResearch.WordTrace tailWord_3909351 prefixEnd_3909351 2007376110135039379933729 := by
  unfold tailWord_3909351
  simp only [CollatzResearch.WordTrace]
  refine ⟨142585744860096465840463907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95057163240064310560309271 142585744860096465840463907)
  ·
    refine ⟨213878617290144698760695861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142585744860096465840463907 213878617290144698760695861)
    ·
      refine ⟨20051120370951065508815237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 213878617290144698760695861 20051120370951065508815237)
      ·
        refine ⟨3759585069553324782902857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20051120370951065508815237 3759585069553324782902857)
        ·
          refine ⟨2819688802164993587177143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3759585069553324782902857 2819688802164993587177143)
          ·
            refine ⟨4229533203247490380765715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2819688802164993587177143 4229533203247490380765715)
            ·
              refine ⟨6344299804871235571148573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4229533203247490380765715 6344299804871235571148573)
              ·
                refine ⟨2379112426826713339180715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6344299804871235571148573 2379112426826713339180715)
                ·
                  refine ⟨3568668640240070008771073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379112426826713339180715 3568668640240070008771073)
                  ·
                    refine ⟨2676501480180052506578305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3568668640240070008771073 2676501480180052506578305)
                    ·
                      refine ⟨2007376110135039379933729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2676501480180052506578305 2007376110135039379933729)
                      ·
                        rfl

theorem cell23_3909351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3909351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909351 prefixEnd_3909351 := by exact prefixLift 3909351
  have htrace : WordTrace (prefixWord ++ tailWord_3909351) baseStart_3909351 baseEnd_3909351 := by
    simpa [prefixWord, tailWord_3909351, baseEnd_3909351] using wordTrace_append hprefix tailTrace_3909351
  have hstable : (prefixWord ++ tailWord_3909351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909351).length < 2 ^ (prefixWord ++ tailWord_3909351).sum := by decide
  have hdescent : baseEnd_3909351 < baseStart_3909351 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909356 : List Nat := [2, 2, 1, 1, 2, 2, 2, 4, 1, 4, 2]
def baseStart_3909356 : Nat := 118140960795 + 3909356 * 2 ^ 59
def prefixEnd_3909356 : Nat := 4983230072969 + 3 ^ 40 * 3909356 * 2
def baseEnd_3909356 : Nat := 2007378677538311860371205

theorem tailTrace_3909356 : CollatzResearch.WordTrace tailWord_3909356 prefixEnd_3909356 2007378677538311860371205 := by
  unfold tailWord_3909356
  simp only [CollatzResearch.WordTrace]
  refine ⟨71292963612539175847197961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95057284816718901129597281 71292963612539175847197961)
  ·
    refine ⟨53469722709404381885398471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71292963612539175847197961 53469722709404381885398471)
    ·
      refine ⟨80204584064106572828097707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53469722709404381885398471 80204584064106572828097707)
      ·
        refine ⟨120306876096159859242146561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80204584064106572828097707 120306876096159859242146561)
        ·
          refine ⟨90230157072119894431609921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120306876096159859242146561 90230157072119894431609921)
          ·
            refine ⟨67672617804089920823707441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90230157072119894431609921 67672617804089920823707441)
            ·
              refine ⟨50754463353067440617780581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67672617804089920823707441 50754463353067440617780581)
              ·
                refine ⟨9516461878700145115833859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50754463353067440617780581 9516461878700145115833859)
                ·
                  refine ⟨14274692818050217673750789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9516461878700145115833859 14274692818050217673750789)
                  ·
                    refine ⟨2676504903384415813828273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14274692818050217673750789 2676504903384415813828273)
                    ·
                      refine ⟨2007378677538311860371205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2676504903384415813828273 2007378677538311860371205)
                      ·
                        rfl

theorem cell23_3909356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 4, 2].length) (baseStart_3909356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909356 prefixEnd_3909356 := by exact prefixLift 3909356
  have htrace : WordTrace (prefixWord ++ tailWord_3909356) baseStart_3909356 baseEnd_3909356 := by
    simpa [prefixWord, tailWord_3909356, baseEnd_3909356] using wordTrace_append hprefix tailTrace_3909356
  have hstable : (prefixWord ++ tailWord_3909356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909356).length < 2 ^ (prefixWord ++ tailWord_3909356).sum := by decide
  have hdescent : baseEnd_3909356 < baseStart_3909356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909359 : List Nat := [1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_3909359 : Nat := 118140960795 + 3909359 * 2 ^ 59
def prefixEnd_3909359 : Nat := 4983230072969 + 3 ^ 40 * 3909359 * 2
def baseEnd_3909359 : Nat := 2007380217980275348633691

theorem tailTrace_3909359 : CollatzResearch.WordTrace tailWord_3909359 prefixEnd_3909359 2007380217980275348633691 := by
  unfold tailWord_3909359
  simp only [CollatzResearch.WordTrace]
  refine ⟨142586036644067483206755131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95057357762711655471170087 142586036644067483206755131)
  ·
    refine ⟨213879054966101224810132697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142586036644067483206755131 213879054966101224810132697)
    ·
      refine ⟨160409291224575918607599523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213879054966101224810132697 160409291224575918607599523)
      ·
        refine ⟨240613936836863877911399285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160409291224575918607599523 240613936836863877911399285)
        ·
          refine ⟨22557556578455988554193683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240613936836863877911399285 22557556578455988554193683)
          ·
            refine ⟨33836334867683982831290525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22557556578455988554193683 33836334867683982831290525)
            ·
              refine ⟨12688625575381493561733947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33836334867683982831290525 12688625575381493561733947)
              ·
                refine ⟨19032938363072240342600921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688625575381493561733947 19032938363072240342600921)
                ·
                  refine ⟨14274703772304180256950691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19032938363072240342600921 14274703772304180256950691)
                  ·
                    refine ⟨21412055658456270385426037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14274703772304180256950691 21412055658456270385426037)
                    ·
                      refine ⟨2007380217980275348633691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21412055658456270385426037 2007380217980275348633691)
                      ·
                        rfl

theorem cell23_3909359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_3909359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909359 prefixEnd_3909359 := by exact prefixLift 3909359
  have htrace : WordTrace (prefixWord ++ tailWord_3909359) baseStart_3909359 baseEnd_3909359 := by
    simpa [prefixWord, tailWord_3909359, baseEnd_3909359] using wordTrace_append hprefix tailTrace_3909359
  have hstable : (prefixWord ++ tailWord_3909359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909359).length < 2 ^ (prefixWord ++ tailWord_3909359).sum := by decide
  have hdescent : baseEnd_3909359 < baseStart_3909359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909379 : List Nat := [1, 1, 1, 3, 2, 2, 5, 1, 7]
def baseStart_3909379 : Nat := 118140960795 + 3909379 * 2 ^ 59
def prefixEnd_3909379 : Nat := 4983230072969 + 3 ^ 40 * 3909379 * 2
def baseEnd_3909379 : Nat := 223043387510373918931511

theorem tailTrace_3909379 : CollatzResearch.WordTrace tailWord_3909379 prefixEnd_3909379 223043387510373918931511 := by
  unfold tailWord_3909379
  simp only [CollatzResearch.WordTrace]
  refine ⟨142586766103995026622483191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95057844069330017748322127 142586766103995026622483191)
  ·
    refine ⟨213880149155992539933724787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142586766103995026622483191 213880149155992539933724787)
    ·
      refine ⟨320820223733988809900587181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213880149155992539933724787 320820223733988809900587181)
      ·
        refine ⟨120307583900245803712720193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320820223733988809900587181 120307583900245803712720193)
        ·
          refine ⟨90230687925184352784540145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120307583900245803712720193 90230687925184352784540145)
          ·
            refine ⟨67673015943888264588405109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90230687925184352784540145 67673015943888264588405109)
            ·
              refine ⟨6344345244739524805162979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67673015943888264588405109 6344345244739524805162979)
              ·
                refine ⟨9516517867109287207744469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6344345244739524805162979 9516517867109287207744469)
                ·
                  refine ⟨223043387510373918931511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 9516517867109287207744469 223043387510373918931511)
                  ·
                    rfl

theorem cell23_3909379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 7].length) (baseStart_3909379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909379 prefixEnd_3909379 := by exact prefixLift 3909379
  have htrace : WordTrace (prefixWord ++ tailWord_3909379) baseStart_3909379 baseEnd_3909379 := by
    simpa [prefixWord, tailWord_3909379, baseEnd_3909379] using wordTrace_append hprefix tailTrace_3909379
  have hstable : (prefixWord ++ tailWord_3909379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909379).length < 2 ^ (prefixWord ++ tailWord_3909379).sum := by decide
  have hdescent : baseEnd_3909379 < baseStart_3909379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909426 : List Nat := [3, 2, 1, 1, 3, 2, 2, 2, 2, 5]
def baseStart_3909426 : Nat := 118140960795 + 3909426 * 2 ^ 59
def prefixEnd_3909426 : Nat := 4983230072969 + 3 ^ 40 * 3909426 * 2
def baseEnd_3909426 : Nat := 669138207061375528831961

theorem tailTrace_3909426 : CollatzResearch.WordTrace tailWord_3909426 prefixEnd_3909426 669138207061375528831961 := by
  unfold tailWord_3909426
  simp only [CollatzResearch.WordTrace]
  refine ⟨35647120083706188412361033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95058986889883169099629421 35647120083706188412361033)
  ·
    refine ⟨26735340062779641309270775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35647120083706188412361033 26735340062779641309270775)
    ·
      refine ⟨40103010094169461963906163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26735340062779641309270775 40103010094169461963906163)
      ·
        refine ⟨60154515141254192945859245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40103010094169461963906163 60154515141254192945859245)
        ·
          refine ⟨22557943177970322354697217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60154515141254192945859245 22557943177970322354697217)
          ·
            refine ⟨16918457383477741766022913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22557943177970322354697217 16918457383477741766022913)
            ·
              refine ⟨12688843037608306324517185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16918457383477741766022913 12688843037608306324517185)
              ·
                refine ⟨9516632278206229743387889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12688843037608306324517185 9516632278206229743387889)
                ·
                  refine ⟨7137474208654672307540917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9516632278206229743387889 7137474208654672307540917)
                  ·
                    refine ⟨669138207061375528831961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7137474208654672307540917 669138207061375528831961)
                    ·
                      rfl

theorem cell23_3909426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 2, 5].length) (baseStart_3909426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909426 prefixEnd_3909426 := by exact prefixLift 3909426
  have htrace : WordTrace (prefixWord ++ tailWord_3909426) baseStart_3909426 baseEnd_3909426 := by
    simpa [prefixWord, tailWord_3909426, baseEnd_3909426] using wordTrace_append hprefix tailTrace_3909426
  have hstable : (prefixWord ++ tailWord_3909426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909426).length < 2 ^ (prefixWord ++ tailWord_3909426).sum := by decide
  have hdescent : baseEnd_3909426 < baseStart_3909426 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909430 : List Nat := [5, 1, 2, 2, 1, 2, 1, 4, 5]
def baseStart_3909430 : Nat := 118140960795 + 3909430 * 2 ^ 59
def prefixEnd_3909430 : Nat := 4983230072969 + 3 ^ 40 * 3909430 * 2
def baseEnd_3909430 : Nat := 223046297234082730093985

theorem tailTrace_3909430 : CollatzResearch.WordTrace tailWord_3909430 prefixEnd_3909430 223046297234082730093985 := by
  unfold tailWord_3909430
  simp only [CollatzResearch.WordTrace]
  refine ⟨8911789139175641395786859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95059084151206841555059829 8911789139175641395786859)
  ·
    refine ⟨13367683708763462093680289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8911789139175641395786859 13367683708763462093680289)
    ·
      refine ⟨10025762781572596570260217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13367683708763462093680289 10025762781572596570260217)
      ·
        refine ⟨7519322086179447427695163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10025762781572596570260217 7519322086179447427695163)
        ·
          refine ⟨11278983129269171141542745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7519322086179447427695163 11278983129269171141542745)
          ·
            refine ⟨8459237346951878356157059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11278983129269171141542745 8459237346951878356157059)
            ·
              refine ⟨12688856020427817534235589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8459237346951878356157059 12688856020427817534235589)
              ·
                refine ⟨2379160503830215787669173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12688856020427817534235589 2379160503830215787669173)
                ·
                  refine ⟨223046297234082730093985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2379160503830215787669173 223046297234082730093985)
                  ·
                    rfl

theorem cell23_3909430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 5].length) (baseStart_3909430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909430 prefixEnd_3909430 := by exact prefixLift 3909430
  have htrace : WordTrace (prefixWord ++ tailWord_3909430) baseStart_3909430 baseEnd_3909430 := by
    simpa [prefixWord, tailWord_3909430, baseEnd_3909430] using wordTrace_append hprefix tailTrace_3909430
  have hstable : (prefixWord ++ tailWord_3909430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909430).length < 2 ^ (prefixWord ++ tailWord_3909430).sum := by decide
  have hdescent : baseEnd_3909430 < baseStart_3909430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909466 : List Nat := [3, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3]
def baseStart_3909466 : Nat := 118140960795 + 3909466 * 2 ^ 59
def prefixEnd_3909466 : Nat := 4983230072969 + 3 ^ 40 * 3909466 * 2
def baseEnd_3909466 : Nat := 2007435160410306429995699

theorem tailTrace_3909466 : CollatzResearch.WordTrace tailWord_3909466 prefixEnd_3909466 2007435160410306429995699 := by
  unfold tailWord_3909466
  simp only [CollatzResearch.WordTrace]
  refine ⟨35647484813669960120225063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95059959503119893653933501 35647484813669960120225063)
  ·
    refine ⟨53471227220504940180337595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35647484813669960120225063 53471227220504940180337595)
    ·
      refine ⟨80206840830757410270506393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53471227220504940180337595 80206840830757410270506393)
      ·
        refine ⟨60155130623068057702879795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80206840830757410270506393 60155130623068057702879795)
        ·
          refine ⟨90232695934602086554319693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60155130623068057702879795 90232695934602086554319693)
          ·
            refine ⟨33837260975475782457869885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90232695934602086554319693 33837260975475782457869885)
            ·
              refine ⟨12688972865803418421701207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33837260975475782457869885 12688972865803418421701207)
              ·
                refine ⟨19033459298705127632551811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12688972865803418421701207 19033459298705127632551811)
                ·
                  refine ⟨28550188948057691448827717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19033459298705127632551811 28550188948057691448827717)
                  ·
                    refine ⟨5353160427760817146655197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28550188948057691448827717 5353160427760817146655197)
                    ·
                      refine ⟨2007435160410306429995699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5353160427760817146655197 2007435160410306429995699)
                      ·
                        rfl

theorem cell23_3909466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3].length) (baseStart_3909466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909466 prefixEnd_3909466 := by exact prefixLift 3909466
  have htrace : WordTrace (prefixWord ++ tailWord_3909466) baseStart_3909466 baseEnd_3909466 := by
    simpa [prefixWord, tailWord_3909466, baseEnd_3909466] using wordTrace_append hprefix tailTrace_3909466
  have hstable : (prefixWord ++ tailWord_3909466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909466).length < 2 ^ (prefixWord ++ tailWord_3909466).sum := by decide
  have hdescent : baseEnd_3909466 < baseStart_3909466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909489 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_3909489 : Nat := 118140960795 + 3909489 * 2 ^ 59
def prefixEnd_3909489 : Nat := 4983230072969 + 3 ^ 40 * 3909489 * 2
def baseEnd_3909489 : Nat := 2007446970465359840008093

theorem tailTrace_3909489 : CollatzResearch.WordTrace tailWord_3909489 prefixEnd_3909489 2007446970465359840008093 := by
  unfold tailWord_3909489
  simp only [CollatzResearch.WordTrace]
  refine ⟨142590778133596515408987521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95060518755731010272658347 142590778133596515408987521)
  ·
    refine ⟨106943083600197386556740641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142590778133596515408987521 106943083600197386556740641)
    ·
      refine ⟨80207312700148039917555481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106943083600197386556740641 80207312700148039917555481)
      ·
        refine ⟨60155484525111029938166611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80207312700148039917555481 60155484525111029938166611)
        ·
          refine ⟨90233226787666544907249917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60155484525111029938166611 90233226787666544907249917)
          ·
            refine ⟨33837460045374954340218719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90233226787666544907249917 33837460045374954340218719)
            ·
              refine ⟨50756190068062431510328079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33837460045374954340218719 50756190068062431510328079)
              ·
                refine ⟨76134285102093647265492119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50756190068062431510328079 76134285102093647265492119)
                ·
                  refine ⟨114201427653140470898238179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76134285102093647265492119 114201427653140470898238179)
                  ·
                    refine ⟨171302141479710706347357269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114201427653140470898238179 171302141479710706347357269)
                    ·
                      refine ⟨2007446970465359840008093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 171302141479710706347357269 2007446970465359840008093)
                      ·
                        rfl

theorem cell23_3909489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_3909489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909489 prefixEnd_3909489 := by exact prefixLift 3909489
  have htrace : WordTrace (prefixWord ++ tailWord_3909489) baseStart_3909489 baseEnd_3909489 := by
    simpa [prefixWord, tailWord_3909489, baseEnd_3909489] using wordTrace_append hprefix tailTrace_3909489
  have hstable : (prefixWord ++ tailWord_3909489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909489).length < 2 ^ (prefixWord ++ tailWord_3909489).sum := by decide
  have hdescent : baseEnd_3909489 < baseStart_3909489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909513 : List Nat := [1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 3]
def baseStart_3909513 : Nat := 118140960795 + 3909513 * 2 ^ 59
def prefixEnd_3909513 : Nat := 4983230072969 + 3 ^ 40 * 3909513 * 2
def baseEnd_3909513 : Nat := 2007459294001067746107983

theorem tailTrace_3909513 : CollatzResearch.WordTrace tailWord_3909513 prefixEnd_3909513 2007459294001067746107983 := by
  unfold tailWord_3909513
  simp only [CollatzResearch.WordTrace]
  refine ⟨142591653485509567507861193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95061102323673045005240795 142591653485509567507861193)
  ·
    refine ⟨106943740114132175630895895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142591653485509567507861193 106943740114132175630895895)
    ·
      refine ⟨160415610171198263446343843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106943740114132175630895895 160415610171198263446343843)
      ·
        refine ⟨240623415256797395169515765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160415610171198263446343843 240623415256797395169515765)
        ·
          refine ⟨22558445180324755797142103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 240623415256797395169515765 22558445180324755797142103)
          ·
            refine ⟨33837667770487133695713155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22558445180324755797142103 33837667770487133695713155)
            ·
              refine ⟨50756501655730700543569733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33837667770487133695713155 50756501655730700543569733)
              ·
                refine ⟨9516844060449506351919325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50756501655730700543569733 9516844060449506351919325)
                ·
                  refine ⟨3568816522668564881969747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9516844060449506351919325 3568816522668564881969747)
                  ·
                    refine ⟨5353224784002847322954621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3568816522668564881969747 5353224784002847322954621)
                    ·
                      refine ⟨2007459294001067746107983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5353224784002847322954621 2007459294001067746107983)
                      ·
                        rfl

theorem cell23_3909513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 3].length) (baseStart_3909513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909513 prefixEnd_3909513 := by exact prefixLift 3909513
  have htrace : WordTrace (prefixWord ++ tailWord_3909513) baseStart_3909513 baseEnd_3909513 := by
    simpa [prefixWord, tailWord_3909513, baseEnd_3909513] using wordTrace_append hprefix tailTrace_3909513
  have hstable : (prefixWord ++ tailWord_3909513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909513).length < 2 ^ (prefixWord ++ tailWord_3909513).sum := by decide
  have hdescent : baseEnd_3909513 < baseStart_3909513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909533 : List Nat := [1, 4, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_3909533 : Nat := 118140960795 + 3909533 * 2 ^ 59
def prefixEnd_3909533 : Nat := 4983230072969 + 3 ^ 40 * 3909533 * 2
def baseEnd_3909533 : Nat := 669156521204719222619297

theorem tailTrace_3909533 : CollatzResearch.WordTrace tailWord_3909533 prefixEnd_3909533 669156521204719222619297 := by
  unfold tailWord_3909533
  simp only [CollatzResearch.WordTrace]
  refine ⟨142592382945437110923589253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95061588630291407282392835 142592382945437110923589253)
  ·
    refine ⟨26736071802269458298172985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142592382945437110923589253 26736071802269458298172985)
    ·
      refine ⟨20052053851702093723629739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26736071802269458298172985 20052053851702093723629739)
      ·
        refine ⟨30078080777553140585444609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20052053851702093723629739 30078080777553140585444609)
        ·
          refine ⟨22558560583164855439083457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30078080777553140585444609 22558560583164855439083457)
          ·
            refine ⟨16918920437373641579312593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22558560583164855439083457 16918920437373641579312593)
            ·
              refine ⟨12689190328030231184484445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16918920437373641579312593 12689190328030231184484445)
              ·
                refine ⟨4758446373011336694181667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12689190328030231184484445 4758446373011336694181667)
                ·
                  refine ⟨7137669559517005041272501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758446373011336694181667 7137669559517005041272501)
                  ·
                    refine ⟨669156521204719222619297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7137669559517005041272501 669156521204719222619297)
                    ·
                      rfl

theorem cell23_3909533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_3909533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909533 prefixEnd_3909533 := by exact prefixLift 3909533
  have htrace : WordTrace (prefixWord ++ tailWord_3909533) baseStart_3909533 baseEnd_3909533 := by
    simpa [prefixWord, tailWord_3909533, baseEnd_3909533] using wordTrace_append hprefix tailTrace_3909533
  have hstable : (prefixWord ++ tailWord_3909533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909533).length < 2 ^ (prefixWord ++ tailWord_3909533).sum := by decide
  have hdescent : baseEnd_3909533 < baseStart_3909533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909536 : List Nat := [2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_3909536 : Nat := 118140960795 + 3909536 * 2 ^ 59
def prefixEnd_3909536 : Nat := 4983230072969 + 3 ^ 40 * 3909536 * 2
def baseEnd_3909536 : Nat := 2007471104056121156120377

theorem tailTrace_3909536 : CollatzResearch.WordTrace tailWord_3909536 prefixEnd_3909536 2007471104056121156120377 := by
  unfold tailWord_3909536
  simp only [CollatzResearch.WordTrace]
  refine ⟨71296246182213121217974231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95061661576284161623965641 71296246182213121217974231)
  ·
    refine ⟨106944369273319681826961347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71296246182213121217974231 106944369273319681826961347)
    ·
      refine ⟨160416553909979522740442021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106944369273319681826961347 160416553909979522740442021)
      ·
        refine ⟨30078103858121160513832879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160416553909979522740442021 30078103858121160513832879)
        ·
          refine ⟨45117155787181740770749319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30078103858121160513832879 45117155787181740770749319)
          ·
            refine ⟨67675733680772611156123979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45117155787181740770749319 67675733680772611156123979)
            ·
              refine ⟨101513600521158916734185969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67675733680772611156123979 101513600521158916734185969)
              ·
                refine ⟨76135200390869187550639477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101513600521158916734185969 76135200390869187550639477)
                ·
                  refine ⟨7137675036643986332872451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76135200390869187550639477 7137675036643986332872451)
                  ·
                    refine ⟨10706512554965979499308677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7137675036643986332872451 10706512554965979499308677)
                    ·
                      refine ⟨2007471104056121156120377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10706512554965979499308677 2007471104056121156120377)
                      ·
                        rfl

theorem cell23_3909536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_3909536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909536 prefixEnd_3909536 := by exact prefixLift 3909536
  have htrace : WordTrace (prefixWord ++ tailWord_3909536) baseStart_3909536 baseEnd_3909536 := by
    simpa [prefixWord, tailWord_3909536, baseEnd_3909536] using wordTrace_append hprefix tailTrace_3909536
  have hstable : (prefixWord ++ tailWord_3909536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909536).length < 2 ^ (prefixWord ++ tailWord_3909536).sum := by decide
  have hdescent : baseEnd_3909536 < baseStart_3909536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909540 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 2, 3, 2]
def baseStart_3909540 : Nat := 118140960795 + 3909540 * 2 ^ 59
def prefixEnd_3909540 : Nat := 4983230072969 + 3 ^ 40 * 3909540 * 2
def baseEnd_3909540 : Nat := 2007473157978739140470359

theorem tailTrace_3909540 : CollatzResearch.WordTrace tailWord_3909540 prefixEnd_3909540 2007473157978739140470359 := by
  unfold tailWord_3909540
  simp only [CollatzResearch.WordTrace]
  refine ⟨71296319128205875559547037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95061758837607834079396049 71296319128205875559547037)
  ·
    refine ⟨26736119673077203334830139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71296319128205875559547037 26736119673077203334830139)
    ·
      refine ⟨40104179509615805002245209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26736119673077203334830139 40104179509615805002245209)
      ·
        refine ⟨30078134632211853751683907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40104179509615805002245209 30078134632211853751683907)
        ·
          refine ⟨45117201948317780627525861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30078134632211853751683907 45117201948317780627525861)
          ·
            refine ⟨8459475365309583867661099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45117201948317780627525861 8459475365309583867661099)
            ·
              refine ⟨12689213047964375801491649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8459475365309583867661099 12689213047964375801491649)
              ·
                refine ⟨9516909785973281851118737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12689213047964375801491649 9516909785973281851118737)
                ·
                  refine ⟨7137682339479961388339053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9516909785973281851118737 7137682339479961388339053)
                  ·
                    refine ⟨2676630877304985520627145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7137682339479961388339053 2676630877304985520627145)
                    ·
                      refine ⟨2007473157978739140470359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2676630877304985520627145 2007473157978739140470359)
                      ·
                        rfl

theorem cell23_3909540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_3909540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909540 prefixEnd_3909540 := by exact prefixLift 3909540
  have htrace : WordTrace (prefixWord ++ tailWord_3909540) baseStart_3909540 baseEnd_3909540 := by
    simpa [prefixWord, tailWord_3909540, baseEnd_3909540] using wordTrace_append hprefix tailTrace_3909540
  have hstable : (prefixWord ++ tailWord_3909540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909540).length < 2 ^ (prefixWord ++ tailWord_3909540).sum := by decide
  have hdescent : baseEnd_3909540 < baseStart_3909540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909573 : List Nat := [1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 3]
def baseStart_3909573 : Nat := 118140960795 + 3909573 * 2 ^ 59
def prefixEnd_3909573 : Nat := 4983230072969 + 3 ^ 40 * 3909573 * 2
def baseEnd_3909573 : Nat := 2007490102840337511357707

theorem tailTrace_3909573 : CollatzResearch.WordTrace tailWord_3909573 prefixEnd_3909573 2007490102840337511357707 := by
  unfold tailWord_3909573
  simp only [CollatzResearch.WordTrace]
  refine ⟨142593841865292197755045373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95062561243528131836696915 142593841865292197755045373)
  ·
    refine ⟨53472690699484574158142015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142593841865292197755045373 53472690699484574158142015)
    ·
      refine ⟨80209036049226861237213023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53472690699484574158142015 80209036049226861237213023)
      ·
        refine ⟨120313554073840291855819535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80209036049226861237213023 120313554073840291855819535)
        ·
          refine ⟨180470331110760437783729303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120313554073840291855819535 180470331110760437783729303)
          ·
            refine ⟨270705496666140656675593955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180470331110760437783729303 270705496666140656675593955)
            ·
              refine ⟨406058244999210985013390933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270705496666140656675593955 406058244999210985013390933)
              ·
                refine ⟨4758495058584503730625675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 406058244999210985013390933 4758495058584503730625675)
                ·
                  refine ⟨7137742587876755595938513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758495058584503730625675 7137742587876755595938513)
                  ·
                    refine ⟨5353306940907566696953885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7137742587876755595938513 5353306940907566696953885)
                    ·
                      refine ⟨2007490102840337511357707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5353306940907566696953885 2007490102840337511357707)
                      ·
                        rfl

theorem cell23_3909573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_3909573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909573 prefixEnd_3909573 := by exact prefixLift 3909573
  have htrace : WordTrace (prefixWord ++ tailWord_3909573) baseStart_3909573 baseEnd_3909573 := by
    simpa [prefixWord, tailWord_3909573, baseEnd_3909573] using wordTrace_append hprefix tailTrace_3909573
  have hstable : (prefixWord ++ tailWord_3909573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909573).length < 2 ^ (prefixWord ++ tailWord_3909573).sum := by decide
  have hdescent : baseEnd_3909573 < baseStart_3909573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909576 : List Nat := [2, 1, 3, 1, 4, 1, 2, 9]
def baseStart_3909576 : Nat := 118140960795 + 3909576 * 2 ^ 59
def prefixEnd_3909576 : Nat := 4983230072969 + 3 ^ 40 * 3909576 * 2
def baseEnd_3909576 : Nat := 74351542343788925911859

theorem tailTrace_3909576 : CollatzResearch.WordTrace tailWord_3909576 prefixEnd_3909576 74351542343788925911859 := by
  unfold tailWord_3909576
  simp only [CollatzResearch.WordTrace]
  refine ⟨71296975642140664633702291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95062634189520886178269721 71296975642140664633702291)
  ·
    refine ⟨106945463463210996950553437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71296975642140664633702291 106945463463210996950553437)
    ·
      refine ⟨40104548798704123856457539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106945463463210996950553437 40104548798704123856457539)
      ·
        refine ⟨60156823198056185784686309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40104548798704123856457539 60156823198056185784686309)
        ·
          refine ⟨11279404349635534834628683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60156823198056185784686309 11279404349635534834628683)
          ·
            refine ⟨16919106524453302251943025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11279404349635534834628683 16919106524453302251943025)
            ·
              refine ⟨12689329893339976688957269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16919106524453302251943025 12689329893339976688957269)
              ·
                refine ⟨74351542343788925911859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 12689329893339976688957269 74351542343788925911859)
                ·
                  rfl

theorem cell23_3909576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 9].length) (baseStart_3909576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909576 prefixEnd_3909576 := by exact prefixLift 3909576
  have htrace : WordTrace (prefixWord ++ tailWord_3909576) baseStart_3909576 baseEnd_3909576 := by
    simpa [prefixWord, tailWord_3909576, baseEnd_3909576] using wordTrace_append hprefix tailTrace_3909576
  have hstable : (prefixWord ++ tailWord_3909576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909576).length < 2 ^ (prefixWord ++ tailWord_3909576).sum := by decide
  have hdescent : baseEnd_3909576 < baseStart_3909576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909597 : List Nat := [1, 4, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_3909597 : Nat := 118140960795 + 3909597 * 2 ^ 59
def prefixEnd_3909597 : Nat := 4983230072969 + 3 ^ 40 * 3909597 * 2
def baseEnd_3909597 : Nat := 669167475458681805819199

theorem tailTrace_3909597 : CollatzResearch.WordTrace tailWord_3909597 prefixEnd_3909597 669167475458681805819199 := by
  unfold tailWord_3909597
  simp only [CollatzResearch.WordTrace]
  refine ⟨142594717217205249853919045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95063144811470166569279363 142594717217205249853919045)
  ·
    refine ⟨26736509478225984347609821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142594717217205249853919045 26736509478225984347609821)
    ·
      refine ⟨10026191054334744130353683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26736509478225984347609821 10026191054334744130353683)
      ·
        refine ⟨15039286581502116195530525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10026191054334744130353683 15039286581502116195530525)
        ·
          refine ⟨5639732468063293573323947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15039286581502116195530525 5639732468063293573323947)
          ·
            refine ⟨8459598702094940359985921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639732468063293573323947 8459598702094940359985921)
            ·
              refine ⟨6344699026571205269989441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8459598702094940359985921 6344699026571205269989441)
              ·
                refine ⟨4758524269928403952492081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6344699026571205269989441 4758524269928403952492081)
                ·
                  refine ⟨3568893202446302964369061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4758524269928403952492081 3568893202446302964369061)
                  ·
                    refine ⟨669167475458681805819199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3568893202446302964369061 669167475458681805819199)
                    ·
                      rfl

theorem cell23_3909597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_3909597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909597 prefixEnd_3909597 := by exact prefixLift 3909597
  have htrace : WordTrace (prefixWord ++ tailWord_3909597) baseStart_3909597 baseEnd_3909597 := by
    simpa [prefixWord, tailWord_3909597, baseEnd_3909597] using wordTrace_append hprefix tailTrace_3909597
  have hstable : (prefixWord ++ tailWord_3909597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909597).length < 2 ^ (prefixWord ++ tailWord_3909597).sum := by decide
  have hdescent : baseEnd_3909597 < baseStart_3909597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909671 : List Nat := [1, 1, 7, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_3909671 : Nat := 118140960795 + 3909671 * 2 ^ 59
def prefixEnd_3909671 : Nat := 4983230072969 + 3 ^ 40 * 3909671 * 2
def baseEnd_3909671 : Nat := 2007540423944478127932257

theorem tailTrace_3909671 : CollatzResearch.WordTrace tailWord_3909671 prefixEnd_3909671 2007540423944478127932257 := by
  unfold tailWord_3909671
  simp only [CollatzResearch.WordTrace]
  refine ⟨142597416218937160492112867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95064944145958106994741911 142597416218937160492112867)
  ·
    refine ⟨213896124328405740738169301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142597416218937160492112867 213896124328405740738169301)
    ·
      refine ⟨5013190413947009548550843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 213896124328405740738169301 5013190413947009548550843)
      ·
        refine ⟨7519785620920514322826265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5013190413947009548550843 7519785620920514322826265)
        ·
          refine ⟨5639839215690385742119699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7519785620920514322826265 5639839215690385742119699)
          ·
            refine ⟨8459758823535578613179549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5639839215690385742119699 8459758823535578613179549)
            ·
              refine ⟨3172409558825841979942331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8459758823535578613179549 3172409558825841979942331)
              ·
                refine ⟨4758614338238762969913497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172409558825841979942331 4758614338238762969913497)
                ·
                  refine ⟨3568960753679072227435123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4758614338238762969913497 3568960753679072227435123)
                  ·
                    refine ⟨5353441130518608341152685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3568960753679072227435123 5353441130518608341152685)
                    ·
                      refine ⟨2007540423944478127932257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5353441130518608341152685 2007540423944478127932257)
                      ·
                        rfl

theorem cell23_3909671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_3909671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909671 prefixEnd_3909671 := by exact prefixLift 3909671
  have htrace : WordTrace (prefixWord ++ tailWord_3909671) baseStart_3909671 baseEnd_3909671 := by
    simpa [prefixWord, tailWord_3909671, baseEnd_3909671] using wordTrace_append hprefix tailTrace_3909671
  have hstable : (prefixWord ++ tailWord_3909671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909671).length < 2 ^ (prefixWord ++ tailWord_3909671).sum := by decide
  have hdescent : baseEnd_3909671 < baseStart_3909671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909717 : List Nat := [1, 3, 2, 2, 1, 4, 3, 2, 5]
def baseStart_3909717 : Nat := 118140960795 + 3909717 * 2 ^ 59
def prefixEnd_3909717 : Nat := 4983230072969 + 3 ^ 40 * 3909717 * 2
def baseEnd_3909717 : Nat := 223062671561620549773005

theorem tailTrace_3909717 : CollatzResearch.WordTrace tailWord_3909717 prefixEnd_3909717 223062671561620549773005 := by
  unfold tailWord_3909717
  simp only [CollatzResearch.WordTrace]
  refine ⟨142599093976770510348287405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95066062651180340232191603 142599093976770510348287405)
  ·
    refine ⟨53474660241288941380607777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142599093976770510348287405 53474660241288941380607777)
    ·
      refine ⟨40105995180966706035455833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53474660241288941380607777 40105995180966706035455833)
      ·
        refine ⟨30079496385725029526591875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40105995180966706035455833 30079496385725029526591875)
        ·
          refine ⟨45119244578587544289887813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30079496385725029526591875 45119244578587544289887813)
          ·
            refine ⟨8459858358485164554353965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45119244578587544289887813 8459858358485164554353965)
            ·
              refine ⟨3172446884431936707882737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8459858358485164554353965 3172446884431936707882737)
              ·
                refine ⟨2379335163323952530912053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172446884431936707882737 2379335163323952530912053)
                ·
                  refine ⟨223062671561620549773005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2379335163323952530912053 223062671561620549773005)
                  ·
                    rfl

theorem cell23_3909717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 3, 2, 5].length) (baseStart_3909717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909717 prefixEnd_3909717 := by exact prefixLift 3909717
  have htrace : WordTrace (prefixWord ++ tailWord_3909717) baseStart_3909717 baseEnd_3909717 := by
    simpa [prefixWord, tailWord_3909717, baseEnd_3909717] using wordTrace_append hprefix tailTrace_3909717
  have hstable : (prefixWord ++ tailWord_3909717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909717).length < 2 ^ (prefixWord ++ tailWord_3909717).sum := by decide
  have hdescent : baseEnd_3909717 < baseStart_3909717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909834 : List Nat := [3, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3]
def baseStart_3909834 : Nat := 118140960795 + 3909834 * 2 ^ 59
def prefixEnd_3909834 : Nat := 4983230072969 + 3 ^ 40 * 3909834 * 2
def baseEnd_3909834 : Nat := 2007624121291160990194007

theorem tailTrace_3909834 : CollatzResearch.WordTrace tailWord_3909834 prefixEnd_3909834 2007624121291160990194007 := by
  unfold tailWord_3909834
  simp only [CollatzResearch.WordTrace]
  refine ⟨35650840329336659832574139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95068907544897759553531037 35650840329336659832574139)
  ·
    refine ⟨53476260494004989748861209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35650840329336659832574139 53476260494004989748861209)
    ·
      refine ⟨40107195370503742311645907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53476260494004989748861209 40107195370503742311645907)
      ·
        refine ⟨60160793055755613467468861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40107195370503742311645907 60160793055755613467468861)
        ·
          refine ⟨22560297395908355050300823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60160793055755613467468861 22560297395908355050300823)
          ·
            refine ⟨33840446093862532575451235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22560297395908355050300823 33840446093862532575451235)
            ·
              refine ⟨50760669140793798863176853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33840446093862532575451235 50760669140793798863176853)
              ·
                refine ⟨2379406365974709321711415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 50760669140793798863176853 2379406365974709321711415)
                ·
                  refine ⟨3569109548962063982567123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379406365974709321711415 3569109548962063982567123)
                  ·
                    refine ⟨5353664323443095973850685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3569109548962063982567123 5353664323443095973850685)
                    ·
                      refine ⟨2007624121291160990194007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5353664323443095973850685 2007624121291160990194007)
                      ·
                        rfl

theorem cell23_3909834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_3909834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909834 prefixEnd_3909834 := by exact prefixLift 3909834
  have htrace : WordTrace (prefixWord ++ tailWord_3909834) baseStart_3909834 baseEnd_3909834 := by
    simpa [prefixWord, tailWord_3909834, baseEnd_3909834] using wordTrace_append hprefix tailTrace_3909834
  have hstable : (prefixWord ++ tailWord_3909834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909834).length < 2 ^ (prefixWord ++ tailWord_3909834).sum := by decide
  have hdescent : baseEnd_3909834 < baseStart_3909834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909850 : List Nat := [3, 1, 1, 2, 2, 1, 5, 1, 1, 6]
def baseStart_3909850 : Nat := 118140960795 + 3909850 * 2 ^ 59
def prefixEnd_3909850 : Nat := 4983230072969 + 3 ^ 40 * 3909850 * 2
def baseEnd_3909850 : Nat := 669210778993877642531311

theorem tailTrace_3909850 : CollatzResearch.WordTrace tailWord_3909850 prefixEnd_3909850 669210778993877642531311 := by
  unfold tailWord_3909850
  simp only [CollatzResearch.WordTrace]
  refine ⟨35650986221322168515719751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95069296590192449375252669 35650986221322168515719751)
  ·
    refine ⟨53476479331983252773579627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35650986221322168515719751 53476479331983252773579627)
    ·
      refine ⟨80214718997974879160369441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53476479331983252773579627 80214718997974879160369441)
      ·
        refine ⟨60161039248481159370277081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80214718997974879160369441 60161039248481159370277081)
        ·
          refine ⟨45120779436360869527707811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60161039248481159370277081 45120779436360869527707811)
          ·
            refine ⟨67681169154541304291561717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45120779436360869527707811 67681169154541304291561717)
            ·
              refine ⟨6345109608238247277333911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67681169154541304291561717 6345109608238247277333911)
              ·
                refine ⟨9517664412357370916000867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345109608238247277333911 9517664412357370916000867)
                ·
                  refine ⟨14276496618536056374001301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9517664412357370916000867 14276496618536056374001301)
                  ·
                    refine ⟨669210778993877642531311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14276496618536056374001301 669210778993877642531311)
                    ·
                      rfl

theorem cell23_3909850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 1, 1, 6].length) (baseStart_3909850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909850 prefixEnd_3909850 := by exact prefixLift 3909850
  have htrace : WordTrace (prefixWord ++ tailWord_3909850) baseStart_3909850 baseEnd_3909850 := by
    simpa [prefixWord, tailWord_3909850, baseEnd_3909850] using wordTrace_append hprefix tailTrace_3909850
  have hstable : (prefixWord ++ tailWord_3909850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909850).length < 2 ^ (prefixWord ++ tailWord_3909850).sum := by decide
  have hdescent : baseEnd_3909850 < baseStart_3909850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909857 : List Nat := [1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_3909857 : Nat := 118140960795 + 3909857 * 2 ^ 59
def prefixEnd_3909857 : Nat := 4983230072969 + 3 ^ 40 * 3909857 * 2
def baseEnd_3909857 : Nat := 2007635931346214400206401

theorem tailTrace_3909857 : CollatzResearch.WordTrace tailWord_3909857 prefixEnd_3909857 2007635931346214400206401 := by
  unfold tailWord_3909857
  simp only [CollatzResearch.WordTrace]
  refine ⟨142604200196263314258383825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95069466797508876172255883 142604200196263314258383825)
  ·
    refine ⟨106953150147197485693787869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142604200196263314258383825 106953150147197485693787869)
    ·
      refine ⟨40107431305199057135170451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106953150147197485693787869 40107431305199057135170451)
      ·
        refine ⟨60161146957798585702755677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40107431305199057135170451 60161146957798585702755677)
        ·
          refine ⟨22560430109174469638533379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60161146957798585702755677 22560430109174469638533379)
          ·
            refine ⟨33840645163761704457800069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22560430109174469638533379 33840645163761704457800069)
            ·
              refine ⟨6345120968205319585837513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33840645163761704457800069 6345120968205319585837513)
              ·
                refine ⟨4758840726153989689378135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6345120968205319585837513 4758840726153989689378135)
                ·
                  refine ⟨7138261089230984534067203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4758840726153989689378135 7138261089230984534067203)
                  ·
                    refine ⟨10707391633846476801100805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7138261089230984534067203 10707391633846476801100805)
                    ·
                      refine ⟨2007635931346214400206401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10707391633846476801100805 2007635931346214400206401)
                      ·
                        rfl

theorem cell23_3909857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_3909857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909857 prefixEnd_3909857 := by exact prefixLift 3909857
  have htrace : WordTrace (prefixWord ++ tailWord_3909857) baseStart_3909857 baseEnd_3909857 := by
    simpa [prefixWord, tailWord_3909857, baseEnd_3909857] using wordTrace_append hprefix tailTrace_3909857
  have hstable : (prefixWord ++ tailWord_3909857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909857).length < 2 ^ (prefixWord ++ tailWord_3909857).sum := by decide
  have hdescent : baseEnd_3909857 < baseStart_3909857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909870 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_3909870 : Nat := 118140960795 + 3909870 * 2 ^ 59
def prefixEnd_3909870 : Nat := 4983230072969 + 3 ^ 40 * 3909870 * 2
def baseEnd_3909870 : Nat := 2007642606594722849343841

theorem tailTrace_3909870 : CollatzResearch.WordTrace tailWord_3909870 prefixEnd_3909870 2007642606594722849343841 := by
  unfold tailWord_3909870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17825584293152027184825883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95069782896810811652404709 17825584293152027184825883)
  ·
    refine ⟨26738376439728040777238825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17825584293152027184825883 26738376439728040777238825)
    ·
      refine ⟨20053782329796030582929119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26738376439728040777238825 20053782329796030582929119)
      ·
        refine ⟨30080673494694045874393679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20053782329796030582929119 30080673494694045874393679)
        ·
          refine ⟨45121010242041068811590519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30080673494694045874393679 45121010242041068811590519)
          ·
            refine ⟨67681515363061603217385779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45121010242041068811590519 67681515363061603217385779)
            ·
              refine ⟨101522273044592404826078669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67681515363061603217385779 101522273044592404826078669)
              ·
                refine ⟨38070852391722151809779501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101522273044592404826078669 38070852391722151809779501)
                ·
                  refine ⟨14276569646895806928667313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38070852391722151809779501 14276569646895806928667313)
                  ·
                    refine ⟨10707427235171855196500485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14276569646895806928667313 10707427235171855196500485)
                    ·
                      refine ⟨2007642606594722849343841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10707427235171855196500485 2007642606594722849343841)
                      ·
                        rfl

theorem cell23_3909870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_3909870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909870 prefixEnd_3909870 := by exact prefixLift 3909870
  have htrace : WordTrace (prefixWord ++ tailWord_3909870) baseStart_3909870 baseEnd_3909870 := by
    simpa [prefixWord, tailWord_3909870, baseEnd_3909870] using wordTrace_append hprefix tailTrace_3909870
  have hstable : (prefixWord ++ tailWord_3909870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909870).length < 2 ^ (prefixWord ++ tailWord_3909870).sum := by decide
  have hdescent : baseEnd_3909870 < baseStart_3909870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909960 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_3909960 : Nat := 118140960795 + 3909960 * 2 ^ 59
def prefixEnd_3909960 : Nat := 4983230072969 + 3 ^ 40 * 3909960 * 2
def baseEnd_3909960 : Nat := 2007688819853627497218427

theorem tailTrace_3909960 : CollatzResearch.WordTrace tailWord_3909960 prefixEnd_3909960 2007688819853627497218427 := by
  unfold tailWord_3909960
  simp only [CollatzResearch.WordTrace]
  refine ⟨71303978457445081424691667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95071971276593441899588889 71303978457445081424691667)
  ·
    refine ⟨106955967686167622137037501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71303978457445081424691667 106955967686167622137037501)
    ·
      refine ⟨40108487882312858301389063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106955967686167622137037501 40108487882312858301389063)
      ·
        refine ⟨60162731823469287452083595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40108487882312858301389063 60162731823469287452083595)
        ·
          refine ⟨90244097735203931178125393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60162731823469287452083595 90244097735203931178125393)
          ·
            refine ⟨67683073301402948383594045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90244097735203931178125393 67683073301402948383594045)
            ·
              refine ⟨25381152488026105643847767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67683073301402948383594045 25381152488026105643847767)
              ·
                refine ⟨38071728732039158465771651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25381152488026105643847767 38071728732039158465771651)
                ·
                  refine ⟨57107593098058737698657477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38071728732039158465771651 57107593098058737698657477)
                  ·
                    refine ⟨10707673705886013318498277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57107593098058737698657477 10707673705886013318498277)
                    ·
                      refine ⟨2007688819853627497218427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10707673705886013318498277 2007688819853627497218427)
                      ·
                        rfl

theorem cell23_3909960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_3909960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909960 prefixEnd_3909960 := by exact prefixLift 3909960
  have htrace : WordTrace (prefixWord ++ tailWord_3909960) baseStart_3909960 baseEnd_3909960 := by
    simpa [prefixWord, tailWord_3909960, baseEnd_3909960] using wordTrace_append hprefix tailTrace_3909960
  have hstable : (prefixWord ++ tailWord_3909960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909960).length < 2 ^ (prefixWord ++ tailWord_3909960).sum := by decide
  have hdescent : baseEnd_3909960 < baseStart_3909960 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909964 : List Nat := [2, 2, 1, 3, 2, 1, 4, 1, 1, 4, 2]
def baseStart_3909964 : Nat := 118140960795 + 3909964 * 2 ^ 59
def prefixEnd_3909964 : Nat := 4983230072969 + 3 ^ 40 * 3909964 * 2
def baseEnd_3909964 : Nat := 2007690873776245481568409

theorem tailTrace_3909964 : CollatzResearch.WordTrace tailWord_3909964 prefixEnd_3909964 2007690873776245481568409 := by
  unfold tailWord_3909964
  simp only [CollatzResearch.WordTrace]
  refine ⟨71304051403437835766264473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95072068537917114355019297 71304051403437835766264473)
  ·
    refine ⟨53478038552578376824698355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71304051403437835766264473 53478038552578376824698355)
    ·
      refine ⟨80217057828867565237047533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53478038552578376824698355 80217057828867565237047533)
      ·
        refine ⟨30081396685825336963892825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80217057828867565237047533 30081396685825336963892825)
        ·
          refine ⟨22561047514369002722919619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30081396685825336963892825 22561047514369002722919619)
          ·
            refine ⟨33841571271553504084379429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22561047514369002722919619 33841571271553504084379429)
            ·
              refine ⟨6345294613416282015821143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33841571271553504084379429 6345294613416282015821143)
              ·
                refine ⟨9517941920124423023731715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345294613416282015821143 9517941920124423023731715)
                ·
                  refine ⟨14276912880186634535597573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9517941920124423023731715 14276912880186634535597573)
                  ·
                    refine ⟨2676921165034993975424545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14276912880186634535597573 2676921165034993975424545)
                    ·
                      refine ⟨2007690873776245481568409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2676921165034993975424545 2007690873776245481568409)
                      ·
                        rfl

theorem cell23_3909964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 1, 1, 4, 2].length) (baseStart_3909964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909964 prefixEnd_3909964 := by exact prefixLift 3909964
  have htrace : WordTrace (prefixWord ++ tailWord_3909964) baseStart_3909964 baseEnd_3909964 := by
    simpa [prefixWord, tailWord_3909964, baseEnd_3909964] using wordTrace_append hprefix tailTrace_3909964
  have hstable : (prefixWord ++ tailWord_3909964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909964).length < 2 ^ (prefixWord ++ tailWord_3909964).sum := by decide
  have hdescent : baseEnd_3909964 < baseStart_3909964 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909970 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 9]
def baseStart_3909970 : Nat := 118140960795 + 3909970 * 2 ^ 59
def prefixEnd_3909970 : Nat := 4983230072969 + 3 ^ 40 * 3909970 * 2
def baseEnd_3909970 : Nat := 223077106073352495343709

theorem tailTrace_3909970 : CollatzResearch.WordTrace tailWord_3909970 prefixEnd_3909970 223077106073352495343709 := by
  unfold tailWord_3909970
  simp only [CollatzResearch.WordTrace]
  refine ⟨35652080411213483639311841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95072214429902623038164909 35652080411213483639311841)
  ·
    refine ⟨26739060308410112729483881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35652080411213483639311841 26739060308410112729483881)
    ·
      refine ⟨20054295231307584547112911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26739060308410112729483881 20054295231307584547112911)
      ·
        refine ⟨30081442846961376820669367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20054295231307584547112911 30081442846961376820669367)
        ·
          refine ⟨45122164270442065231004051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30081442846961376820669367 45122164270442065231004051)
          ·
            refine ⟨67683246405663097846506077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45122164270442065231004051 67683246405663097846506077)
            ·
              refine ⟨25381217402123661692439779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67683246405663097846506077 25381217402123661692439779)
              ·
                refine ⟨38071826103185492538659669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25381217402123661692439779 38071826103185492538659669)
                ·
                  refine ⟨223077106073352495343709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38071826103185492538659669 223077106073352495343709)
                  ·
                    rfl

theorem cell23_3909970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 9].length) (baseStart_3909970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909970 prefixEnd_3909970 := by exact prefixLift 3909970
  have htrace : WordTrace (prefixWord ++ tailWord_3909970) baseStart_3909970 baseEnd_3909970 := by
    simpa [prefixWord, tailWord_3909970, baseEnd_3909970] using wordTrace_append hprefix tailTrace_3909970
  have hstable : (prefixWord ++ tailWord_3909970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909970).length < 2 ^ (prefixWord ++ tailWord_3909970).sum := by decide
  have hdescent : baseEnd_3909970 < baseStart_3909970 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3909997 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_3909997 : Nat := 118140960795 + 3909997 * 2 ^ 59
def prefixEnd_3909997 : Nat := 4983230072969 + 3 ^ 40 * 3909997 * 2
def baseEnd_3909997 : Nat := 2007707818637843852455757

theorem tailTrace_3909997 : CollatzResearch.WordTrace tailWord_3909997 prefixEnd_3909997 2007707818637843852455757 := by
  unfold tailWord_3909997
  simp only [CollatzResearch.WordTrace]
  refine ⟨142609306415756118168480245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95072870943837412112320163 142609306415756118168480245)
  ·
    refine ⟨13369622476477136078295023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142609306415756118168480245 13369622476477136078295023)
    ·
      refine ⟨20054433714715704117442535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13369622476477136078295023 20054433714715704117442535)
      ·
        refine ⟨30081650572073556176163803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20054433714715704117442535 30081650572073556176163803)
        ·
          refine ⟨45122475858110334264245705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30081650572073556176163803 45122475858110334264245705)
          ·
            refine ⟨33841856893582750698184279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45122475858110334264245705 33841856893582750698184279)
            ·
              refine ⟨50762785340374126047276419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33841856893582750698184279 50762785340374126047276419)
              ·
                refine ⟨76144178010561189070914629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50762785340374126047276419 76144178010561189070914629)
                ·
                  refine ⟨14277033376980222950796493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76144178010561189070914629 14277033376980222950796493)
                  ·
                    refine ⟨5353887516367583606548685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14277033376980222950796493 5353887516367583606548685)
                    ·
                      refine ⟨2007707818637843852455757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5353887516367583606548685 2007707818637843852455757)
                      ·
                        rfl

theorem cell23_3909997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_3909997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3909997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3909997 prefixEnd_3909997 := by exact prefixLift 3909997
  have htrace : WordTrace (prefixWord ++ tailWord_3909997) baseStart_3909997 baseEnd_3909997 := by
    simpa [prefixWord, tailWord_3909997, baseEnd_3909997] using wordTrace_append hprefix tailTrace_3909997
  have hstable : (prefixWord ++ tailWord_3909997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3909997).length < 2 ^ (prefixWord ++ tailWord_3909997).sum := by decide
  have hdescent : baseEnd_3909997 < baseStart_3909997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3909997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910007 : List Nat := [1, 1, 3, 1, 1, 2, 2, 3, 2, 5, 2]
def baseStart_3910007 : Nat := 118140960795 + 3910007 * 2 ^ 59
def prefixEnd_3910007 : Nat := 4983230072969 + 3 ^ 40 * 3910007 * 2
def baseEnd_3910007 : Nat := 2007712953444388813330711

theorem tailTrace_3910007 : CollatzResearch.WordTrace tailWord_3910007 prefixEnd_3910007 2007712953444388813330711 := by
  unfold tailWord_3910007
  simp only [CollatzResearch.WordTrace]
  refine ⟨142609671145719889876344275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95073114097146593250896183 142609671145719889876344275)
  ·
    refine ⟨213914506718579834814516413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142609671145719889876344275 213914506718579834814516413)
    ·
      refine ⟨80217940019467438055443655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213914506718579834814516413 80217940019467438055443655)
      ·
        refine ⟨120326910029201157083165483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80217940019467438055443655 120326910029201157083165483)
        ·
          refine ⟨180490365043801735624748225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120326910029201157083165483 180490365043801735624748225)
          ·
            refine ⟨135367773782851301718561169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180490365043801735624748225 135367773782851301718561169)
            ·
              refine ⟨101525830337138476288920877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135367773782851301718561169 101525830337138476288920877)
              ·
                refine ⟨38072186376426928608345329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101525830337138476288920877 38072186376426928608345329)
                ·
                  refine ⟨28554139782320196456258997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38072186376426928608345329 28554139782320196456258997)
                  ·
                    refine ⟨2676950604592518417774281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28554139782320196456258997 2676950604592518417774281)
                    ·
                      refine ⟨2007712953444388813330711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2676950604592518417774281 2007712953444388813330711)
                      ·
                        rfl

theorem cell23_3910007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 5, 2].length) (baseStart_3910007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910007 prefixEnd_3910007 := by exact prefixLift 3910007
  have htrace : WordTrace (prefixWord ++ tailWord_3910007) baseStart_3910007 baseEnd_3910007 := by
    simpa [prefixWord, tailWord_3910007, baseEnd_3910007] using wordTrace_append hprefix tailTrace_3910007
  have hstable : (prefixWord ++ tailWord_3910007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910007).length < 2 ^ (prefixWord ++ tailWord_3910007).sum := by decide
  have hdescent : baseEnd_3910007 < baseStart_3910007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910017 : List Nat := [1, 2, 4, 3, 1, 1, 1, 2, 1, 7]
def baseStart_3910017 : Nat := 118140960795 + 3910017 * 2 ^ 59
def prefixEnd_3910017 : Nat := 4983230072969 + 3 ^ 40 * 3910017 * 2
def baseEnd_3910017 : Nat := 669239362750311258068555

theorem tailTrace_3910017 : CollatzResearch.WordTrace tailWord_3910017 prefixEnd_3910017 669239362750311258068555 := by
  unfold tailWord_3910017
  simp only [CollatzResearch.WordTrace]
  refine ⟨142610035875683661584208305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95073357250455774389472203 142610035875683661584208305)
  ·
    refine ⟨106957526906762746188156229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142610035875683661584208305 106957526906762746188156229)
    ·
      refine ⟨20054536295018014910279293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 106957526906762746188156229 20054536295018014910279293)
      ·
        refine ⟨7520451110631755591354735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20054536295018014910279293 7520451110631755591354735)
        ·
          refine ⟨11280676665947633387032103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520451110631755591354735 11280676665947633387032103)
          ·
            refine ⟨16921014998921450080548155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11280676665947633387032103 16921014998921450080548155)
            ·
              refine ⟨25381522498382175120822233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16921014998921450080548155 25381522498382175120822233)
              ·
                refine ⟨19036141873786631340616675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25381522498382175120822233 19036141873786631340616675)
                ·
                  refine ⟨28554212810679947010925013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19036141873786631340616675 28554212810679947010925013)
                  ·
                    refine ⟨669239362750311258068555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28554212810679947010925013 669239362750311258068555)
                    ·
                      rfl

theorem cell23_3910017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_3910017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910017 prefixEnd_3910017 := by exact prefixLift 3910017
  have htrace : WordTrace (prefixWord ++ tailWord_3910017) baseStart_3910017 baseEnd_3910017 := by
    simpa [prefixWord, tailWord_3910017, baseEnd_3910017] using wordTrace_append hprefix tailTrace_3910017
  have hstable : (prefixWord ++ tailWord_3910017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910017).length < 2 ^ (prefixWord ++ tailWord_3910017).sum := by decide
  have hdescent : baseEnd_3910017 < baseStart_3910017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910037 : List Nat := [1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_3910037 : Nat := 118140960795 + 3910037 * 2 ^ 59
def prefixEnd_3910037 : Nat := 4983230072969 + 3 ^ 40 * 3910037 * 2
def baseEnd_3910037 : Nat := 2007728357864023695955573

theorem tailTrace_3910037 : CollatzResearch.WordTrace tailWord_3910037 prefixEnd_3910037 2007728357864023695955573 := by
  unfold tailWord_3910037
  simp only [CollatzResearch.WordTrace]
  refine ⟨142610765335611204999936365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95073843557074136666624243 142610765335611204999936365)
  ·
    refine ⟨53479037000854201874976137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142610765335611204999936365 53479037000854201874976137)
    ·
      refine ⟨40109277750640651406232103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53479037000854201874976137 40109277750640651406232103)
      ·
        refine ⟨60163916625960977109348155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40109277750640651406232103 60163916625960977109348155)
        ·
          refine ⟨90245874938941465664022233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60163916625960977109348155 90245874938941465664022233)
          ·
            refine ⟨67684406204206099248016675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90245874938941465664022233 67684406204206099248016675)
            ·
              refine ⟨101526609306309148872025013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67684406204206099248016675 101526609306309148872025013)
              ·
                refine ⟨9518119622466482706752345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101526609306309148872025013 9518119622466482706752345)
                ·
                  refine ⟨7138589716849862030064259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9518119622466482706752345 7138589716849862030064259)
                  ·
                    refine ⟨10707884575274793045096389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7138589716849862030064259 10707884575274793045096389)
                    ·
                      refine ⟨2007728357864023695955573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10707884575274793045096389 2007728357864023695955573)
                      ·
                        rfl

theorem cell23_3910037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_3910037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910037 prefixEnd_3910037 := by exact prefixLift 3910037
  have htrace : WordTrace (prefixWord ++ tailWord_3910037) baseStart_3910037 baseEnd_3910037 := by
    simpa [prefixWord, tailWord_3910037, baseEnd_3910037] using wordTrace_append hprefix tailTrace_3910037
  have hstable : (prefixWord ++ tailWord_3910037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910037).length < 2 ^ (prefixWord ++ tailWord_3910037).sum := by decide
  have hdescent : baseEnd_3910037 < baseStart_3910037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910115 : List Nat := [1, 1, 1, 6, 3, 2, 2, 2, 1, 4]
def baseStart_3910115 : Nat := 118140960795 + 3910115 * 2 ^ 59
def prefixEnd_3910115 : Nat := 4983230072969 + 3 ^ 40 * 3910115 * 2
def baseEnd_3910115 : Nat := 669256136451691463593405

theorem tailTrace_3910115 : CollatzResearch.WordTrace tailWord_3910115 prefixEnd_3910115 669256136451691463593405 := by
  unfold tailWord_3910115
  simp only [CollatzResearch.WordTrace]
  refine ⟨142613610229328624321275799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95075740152885749547517199 142613610229328624321275799)
  ·
    refine ⟨213920415343992936481913699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142613610229328624321275799 213920415343992936481913699)
    ·
      refine ⟨320880623015989404722870549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213920415343992936481913699 320880623015989404722870549)
      ·
        refine ⟨15041279203874503346384557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 320880623015989404722870549 15041279203874503346384557)
        ·
          refine ⟨5640479701452938754894209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15041279203874503346384557 5640479701452938754894209)
          ·
            refine ⟨4230359776089704066170657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5640479701452938754894209 4230359776089704066170657)
            ·
              refine ⟨3172769832067278049627993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4230359776089704066170657 3172769832067278049627993)
              ·
                refine ⟨2379577374050458537220995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3172769832067278049627993 2379577374050458537220995)
                ·
                  refine ⟨3569366061075687805831493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379577374050458537220995 3569366061075687805831493)
                  ·
                    refine ⟨669256136451691463593405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3569366061075687805831493 669256136451691463593405)
                    ·
                      rfl

theorem cell23_3910115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 2, 1, 4].length) (baseStart_3910115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910115 prefixEnd_3910115 := by exact prefixLift 3910115
  have htrace : WordTrace (prefixWord ++ tailWord_3910115) baseStart_3910115 baseEnd_3910115 := by
    simpa [prefixWord, tailWord_3910115, baseEnd_3910115] using wordTrace_append hprefix tailTrace_3910115
  have hstable : (prefixWord ++ tailWord_3910115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910115).length < 2 ^ (prefixWord ++ tailWord_3910115).sum := by decide
  have hdescent : baseEnd_3910115 < baseStart_3910115 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910137 : List Nat := [1, 2, 1, 3, 1, 2, 3, 3, 1, 6]
def baseStart_3910137 : Nat := 118140960795 + 3910137 * 2 ^ 59
def prefixEnd_3910137 : Nat := 4983230072969 + 3 ^ 40 * 3910137 * 2
def baseEnd_3910137 : Nat := 669259901976491101568371

theorem tailTrace_3910137 : CollatzResearch.WordTrace tailWord_3910137 prefixEnd_3910137 669259901976491101568371 := by
  unfold tailWord_3910137
  simp only [CollatzResearch.WordTrace]
  refine ⟨142614412635248922078576665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95076275090165948052384443 142614412635248922078576665)
  ·
    refine ⟨106960809476436691558932499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142614412635248922078576665 106960809476436691558932499)
    ·
      refine ⟨160441214214655037338398749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106960809476436691558932499 160441214214655037338398749)
      ·
        refine ⟨60165455330495639001899531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160441214214655037338398749 60165455330495639001899531)
        ·
          refine ⟨90248182995743458502849297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60165455330495639001899531 90248182995743458502849297)
          ·
            refine ⟨67686137246807593877136973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90248182995743458502849297 67686137246807593877136973)
            ·
              refine ⟨25382301467552847703926365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67686137246807593877136973 25382301467552847703926365)
              ·
                refine ⟨9518363050332317888972387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25382301467552847703926365 9518363050332317888972387)
                ·
                  refine ⟨14277544575498476833458581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9518363050332317888972387 14277544575498476833458581)
                  ·
                    refine ⟨669259901976491101568371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14277544575498476833458581 669259901976491101568371)
                    ·
                      rfl

theorem cell23_3910137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_3910137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910137 prefixEnd_3910137 := by exact prefixLift 3910137
  have htrace : WordTrace (prefixWord ++ tailWord_3910137) baseStart_3910137 baseEnd_3910137 := by
    simpa [prefixWord, tailWord_3910137, baseEnd_3910137] using wordTrace_append hprefix tailTrace_3910137
  have hstable : (prefixWord ++ tailWord_3910137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910137).length < 2 ^ (prefixWord ++ tailWord_3910137).sum := by decide
  have hdescent : baseEnd_3910137 < baseStart_3910137 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910148 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 2, 3, 2]
def baseStart_3910148 : Nat := 118140960795 + 3910148 * 2 ^ 59
def prefixEnd_3910148 : Nat := 4983230072969 + 3 ^ 40 * 3910148 * 2
def baseEnd_3910148 : Nat := 2007785354216672761667563

theorem tailTrace_3910148 : CollatzResearch.WordTrace tailWord_3910148 prefixEnd_3910148 2007785354216672761667563 := by
  unfold tailWord_3910148
  simp only [CollatzResearch.WordTrace]
  refine ⟨71307406919104535478613549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95076542558806047304818065 71307406919104535478613549)
  ·
    refine ⟨26740277594664200804480081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71307406919104535478613549 26740277594664200804480081)
    ·
      refine ⟨20055208195998150603360061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26740277594664200804480081 20055208195998150603360061)
      ·
        refine ⟨7520703073499306476260023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20055208195998150603360061 7520703073499306476260023)
        ·
          refine ⟨11281054610248959714390035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7520703073499306476260023 11281054610248959714390035)
          ·
            refine ⟨16921581915373439571585053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11281054610248959714390035 16921581915373439571585053)
            ·
              refine ⟨6345593218265039839344395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16921581915373439571585053 6345593218265039839344395)
              ·
                refine ⟨9518389827397559759016593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6345593218265039839344395 9518389827397559759016593)
                ·
                  refine ⟨7138792370548169819262445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9518389827397559759016593 7138792370548169819262445)
                  ·
                    refine ⟨2677047138955563682223417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7138792370548169819262445 2677047138955563682223417)
                    ·
                      refine ⟨2007785354216672761667563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677047138955563682223417 2007785354216672761667563)
                      ·
                        rfl

theorem cell23_3910148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_3910148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910148 prefixEnd_3910148 := by exact prefixLift 3910148
  have htrace : WordTrace (prefixWord ++ tailWord_3910148) baseStart_3910148 baseEnd_3910148 := by
    simpa [prefixWord, tailWord_3910148, baseEnd_3910148] using wordTrace_append hprefix tailTrace_3910148
  have hstable : (prefixWord ++ tailWord_3910148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910148).length < 2 ^ (prefixWord ++ tailWord_3910148).sum := by decide
  have hdescent : baseEnd_3910148 < baseStart_3910148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910154 : List Nat := [3, 1, 2, 2, 2, 1, 2, 2, 4, 4]
def baseStart_3910154 : Nat := 118140960795 + 3910154 * 2 ^ 59
def prefixEnd_3910154 : Nat := 4983230072969 + 3 ^ 40 * 3910154 * 2
def baseEnd_3910154 : Nat := 669262811700199912730845

theorem tailTrace_3910154 : CollatzResearch.WordTrace tailWord_3910154 prefixEnd_3910154 669262811700199912730845 := by
  unfold tailWord_3910154
  simp only [CollatzResearch.WordTrace]
  refine ⟨35653758169046833495486379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95076688450791555987963677 35653758169046833495486379)
  ·
    refine ⟨53480637253570250243229569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35653758169046833495486379 53480637253570250243229569)
    ·
      refine ⟨40110477940177687682422177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53480637253570250243229569 40110477940177687682422177)
      ·
        refine ⟨30082858455133265761816633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40110477940177687682422177 30082858455133265761816633)
        ·
          refine ⟨22562143841349949321362475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30082858455133265761816633 22562143841349949321362475)
          ·
            refine ⟨33843215762024923982043713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22562143841349949321362475 33843215762024923982043713)
            ·
              refine ⟨25382411821518692986532785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33843215762024923982043713 25382411821518692986532785)
              ·
                refine ⟨19036808866139019739899589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25382411821518692986532785 19036808866139019739899589)
                ·
                  refine ⟨3569401662401066201231173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19036808866139019739899589 3569401662401066201231173)
                  ·
                    refine ⟨669262811700199912730845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3569401662401066201231173 669262811700199912730845)
                    ·
                      rfl

theorem cell23_3910154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_3910154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910154 prefixEnd_3910154 := by exact prefixLift 3910154
  have htrace : WordTrace (prefixWord ++ tailWord_3910154) baseStart_3910154 baseEnd_3910154 := by
    simpa [prefixWord, tailWord_3910154, baseEnd_3910154] using wordTrace_append hprefix tailTrace_3910154
  have hstable : (prefixWord ++ tailWord_3910154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910154).length < 2 ^ (prefixWord ++ tailWord_3910154).sum := by decide
  have hdescent : baseEnd_3910154 < baseStart_3910154 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910158 : List Nat := [4, 1, 1, 2, 3, 3, 2, 1, 1, 5]
def baseStart_3910158 : Nat := 118140960795 + 3910158 * 2 ^ 59
def prefixEnd_3910158 : Nat := 4983230072969 + 3 ^ 40 * 3910158 * 2
def baseEnd_3910158 : Nat := 669263496341072574180839

theorem tailTrace_3910158 : CollatzResearch.WordTrace tailWord_3910158 prefixEnd_3910158 669263496341072574180839 := by
  unfold tailWord_3910158
  simp only [CollatzResearch.WordTrace]
  refine ⟨17826897321021605333136391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95076785712115228443394085 17826897321021605333136391)
  ·
    refine ⟨26740345981532407999704587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17826897321021605333136391 26740345981532407999704587)
    ·
      refine ⟨40110518972298611999556881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26740345981532407999704587 40110518972298611999556881)
      ·
        refine ⟨30082889229223958999667661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40110518972298611999556881 30082889229223958999667661)
        ·
          refine ⟨11281083460958984624875373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30082889229223958999667661 11281083460958984624875373)
          ·
            refine ⟨4230406297859619234328265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11281083460958984624875373 4230406297859619234328265)
            ·
              refine ⟨3172804723394714425746199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4230406297859619234328265 3172804723394714425746199)
              ·
                refine ⟨4759207085092071638619299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3172804723394714425746199 4759207085092071638619299)
                ·
                  refine ⟨7138810627638107457928949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4759207085092071638619299 7138810627638107457928949)
                  ·
                    refine ⟨669263496341072574180839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7138810627638107457928949 669263496341072574180839)
                    ·
                      rfl

theorem cell23_3910158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 1, 5].length) (baseStart_3910158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910158 prefixEnd_3910158 := by exact prefixLift 3910158
  have htrace : WordTrace (prefixWord ++ tailWord_3910158) baseStart_3910158 baseEnd_3910158 := by
    simpa [prefixWord, tailWord_3910158, baseEnd_3910158] using wordTrace_append hprefix tailTrace_3910158
  have hstable : (prefixWord ++ tailWord_3910158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910158).length < 2 ^ (prefixWord ++ tailWord_3910158).sum := by decide
  have hdescent : baseEnd_3910158 < baseStart_3910158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910198 : List Nat := [5, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3]
def baseStart_3910198 : Nat := 118140960795 + 3910198 * 2 ^ 59
def prefixEnd_3910198 : Nat := 4983230072969 + 3 ^ 40 * 3910198 * 2
def baseEnd_3910198 : Nat := 2007811028249397566042333

theorem tailTrace_3910198 : CollatzResearch.WordTrace tailWord_3910198 prefixEnd_3910198 2007811028249397566042333 := by
  unfold tailWord_3910198
  simp only [CollatzResearch.WordTrace]
  refine ⟨8913539843001745593534203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95077758325351952997698165 8913539843001745593534203)
  ·
    refine ⟨13370309764502618390301305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8913539843001745593534203 13370309764502618390301305)
    ·
      refine ⟨10027732323376963792725979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13370309764502618390301305 10027732323376963792725979)
      ·
        refine ⟨15041598485065445689088969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10027732323376963792725979 15041598485065445689088969)
        ·
          refine ⟨11281198863799084266816727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15041598485065445689088969 11281198863799084266816727)
          ·
            refine ⟨16921798295698626400225091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11281198863799084266816727 16921798295698626400225091)
            ·
              refine ⟨25382697443547939600337637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16921798295698626400225091 25382697443547939600337637)
              ·
                refine ⟨4759255770665238675063307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25382697443547939600337637 4759255770665238675063307)
                ·
                  refine ⟨7138883655997858012594961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4759255770665238675063307 7138883655997858012594961)
                  ·
                    refine ⟨5354162741998393509446221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7138883655997858012594961 5354162741998393509446221)
                    ·
                      refine ⟨2007811028249397566042333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5354162741998393509446221 2007811028249397566042333)
                      ·
                        rfl

theorem cell23_3910198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_3910198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910198 prefixEnd_3910198 := by exact prefixLift 3910198
  have htrace : WordTrace (prefixWord ++ tailWord_3910198) baseStart_3910198 baseEnd_3910198 := by
    simpa [prefixWord, tailWord_3910198, baseEnd_3910198] using wordTrace_append hprefix tailTrace_3910198
  have hstable : (prefixWord ++ tailWord_3910198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910198).length < 2 ^ (prefixWord ++ tailWord_3910198).sum := by decide
  have hdescent : baseEnd_3910198 < baseStart_3910198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910207 : List Nat := [1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_3910207 : Nat := 118140960795 + 3910207 * 2 ^ 59
def prefixEnd_3910207 : Nat := 4983230072969 + 3 ^ 40 * 3910207 * 2
def baseEnd_3910207 : Nat := 2007815649575288030829791

theorem tailTrace_3910207 : CollatzResearch.WordTrace tailWord_3910207 prefixEnd_3910207 2007815649575288030829791 := by
  unfold tailWord_3910207
  simp only [CollatzResearch.WordTrace]
  refine ⟨142616965744995324033624875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95077977163330216022416583 142616965744995324033624875)
  ·
    refine ⟨213925448617492986050437313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142616965744995324033624875 213925448617492986050437313)
    ·
      refine ⟨160444086463119739537827985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213925448617492986050437313 160444086463119739537827985)
      ·
        refine ⟨120333064847339804653370989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160444086463119739537827985 120333064847339804653370989)
        ·
          refine ⟨45124899317752426745014121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120333064847339804653370989 45124899317752426745014121)
          ·
            refine ⟨33843674488314320058760591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45124899317752426745014121 33843674488314320058760591)
            ·
              refine ⟨50765511732471480088140887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33843674488314320058760591 50765511732471480088140887)
              ·
                refine ⟨76148267598707220132211331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50765511732471480088140887 76148267598707220132211331)
                ·
                  refine ⟨114222401398060830198316997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76148267598707220132211331 114222401398060830198316997)
                  ·
                    refine ⟨21416700262136405662184437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114222401398060830198316997 21416700262136405662184437)
                    ·
                      refine ⟨2007815649575288030829791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21416700262136405662184437 2007815649575288030829791)
                      ·
                        rfl

theorem cell23_3910207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_3910207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910207 prefixEnd_3910207 := by exact prefixLift 3910207
  have htrace : WordTrace (prefixWord ++ tailWord_3910207) baseStart_3910207 baseEnd_3910207 := by
    simpa [prefixWord, tailWord_3910207, baseEnd_3910207] using wordTrace_append hprefix tailTrace_3910207
  have hstable : (prefixWord ++ tailWord_3910207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910207).length < 2 ^ (prefixWord ++ tailWord_3910207).sum := by decide
  have hdescent : baseEnd_3910207 < baseStart_3910207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910217 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_3910217 : Nat := 118140960795 + 3910217 * 2 ^ 59
def prefixEnd_3910217 : Nat := 4983230072969 + 3 ^ 40 * 3910217 * 2
def baseEnd_3910217 : Nat := 2007820784381832991704745

theorem tailTrace_3910217 : CollatzResearch.WordTrace tailWord_3910217 prefixEnd_3910217 2007820784381832991704745 := by
  unfold tailWord_3910217
  simp only [CollatzResearch.WordTrace]
  refine ⟨142617330474959095741488905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95078220316639397160992603 142617330474959095741488905)
  ·
    refine ⟨106962997856219321806116679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142617330474959095741488905 106962997856219321806116679)
    ·
      refine ⟨160444496784328982709175019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106962997856219321806116679 160444496784328982709175019)
      ·
        refine ⟨240666745176493474063762529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160444496784328982709175019 240666745176493474063762529)
        ·
          refine ⟨180500058882370105547821897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240666745176493474063762529 180500058882370105547821897)
          ·
            refine ⟨135375044161777579160866423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180500058882370105547821897 135375044161777579160866423)
            ·
              refine ⟨203062566242666368741299635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135375044161777579160866423 203062566242666368741299635)
              ·
                refine ⟨304593849363999553111949453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203062566242666368741299635 304593849363999553111949453)
                ·
                  refine ⟨114222693511499832416981045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 304593849363999553111949453 114222693511499832416981045)
                  ·
                    refine ⟨10708377516703109289091973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114222693511499832416981045 10708377516703109289091973)
                    ·
                      refine ⟨2007820784381832991704745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10708377516703109289091973 2007820784381832991704745)
                      ·
                        rfl

theorem cell23_3910217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_3910217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910217 prefixEnd_3910217 := by exact prefixLift 3910217
  have htrace : WordTrace (prefixWord ++ tailWord_3910217) baseStart_3910217 baseEnd_3910217 := by
    simpa [prefixWord, tailWord_3910217, baseEnd_3910217] using wordTrace_append hprefix tailTrace_3910217
  have hstable : (prefixWord ++ tailWord_3910217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910217).length < 2 ^ (prefixWord ++ tailWord_3910217).sum := by decide
  have hdescent : baseEnd_3910217 < baseStart_3910217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910251 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 6, 2, 2]
def baseStart_3910251 : Nat := 118140960795 + 3910251 * 2 ^ 59
def prefixEnd_3910251 : Nat := 4983230072969 + 3 ^ 40 * 3910251 * 2
def baseEnd_3910251 : Nat := 2007838242724085858679589

theorem tailTrace_3910251 : CollatzResearch.WordTrace tailWord_3910251 prefixEnd_3910251 2007838242724085858679589 := by
  unfold tailWord_3910251
  simp only [CollatzResearch.WordTrace]
  refine ⟨142618570556835919548226607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95079047037890613032151071 142618570556835919548226607)
  ·
    refine ⟨213927855835253879322339911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142618570556835919548226607 213927855835253879322339911)
    ·
      refine ⟨320891783752880818983509867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213927855835253879322339911 320891783752880818983509867)
      ·
        refine ⟨481337675629321228475264801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320891783752880818983509867 481337675629321228475264801)
        ·
          refine ⟨361003256721990921356448601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481337675629321228475264801 361003256721990921356448601)
          ·
            refine ⟨270752442541493191017336451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361003256721990921356448601 270752442541493191017336451)
            ·
              refine ⟨406128663812239786526004677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 270752442541493191017336451 406128663812239786526004677)
              ·
                refine ⟨76149124464794959973625877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 406128663812239786526004677 76149124464794959973625877)
                ·
                  refine ⟨3569490209287263748763713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76149124464794959973625877 3569490209287263748763713)
                  ·
                    refine ⟨2677117656965447811572785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3569490209287263748763713 2677117656965447811572785)
                    ·
                      refine ⟨2007838242724085858679589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677117656965447811572785 2007838242724085858679589)
                      ·
                        rfl

theorem cell23_3910251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 6, 2, 2].length) (baseStart_3910251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910251 prefixEnd_3910251 := by exact prefixLift 3910251
  have htrace : WordTrace (prefixWord ++ tailWord_3910251) baseStart_3910251 baseEnd_3910251 := by
    simpa [prefixWord, tailWord_3910251, baseEnd_3910251] using wordTrace_append hprefix tailTrace_3910251
  have hstable : (prefixWord ++ tailWord_3910251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910251).length < 2 ^ (prefixWord ++ tailWord_3910251).sum := by decide
  have hdescent : baseEnd_3910251 < baseStart_3910251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910267 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 7]
def baseStart_3910267 : Nat := 118140960795 + 3910267 * 2 ^ 59
def prefixEnd_3910267 : Nat := 4983230072969 + 3 ^ 40 * 3910267 * 2
def baseEnd_3910267 : Nat := 2007846458414557796079515

theorem tailTrace_3910267 : CollatzResearch.WordTrace tailWord_3910267 prefixEnd_3910267 2007846458414557796079515 := by
  unfold tailWord_3910267
  simp only [CollatzResearch.WordTrace]
  refine ⟨142619154124777954280809055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95079436083185302853872703 142619154124777954280809055)
  ·
    refine ⟨213928731187166931421213583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142619154124777954280809055 213928731187166931421213583)
    ·
      refine ⟨320893096780750397131820375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213928731187166931421213583 320893096780750397131820375)
      ·
        refine ⟨481339645171125595697730563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320893096780750397131820375 481339645171125595697730563)
        ·
          refine ⟨722009467756688393546595845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481339645171125595697730563 722009467756688393546595845)
          ·
            refine ⟨135376775204379073789986721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 722009467756688393546595845 135376775204379073789986721)
            ·
              refine ⟨101532581403284305342490041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135376775204379073789986721 101532581403284305342490041)
              ·
                refine ⟨76149436052463229006867531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101532581403284305342490041 76149436052463229006867531)
                ·
                  refine ⟨114224154078694843510301297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76149436052463229006867531 114224154078694843510301297)
                  ·
                    refine ⟨85668115559021132632725973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114224154078694843510301297 85668115559021132632725973)
                    ·
                      refine ⟨2007846458414557796079515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85668115559021132632725973 2007846458414557796079515)
                      ·
                        rfl

theorem cell23_3910267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_3910267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910267 prefixEnd_3910267 := by exact prefixLift 3910267
  have htrace : WordTrace (prefixWord ++ tailWord_3910267) baseStart_3910267 baseEnd_3910267 := by
    simpa [prefixWord, tailWord_3910267, baseEnd_3910267] using wordTrace_append hprefix tailTrace_3910267
  have hstable : (prefixWord ++ tailWord_3910267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910267).length < 2 ^ (prefixWord ++ tailWord_3910267).sum := by decide
  have hdescent : baseEnd_3910267 < baseStart_3910267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910298 : List Nat := [3, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3910298 : Nat := 118140960795 + 3910298 * 2 ^ 59
def prefixEnd_3910298 : Nat := 4983230072969 + 3 ^ 40 * 3910298 * 2
def baseEnd_3910298 : Nat := 2007862376314847174791873

theorem tailTrace_3910298 : CollatzResearch.WordTrace tailWord_3910298 prefixEnd_3910298 2007862376314847174791873 := by
  unfold tailWord_3910298
  simp only [CollatzResearch.WordTrace]
  refine ⟨35655071196916411643796887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95080189858443764383458365 35655071196916411643796887)
  ·
    refine ⟨53482606795374617465695331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35655071196916411643796887 53482606795374617465695331)
    ·
      refine ⟨80223910193061926198542997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53482606795374617465695331 80223910193061926198542997)
      ·
        refine ⟨3760495790299777790556703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80223910193061926198542997 3760495790299777790556703)
        ·
          refine ⟨5640743685449666685835055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3760495790299777790556703 5640743685449666685835055)
          ·
            refine ⟨8461115528174500028752583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5640743685449666685835055 8461115528174500028752583)
            ·
              refine ⟨12691673292261750043128875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461115528174500028752583 12691673292261750043128875)
              ·
                refine ⟨19037509938392625064693313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12691673292261750043128875 19037509938392625064693313)
                ·
                  refine ⟨14278132453794468798519985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19037509938392625064693313 14278132453794468798519985)
                  ·
                    refine ⟨10708599340345851598889989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14278132453794468798519985 10708599340345851598889989)
                    ·
                      refine ⟨2007862376314847174791873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10708599340345851598889989 2007862376314847174791873)
                      ·
                        rfl

theorem cell23_3910298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3910298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910298 prefixEnd_3910298 := by exact prefixLift 3910298
  have htrace : WordTrace (prefixWord ++ tailWord_3910298) baseStart_3910298 baseEnd_3910298 := by
    simpa [prefixWord, tailWord_3910298, baseEnd_3910298] using wordTrace_append hprefix tailTrace_3910298
  have hstable : (prefixWord ++ tailWord_3910298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910298).length < 2 ^ (prefixWord ++ tailWord_3910298).sum := by decide
  have hdescent : baseEnd_3910298 < baseStart_3910298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910428 : List Nat := [2, 2, 3, 1, 1, 3, 3, 2, 1, 5]
def baseStart_3910428 : Nat := 118140960795 + 3910428 * 2 ^ 59
def prefixEnd_3910428 : Nat := 4983230072969 + 3 ^ 40 * 3910428 * 2
def baseEnd_3910428 : Nat := 669309709599977222055425

theorem tailTrace_3910428 : CollatzResearch.WordTrace tailWord_3910428 prefixEnd_3910428 669309709599977222055425 := by
  unfold tailWord_3910428
  simp only [CollatzResearch.WordTrace]
  refine ⟨71312513138597339388709969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95083350851463119184946625 71312513138597339388709969)
  ·
    refine ⟨53484384853948004541532477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71312513138597339388709969 53484384853948004541532477)
    ·
      refine ⟨20056644320230501703074679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53484384853948004541532477 20056644320230501703074679)
      ·
        refine ⟨30084966480345752554612019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20056644320230501703074679 30084966480345752554612019)
        ·
          refine ⟨45127449720518628831918029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30084966480345752554612019 45127449720518628831918029)
          ·
            refine ⟨16922793645194485811969261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45127449720518628831918029 16922793645194485811969261)
            ·
              refine ⟨6346047616947932179488473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16922793645194485811969261 6346047616947932179488473)
              ·
                refine ⟨4759535712710949134616355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6346047616947932179488473 4759535712710949134616355)
                ·
                  refine ⟨7139303569066423701924533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4759535712710949134616355 7139303569066423701924533)
                  ·
                    refine ⟨669309709599977222055425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7139303569066423701924533 669309709599977222055425)
                    ·
                      rfl

theorem cell23_3910428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 1, 5].length) (baseStart_3910428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910428 prefixEnd_3910428 := by exact prefixLift 3910428
  have htrace : WordTrace (prefixWord ++ tailWord_3910428) baseStart_3910428 baseEnd_3910428 := by
    simpa [prefixWord, tailWord_3910428, baseEnd_3910428] using wordTrace_append hprefix tailTrace_3910428
  have hstable : (prefixWord ++ tailWord_3910428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910428).length < 2 ^ (prefixWord ++ tailWord_3910428).sum := by decide
  have hdescent : baseEnd_3910428 < baseStart_3910428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910499 : List Nat := [1, 1, 1, 5, 3, 2, 2, 3, 1, 2, 2]
def baseStart_3910499 : Nat := 118140960795 + 3910499 * 2 ^ 59
def prefixEnd_3910499 : Nat := 4983230072969 + 3 ^ 40 * 3910499 * 2
def baseEnd_3910499 : Nat := 2007965585926400888378449

theorem tailTrace_3910499 : CollatzResearch.WordTrace tailWord_3910499 prefixEnd_3910499 2007965585926400888378449 := by
  unfold tailWord_3910499
  simp only [CollatzResearch.WordTrace]
  refine ⟨142627615859937457903254551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95085077239958305268836367 142627615859937457903254551)
  ·
    refine ⟨213941423789906186854881827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142627615859937457903254551 213941423789906186854881827)
    ·
      refine ⟨320912135684859280282322741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213941423789906186854881827 320912135684859280282322741)
      ·
        refine ⟨30085512720455557526467757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320912135684859280282322741 30085512720455557526467757)
        ·
          refine ⟨11282067270170834072425409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30085512720455557526467757 11282067270170834072425409)
          ·
            refine ⟨8461550452628125554319057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11282067270170834072425409 8461550452628125554319057)
            ·
              refine ⟨6346162839471094165739293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8461550452628125554319057 6346162839471094165739293)
              ·
                refine ⟨2379811064801660312152235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6346162839471094165739293 2379811064801660312152235)
                ·
                  refine ⟨3569716597202490468228353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379811064801660312152235 3569716597202490468228353)
                  ·
                    refine ⟨2677287447901867851171265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3569716597202490468228353 2677287447901867851171265)
                    ·
                      refine ⟨2007965585926400888378449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677287447901867851171265 2007965585926400888378449)
                      ·
                        rfl

theorem cell23_3910499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_3910499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910499 prefixEnd_3910499 := by exact prefixLift 3910499
  have htrace : WordTrace (prefixWord ++ tailWord_3910499) baseStart_3910499 baseEnd_3910499 := by
    simpa [prefixWord, tailWord_3910499, baseEnd_3910499] using wordTrace_append hprefix tailTrace_3910499
  have hstable : (prefixWord ++ tailWord_3910499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910499).length < 2 ^ (prefixWord ++ tailWord_3910499).sum := by decide
  have hdescent : baseEnd_3910499 < baseStart_3910499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910515 : List Nat := [1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 3]
def baseStart_3910515 : Nat := 118140960795 + 3910515 * 2 ^ 59
def prefixEnd_3910515 : Nat := 4983230072969 + 3 ^ 40 * 3910515 * 2
def baseEnd_3910515 : Nat := 2007973801616872825778375

theorem tailTrace_3910515 : CollatzResearch.WordTrace tailWord_3910515 prefixEnd_3910515 2007973801616872825778375 := by
  unfold tailWord_3910515
  simp only [CollatzResearch.WordTrace]
  refine ⟨142628199427879492635836999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95085466285252995090557999 142628199427879492635836999)
  ·
    refine ⟨213942299141819238953755499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142628199427879492635836999 213942299141819238953755499)
    ·
      refine ⟨320913448712728858430633249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213942299141819238953755499 320913448712728858430633249)
      ·
        refine ⟨240685086534546643822974937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320913448712728858430633249 240685086534546643822974937)
        ·
          refine ⟨180513814900909982867231203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240685086534546643822974937 180513814900909982867231203)
          ·
            refine ⟨270770722351364974300846805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180513814900909982867231203 270770722351364974300846805)
            ·
              refine ⟨6346188805110116585176097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 270770722351364974300846805 6346188805110116585176097)
              ·
                refine ⟨4759641603832587438882073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6346188805110116585176097 4759641603832587438882073)
                ·
                  refine ⟨3569731202874440579161555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4759641603832587438882073 3569731202874440579161555)
                  ·
                    refine ⟨5354596804311660868742333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3569731202874440579161555 5354596804311660868742333)
                    ·
                      refine ⟨2007973801616872825778375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5354596804311660868742333 2007973801616872825778375)
                      ·
                        rfl

theorem cell23_3910515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 3].length) (baseStart_3910515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910515 prefixEnd_3910515 := by exact prefixLift 3910515
  have htrace : WordTrace (prefixWord ++ tailWord_3910515) baseStart_3910515 baseEnd_3910515 := by
    simpa [prefixWord, tailWord_3910515, baseEnd_3910515] using wordTrace_append hprefix tailTrace_3910515
  have hstable : (prefixWord ++ tailWord_3910515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910515).length < 2 ^ (prefixWord ++ tailWord_3910515).sum := by decide
  have hdescent : baseEnd_3910515 < baseStart_3910515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910531 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 2, 6]
def baseStart_3910531 : Nat := 118140960795 + 3910531 * 2 ^ 59
def prefixEnd_3910531 : Nat := 4983230072969 + 3 ^ 40 * 3910531 * 2
def baseEnd_3910531 : Nat := 669327339102448254392767

theorem tailTrace_3910531 : CollatzResearch.WordTrace tailWord_3910531 prefixEnd_3910531 669327339102448254392767 := by
  unfold tailWord_3910531
  simp only [CollatzResearch.WordTrace]
  refine ⟨142628782995821527368419447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95085855330547684912279631 142628782995821527368419447)
  ·
    refine ⟨213943174493732291052629171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142628782995821527368419447 213943174493732291052629171)
    ·
      refine ⟨320914761740598436578943757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213943174493732291052629171 320914761740598436578943757)
      ·
        refine ⟨120343035652724413717103909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 320914761740598436578943757 120343035652724413717103909)
        ·
          refine ⟨22564319184885827571956983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120343035652724413717103909 22564319184885827571956983)
          ·
            refine ⟨33846478777328741357935475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22564319184885827571956983 33846478777328741357935475)
            ·
              refine ⟨50769718165993112036903213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33846478777328741357935475 50769718165993112036903213)
              ·
                refine ⟨19038644312247417013838705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50769718165993112036903213 19038644312247417013838705)
                ·
                  refine ⟨14278983234185562760379029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19038644312247417013838705 14278983234185562760379029)
                  ·
                    refine ⟨669327339102448254392767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14278983234185562760379029 669327339102448254392767)
                    ·
                      rfl

theorem cell23_3910531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 6].length) (baseStart_3910531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910531 prefixEnd_3910531 := by exact prefixLift 3910531
  have htrace : WordTrace (prefixWord ++ tailWord_3910531) baseStart_3910531 baseEnd_3910531 := by
    simpa [prefixWord, tailWord_3910531, baseEnd_3910531] using wordTrace_append hprefix tailTrace_3910531
  have hstable : (prefixWord ++ tailWord_3910531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910531).length < 2 ^ (prefixWord ++ tailWord_3910531).sum := by decide
  have hdescent : baseEnd_3910531 < baseStart_3910531 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910550 : List Nat := [5, 3, 1, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_3910550 : Nat := 118140960795 + 3910550 * 2 ^ 59
def prefixEnd_3910550 : Nat := 4983230072969 + 3 ^ 40 * 3910550 * 2
def baseEnd_3910550 : Nat := 2007991773439780188840715

theorem tailTrace_3910550 : CollatzResearch.WordTrace tailWord_3910550 prefixEnd_3910550 2007991773439780188840715 := by
  unfold tailWord_3910550
  simp only [CollatzResearch.WordTrace]
  refine ⟨8914342248922043350835069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95086317321835129075574069 8914342248922043350835069)
  ·
    refine ⟨3342878343345766256563151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8914342248922043350835069 3342878343345766256563151)
    ·
      refine ⟨5014317515018649384844727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3342878343345766256563151 5014317515018649384844727)
      ·
        refine ⟨7521476272527974077267091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5014317515018649384844727 7521476272527974077267091)
        ·
          refine ⟨11282214408791961115900637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7521476272527974077267091 11282214408791961115900637)
          ·
            refine ⟨4230830403296985418462739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11282214408791961115900637 4230830403296985418462739)
            ·
              refine ⟨6346245604945478127694109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4230830403296985418462739 6346245604945478127694109)
              ·
                refine ⟨2379842101854554297885291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6346245604945478127694109 2379842101854554297885291)
                ·
                  refine ⟨3569763152781831446827937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2379842101854554297885291 3569763152781831446827937)
                  ·
                    refine ⟨2677322364586373585120953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3569763152781831446827937 2677322364586373585120953)
                    ·
                      refine ⟨2007991773439780188840715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677322364586373585120953 2007991773439780188840715)
                      ·
                        rfl

theorem cell23_3910550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_3910550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910550 prefixEnd_3910550 := by exact prefixLift 3910550
  have htrace : WordTrace (prefixWord ++ tailWord_3910550) baseStart_3910550 baseEnd_3910550 := by
    simpa [prefixWord, tailWord_3910550, baseEnd_3910550] using wordTrace_append hprefix tailTrace_3910550
  have hstable : (prefixWord ++ tailWord_3910550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910550).length < 2 ^ (prefixWord ++ tailWord_3910550).sum := by decide
  have hdescent : baseEnd_3910550 < baseStart_3910550 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910589 : List Nat := [1, 4, 1, 2, 4, 1, 1, 3, 2, 2, 2]
def baseStart_3910589 : Nat := 118140960795 + 3910589 * 2 ^ 59
def prefixEnd_3910589 : Nat := 4983230072969 + 3 ^ 40 * 3910589 * 2
def baseEnd_3910589 : Nat := 2008011799185305536253035

theorem tailTrace_3910589 : CollatzResearch.WordTrace tailWord_3910589 prefixEnd_3910589 2008011799185305536253035 := by
  unfold tailWord_3910589
  simp only [CollatzResearch.WordTrace]
  refine ⟨142630898429611403274030821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95087265619740935516020547 142630898429611403274030821)
  ·
    refine ⟨26743293455552138113880779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142630898429611403274030821 26743293455552138113880779)
    ·
      refine ⟨40114940183328207170821169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26743293455552138113880779 40114940183328207170821169)
      ·
        refine ⟨30086205137496155378115877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40114940183328207170821169 30086205137496155378115877)
        ·
          refine ⟨5641163463280529133396727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30086205137496155378115877 5641163463280529133396727)
          ·
            refine ⟨8461745194920793700095091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5641163463280529133396727 8461745194920793700095091)
            ·
              refine ⟨12692617792381190550142637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461745194920793700095091 12692617792381190550142637)
              ·
                refine ⟨4759731672142946456303489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12692617792381190550142637 4759731672142946456303489)
                ·
                  refine ⟨3569798754107209842227617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4759731672142946456303489 3569798754107209842227617)
                  ·
                    refine ⟨2677349065580407381670713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3569798754107209842227617 2677349065580407381670713)
                    ·
                      refine ⟨2008011799185305536253035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677349065580407381670713 2008011799185305536253035)
                      ·
                        rfl

theorem cell23_3910589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 2, 2].length) (baseStart_3910589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910589 prefixEnd_3910589 := by exact prefixLift 3910589
  have htrace : WordTrace (prefixWord ++ tailWord_3910589) baseStart_3910589 baseEnd_3910589 := by
    simpa [prefixWord, tailWord_3910589, baseEnd_3910589] using wordTrace_append hprefix tailTrace_3910589
  have hstable : (prefixWord ++ tailWord_3910589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910589).length < 2 ^ (prefixWord ++ tailWord_3910589).sum := by decide
  have hdescent : baseEnd_3910589 < baseStart_3910589 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910591 : List Nat := [1, 1, 2, 2, 2, 1, 2, 4, 1, 7]
def baseStart_3910591 : Nat := 118140960795 + 3910591 * 2 ^ 59
def prefixEnd_3910591 : Nat := 4983230072969 + 3 ^ 40 * 3910591 * 2
def baseEnd_3910591 : Nat := 669337608715538176142675

theorem tailTrace_3910591 : CollatzResearch.WordTrace tailWord_3910591 prefixEnd_3910591 669337608715538176142675 := by
  unfold tailWord_3910591
  simp only [CollatzResearch.WordTrace]
  refine ⟨142630971375604157615603627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95087314250402771743735751 142630971375604157615603627)
  ·
    refine ⟨213946457063406236423405441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142630971375604157615603627 213946457063406236423405441)
    ·
      refine ⟨160459842797554677317554081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213946457063406236423405441 160459842797554677317554081)
      ·
        refine ⟨120344882098166007988165561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160459842797554677317554081 120344882098166007988165561)
        ·
          refine ⟨90258661573624505991124171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120344882098166007988165561 90258661573624505991124171)
          ·
            refine ⟨135387992360436758986686257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90258661573624505991124171 135387992360436758986686257)
            ·
              refine ⟨101540994270327569240014693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135387992360436758986686257 101540994270327569240014693)
              ·
                refine ⟨19038936425686419232502755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101540994270327569240014693 19038936425686419232502755)
                ·
                  refine ⟨28558404638529628848754133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19038936425686419232502755 28558404638529628848754133)
                  ·
                    refine ⟨669337608715538176142675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28558404638529628848754133 669337608715538176142675)
                    ·
                      rfl

theorem cell23_3910591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_3910591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910591 prefixEnd_3910591 := by exact prefixLift 3910591
  have htrace : WordTrace (prefixWord ++ tailWord_3910591) baseStart_3910591 baseEnd_3910591 := by
    simpa [prefixWord, tailWord_3910591, baseEnd_3910591] using wordTrace_append hprefix tailTrace_3910591
  have hstable : (prefixWord ++ tailWord_3910591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910591).length < 2 ^ (prefixWord ++ tailWord_3910591).sum := by decide
  have hdescent : baseEnd_3910591 < baseStart_3910591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910601 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_3910601 : Nat := 118140960795 + 3910601 * 2 ^ 59
def prefixEnd_3910601 : Nat := 4983230072969 + 3 ^ 40 * 3910601 * 2
def baseEnd_3910601 : Nat := 2008017960953159489302979

theorem tailTrace_3910601 : CollatzResearch.WordTrace tailWord_3910601 prefixEnd_3910601 2008017960953159489302979 := by
  unfold tailWord_3910601
  simp only [CollatzResearch.WordTrace]
  refine ⟨142631336105567929323467657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95087557403711952882311771 142631336105567929323467657)
  ·
    refine ⟨106973502079175946992600743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142631336105567929323467657 106973502079175946992600743)
    ·
      refine ⟨160460253118763920488901115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106973502079175946992600743 160460253118763920488901115)
      ·
        refine ⟨240690379678145880733351673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160460253118763920488901115 240690379678145880733351673)
        ·
          refine ⟨180517784758609410550013755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240690379678145880733351673 180517784758609410550013755)
          ·
            refine ⟨270776677137914115825020633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180517784758609410550013755 270776677137914115825020633)
            ·
              refine ⟨203082507853435586868765475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270776677137914115825020633 203082507853435586868765475)
              ·
                refine ⟨304623761780153380303148213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203082507853435586868765475 304623761780153380303148213)
                ·
                  refine ⟨28558477666889379403420145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 304623761780153380303148213 28558477666889379403420145)
                  ·
                    refine ⟨21418858250167034552565109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28558477666889379403420145 21418858250167034552565109)
                    ·
                      refine ⟨2008017960953159489302979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21418858250167034552565109 2008017960953159489302979)
                      ·
                        rfl

theorem cell23_3910601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_3910601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910601 prefixEnd_3910601 := by exact prefixLift 3910601
  have htrace : WordTrace (prefixWord ++ tailWord_3910601) baseStart_3910601 baseEnd_3910601 := by
    simpa [prefixWord, tailWord_3910601, baseEnd_3910601] using wordTrace_append hprefix tailTrace_3910601
  have hstable : (prefixWord ++ tailWord_3910601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910601).length < 2 ^ (prefixWord ++ tailWord_3910601).sum := by decide
  have hdescent : baseEnd_3910601 < baseStart_3910601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910618 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5]
def baseStart_3910618 : Nat := 118140960795 + 3910618 * 2 ^ 59
def prefixEnd_3910618 : Nat := 4983230072969 + 3 ^ 40 * 3910618 * 2
def baseEnd_3910618 : Nat := 2008026690124285922790401

theorem tailTrace_3910618 : CollatzResearch.WordTrace tailWord_3910618 prefixEnd_3910618 2008026690124285922790401 := by
  unfold tailWord_3910618
  simp only [CollatzResearch.WordTrace]
  refine ⟨35657989036626585306709127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95087970764337560817891005 35657989036626585306709127)
  ·
    refine ⟨53486983554939877960063691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35657989036626585306709127 53486983554939877960063691)
    ·
      refine ⟨80230475332409816940095537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53486983554939877960063691 80230475332409816940095537)
      ·
        refine ⟨60172856499307362705071653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80230475332409816940095537 60172856499307362705071653)
        ·
          refine ⟨11282410593620130507200935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60172856499307362705071653 11282410593620130507200935)
          ·
            refine ⟨16923615890430195760801403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282410593620130507200935 16923615890430195760801403)
            ·
              refine ⟨25385423835645293641202105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16923615890430195760801403 25385423835645293641202105)
              ·
                refine ⟨19039067876733970230901579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25385423835645293641202105 19039067876733970230901579)
                ·
                  refine ⟨28558601815100955346352369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19039067876733970230901579 28558601815100955346352369)
                  ·
                    refine ⟨21418951361325716509764277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28558601815100955346352369 21418951361325716509764277)
                    ·
                      refine ⟨2008026690124285922790401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21418951361325716509764277 2008026690124285922790401)
                      ·
                        rfl

theorem cell23_3910618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_3910618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910618 prefixEnd_3910618 := by exact prefixLift 3910618
  have htrace : WordTrace (prefixWord ++ tailWord_3910618) baseStart_3910618 baseEnd_3910618 := by
    simpa [prefixWord, tailWord_3910618, baseEnd_3910618] using wordTrace_append hprefix tailTrace_3910618
  have hstable : (prefixWord ++ tailWord_3910618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910618).length < 2 ^ (prefixWord ++ tailWord_3910618).sum := by decide
  have hdescent : baseEnd_3910618 < baseStart_3910618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910628 : List Nat := [2, 3, 1, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_3910628 : Nat := 118140960795 + 3910628 * 2 ^ 59
def prefixEnd_3910628 : Nat := 4983230072969 + 3 ^ 40 * 3910628 * 2
def baseEnd_3910628 : Nat := 2008031824930830883665355

theorem tailTrace_3910628 : CollatzResearch.WordTrace tailWord_3910628 prefixEnd_3910628 2008031824930830883665355 := by
  unfold tailWord_3910628
  simp only [CollatzResearch.WordTrace]
  refine ⟨71316160438235056467350269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95088213917646741956467025 71316160438235056467350269)
  ·
    refine ⟨26743560164338146175256351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71316160438235056467350269 26743560164338146175256351)
    ·
      refine ⟨40115340246507219262884527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26743560164338146175256351 40115340246507219262884527)
      ·
        refine ⟨60173010369760828894326791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40115340246507219262884527 60173010369760828894326791)
        ·
          refine ⟨90259515554641243341490187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60173010369760828894326791 90259515554641243341490187)
          ·
            refine ⟨135389273331961865012235281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90259515554641243341490187 135389273331961865012235281)
            ·
              refine ⟨101541954998971398759176461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135389273331961865012235281 101541954998971398759176461)
              ·
                refine ⟨38078233124614274534691173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101541954998971398759176461 38078233124614274534691173)
                ·
                  refine ⟨7139668710865176475254595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38078233124614274534691173 7139668710865176475254595)
                  ·
                    refine ⟨10709503066297764712881893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7139668710865176475254595 10709503066297764712881893)
                    ·
                      refine ⟨2008031824930830883665355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10709503066297764712881893 2008031824930830883665355)
                      ·
                        rfl

theorem cell23_3910628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_3910628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910628 prefixEnd_3910628 := by exact prefixLift 3910628
  have htrace : WordTrace (prefixWord ++ tailWord_3910628) baseStart_3910628 baseEnd_3910628 := by
    simpa [prefixWord, tailWord_3910628, baseEnd_3910628] using wordTrace_append hprefix tailTrace_3910628
  have hstable : (prefixWord ++ tailWord_3910628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910628).length < 2 ^ (prefixWord ++ tailWord_3910628).sum := by decide
  have hdescent : baseEnd_3910628 < baseStart_3910628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910648 : List Nat := [2, 1, 2, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_3910648 : Nat := 118140960795 + 3910648 * 2 ^ 59
def prefixEnd_3910648 : Nat := 4983230072969 + 3 ^ 40 * 3910648 * 2
def baseEnd_3910648 : Nat := 2008042094543920805415263

theorem tailTrace_3910648 : CollatzResearch.WordTrace tailWord_3910648 prefixEnd_3910648 2008042094543920805415263 := by
  unfold tailWord_3910648
  simp only [CollatzResearch.WordTrace]
  refine ⟨71316525168198828175214299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95088700224265104233619065 71316525168198828175214299)
  ·
    refine ⟨106974787752298242262821449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71316525168198828175214299 106974787752298242262821449)
    ·
      refine ⟨80231090814223681697116087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106974787752298242262821449 80231090814223681697116087)
      ·
        refine ⟨120346636221335522545674131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80231090814223681697116087 120346636221335522545674131)
        ·
          refine ⟨180519954332003283818511197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120346636221335522545674131 180519954332003283818511197)
          ·
            refine ⟨67694982874501231431941699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180519954332003283818511197 67694982874501231431941699)
            ·
              refine ⟨101542474311751847147912549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67694982874501231431941699 101542474311751847147912549)
              ·
                refine ⟨19039213933453471340233603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101542474311751847147912549 19039213933453471340233603)
                ·
                  refine ⟨28558820900180207010350405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19039213933453471340233603 28558820900180207010350405)
                  ·
                    refine ⟨5354778918783788814440701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28558820900180207010350405 5354778918783788814440701)
                    ·
                      refine ⟨2008042094543920805415263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5354778918783788814440701 2008042094543920805415263)
                      ·
                        rfl

theorem cell23_3910648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_3910648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910648 prefixEnd_3910648 := by exact prefixLift 3910648
  have htrace : WordTrace (prefixWord ++ tailWord_3910648) baseStart_3910648 baseEnd_3910648 := by
    simpa [prefixWord, tailWord_3910648, baseEnd_3910648] using wordTrace_append hprefix tailTrace_3910648
  have hstable : (prefixWord ++ tailWord_3910648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910648).length < 2 ^ (prefixWord ++ tailWord_3910648).sum := by decide
  have hdescent : baseEnd_3910648 < baseStart_3910648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910651 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 10]
def baseStart_3910651 : Nat := 118140960795 + 3910651 * 2 ^ 59
def prefixEnd_3910651 : Nat := 4983230072969 + 3 ^ 40 * 3910651 * 2
def baseEnd_3910651 : Nat := 223115959442876032630861

theorem tailTrace_3910651 : CollatzResearch.WordTrace tailWord_3910651 prefixEnd_3910651 223115959442876032630861 := by
  unfold tailWord_3910651
  simp only [CollatzResearch.WordTrace]
  refine ⟨142633159755386787862787807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95088773170257858575191871 142633159755386787862787807)
  ·
    refine ⟨213949739633080181794181711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142633159755386787862787807 213949739633080181794181711)
    ·
      refine ⟨320924609449620272691272567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213949739633080181794181711 320924609449620272691272567)
      ·
        refine ⟨481386914174430409036908851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320924609449620272691272567 481386914174430409036908851)
        ·
          refine ⟨722080371261645613555363277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481386914174430409036908851 722080371261645613555363277)
          ·
            refine ⟨270780139223117105083261229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 722080371261645613555363277 270780139223117105083261229)
            ·
              refine ⟨101542552208668914406222961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270780139223117105083261229 101542552208668914406222961)
              ·
                refine ⟨76156914156501685804667221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101542552208668914406222961 76156914156501685804667221)
                ·
                  refine ⟨223115959442876032630861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 76156914156501685804667221 223115959442876032630861)
                  ·
                    rfl

theorem cell23_3910651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 10].length) (baseStart_3910651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910651 prefixEnd_3910651 := by exact prefixLift 3910651
  have htrace : WordTrace (prefixWord ++ tailWord_3910651) baseStart_3910651 baseEnd_3910651 := by
    simpa [prefixWord, tailWord_3910651, baseEnd_3910651] using wordTrace_append hprefix tailTrace_3910651
  have hstable : (prefixWord ++ tailWord_3910651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910651).length < 2 ^ (prefixWord ++ tailWord_3910651).sum := by decide
  have hdescent : baseEnd_3910651 < baseStart_3910651 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910685 : List Nat := [1, 4, 2, 2, 3, 1, 1, 1, 8]
def baseStart_3910685 : Nat := 118140960795 + 3910685 * 2 ^ 59
def prefixEnd_3910685 : Nat := 4983230072969 + 3 ^ 40 * 3910685 * 2
def baseEnd_3910685 : Nat := 223117899258681906739177

theorem tailTrace_3910685 : CollatzResearch.WordTrace tailWord_3910685 prefixEnd_3910685 223117899258681906739177 := by
  unfold tailWord_3910685
  simp only [CollatzResearch.WordTrace]
  refine ⟨142634399837263611669525509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95089599891509074446350339 142634399837263611669525509)
  ·
    refine ⟨26743949969486927188036033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142634399837263611669525509 26743949969486927188036033)
    ·
      refine ⟨20057962477115195391027025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26743949969486927188036033 20057962477115195391027025)
      ·
        refine ⟨15043471857836396543270269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20057962477115195391027025 15043471857836396543270269)
        ·
          refine ⟨5641301946688648703726351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15043471857836396543270269 5641301946688648703726351)
          ·
            refine ⟨8461952920032973055589527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5641301946688648703726351 8461952920032973055589527)
            ·
              refine ⟨12692929380049459583384291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8461952920032973055589527 12692929380049459583384291)
              ·
                refine ⟨19039394070074189375076437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12692929380049459583384291 19039394070074189375076437)
                ·
                  refine ⟨223117899258681906739177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19039394070074189375076437 223117899258681906739177)
                  ·
                    rfl

theorem cell23_3910685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_3910685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910685 prefixEnd_3910685 := by exact prefixLift 3910685
  have htrace : WordTrace (prefixWord ++ tailWord_3910685) baseStart_3910685 baseEnd_3910685 := by
    simpa [prefixWord, tailWord_3910685, baseEnd_3910685] using wordTrace_append hprefix tailTrace_3910685
  have hstable : (prefixWord ++ tailWord_3910685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910685).length < 2 ^ (prefixWord ++ tailWord_3910685).sum := by decide
  have hdescent : baseEnd_3910685 < baseStart_3910685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910702 : List Nat := [4, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_3910702 : Nat := 118140960795 + 3910702 * 2 ^ 59
def prefixEnd_3910702 : Nat := 4983230072969 + 3 ^ 40 * 3910702 * 2
def baseEnd_3910702 : Nat := 223118869166584843793335

theorem tailTrace_3910702 : CollatzResearch.WordTrace tailWord_3910702 prefixEnd_3910702 223118869166584843793335 := by
  unfold tailWord_3910702
  simp only [CollatzResearch.WordTrace]
  refine ⟨17829377484775252946611795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95090013252134682381929573 17829377484775252946611795)
  ·
    refine ⟨26744066227162879419917693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17829377484775252946611795 26744066227162879419917693)
    ·
      refine ⟨10029024835186079782469135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26744066227162879419917693 10029024835186079782469135)
      ·
        refine ⟨15043537252779119673703703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10029024835186079782469135 15043537252779119673703703)
        ·
          refine ⟨22565305879168679510555555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15043537252779119673703703 22565305879168679510555555)
          ·
            refine ⟨33847958818753019265833333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22565305879168679510555555 33847958818753019265833333)
            ·
              refine ⟨3173246139258095556171875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 33847958818753019265833333 3173246139258095556171875)
              ·
                refine ⟨4759869208887143334257813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173246139258095556171875 4759869208887143334257813)
                ·
                  refine ⟨223118869166584843793335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4759869208887143334257813 223118869166584843793335)
                  ·
                    rfl

theorem cell23_3910702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_3910702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910702 prefixEnd_3910702 := by exact prefixLift 3910702
  have htrace : WordTrace (prefixWord ++ tailWord_3910702) baseStart_3910702 baseEnd_3910702 := by
    simpa [prefixWord, tailWord_3910702, baseEnd_3910702] using wordTrace_append hprefix tailTrace_3910702
  have hstable : (prefixWord ++ tailWord_3910702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910702).length < 2 ^ (prefixWord ++ tailWord_3910702).sum := by decide
  have hdescent : baseEnd_3910702 < baseStart_3910702 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910705 : List Nat := [1, 2, 2, 3, 1, 2, 1, 1, 3, 5, 2]
def baseStart_3910705 : Nat := 118140960795 + 3910705 * 2 ^ 59
def prefixEnd_3910705 : Nat := 4983230072969 + 3 ^ 40 * 3910705 * 2
def baseEnd_3910705 : Nat := 2008071362941227082402501

theorem tailTrace_3910705 : CollatzResearch.WordTrace tailWord_3910705 prefixEnd_3910705 2008071362941227082402501 := by
  unfold tailWord_3910705
  simp only [CollatzResearch.WordTrace]
  refine ⟨142635129297191155085253569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95090086198127436723502379 142635129297191155085253569)
  ·
    refine ⟨106976346972893366313940177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142635129297191155085253569 106976346972893366313940177)
    ·
      refine ⟨80232260229670024735455133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106976346972893366313940177 80232260229670024735455133)
      ·
        refine ⟨30087097586126259275795675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80232260229670024735455133 30087097586126259275795675)
        ·
          refine ⟨45130646379189388913693513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30087097586126259275795675 45130646379189388913693513)
          ·
            refine ⟨33847984784392041685270135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45130646379189388913693513 33847984784392041685270135)
            ·
              refine ⟨50771977176588062527905203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33847984784392041685270135 50771977176588062527905203)
              ·
                refine ⟨76157965764882093791857805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50771977176588062527905203 76157965764882093791857805)
                ·
                  refine ⟨28559237161830785171946677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76157965764882093791857805 28559237161830785171946677)
                  ·
                    refine ⟨2677428483921636109870001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28559237161830785171946677 2677428483921636109870001)
                    ·
                      refine ⟨2008071362941227082402501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677428483921636109870001 2008071362941227082402501)
                      ·
                        rfl

theorem cell23_3910705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_3910705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910705 prefixEnd_3910705 := by exact prefixLift 3910705
  have htrace : WordTrace (prefixWord ++ tailWord_3910705) baseStart_3910705 baseEnd_3910705 := by
    simpa [prefixWord, tailWord_3910705, baseEnd_3910705] using wordTrace_append hprefix tailTrace_3910705
  have hstable : (prefixWord ++ tailWord_3910705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910705).length < 2 ^ (prefixWord ++ tailWord_3910705).sum := by decide
  have hdescent : baseEnd_3910705 < baseStart_3910705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910712 : List Nat := [2, 1, 2, 1, 5, 1, 2, 2, 3, 1, 3]
def baseStart_3910712 : Nat := 118140960795 + 3910712 * 2 ^ 59
def prefixEnd_3910712 : Nat := 4983230072969 + 3 ^ 40 * 3910712 * 2
def baseEnd_3910712 : Nat := 2008074957305808555014969

theorem tailTrace_3910712 : CollatzResearch.WordTrace tailWord_3910712 prefixEnd_3910712 2008074957305808555014969 := by
  unfold tailWord_3910712
  simp only [CollatzResearch.WordTrace]
  refine ⟨71317692304082897640379195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95090256405443863520505593 71317692304082897640379195)
  ·
    refine ⟨106976538456124346460568793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71317692304082897640379195 106976538456124346460568793)
    ·
      refine ⟨80232403842093259845426595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106976538456124346460568793 80232403842093259845426595)
      ·
        refine ⟨120348605763139889768139893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80232403842093259845426595 120348605763139889768139893)
        ·
          refine ⟨11282681790294364665763115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120348605763139889768139893 11282681790294364665763115)
          ·
            refine ⟨16924022685441546998644673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11282681790294364665763115 16924022685441546998644673)
            ·
              refine ⟨12693017014081160248983505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16924022685441546998644673 12693017014081160248983505)
              ·
                refine ⟨9519762760560870186737629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12693017014081160248983505 9519762760560870186737629)
                ·
                  refine ⟨3569911035210326320026611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9519762760560870186737629 3569911035210326320026611)
                  ·
                    refine ⟨5354866552815489480039917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3569911035210326320026611 5354866552815489480039917)
                    ·
                      refine ⟨2008074957305808555014969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5354866552815489480039917 2008074957305808555014969)
                      ·
                        rfl

theorem cell23_3910712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_3910712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910712 prefixEnd_3910712 := by exact prefixLift 3910712
  have htrace : WordTrace (prefixWord ++ tailWord_3910712) baseStart_3910712 baseEnd_3910712 := by
    simpa [prefixWord, tailWord_3910712, baseEnd_3910712] using wordTrace_append hprefix tailTrace_3910712
  have hstable : (prefixWord ++ tailWord_3910712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910712).length < 2 ^ (prefixWord ++ tailWord_3910712).sum := by decide
  have hdescent : baseEnd_3910712 < baseStart_3910712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910728 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 3, 6]
def baseStart_3910728 : Nat := 118140960795 + 3910728 * 2 ^ 59
def prefixEnd_3910728 : Nat := 4983230072969 + 3 ^ 40 * 3910728 * 2
def baseEnd_3910728 : Nat := 669361057665426830804965

theorem tailTrace_3910728 : CollatzResearch.WordTrace tailWord_3910728 prefixEnd_3910728 669361057665426830804965 := by
  unfold tailWord_3910728
  simp only [CollatzResearch.WordTrace]
  refine ⟨71317984088053915006670419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95090645450738553342227225 71317984088053915006670419)
  ·
    refine ⟨106976976132080872510005629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71317984088053915006670419 106976976132080872510005629)
    ·
      refine ⟨40116366049530327191252111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106976976132080872510005629 40116366049530327191252111)
      ·
        refine ⟨60174549074295490786878167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40116366049530327191252111 60174549074295490786878167)
        ·
          refine ⟨90261823611443236180317251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60174549074295490786878167 90261823611443236180317251)
          ·
            refine ⟨135392735417164854270475877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90261823611443236180317251 135392735417164854270475877)
            ·
              refine ⟨25386137890718410175714227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135392735417164854270475877 25386137890718410175714227)
              ·
                refine ⟨38079206836077615263571341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25386137890718410175714227 38079206836077615263571341)
                ·
                  refine ⟨14279702563529105723839253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38079206836077615263571341 14279702563529105723839253)
                  ·
                    refine ⟨669361057665426830804965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14279702563529105723839253 669361057665426830804965)
                    ·
                      rfl

theorem cell23_3910728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_3910728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910728 prefixEnd_3910728 := by exact prefixLift 3910728
  have htrace : WordTrace (prefixWord ++ tailWord_3910728) baseStart_3910728 baseEnd_3910728 := by
    simpa [prefixWord, tailWord_3910728, baseEnd_3910728] using wordTrace_append hprefix tailTrace_3910728
  have hstable : (prefixWord ++ tailWord_3910728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910728).length < 2 ^ (prefixWord ++ tailWord_3910728).sum := by decide
  have hdescent : baseEnd_3910728 < baseStart_3910728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910755 : List Nat := [1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 3]
def baseStart_3910755 : Nat := 118140960795 + 3910755 * 2 ^ 59
def prefixEnd_3910755 : Nat := 4983230072969 + 3 ^ 40 * 3910755 * 2
def baseEnd_3910755 : Nat := 2008097036973951886777271

theorem tailTrace_3910755 : CollatzResearch.WordTrace tailWord_3910755 prefixEnd_3910755 2008097036973951886777271 := by
  unfold tailWord_3910755
  simp only [CollatzResearch.WordTrace]
  refine ⟨142636952947010013624573719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95091301964673342416382479 142636952947010013624573719)
  ·
    refine ⟨213955429420515020436860579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142636952947010013624573719 213955429420515020436860579)
    ·
      refine ⟨320933144130772530655290869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213955429420515020436860579 320933144130772530655290869)
      ·
        refine ⟨30087482262259924748933519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 320933144130772530655290869 30087482262259924748933519)
        ·
          refine ⟨45131223393389887123400279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30087482262259924748933519 45131223393389887123400279)
          ·
            refine ⟨67696835090084830685100419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45131223393389887123400279 67696835090084830685100419)
            ·
              refine ⟨101545252635127246027650629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67696835090084830685100419 101545252635127246027650629)
              ·
                refine ⟨19039734869086358630184493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101545252635127246027650629 19039734869086358630184493)
                ·
                  refine ⟨7139900575907384486319185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19039734869086358630184493 7139900575907384486319185)
                  ·
                    refine ⟨5354925431930538364739389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7139900575907384486319185 5354925431930538364739389)
                    ·
                      refine ⟨2008097036973951886777271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5354925431930538364739389 2008097036973951886777271)
                      ·
                        rfl

theorem cell23_3910755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_3910755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910755 prefixEnd_3910755 := by exact prefixLift 3910755
  have htrace : WordTrace (prefixWord ++ tailWord_3910755) baseStart_3910755 baseEnd_3910755 := by
    simpa [prefixWord, tailWord_3910755, baseEnd_3910755] using wordTrace_append hprefix tailTrace_3910755
  have hstable : (prefixWord ++ tailWord_3910755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910755).length < 2 ^ (prefixWord ++ tailWord_3910755).sum := by decide
  have hdescent : baseEnd_3910755 < baseStart_3910755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910765 : List Nat := [1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_3910765 : Nat := 118140960795 + 3910765 * 2 ^ 59
def prefixEnd_3910765 : Nat := 4983230072969 + 3 ^ 40 * 3910765 * 2
def baseEnd_3910765 : Nat := 2008102171780496847652225

theorem tailTrace_3910765 : CollatzResearch.WordTrace tailWord_3910765 prefixEnd_3910765 2008102171780496847652225 := by
  unfold tailWord_3910765
  simp only [CollatzResearch.WordTrace]
  refine ⟨142637317676973785332437749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95091545117982523554958499 142637317676973785332437749)
  ·
    refine ⟨13372248532216292374916039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 142637317676973785332437749 13372248532216292374916039)
    ·
      refine ⟨20058372798324438562374059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13372248532216292374916039 20058372798324438562374059)
      ·
        refine ⟨30087559197486657843561089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20058372798324438562374059 30087559197486657843561089)
        ·
          refine ⟨22565669398114993382670817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30087559197486657843561089 22565669398114993382670817)
          ·
            refine ⟨16924252048586245037003113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22565669398114993382670817 16924252048586245037003113)
            ·
              refine ⟨12693189036439683777752335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16924252048586245037003113 12693189036439683777752335)
              ·
                refine ⟨19039783554659525666628503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12693189036439683777752335 19039783554659525666628503)
                ·
                  refine ⟨28559675331989288499942755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19039783554659525666628503 28559675331989288499942755)
                  ·
                    refine ⟨42839512997983932749914133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28559675331989288499942755 42839512997983932749914133)
                    ·
                      refine ⟨2008102171780496847652225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42839512997983932749914133 2008102171780496847652225)
                      ·
                        rfl

theorem cell23_3910765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_3910765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910765 prefixEnd_3910765 := by exact prefixLift 3910765
  have htrace : WordTrace (prefixWord ++ tailWord_3910765) baseStart_3910765 baseEnd_3910765 := by
    simpa [prefixWord, tailWord_3910765, baseEnd_3910765] using wordTrace_append hprefix tailTrace_3910765
  have hstable : (prefixWord ++ tailWord_3910765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910765).length < 2 ^ (prefixWord ++ tailWord_3910765).sum := by decide
  have hdescent : baseEnd_3910765 < baseStart_3910765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910789 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 1, 1, 5]
def baseStart_3910789 : Nat := 118140960795 + 3910789 * 2 ^ 59
def prefixEnd_3910789 : Nat := 4983230072969 + 3 ^ 40 * 3910789 * 2
def baseEnd_3910789 : Nat := 2008114495316204753752115

theorem tailTrace_3910789 : CollatzResearch.WordTrace tailWord_3910789 prefixEnd_3910789 2008114495316204753752115 := by
  unfold tailWord_3910789
  simp only [CollatzResearch.WordTrace]
  refine ⟨142638193028886837431311421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95092128685924558287540947 142638193028886837431311421)
  ·
    refine ⟨53489322385832564036741783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142638193028886837431311421 53489322385832564036741783)
    ·
      refine ⟨80233983578748846055112675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53489322385832564036741783 80233983578748846055112675)
      ·
        refine ⟨120350975368123269082669013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80233983578748846055112675 120350975368123269082669013)
        ·
          refine ⟨2820725985190389119125055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 120350975368123269082669013 2820725985190389119125055)
          ·
            refine ⟨4231088977785583678687583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2820725985190389119125055 4231088977785583678687583)
            ·
              refine ⟨6346633466678375518031375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231088977785583678687583 6346633466678375518031375)
              ·
                refine ⟨9519950200017563277047063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6346633466678375518031375 9519950200017563277047063)
                ·
                  refine ⟨14279925300026344915570595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9519950200017563277047063 14279925300026344915570595)
                  ·
                    refine ⟨21419887950039517373355893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14279925300026344915570595 21419887950039517373355893)
                    ·
                      refine ⟨2008114495316204753752115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21419887950039517373355893 2008114495316204753752115)
                      ·
                        rfl

theorem cell23_3910789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 1, 1, 5].length) (baseStart_3910789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910789 prefixEnd_3910789 := by exact prefixLift 3910789
  have htrace : WordTrace (prefixWord ++ tailWord_3910789) baseStart_3910789 baseEnd_3910789 := by
    simpa [prefixWord, tailWord_3910789, baseEnd_3910789] using wordTrace_append hprefix tailTrace_3910789
  have hstable : (prefixWord ++ tailWord_3910789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910789).length < 2 ^ (prefixWord ++ tailWord_3910789).sum := by decide
  have hdescent : baseEnd_3910789 < baseStart_3910789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910845 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_3910845 : Nat := 118140960795 + 3910845 * 2 ^ 59
def prefixEnd_3910845 : Nat := 4983230072969 + 3 ^ 40 * 3910845 * 2
def baseEnd_3910845 : Nat := 2008143250232856534651857

theorem tailTrace_3910845 : CollatzResearch.WordTrace tailWord_3910845 prefixEnd_3910845 2008143250232856534651857 := by
  unfold tailWord_3910845
  simp only [CollatzResearch.WordTrace]
  refine ⟨142640235516683958995349989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95093490344455972663566659 142640235516683958995349989)
  ·
    refine ⟨26745044159378242311628123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142640235516683958995349989 26745044159378242311628123)
    ·
      refine ⟨40117566239067363467442185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26745044159378242311628123 40117566239067363467442185)
      ·
        refine ⟨30088174679300522600581639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40117566239067363467442185 30088174679300522600581639)
        ·
          refine ⟨45132262018950783900872459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30088174679300522600581639 45132262018950783900872459)
          ·
            refine ⟨67698393028426175851308689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45132262018950783900872459 67698393028426175851308689)
            ·
              refine ⟨50773794771319631888481517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67698393028426175851308689 50773794771319631888481517)
              ·
                refine ⟨19040173039244861958180569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50773794771319631888481517 19040173039244861958180569)
                ·
                  refine ⟨14280129779433646468635427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19040173039244861958180569 14280129779433646468635427)
                  ·
                    refine ⟨21420194669150469702953141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14280129779433646468635427 21420194669150469702953141)
                    ·
                      refine ⟨2008143250232856534651857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21420194669150469702953141 2008143250232856534651857)
                      ·
                        rfl

theorem cell23_3910845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_3910845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910845 prefixEnd_3910845 := by exact prefixLift 3910845
  have htrace : WordTrace (prefixWord ++ tailWord_3910845) baseStart_3910845 baseEnd_3910845 := by
    simpa [prefixWord, tailWord_3910845, baseEnd_3910845] using wordTrace_append hprefix tailTrace_3910845
  have hstable : (prefixWord ++ tailWord_3910845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910845).length < 2 ^ (prefixWord ++ tailWord_3910845).sum := by decide
  have hdescent : baseEnd_3910845 < baseStart_3910845 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910846 : List Nat := [4, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2]
def baseStart_3910846 : Nat := 118140960795 + 3910846 * 2 ^ 59
def prefixEnd_3910846 : Nat := 4983230072969 + 3 ^ 40 * 3910846 * 2
def baseEnd_3910846 : Nat := 2008143763713511030739353

theorem tailTrace_3910846 : CollatzResearch.WordTrace tailWord_3910846 prefixEnd_3910846 2008143763713511030739353 := by
  unfold tailWord_3910846
  simp only [CollatzResearch.WordTrace]
  refine ⟨17830033998710042020767049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95093514659786890777424261 17830033998710042020767049)
  ·
    refine ⟨13372525499032531515575287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17830033998710042020767049 13372525499032531515575287)
    ·
      refine ⟨20058788248548797273362931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13372525499032531515575287 20058788248548797273362931)
      ·
        refine ⟨30088182372823195910044397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20058788248548797273362931 30088182372823195910044397)
        ·
          refine ⟨11283068389808698466266649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30088182372823195910044397 11283068389808698466266649)
          ·
            refine ⟨8462301292356523849699987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11283068389808698466266649 8462301292356523849699987)
            ·
              refine ⟨12693451938534785774549981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8462301292356523849699987 12693451938534785774549981)
              ·
                refine ⟨4760044476950544665456243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12693451938534785774549981 4760044476950544665456243)
                ·
                  refine ⟨7140066715425816998184365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760044476950544665456243 7140066715425816998184365)
                  ·
                    refine ⟨2677525018284681374319137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7140066715425816998184365 2677525018284681374319137)
                    ·
                      refine ⟨2008143763713511030739353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677525018284681374319137 2008143763713511030739353)
                      ·
                        rfl

theorem cell23_3910846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_3910846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910846 prefixEnd_3910846 := by exact prefixLift 3910846
  have htrace : WordTrace (prefixWord ++ tailWord_3910846) baseStart_3910846 baseEnd_3910846 := by
    simpa [prefixWord, tailWord_3910846, baseEnd_3910846] using wordTrace_append hprefix tailTrace_3910846
  have hstable : (prefixWord ++ tailWord_3910846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910846).length < 2 ^ (prefixWord ++ tailWord_3910846).sum := by decide
  have hdescent : baseEnd_3910846 < baseStart_3910846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910859 : List Nat := [1, 1, 1, 1, 3, 2, 2, 6, 2, 2, 2]
def baseStart_3910859 : Nat := 118140960795 + 3910859 * 2 ^ 59
def prefixEnd_3910859 : Nat := 4983230072969 + 3 ^ 40 * 3910859 * 2
def baseEnd_3910859 : Nat := 2008150438962019479876793

theorem tailTrace_3910859 : CollatzResearch.WordTrace tailWord_3910859 prefixEnd_3910859 2008150438962019479876793 := by
  unfold tailWord_3910859
  simp only [CollatzResearch.WordTrace]
  refine ⟨142640746138633239386359631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95093830759088826257573087 142640746138633239386359631)
  ·
    refine ⟨213961119207949859079539447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142640746138633239386359631 213961119207949859079539447)
    ·
      refine ⟨320941678811924788619309171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213961119207949859079539447 320941678811924788619309171)
      ·
        refine ⟨481412518217887182928963757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320941678811924788619309171 481412518217887182928963757)
        ·
          refine ⟨180529694331707693598361409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 481412518217887182928963757 180529694331707693598361409)
          ·
            refine ⟨135397270748780770198771057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180529694331707693598361409 135397270748780770198771057)
            ·
              refine ⟨101547953061585577649078293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135397270748780770198771057 101547953061585577649078293)
              ·
                refine ⟨4760060299761823952300545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101547953061585577649078293 4760060299761823952300545)
                ·
                  refine ⟨3570045224821367964225409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4760060299761823952300545 3570045224821367964225409)
                  ·
                    refine ⟨2677533918616025973169057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3570045224821367964225409 2677533918616025973169057)
                    ·
                      refine ⟨2008150438962019479876793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677533918616025973169057 2008150438962019479876793)
                      ·
                        rfl

theorem cell23_3910859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 2, 2, 2].length) (baseStart_3910859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910859 prefixEnd_3910859 := by exact prefixLift 3910859
  have htrace : WordTrace (prefixWord ++ tailWord_3910859) baseStart_3910859 baseEnd_3910859 := by
    simpa [prefixWord, tailWord_3910859, baseEnd_3910859] using wordTrace_append hprefix tailTrace_3910859
  have hstable : (prefixWord ++ tailWord_3910859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910859).length < 2 ^ (prefixWord ++ tailWord_3910859).sum := by decide
  have hdescent : baseEnd_3910859 < baseStart_3910859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910870 : List Nat := [5, 2, 1, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_3910870 : Nat := 118140960795 + 3910870 * 2 ^ 59
def prefixEnd_3910870 : Nat := 4983230072969 + 3 ^ 40 * 3910870 * 2
def baseEnd_3910870 : Nat := 2008156087249218936839243

theorem tailTrace_3910870 : CollatzResearch.WordTrace tailWord_3910870 prefixEnd_3910870 2008156087249218936839243 := by
  unfold tailWord_3910870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915071708849586766563129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95094098227728925510006709 8915071708849586766563129)
  ·
    refine ⟨6686303781637190074922347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8915071708849586766563129 6686303781637190074922347)
    ·
      refine ⟨10029455672455785112383521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6686303781637190074922347 10029455672455785112383521)
      ·
        refine ⟨7522091754341838834287641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10029455672455785112383521 7522091754341838834287641)
        ·
          refine ⟨5641568815756379125715731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7522091754341838834287641 5641568815756379125715731)
          ·
            refine ⟨8462353223634568688573597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5641568815756379125715731 8462353223634568688573597)
            ·
              refine ⟨3173382458862963258215099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8462353223634568688573597 3173382458862963258215099)
              ·
                refine ⟨4760073688294444887322649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173382458862963258215099 4760073688294444887322649)
                ·
                  refine ⟨3570055266220833665491987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4760073688294444887322649 3570055266220833665491987)
                  ·
                    refine ⟨5355082899331250498237981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3570055266220833665491987 5355082899331250498237981)
                    ·
                      refine ⟨2008156087249218936839243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5355082899331250498237981 2008156087249218936839243)
                      ·
                        rfl

theorem cell23_3910870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_3910870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910870 prefixEnd_3910870 := by exact prefixLift 3910870
  have htrace : WordTrace (prefixWord ++ tailWord_3910870) baseStart_3910870 baseEnd_3910870 := by
    simpa [prefixWord, tailWord_3910870, baseEnd_3910870] using wordTrace_append hprefix tailTrace_3910870
  have hstable : (prefixWord ++ tailWord_3910870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910870).length < 2 ^ (prefixWord ++ tailWord_3910870).sum := by decide
  have hdescent : baseEnd_3910870 < baseStart_3910870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910875 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 3]
def baseStart_3910875 : Nat := 118140960795 + 3910875 * 2 ^ 59
def prefixEnd_3910875 : Nat := 4983230072969 + 3 ^ 40 * 3910875 * 2
def baseEnd_3910875 : Nat := 2008158654652491417276719

theorem tailTrace_3910875 : CollatzResearch.WordTrace tailWord_3910875 prefixEnd_3910875 2008158654652491417276719 := by
  unfold tailWord_3910875
  simp only [CollatzResearch.WordTrace]
  refine ⟨142641329706575274118942079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95094219804383516079294719 142641329706575274118942079)
  ·
    refine ⟨213961994559862911178413119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142641329706575274118942079 213961994559862911178413119)
    ·
      refine ⟨320942991839794366767619679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213961994559862911178413119 320942991839794366767619679)
      ·
        refine ⟨481414487759691550151429519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320942991839794366767619679 481414487759691550151429519)
        ·
          refine ⟨722121731639537325227144279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481414487759691550151429519 722121731639537325227144279)
          ·
            refine ⟨1083182597459305987840716419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722121731639537325227144279 1083182597459305987840716419)
            ·
              refine ⟨1624773896188958981761074629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083182597459305987840716419 1624773896188958981761074629)
              ·
                refine ⟨304645105535429809080201493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1624773896188958981761074629 304645105535429809080201493)
                ·
                  refine ⟨14280239321973272300634445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 304645105535429809080201493 14280239321973272300634445)
                  ·
                    refine ⟨5355089745739977112737917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14280239321973272300634445 5355089745739977112737917)
                    ·
                      refine ⟨2008158654652491417276719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5355089745739977112737917 2008158654652491417276719)
                      ·
                        rfl

theorem cell23_3910875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 3].length) (baseStart_3910875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910875 prefixEnd_3910875 := by exact prefixLift 3910875
  have htrace : WordTrace (prefixWord ++ tailWord_3910875) baseStart_3910875 baseEnd_3910875 := by
    simpa [prefixWord, tailWord_3910875, baseEnd_3910875] using wordTrace_append hprefix tailTrace_3910875
  have hstable : (prefixWord ++ tailWord_3910875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910875).length < 2 ^ (prefixWord ++ tailWord_3910875).sum := by decide
  have hdescent : baseEnd_3910875 < baseStart_3910875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910899 : List Nat := [1, 1, 1, 2, 2, 7, 1, 3, 5]
def baseStart_3910899 : Nat := 118140960795 + 3910899 * 2 ^ 59
def prefixEnd_3910899 : Nat := 4983230072969 + 3 ^ 40 * 3910899 * 2
def baseEnd_3910899 : Nat := 223130108687577702597401

theorem tailTrace_3910899 : CollatzResearch.WordTrace tailWord_3910899 prefixEnd_3910899 223130108687577702597401 := by
  unfold tailWord_3910899
  simp only [CollatzResearch.WordTrace]
  refine ⟨142642205058488326217815751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95094803372325550811877167 142642205058488326217815751)
  ·
    refine ⟨213963307587732489326723627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142642205058488326217815751 213963307587732489326723627)
    ·
      refine ⟨320944961381598733990085441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213963307587732489326723627 320944961381598733990085441)
      ·
        refine ⟨240708721036199050492564081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320944961381598733990085441 240708721036199050492564081)
        ·
          refine ⟨180531540777149287869423061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240708721036199050492564081 180531540777149287869423061)
          ·
            refine ⟨4231207986964436434439603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 180531540777149287869423061 4231207986964436434439603)
            ·
              refine ⟨6346811980446654651659405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231207986964436434439603 6346811980446654651659405)
              ·
                refine ⟨2380054492667495494372277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6346811980446654651659405 2380054492667495494372277)
                ·
                  refine ⟨223130108687577702597401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2380054492667495494372277 223130108687577702597401)
                  ·
                    rfl

theorem cell23_3910899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 3, 5].length) (baseStart_3910899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910899 prefixEnd_3910899 := by exact prefixLift 3910899
  have htrace : WordTrace (prefixWord ++ tailWord_3910899) baseStart_3910899 baseEnd_3910899 := by
    simpa [prefixWord, tailWord_3910899, baseEnd_3910899] using wordTrace_append hprefix tailTrace_3910899
  have hstable : (prefixWord ++ tailWord_3910899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910899).length < 2 ^ (prefixWord ++ tailWord_3910899).sum := by decide
  have hdescent : baseEnd_3910899 < baseStart_3910899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910905 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_3910905 : Nat := 118140960795 + 3910905 * 2 ^ 59
def prefixEnd_3910905 : Nat := 4983230072969 + 3 ^ 40 * 3910905 * 2
def baseEnd_3910905 : Nat := 2008174059072126299901581

theorem tailTrace_3910905 : CollatzResearch.WordTrace tailWord_3910905 prefixEnd_3910905 2008174059072126299901581 := by
  unfold tailWord_3910905
  simp only [CollatzResearch.WordTrace]
  refine ⟨142642423896466589242534169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95094949264311059495022779 142642423896466589242534169)
  ·
    refine ⟨106981817922349941931900627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142642423896466589242534169 106981817922349941931900627)
    ·
      refine ⟨160472726883524912897850941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106981817922349941931900627 160472726883524912897850941)
      ·
        refine ⟨60177272581321842336694103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160472726883524912897850941 60177272581321842336694103)
        ·
          refine ⟨90265908871982763505041155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60177272581321842336694103 90265908871982763505041155)
          ·
            refine ⟨135398863307974145257561733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90265908871982763505041155 135398863307974145257561733)
            ·
              refine ⟨25387286870245152235792825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135398863307974145257561733 25387286870245152235792825)
              ·
                refine ⟨19040465152683864176844619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25387286870245152235792825 19040465152683864176844619)
                ·
                  refine ⟨28560697729025796265266929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19040465152683864176844619 28560697729025796265266929)
                  ·
                    refine ⟨21420523296769347198950197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28560697729025796265266929 21420523296769347198950197)
                    ·
                      refine ⟨2008174059072126299901581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21420523296769347198950197 2008174059072126299901581)
                      ·
                        rfl

theorem cell23_3910905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_3910905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910905 prefixEnd_3910905 := by exact prefixLift 3910905
  have htrace : WordTrace (prefixWord ++ tailWord_3910905) baseStart_3910905 baseEnd_3910905 := by
    simpa [prefixWord, tailWord_3910905, baseEnd_3910905] using wordTrace_append hprefix tailTrace_3910905
  have hstable : (prefixWord ++ tailWord_3910905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910905).length < 2 ^ (prefixWord ++ tailWord_3910905).sum := by decide
  have hdescent : baseEnd_3910905 < baseStart_3910905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910916 : List Nat := [2, 3, 2, 2, 2, 2, 3, 2, 5]
def baseStart_3910916 : Nat := 118140960795 + 3910916 * 2 ^ 59
def prefixEnd_3910916 : Nat := 4983230072969 + 3 ^ 40 * 3910916 * 2
def baseEnd_3910916 : Nat := 223131078595480639651559

theorem tailTrace_3910916 : CollatzResearch.WordTrace tailWord_3910916 prefixEnd_3910916 223131078595480639651559 := by
  unfold tailWord_3910916
  simp only [CollatzResearch.WordTrace]
  refine ⟨71321412549713369060592301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95095216732951158747456401 71321412549713369060592301)
  ·
    refine ⟨26745529706142513397722113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71321412549713369060592301 26745529706142513397722113)
    ·
      refine ⟨20059147279606885048291585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26745529706142513397722113 20059147279606885048291585)
      ·
        refine ⟨15044360459705163786218689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20059147279606885048291585 15044360459705163786218689)
        ·
          refine ⟨11283270344778872839664017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15044360459705163786218689 11283270344778872839664017)
          ·
            refine ⟨8462452758584154629748013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11283270344778872839664017 8462452758584154629748013)
            ·
              refine ⟨3173419784469057986155505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8462452758584154629748013 3173419784469057986155505)
              ·
                refine ⟨2380064838351793489616629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173419784469057986155505 2380064838351793489616629)
                ·
                  refine ⟨223131078595480639651559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2380064838351793489616629 223131078595480639651559)
                  ·
                    rfl

theorem cell23_3910916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 3, 2, 5].length) (baseStart_3910916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910916 prefixEnd_3910916 := by exact prefixLift 3910916
  have htrace : WordTrace (prefixWord ++ tailWord_3910916) baseStart_3910916 baseEnd_3910916 := by
    simpa [prefixWord, tailWord_3910916, baseEnd_3910916] using wordTrace_append hprefix tailTrace_3910916
  have hstable : (prefixWord ++ tailWord_3910916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910916).length < 2 ^ (prefixWord ++ tailWord_3910916).sum := by decide
  have hdescent : baseEnd_3910916 < baseStart_3910916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910945 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3910945 : Nat := 118140960795 + 3910945 * 2 ^ 59
def prefixEnd_3910945 : Nat := 4983230072969 + 3 ^ 40 * 3910945 * 2
def baseEnd_3910945 : Nat := 2008194598298306143401397

theorem tailTrace_3910945 : CollatzResearch.WordTrace tailWord_3910945 prefixEnd_3910945 2008194598298306143401397 := by
  unfold tailWord_3910945
  simp only [CollatzResearch.WordTrace]
  refine ⟨142643882816321676073990289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95095921877547784049326859 142643882816321676073990289)
  ·
    refine ⟨106982912112241257055492717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142643882816321676073990289 106982912112241257055492717)
    ·
      refine ⟨40118592042090471395809769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 106982912112241257055492717 40118592042090471395809769)
      ·
        refine ⟨30088944031567853546857327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40118592042090471395809769 30088944031567853546857327)
        ·
          refine ⟨45133416047351780320285991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30088944031567853546857327 45133416047351780320285991)
          ·
            refine ⟨67700124071027670480428987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45133416047351780320285991 67700124071027670480428987)
            ·
              refine ⟨101550186106541505720643481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67700124071027670480428987 101550186106541505720643481)
              ·
                refine ⟨76162639579906129290482611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101550186106541505720643481 76162639579906129290482611)
                ·
                  refine ⟨114243959369859193935723917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76162639579906129290482611 114243959369859193935723917)
                  ·
                    refine ⟨42841484763697197725896469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114243959369859193935723917 42841484763697197725896469)
                    ·
                      refine ⟨2008194598298306143401397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42841484763697197725896469 2008194598298306143401397)
                      ·
                        rfl

theorem cell23_3910945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3910945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910945 prefixEnd_3910945 := by exact prefixLift 3910945
  have htrace : WordTrace (prefixWord ++ tailWord_3910945) baseStart_3910945 baseEnd_3910945 := by
    simpa [prefixWord, tailWord_3910945, baseEnd_3910945] using wordTrace_append hprefix tailTrace_3910945
  have hstable : (prefixWord ++ tailWord_3910945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910945).length < 2 ^ (prefixWord ++ tailWord_3910945).sum := by decide
  have hdescent : baseEnd_3910945 < baseStart_3910945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910949 : List Nat := [1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_3910949 : Nat := 118140960795 + 3910949 * 2 ^ 59
def prefixEnd_3910949 : Nat := 4983230072969 + 3 ^ 40 * 3910949 * 2
def baseEnd_3910949 : Nat := 2008196652220924127751379

theorem tailTrace_3910949 : CollatzResearch.WordTrace tailWord_3910949 prefixEnd_3910949 2008196652220924127751379 := by
  unfold tailWord_3910949
  simp only [CollatzResearch.WordTrace]
  refine ⟨142644028708307184757135901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95096019138871456504757267 142644028708307184757135901)
  ·
    refine ⟨53491510765615194283925963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142644028708307184757135901 53491510765615194283925963)
    ·
      refine ⟨80237266148422791425888945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53491510765615194283925963 80237266148422791425888945)
      ·
        refine ⟨60177949611317093569416709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80237266148422791425888945 60177949611317093569416709)
        ·
          refine ⟨11283365552121955044265633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60177949611317093569416709 11283365552121955044265633)
          ·
            refine ⟨8462524164091466283199225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11283365552121955044265633 8462524164091466283199225)
            ·
              refine ⟨6346893123068599712399419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8462524164091466283199225 6346893123068599712399419)
              ·
                refine ⟨9520339684602899568599129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6346893123068599712399419 9520339684602899568599129)
                ·
                  refine ⟨7140254763452174676449347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9520339684602899568599129 7140254763452174676449347)
                  ·
                    refine ⟨10710382145178262014674021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7140254763452174676449347 10710382145178262014674021)
                    ·
                      refine ⟨2008196652220924127751379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10710382145178262014674021 2008196652220924127751379)
                      ·
                        rfl

theorem cell23_3910949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_3910949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910949 prefixEnd_3910949 := by exact prefixLift 3910949
  have htrace : WordTrace (prefixWord ++ tailWord_3910949) baseStart_3910949 baseEnd_3910949 := by
    simpa [prefixWord, tailWord_3910949, baseEnd_3910949] using wordTrace_append hprefix tailTrace_3910949
  have hstable : (prefixWord ++ tailWord_3910949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910949).length < 2 ^ (prefixWord ++ tailWord_3910949).sum := by decide
  have hdescent : baseEnd_3910949 < baseStart_3910949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910959 : List Nat := [1, 1, 2, 1, 2, 1, 3, 7, 1, 4]
def baseStart_3910959 : Nat := 118140960795 + 3910959 * 2 ^ 59
def prefixEnd_3910959 : Nat := 4983230072969 + 3 ^ 40 * 3910959 * 2
def baseEnd_3910959 : Nat := 669400595675823029542111

theorem tailTrace_3910959 : CollatzResearch.WordTrace tailWord_3910959 prefixEnd_3910959 669400595675823029542111 := by
  unfold tailWord_3910959
  simp only [CollatzResearch.WordTrace]
  refine ⟨142644393438270956464999931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95096262292180637643333287 142644393438270956464999931)
  ·
    refine ⟨213966590157406434697499897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142644393438270956464999931 213966590157406434697499897)
    ·
      refine ⟨160474942618054826023124923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213966590157406434697499897 160474942618054826023124923)
      ·
        refine ⟨240712413927082239034687385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160474942618054826023124923 240712413927082239034687385)
        ·
          refine ⟨180534310445311679276015539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240712413927082239034687385 180534310445311679276015539)
          ·
            refine ⟨270801465667967518914023309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180534310445311679276015539 270801465667967518914023309)
            ·
              refine ⟨101550549625487819592758741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270801465667967518914023309 101550549625487819592758741)
              ·
                refine ⟨2380091006847370771705283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 101550549625487819592758741 2380091006847370771705283)
                ·
                  refine ⟨3570136510271056157557925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380091006847370771705283 3570136510271056157557925)
                  ·
                    refine ⟨669400595675823029542111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3570136510271056157557925 669400595675823029542111)
                    ·
                      rfl

theorem cell23_3910959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 7, 1, 4].length) (baseStart_3910959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910959 prefixEnd_3910959 := by exact prefixLift 3910959
  have htrace : WordTrace (prefixWord ++ tailWord_3910959) baseStart_3910959 baseEnd_3910959 := by
    simpa [prefixWord, tailWord_3910959, baseEnd_3910959] using wordTrace_append hprefix tailTrace_3910959
  have hstable : (prefixWord ++ tailWord_3910959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910959).length < 2 ^ (prefixWord ++ tailWord_3910959).sum := by decide
  have hdescent : baseEnd_3910959 < baseStart_3910959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910972 : List Nat := [2, 2, 2, 2, 1, 3, 1, 4, 6]
def baseStart_3910972 : Nat := 118140960795 + 3910972 * 2 ^ 59
def prefixEnd_3910972 : Nat := 4983230072969 + 3 ^ 40 * 3910972 * 2
def baseEnd_3910972 : Nat := 223134273586219726418197

theorem tailTrace_3910972 : CollatzResearch.WordTrace tailWord_3910972 prefixEnd_3910972 223134273586219726418197 := by
  unfold tailWord_3910972
  simp only [CollatzResearch.WordTrace]
  refine ⟨71322433793611929842611585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95096578391482573123482113 71322433793611929842611585)
  ·
    refine ⟨53491825345208947381958689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71322433793611929842611585 53491825345208947381958689)
    ·
      refine ⟨40118869008906710536469017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53491825345208947381958689 40118869008906710536469017)
      ·
        refine ⟨30089151756680032902351763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40118869008906710536469017 30089151756680032902351763)
        ·
          refine ⟨45133727635020049353527645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30089151756680032902351763 45133727635020049353527645)
          ·
            refine ⟨16925147863132518507572867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45133727635020049353527645 16925147863132518507572867)
            ·
              refine ⟨25387721794698777761359301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16925147863132518507572867 25387721794698777761359301)
              ·
                refine ⟨4760197836506020830254869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25387721794698777761359301 4760197836506020830254869)
                ·
                  refine ⟨223134273586219726418197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4760197836506020830254869 223134273586219726418197)
                  ·
                    rfl

theorem cell23_3910972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 6].length) (baseStart_3910972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910972 prefixEnd_3910972 := by exact prefixLift 3910972
  have htrace : WordTrace (prefixWord ++ tailWord_3910972) baseStart_3910972 baseEnd_3910972 := by
    simpa [prefixWord, tailWord_3910972, baseEnd_3910972] using wordTrace_append hprefix tailTrace_3910972
  have hstable : (prefixWord ++ tailWord_3910972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910972).length < 2 ^ (prefixWord ++ tailWord_3910972).sum := by decide
  have hdescent : baseEnd_3910972 < baseStart_3910972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910995 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 7]
def baseStart_3910995 : Nat := 118140960795 + 3910995 * 2 ^ 59
def prefixEnd_3910995 : Nat := 4983230072969 + 3 ^ 40 * 3910995 * 2
def baseEnd_3910995 : Nat := 2008220272331030947776167

theorem tailTrace_3910995 : CollatzResearch.WordTrace tailWord_3910995 prefixEnd_3910995 2008220272331030947776167 := by
  unfold tailWord_3910995
  simp only [CollatzResearch.WordTrace]
  refine ⟨142645706466140534613310439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95097137644093689742206959 142645706466140534613310439)
  ·
    refine ⟨213968559699210801919965659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142645706466140534613310439 213968559699210801919965659)
    ·
      refine ⟨320952839548816202879948489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213968559699210801919965659 320952839548816202879948489)
      ·
        refine ⟨240714629661612152159961367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320952839548816202879948489 240714629661612152159961367)
        ·
          refine ⟨361071944492418228239942051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240714629661612152159961367 361071944492418228239942051)
          ·
            refine ⟨541607916738627342359913077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361071944492418228239942051 541607916738627342359913077)
            ·
              refine ⟨50775742194246313346241851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 541607916738627342359913077 50775742194246313346241851)
              ·
                refine ⟨76163613291369470019362777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50775742194246313346241851 76163613291369470019362777)
                ·
                  refine ⟨57122709968527102514522083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76163613291369470019362777 57122709968527102514522083)
                  ·
                    refine ⟨85684064952790653771783125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57122709968527102514522083 85684064952790653771783125)
                    ·
                      refine ⟨2008220272331030947776167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85684064952790653771783125 2008220272331030947776167)
                      ·
                        rfl

theorem cell23_3910995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_3910995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910995 prefixEnd_3910995 := by exact prefixLift 3910995
  have htrace : WordTrace (prefixWord ++ tailWord_3910995) baseStart_3910995 baseEnd_3910995 := by
    simpa [prefixWord, tailWord_3910995, baseEnd_3910995] using wordTrace_append hprefix tailTrace_3910995
  have hstable : (prefixWord ++ tailWord_3910995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910995).length < 2 ^ (prefixWord ++ tailWord_3910995).sum := by decide
  have hdescent : baseEnd_3910995 < baseStart_3910995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3910999 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 3]
def baseStart_3910999 : Nat := 118140960795 + 3910999 * 2 ^ 59
def prefixEnd_3910999 : Nat := 4983230072969 + 3 ^ 40 * 3910999 * 2
def baseEnd_3910999 : Nat := 2008222326253648932126149

theorem tailTrace_3910999 : CollatzResearch.WordTrace tailWord_3910999 prefixEnd_3910999 2008222326253648932126149 := by
  unfold tailWord_3910999
  simp only [CollatzResearch.WordTrace]
  refine ⟨142645852358126043296456051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95097234905417362197637367 142645852358126043296456051)
  ·
    refine ⟨213968778537189064944684077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142645852358126043296456051 213968778537189064944684077)
    ·
      refine ⟨80238291951445899354256529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 213968778537189064944684077 80238291951445899354256529)
      ·
        refine ⟨60178718963584424515692397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80238291951445899354256529 60178718963584424515692397)
        ·
          refine ⟨22567019611344159193384649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60178718963584424515692397 22567019611344159193384649)
          ·
            refine ⟨16925264708508119395038487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22567019611344159193384649 16925264708508119395038487)
            ·
              refine ⟨25387897062762179092557731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16925264708508119395038487 25387897062762179092557731)
              ·
                refine ⟨38081845594143268638836597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25387897062762179092557731 38081845594143268638836597)
                ·
                  refine ⟨3570173024450931434890931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38081845594143268638836597 3570173024450931434890931)
                  ·
                    refine ⟨5355259536676397152336397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3570173024450931434890931 5355259536676397152336397)
                    ·
                      refine ⟨2008222326253648932126149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5355259536676397152336397 2008222326253648932126149)
                      ·
                        rfl

theorem cell23_3910999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_3910999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3910999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3910999 prefixEnd_3910999 := by exact prefixLift 3910999
  have htrace : WordTrace (prefixWord ++ tailWord_3910999) baseStart_3910999 baseEnd_3910999 := by
    simpa [prefixWord, tailWord_3910999, baseEnd_3910999] using wordTrace_append hprefix tailTrace_3910999
  have hstable : (prefixWord ++ tailWord_3910999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3910999).length < 2 ^ (prefixWord ++ tailWord_3910999).sum := by decide
  have hdescent : baseEnd_3910999 < baseStart_3910999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3910999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911002 : List Nat := [3, 1, 1, 2, 1, 2, 4, 1, 3, 5]
def baseStart_3911002 : Nat := 118140960795 + 3911002 * 2 ^ 59
def prefixEnd_3911002 : Nat := 4983230072969 + 3 ^ 40 * 3911002 * 2
def baseEnd_3911002 : Nat := 669407955565204140129545

theorem tailTrace_3911002 : CollatzResearch.WordTrace tailWord_3911002 prefixEnd_3911002 669407955565204140129545 := by
  unfold tailWord_3911002
  simp only [CollatzResearch.WordTrace]
  refine ⟨35661490444278793702203815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95097307851410116539210173 35661490444278793702203815)
  ·
    refine ⟨53492235666418190553305723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35661490444278793702203815 53492235666418190553305723)
    ·
      refine ⟨80238353499627285829958585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53492235666418190553305723 80238353499627285829958585)
      ·
        refine ⟨60178765124720464372468939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80238353499627285829958585 60178765124720464372468939)
        ·
          refine ⟨90268147687080696558703409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60178765124720464372468939 90268147687080696558703409)
          ·
            refine ⟨67701110765310522419027557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90268147687080696558703409 67701110765310522419027557)
            ·
              refine ⟨12693958268495722953567667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67701110765310522419027557 12693958268495722953567667)
              ·
                refine ⟨19040937402743584430351501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12693958268495722953567667 19040937402743584430351501)
                ·
                  refine ⟨7140351526028844161381813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19040937402743584430351501 7140351526028844161381813)
                  ·
                    refine ⟨669407955565204140129545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7140351526028844161381813 669407955565204140129545)
                    ·
                      rfl

theorem cell23_3911002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 3, 5].length) (baseStart_3911002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911002 prefixEnd_3911002 := by exact prefixLift 3911002
  have htrace : WordTrace (prefixWord ++ tailWord_3911002) baseStart_3911002 baseEnd_3911002 := by
    simpa [prefixWord, tailWord_3911002, baseEnd_3911002] using wordTrace_append hprefix tailTrace_3911002
  have hstable : (prefixWord ++ tailWord_3911002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911002).length < 2 ^ (prefixWord ++ tailWord_3911002).sum := by decide
  have hdescent : baseEnd_3911002 < baseStart_3911002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911052 : List Nat := [2, 2, 1, 2, 1, 3, 3, 1, 1, 1, 6]
def baseStart_3911052 : Nat := 118140960795 + 3911052 * 2 ^ 59
def prefixEnd_3911052 : Nat := 4983230072969 + 3 ^ 40 * 3911052 * 2
def baseEnd_3911052 : Nat := 2008249540728337224763405

theorem tailTrace_3911052 : CollatzResearch.WordTrace tailWord_3911052 prefixEnd_3911052 2008249540728337224763405 := by
  unfold tailWord_3911052
  simp only [CollatzResearch.WordTrace]
  refine ⟨71323892713467016674067705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95098523617956022232090273 71323892713467016674067705)
  ·
    refine ⟨53492919535100262505550779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71323892713467016674067705 53492919535100262505550779)
    ·
      refine ⟨80239379302650393758326169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53492919535100262505550779 80239379302650393758326169)
      ·
        refine ⟨60179534476987795318744627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80239379302650393758326169 60179534476987795318744627)
        ·
          refine ⟨90269301715481692978116941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60179534476987795318744627 90269301715481692978116941)
          ·
            refine ⟨33850988143305634866793853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90269301715481692978116941 33850988143305634866793853)
            ·
              refine ⟨12694120553739613075047695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33850988143305634866793853 12694120553739613075047695)
              ·
                refine ⟨19041180830609419612571543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12694120553739613075047695 19041180830609419612571543)
                ·
                  refine ⟨28561771245914129418857315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19041180830609419612571543 28561771245914129418857315)
                  ·
                    refine ⟨42842656868871194128285973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28561771245914129418857315 42842656868871194128285973)
                    ·
                      refine ⟨2008249540728337224763405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42842656868871194128285973 2008249540728337224763405)
                      ·
                        rfl

theorem cell23_3911052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_3911052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911052 prefixEnd_3911052 := by exact prefixLift 3911052
  have htrace : WordTrace (prefixWord ++ tailWord_3911052) baseStart_3911052 baseEnd_3911052 := by
    simpa [prefixWord, tailWord_3911052, baseEnd_3911052] using wordTrace_append hprefix tailTrace_3911052
  have hstable : (prefixWord ++ tailWord_3911052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911052).length < 2 ^ (prefixWord ++ tailWord_3911052).sum := by decide
  have hdescent : baseEnd_3911052 < baseStart_3911052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911100 : List Nat := [2, 2, 2, 4, 2, 2, 2, 1, 2, 4]
def baseStart_3911100 : Nat := 118140960795 + 3911100 * 2 ^ 59
def prefixEnd_3911100 : Nat := 4983230072969 + 3 ^ 40 * 3911100 * 2
def baseEnd_3911100 : Nat := 669424729266584345654395

theorem tailTrace_3911100 : CollatzResearch.WordTrace tailWord_3911100 prefixEnd_3911100 669424729266584345654395 := by
  unfold tailWord_3911100
  simp only [CollatzResearch.WordTrace]
  refine ⟨71324768065380068772941377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95099690753840091697255169 71324768065380068772941377)
  ·
    refine ⟨53493576049035051579706033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71324768065380068772941377 53493576049035051579706033)
    ·
      refine ⟨40120182036776288684779525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53493576049035051579706033 40120182036776288684779525)
      ·
        refine ⟨7522534131895554128396161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40120182036776288684779525 7522534131895554128396161)
        ·
          refine ⟨5641900598921665596297121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7522534131895554128396161 5641900598921665596297121)
          ·
            refine ⟨4231425449191249197222841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5641900598921665596297121 4231425449191249197222841)
            ·
              refine ⟨3173569086893436897917131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4231425449191249197222841 3173569086893436897917131)
              ·
                refine ⟨4760353630340155346875697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3173569086893436897917131 4760353630340155346875697)
                ·
                  refine ⟨3570265222755116510156773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4760353630340155346875697 3570265222755116510156773)
                  ·
                    refine ⟨669424729266584345654395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3570265222755116510156773 669424729266584345654395)
                    ·
                      rfl

theorem cell23_3911100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 2, 1, 2, 4].length) (baseStart_3911100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911100 prefixEnd_3911100 := by exact prefixLift 3911100
  have htrace : WordTrace (prefixWord ++ tailWord_3911100) baseStart_3911100 baseEnd_3911100 := by
    simpa [prefixWord, tailWord_3911100, baseEnd_3911100] using wordTrace_append hprefix tailTrace_3911100
  have hstable : (prefixWord ++ tailWord_3911100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911100).length < 2 ^ (prefixWord ++ tailWord_3911100).sum := by decide
  have hdescent : baseEnd_3911100 < baseStart_3911100 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911199 : List Nat := [1, 1, 2, 4, 1, 1, 2, 4, 2, 5]
def baseStart_3911199 : Nat := 118140960795 + 3911199 * 2 ^ 59
def prefixEnd_3911199 : Nat := 4983230072969 + 3 ^ 40 * 3911199 * 2
def baseEnd_3911199 : Nat := 669441674128182716541743

theorem tailTrace_3911199 : CollatzResearch.WordTrace tailWord_3911199 prefixEnd_3911199 669441674128182716541743 := by
  unfold tailWord_3911199
  simp only [CollatzResearch.WordTrace]
  refine ⟨142653146957401477453736651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95102097971600984969157767 142653146957401477453736651)
  ·
    refine ⟨213979720436102216180604977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142653146957401477453736651 213979720436102216180604977)
    ·
      refine ⟨160484790327076662135453733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 213979720436102216180604977 160484790327076662135453733)
      ·
        refine ⟨30090898186326874150397575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160484790327076662135453733 30090898186326874150397575)
        ·
          refine ⟨45136347279490311225596363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30090898186326874150397575 45136347279490311225596363)
          ·
            refine ⟨67704520919235466838394545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45136347279490311225596363 67704520919235466838394545)
            ·
              refine ⟨50778390689426600128795909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67704520919235466838394545 50778390689426600128795909)
              ·
                refine ⟨9520948254267487524149233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50778390689426600128795909 9520948254267487524149233)
                ·
                  refine ⟨7140711190700615643111925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9520948254267487524149233 7140711190700615643111925)
                  ·
                    refine ⟨669441674128182716541743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7140711190700615643111925 669441674128182716541743)
                    ·
                      rfl

theorem cell23_3911199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_3911199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911199 prefixEnd_3911199 := by exact prefixLift 3911199
  have htrace : WordTrace (prefixWord ++ tailWord_3911199) baseStart_3911199 baseEnd_3911199 := by
    simpa [prefixWord, tailWord_3911199, baseEnd_3911199] using wordTrace_append hprefix tailTrace_3911199
  have hstable : (prefixWord ++ tailWord_3911199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911199).length < 2 ^ (prefixWord ++ tailWord_3911199).sum := by decide
  have hdescent : baseEnd_3911199 < baseStart_3911199 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911219 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 4]
def baseStart_3911219 : Nat := 118140960795 + 3911219 * 2 ^ 59
def prefixEnd_3911219 : Nat := 4983230072969 + 3 ^ 40 * 3911219 * 2
def baseEnd_3911219 : Nat := 2008335291997638071375137

theorem tailTrace_3911219 : CollatzResearch.WordTrace tailWord_3911219 prefixEnd_3911219 2008335291997638071375137 := by
  unfold tailWord_3911219
  simp only [CollatzResearch.WordTrace]
  refine ⟨142653876417329020869464711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95102584278219347246309807 142653876417329020869464711)
  ·
    refine ⟨213980814625993531304197067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142653876417329020869464711 213980814625993531304197067)
    ·
      refine ⟨320971221938990296956295601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213980814625993531304197067 320971221938990296956295601)
      ·
        refine ⟨240728416454242722717221701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320971221938990296956295601 240728416454242722717221701)
        ·
          refine ⟨45136578085170510509479069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 240728416454242722717221701 45136578085170510509479069)
          ·
            refine ⟨16926216781938941441054651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45136578085170510509479069 16926216781938941441054651)
            ·
              refine ⟨25389325172908412161581977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16926216781938941441054651 25389325172908412161581977)
              ·
                refine ⟨19041993879681309121186483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25389325172908412161581977 19041993879681309121186483)
                ·
                  refine ⟨28562990819521963681779725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19041993879681309121186483 28562990819521963681779725)
                  ·
                    refine ⟨10711121557320736380667397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28562990819521963681779725 10711121557320736380667397)
                    ·
                      refine ⟨2008335291997638071375137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10711121557320736380667397 2008335291997638071375137)
                      ·
                        rfl

theorem cell23_3911219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_3911219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911219 prefixEnd_3911219 := by exact prefixLift 3911219
  have htrace : WordTrace (prefixWord ++ tailWord_3911219) baseStart_3911219 baseEnd_3911219 := by
    simpa [prefixWord, tailWord_3911219, baseEnd_3911219] using wordTrace_append hprefix tailTrace_3911219
  have hstable : (prefixWord ++ tailWord_3911219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911219).length < 2 ^ (prefixWord ++ tailWord_3911219).sum := by decide
  have hdescent : baseEnd_3911219 < baseStart_3911219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911254 : List Nat := [5, 2, 2, 2, 1, 1, 3, 2, 5]
def baseStart_3911254 : Nat := 118140960795 + 3911254 * 2 ^ 59
def prefixEnd_3911254 : Nat := 4983230072969 + 3 ^ 40 * 3911254 * 2
def baseEnd_3911254 : Nat := 223150362646727270493053

theorem tailTrace_3911254 : CollatzResearch.WordTrace tailWord_3911254 prefixEnd_3911254 223150362646727270493053 := by
  unfold tailWord_3911254
  simp only [CollatzResearch.WordTrace]
  refine ⟨8915947060762638865436801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 95103435314801481231325877 8915947060762638865436801)
  ·
    refine ⟨6686960295571979149077601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8915947060762638865436801 6686960295571979149077601)
    ·
      refine ⟨5015220221678984361808201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6686960295571979149077601 5015220221678984361808201)
      ·
        refine ⟨3761415166259238271356151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5015220221678984361808201 3761415166259238271356151)
        ·
          refine ⟨5642122749388857407034227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3761415166259238271356151 5642122749388857407034227)
          ·
            refine ⟨8463184124083286110551341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642122749388857407034227 8463184124083286110551341)
            ·
              refine ⟨3173694046531232291456753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8463184124083286110551341 3173694046531232291456753)
              ·
                refine ⟨2380270534898424218592565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173694046531232291456753 2380270534898424218592565)
                ·
                  refine ⟨223150362646727270493053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2380270534898424218592565 223150362646727270493053)
                  ·
                    rfl

theorem cell23_3911254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_3911254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911254 prefixEnd_3911254 := by exact prefixLift 3911254
  have htrace : WordTrace (prefixWord ++ tailWord_3911254) baseStart_3911254 baseEnd_3911254 := by
    simpa [prefixWord, tailWord_3911254, baseEnd_3911254] using wordTrace_append hprefix tailTrace_3911254
  have hstable : (prefixWord ++ tailWord_3911254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911254).length < 2 ^ (prefixWord ++ tailWord_3911254).sum := by decide
  have hdescent : baseEnd_3911254 < baseStart_3911254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911314 : List Nat := [3, 2, 3, 1, 3, 2, 2, 2, 1, 4]
def baseStart_3911314 : Nat := 118140960795 + 3911314 * 2 ^ 59
def prefixEnd_3911314 : Nat := 4983230072969 + 3 ^ 40 * 3911314 * 2
def baseEnd_3911314 : Nat := 669461357553271733229067

theorem tailTrace_3911314 : CollatzResearch.WordTrace tailWord_3911314 prefixEnd_3911314 669461357553271733229067 := by
  unfold tailWord_3911314
  simp only [CollatzResearch.WordTrace]
  refine ⟨35664335337996213023543249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95104894234656568062781997 35664335337996213023543249)
  ·
    refine ⟨26748251503497159767657437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35664335337996213023543249 26748251503497159767657437)
    ·
      refine ⟨10030594313811434912871539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26748251503497159767657437 10030594313811434912871539)
      ·
        refine ⟨15045891470717152369307309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10030594313811434912871539 15045891470717152369307309)
        ·
          refine ⟨5642209301518932138490241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15045891470717152369307309 5642209301518932138490241)
          ·
            refine ⟨4231656976139199103867681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5642209301518932138490241 4231656976139199103867681)
            ·
              refine ⟨3173742732104399327900761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4231656976139199103867681 3173742732104399327900761)
              ·
                refine ⟨2380307049078299495925571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3173742732104399327900761 2380307049078299495925571)
                ·
                  refine ⟨3570460573617449243888357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380307049078299495925571 3570460573617449243888357)
                  ·
                    refine ⟨669461357553271733229067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3570460573617449243888357 669461357553271733229067)
                    ·
                      rfl

theorem cell23_3911314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_3911314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911314 prefixEnd_3911314 := by exact prefixLift 3911314
  have htrace : WordTrace (prefixWord ++ tailWord_3911314) baseStart_3911314 baseEnd_3911314 := by
    simpa [prefixWord, tailWord_3911314, baseEnd_3911314] using wordTrace_append hprefix tailTrace_3911314
  have hstable : (prefixWord ++ tailWord_3911314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911314).length < 2 ^ (prefixWord ++ tailWord_3911314).sum := by decide
  have hdescent : baseEnd_3911314 < baseStart_3911314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911377 : List Nat := [1, 2, 2, 1, 2, 4, 2, 4, 1, 2, 2]
def baseStart_3911377 : Nat := 118140960795 + 3911377 * 2 ^ 59
def prefixEnd_3911377 : Nat := 4983230072969 + 3 ^ 40 * 3911377 * 2
def baseEnd_3911377 : Nat := 2008416421941048453199411

theorem tailTrace_3911377 : CollatzResearch.WordTrace tailWord_3911377 prefixEnd_3911377 2008416421941048453199411 := by
  unfold tailWord_3911377
  simp only [CollatzResearch.WordTrace]
  refine ⟨142659639150756613853716385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95106426100504409235810923 142659639150756613853716385)
  ·
    refine ⟨106994729363067460390287289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142659639150756613853716385 106994729363067460390287289)
    ·
      refine ⟨80246047022300595292715467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 106994729363067460390287289 80246047022300595292715467)
      ·
        refine ⟨120369070533450892939073201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80246047022300595292715467 120369070533450892939073201)
        ·
          refine ⟨90276802900088169704304901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120369070533450892939073201 90276802900088169704304901)
          ·
            refine ⟨16926900543766531819557169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90276802900088169704304901 16926900543766531819557169)
            ·
              refine ⟨12695175407824898864667877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16926900543766531819557169 12695175407824898864667877)
              ·
                refine ⟨2380345388967168537125227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12695175407824898864667877 2380345388967168537125227)
                ·
                  refine ⟨3570518083450752805687841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380345388967168537125227 3570518083450752805687841)
                  ·
                    refine ⟨2677888562588064604265881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3570518083450752805687841 2677888562588064604265881)
                    ·
                      refine ⟨2008416421941048453199411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677888562588064604265881 2008416421941048453199411)
                      ·
                        rfl

theorem cell23_3911377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 4, 1, 2, 2].length) (baseStart_3911377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911377 prefixEnd_3911377 := by exact prefixLift 3911377
  have htrace : WordTrace (prefixWord ++ tailWord_3911377) baseStart_3911377 baseEnd_3911377 := by
    simpa [prefixWord, tailWord_3911377, baseEnd_3911377] using wordTrace_append hprefix tailTrace_3911377
  have hstable : (prefixWord ++ tailWord_3911377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911377).length < 2 ^ (prefixWord ++ tailWord_3911377).sum := by decide
  have hdescent : baseEnd_3911377 < baseStart_3911377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911379 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 6, 7]
def baseStart_3911379 : Nat := 118140960795 + 3911379 * 2 ^ 59
def prefixEnd_3911379 : Nat := 4983230072969 + 3 ^ 40 * 3911379 * 2
def baseEnd_3911379 : Nat := 669472482967452481791467

theorem tailTrace_3911379 : CollatzResearch.WordTrace tailWord_3911379 prefixEnd_3911379 669472482967452481791467 := by
  unfold tailWord_3911379
  simp only [CollatzResearch.WordTrace]
  refine ⟨142659712096749368195289191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95106474731166245463526127 142659712096749368195289191)
  ·
    refine ⟨213989568145124052292933787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142659712096749368195289191 213989568145124052292933787)
    ·
      refine ⟨320984352217686078439400681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213989568145124052292933787 320984352217686078439400681)
      ·
        refine ⟨240738264163264558829550511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 320984352217686078439400681 240738264163264558829550511)
        ·
          refine ⟨361107396244896838244325767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240738264163264558829550511 361107396244896838244325767)
          ·
            refine ⟨541661094367345257366488651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361107396244896838244325767 541661094367345257366488651)
            ·
              refine ⟨812491641551017886049732977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 541661094367345257366488651 812491641551017886049732977)
              ·
                refine ⟨609368731163263414537299733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 812491641551017886049732977 609368731163263414537299733)
                ·
                  refine ⟨28564159273277972556435925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 609368731163263414537299733 28564159273277972556435925)
                  ·
                    refine ⟨669472482967452481791467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28564159273277972556435925 669472482967452481791467)
                    ·
                      rfl

theorem cell23_3911379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 7].length) (baseStart_3911379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911379 prefixEnd_3911379 := by exact prefixLift 3911379
  have htrace : WordTrace (prefixWord ++ tailWord_3911379) baseStart_3911379 baseEnd_3911379 := by
    simpa [prefixWord, tailWord_3911379, baseEnd_3911379] using wordTrace_append hprefix tailTrace_3911379
  have hstable : (prefixWord ++ tailWord_3911379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911379).length < 2 ^ (prefixWord ++ tailWord_3911379).sum := by decide
  have hdescent : baseEnd_3911379 < baseStart_3911379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911403 : List Nat := [1, 1, 1, 1, 2, 4, 2, 3, 3, 3, 2]
def baseStart_3911403 : Nat := 118140960795 + 3911403 * 2 ^ 59
def prefixEnd_3911403 : Nat := 4983230072969 + 3 ^ 40 * 3911403 * 2
def baseEnd_3911403 : Nat := 2008429772438065351474291

theorem tailTrace_3911403 : CollatzResearch.WordTrace tailWord_3911403 prefixEnd_3911403 2008429772438065351474291 := by
  unfold tailWord_3911403
  simp only [CollatzResearch.WordTrace]
  refine ⟨142660587448662420294162863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95107058299108280196108575 142660587448662420294162863)
  ·
    refine ⟨213990881172993630441244295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142660587448662420294162863 213990881172993630441244295)
    ·
      refine ⟨320986321759490445661866443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 213990881172993630441244295 320986321759490445661866443)
      ·
        refine ⟨481479482639235668492799665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 320986321759490445661866443 481479482639235668492799665)
        ·
          refine ⟨361109611979426751369599749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481479482639235668492799665 361109611979426751369599749)
          ·
            refine ⟨67708052246142515881799953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361109611979426751369599749 67708052246142515881799953)
            ·
              refine ⟨50781039184606886911349965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67708052246142515881799953 50781039184606886911349965)
              ·
                refine ⟨19042889694227582591756237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50781039184606886911349965 19042889694227582591756237)
                ·
                  refine ⟨7141083635335343471908589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19042889694227582591756237 7141083635335343471908589)
                  ·
                    refine ⟨2677906363250753801965721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7141083635335343471908589 2677906363250753801965721)
                    ·
                      refine ⟨2008429772438065351474291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677906363250753801965721 2008429772438065351474291)
                      ·
                        rfl

theorem cell23_3911403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 3, 2].length) (baseStart_3911403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911403 prefixEnd_3911403 := by exact prefixLift 3911403
  have htrace : WordTrace (prefixWord ++ tailWord_3911403) baseStart_3911403 baseEnd_3911403 := by
    simpa [prefixWord, tailWord_3911403, baseEnd_3911403] using wordTrace_append hprefix tailTrace_3911403
  have hstable : (prefixWord ++ tailWord_3911403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911403).length < 2 ^ (prefixWord ++ tailWord_3911403).sum := by decide
  have hdescent : baseEnd_3911403 < baseStart_3911403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911406 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_3911406 : Nat := 118140960795 + 3911406 * 2 ^ 59
def prefixEnd_3911406 : Nat := 4983230072969 + 3 ^ 40 * 3911406 * 2
def baseEnd_3911406 : Nat := 2008431312880028839736777

theorem tailTrace_3911406 : CollatzResearch.WordTrace tailWord_3911406 prefixEnd_3911406 2008431312880028839736777 := by
  unfold tailWord_3911406
  simp only [CollatzResearch.WordTrace]
  refine ⟨17832587108456443975815259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95107131245101034537681381 17832587108456443975815259)
  ·
    refine ⟨26748880662684665963722889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17832587108456443975815259 26748880662684665963722889)
    ·
      refine ⟨20061660497013499472792167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26748880662684665963722889 20061660497013499472792167)
      ·
        refine ⟨30092490745520249209188251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20061660497013499472792167 30092490745520249209188251)
        ·
          refine ⟨45138736118280373813782377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30092490745520249209188251 45138736118280373813782377)
          ·
            refine ⟨33854052088710280360336783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45138736118280373813782377 33854052088710280360336783)
            ·
              refine ⟨50781078133065420540505175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33854052088710280360336783 50781078133065420540505175)
              ·
                refine ⟨76171617199598130810757763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50781078133065420540505175 76171617199598130810757763)
                ·
                  refine ⟨114257425799397196216136645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76171617199598130810757763 114257425799397196216136645)
                  ·
                    refine ⟨21423267337386974290525621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114257425799397196216136645 21423267337386974290525621)
                    ·
                      refine ⟨2008431312880028839736777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21423267337386974290525621 2008431312880028839736777)
                      ·
                        rfl

theorem cell23_3911406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_3911406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911406 prefixEnd_3911406 := by exact prefixLift 3911406
  have htrace : WordTrace (prefixWord ++ tailWord_3911406) baseStart_3911406 baseEnd_3911406 := by
    simpa [prefixWord, tailWord_3911406, baseEnd_3911406] using wordTrace_append hprefix tailTrace_3911406
  have hstable : (prefixWord ++ tailWord_3911406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911406).length < 2 ^ (prefixWord ++ tailWord_3911406).sum := by decide
  have hdescent : baseEnd_3911406 < baseStart_3911406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911420 : List Nat := [2, 2, 2, 1, 3, 1, 1, 5, 1, 3, 2]
def baseStart_3911420 : Nat := 118140960795 + 3911420 * 2 ^ 59
def prefixEnd_3911420 : Nat := 4983230072969 + 3 ^ 40 * 3911420 * 2
def baseEnd_3911420 : Nat := 2008438501609191784961713

theorem tailTrace_3911420 : CollatzResearch.WordTrace tailWord_3911420 prefixEnd_3911420 2008438501609191784961713 := by
  unfold tailWord_3911420
  simp only [CollatzResearch.WordTrace]
  refine ⟨71330603744800416098765857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95107471659733888131687809 71330603744800416098765857)
  ·
    refine ⟨53497952808600312074074393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71330603744800416098765857 53497952808600312074074393)
    ·
      refine ⟨40123464606450234055555795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53497952808600312074074393 40123464606450234055555795)
      ·
        refine ⟨60185196909675351083333693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40123464606450234055555795 60185196909675351083333693)
        ·
          refine ⟨22569448841128256656250135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60185196909675351083333693 22569448841128256656250135)
          ·
            refine ⟨33854173261692384984375203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22569448841128256656250135 33854173261692384984375203)
            ·
              refine ⟨50781259892538577476562805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33854173261692384984375203 50781259892538577476562805)
              ·
                refine ⟨4760743114925491638427763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50781259892538577476562805 4760743114925491638427763)
                ·
                  refine ⟨7141114672388237457641645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4760743114925491638427763 7141114672388237457641645)
                  ·
                    refine ⟨2677918002145589046615617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7141114672388237457641645 2677918002145589046615617)
                    ·
                      refine ⟨2008438501609191784961713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677918002145589046615617 2008438501609191784961713)
                      ·
                        rfl

theorem cell23_3911420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_3911420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911420 prefixEnd_3911420 := by exact prefixLift 3911420
  have htrace : WordTrace (prefixWord ++ tailWord_3911420) baseStart_3911420 baseEnd_3911420 := by
    simpa [prefixWord, tailWord_3911420, baseEnd_3911420] using wordTrace_append hprefix tailTrace_3911420
  have hstable : (prefixWord ++ tailWord_3911420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911420).length < 2 ^ (prefixWord ++ tailWord_3911420).sum := by decide
  have hdescent : baseEnd_3911420 < baseStart_3911420 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911456 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 9]
def baseStart_3911456 : Nat := 118140960795 + 3911456 * 2 ^ 59
def prefixEnd_3911456 : Nat := 4983230072969 + 3 ^ 40 * 3911456 * 2
def baseEnd_3911456 : Nat := 223161887434750404901283

theorem tailTrace_3911456 : CollatzResearch.WordTrace tailWord_3911456 prefixEnd_3911456 223161887434750404901283 := by
  unfold tailWord_3911456
  simp only [CollatzResearch.WordTrace]
  refine ⟨71331260258735205172921111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95108347011646940230561481 71331260258735205172921111)
  ·
    refine ⟨106996890388102807759381667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71331260258735205172921111 106996890388102807759381667)
    ·
      refine ⟨160495335582154211639072501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106996890388102807759381667 160495335582154211639072501)
      ·
        refine ⟨15046437710826957341163047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160495335582154211639072501 15046437710826957341163047)
        ·
          refine ⟨22569656566240436011744571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15046437710826957341163047 22569656566240436011744571)
          ·
            refine ⟨33854484849360654017616857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22569656566240436011744571 33854484849360654017616857)
            ·
              refine ⟨25390863637020490513212643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33854484849360654017616857 25390863637020490513212643)
              ·
                refine ⟨38086295455530735769818965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25390863637020490513212643 38086295455530735769818965)
                ·
                  refine ⟨223161887434750404901283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 38086295455530735769818965 223161887434750404901283)
                  ·
                    rfl

theorem cell23_3911456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 9].length) (baseStart_3911456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911456 prefixEnd_3911456 := by exact prefixLift 3911456
  have htrace : WordTrace (prefixWord ++ tailWord_3911456) baseStart_3911456 baseEnd_3911456 := by
    simpa [prefixWord, tailWord_3911456, baseEnd_3911456] using wordTrace_append hprefix tailTrace_3911456
  have hstable : (prefixWord ++ tailWord_3911456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911456).length < 2 ^ (prefixWord ++ tailWord_3911456).sum := by decide
  have hdescent : baseEnd_3911456 < baseStart_3911456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911493 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 1, 7, 2]
def baseStart_3911493 : Nat := 118140960795 + 3911493 * 2 ^ 59
def prefixEnd_3911493 : Nat := 4983230072969 + 3 ^ 40 * 3911493 * 2
def baseEnd_3911493 : Nat := 2008475985696969999348877

theorem tailTrace_3911493 : CollatzResearch.WordTrace tailWord_3911493 prefixEnd_3911493 2008475985696969999348877 := by
  unfold tailWord_3911493
  simp only [CollatzResearch.WordTrace]
  refine ⟨142663870018336365664939133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95109246678890910443292755 142663870018336365664939133)
  ·
    refine ⟨53498951256876137124352175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142663870018336365664939133 53498951256876137124352175)
    ·
      refine ⟨80248426885314205686528263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53498951256876137124352175 80248426885314205686528263)
      ·
        refine ⟨120372640327971308529792395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80248426885314205686528263 120372640327971308529792395)
        ·
          refine ⟨180558960491956962794688593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120372640327971308529792395 180558960491956962794688593)
          ·
            refine ⟨135419220368967722096016445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180558960491956962794688593 135419220368967722096016445)
            ·
              refine ⟨50782207638362895786006167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135419220368967722096016445 50782207638362895786006167)
              ·
                refine ⟨76173311457544343679009251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50782207638362895786006167 76173311457544343679009251)
                ·
                  refine ⟨114259967186316515518513877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76173311457544343679009251 114259967186316515518513877)
                  ·
                    refine ⟨2677967980929293332465169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 114259967186316515518513877 2677967980929293332465169)
                    ·
                      refine ⟨2008475985696969999348877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2677967980929293332465169 2008475985696969999348877)
                      ·
                        rfl

theorem cell23_3911493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 7, 2].length) (baseStart_3911493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911493 prefixEnd_3911493 := by exact prefixLift 3911493
  have htrace : WordTrace (prefixWord ++ tailWord_3911493) baseStart_3911493 baseEnd_3911493 := by
    simpa [prefixWord, tailWord_3911493, baseEnd_3911493] using wordTrace_append hprefix tailTrace_3911493
  have hstable : (prefixWord ++ tailWord_3911493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911493).length < 2 ^ (prefixWord ++ tailWord_3911493).sum := by decide
  have hdescent : baseEnd_3911493 < baseStart_3911493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911500 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 2, 3, 3]
def baseStart_3911500 : Nat := 118140960795 + 3911500 * 2 ^ 59
def prefixEnd_3911500 : Nat := 4983230072969 + 3 ^ 40 * 3911500 * 2
def baseEnd_3911500 : Nat := 2008479580061551471961345

theorem tailTrace_3911500 : CollatzResearch.WordTrace tailWord_3911500 prefixEnd_3911500 2008479580061551471961345 := by
  unfold tailWord_3911500
  simp only [CollatzResearch.WordTrace]
  refine ⟨71332062664655502930221977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95109416886207337240295969 71332062664655502930221977)
  ·
    refine ⟨53499046998491627197666483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71332062664655502930221977 53499046998491627197666483)
    ·
      refine ⟨80248570497737440796499725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53499046998491627197666483 80248570497737440796499725)
      ·
        refine ⟨30093213936651540298687397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80248570497737440796499725 30093213936651540298687397)
        ·
          refine ⟨5642477613122163806003887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30093213936651540298687397 5642477613122163806003887)
          ·
            refine ⟨8463716419683245709005831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5642477613122163806003887 8463716419683245709005831)
            ·
              refine ⟨12695574629524868563508747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8463716419683245709005831 12695574629524868563508747)
              ·
                refine ⟨19043361944287302845263121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12695574629524868563508747 19043361944287302845263121)
                ·
                  refine ⟨14282521458215477133947341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19043361944287302845263121 14282521458215477133947341)
                  ·
                    refine ⟨5355945546830803925230253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14282521458215477133947341 5355945546830803925230253)
                    ·
                      refine ⟨2008479580061551471961345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5355945546830803925230253 2008479580061551471961345)
                      ·
                        rfl

theorem cell23_3911500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 2, 3, 3].length) (baseStart_3911500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911500 prefixEnd_3911500 := by exact prefixLift 3911500
  have htrace : WordTrace (prefixWord ++ tailWord_3911500) baseStart_3911500 baseEnd_3911500 := by
    simpa [prefixWord, tailWord_3911500, baseEnd_3911500] using wordTrace_append hprefix tailTrace_3911500
  have hstable : (prefixWord ++ tailWord_3911500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911500).length < 2 ^ (prefixWord ++ tailWord_3911500).sum := by decide
  have hdescent : baseEnd_3911500 < baseStart_3911500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911520 : List Nat := [2, 1, 1, 3, 3, 4, 1, 1, 2, 5]
def baseStart_3911520 : Nat := 118140960795 + 3911520 * 2 ^ 59
def prefixEnd_3911520 : Nat := 4983230072969 + 3 ^ 40 * 3911520 * 2
def baseEnd_3911520 : Nat := 669496616558213797903751

theorem tailTrace_3911520 : CollatzResearch.WordTrace tailWord_3911520 prefixEnd_3911520 669496616558213797903751 := by
  unfold tailWord_3911520
  simp only [CollatzResearch.WordTrace]
  refine ⟨71332427394619274638086007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95109903192825699517448009 71332427394619274638086007)
  ·
    refine ⟨106998641091928911957129011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71332427394619274638086007 106998641091928911957129011)
    ·
      refine ⟨160497961637893367935693517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 106998641091928911957129011 160497961637893367935693517)
      ·
        refine ⟨60186735614210012975885069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160497961637893367935693517 60186735614210012975885069)
        ·
          refine ⟨22570025855328754865956901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60186735614210012975885069 22570025855328754865956901)
          ·
            refine ⟨4231879847874141537366919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22570025855328754865956901 4231879847874141537366919)
            ·
              refine ⟨6347819771811212306050379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4231879847874141537366919 6347819771811212306050379)
              ·
                refine ⟨9521729657716818459075569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6347819771811212306050379 9521729657716818459075569)
                ·
                  refine ⟨7141297243287613844306677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9521729657716818459075569 7141297243287613844306677)
                  ·
                    refine ⟨669496616558213797903751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7141297243287613844306677 669496616558213797903751)
                    ·
                      rfl

theorem cell23_3911520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 2, 5].length) (baseStart_3911520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911520 prefixEnd_3911520 := by exact prefixLift 3911520
  have htrace : WordTrace (prefixWord ++ tailWord_3911520) baseStart_3911520 baseEnd_3911520 := by
    simpa [prefixWord, tailWord_3911520, baseEnd_3911520] using wordTrace_append hprefix tailTrace_3911520
  have hstable : (prefixWord ++ tailWord_3911520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911520).length < 2 ^ (prefixWord ++ tailWord_3911520).sum := by decide
  have hdescent : baseEnd_3911520 < baseStart_3911520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911573 : List Nat := [1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_3911573 : Nat := 118140960795 + 3911573 * 2 ^ 59
def prefixEnd_3911573 : Nat := 4983230072969 + 3 ^ 40 * 3911573 * 2
def baseEnd_3911573 : Nat := 2008517064149329686348509

theorem tailTrace_3911573 : CollatzResearch.WordTrace tailWord_3911573 prefixEnd_3911573 2008517064149329686348509 := by
  unfold tailWord_3911573
  simp only [CollatzResearch.WordTrace]
  refine ⟨142666787858046539327851373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95111191905364359551900915 142666787858046539327851373)
  ·
    refine ⟨53500045446767452247944265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142666787858046539327851373 53500045446767452247944265)
    ·
      refine ⟨40125034085075589185958199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53500045446767452247944265 40125034085075589185958199)
      ·
        refine ⟨60187551127613383778937299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40125034085075589185958199 60187551127613383778937299)
        ·
          refine ⟨90281326691420075668405949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60187551127613383778937299 90281326691420075668405949)
          ·
            refine ⟨33855497509282528375652231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90281326691420075668405949 33855497509282528375652231)
            ·
              refine ⟨50783246263923792563478347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33855497509282528375652231 50783246263923792563478347)
              ·
                refine ⟨76174869395885688845217521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50783246263923792563478347 76174869395885688845217521)
                ·
                  refine ⟨57131152046914266633913141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76174869395885688845217521 57131152046914266633913141)
                  ·
                    refine ⟨5356045504398212496929357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57131152046914266633913141 5356045504398212496929357)
                    ·
                      refine ⟨2008517064149329686348509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5356045504398212496929357 2008517064149329686348509)
                      ·
                        rfl

theorem cell23_3911573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_3911573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911573 prefixEnd_3911573 := by exact prefixLift 3911573
  have htrace : WordTrace (prefixWord ++ tailWord_3911573) baseStart_3911573 baseEnd_3911573 := by
    simpa [prefixWord, tailWord_3911573, baseEnd_3911573] using wordTrace_append hprefix tailTrace_3911573
  have hstable : (prefixWord ++ tailWord_3911573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911573).length < 2 ^ (prefixWord ++ tailWord_3911573).sum := by decide
  have hdescent : baseEnd_3911573 < baseStart_3911573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911623 : List Nat := [1, 1, 4, 1, 1, 2, 1, 5, 1, 6]
def baseStart_3911623 : Nat := 118140960795 + 3911623 * 2 ^ 59
def prefixEnd_3911623 : Nat := 4983230072969 + 3 ^ 40 * 3911623 * 2
def baseEnd_3911623 : Nat := 669514246060684830241093

theorem tailTrace_3911623 : CollatzResearch.WordTrace tailWord_3911623 prefixEnd_3911623 669514246060684830241093 := by
  unfold tailWord_3911623
  simp only [CollatzResearch.WordTrace]
  refine ⟨142668611507865397867171523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95112407671910265244781015 142668611507865397867171523)
  ·
    refine ⟨214002917261798096800757285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142668611507865397867171523 214002917261798096800757285)
    ·
      refine ⟨40125546986587143150141991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214002917261798096800757285 40125546986587143150141991)
      ·
        refine ⟨60188320479880714725212987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40125546986587143150141991 60188320479880714725212987)
        ·
          refine ⟨90282480719821072087819481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60188320479880714725212987 90282480719821072087819481)
          ·
            refine ⟨67711860539865804065864611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90282480719821072087819481 67711860539865804065864611)
            ·
              refine ⟨101567790809798706098796917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67711860539865804065864611 101567790809798706098796917)
              ·
                refine ⟨9521980388418628696762211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101567790809798706098796917 9521980388418628696762211)
                ·
                  refine ⟨14282970582627943045143317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9521980388418628696762211 14282970582627943045143317)
                  ·
                    refine ⟨669514246060684830241093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14282970582627943045143317 669514246060684830241093)
                    ·
                      rfl

theorem cell23_3911623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_3911623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911623 prefixEnd_3911623 := by exact prefixLift 3911623
  have htrace : WordTrace (prefixWord ++ tailWord_3911623) baseStart_3911623 baseEnd_3911623 := by
    simpa [prefixWord, tailWord_3911623, baseEnd_3911623] using wordTrace_append hprefix tailTrace_3911623
  have hstable : (prefixWord ++ tailWord_3911623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911623).length < 2 ^ (prefixWord ++ tailWord_3911623).sum := by decide
  have hdescent : baseEnd_3911623 < baseStart_3911623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911630 : List Nat := [4, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4]
def baseStart_3911630 : Nat := 118140960795 + 3911630 * 2 ^ 59
def prefixEnd_3911630 : Nat := 4983230072969 + 3 ^ 40 * 3911630 * 2
def baseEnd_3911630 : Nat := 2008546332546635963335747

theorem tailTrace_3911630 : CollatzResearch.WordTrace tailWord_3911630 prefixEnd_3911630 2008546332546635963335747 := by
  unfold tailWord_3911630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17833608352355004757834543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95112577879226692041784229 17833608352355004757834543)
  ·
    refine ⟨26750412528532507136751815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17833608352355004757834543 26750412528532507136751815)
    ·
      refine ⟨40125618792798760705127723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26750412528532507136751815 40125618792798760705127723)
      ·
        refine ⟨60188428189198141057691585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40125618792798760705127723 60188428189198141057691585)
        ·
          refine ⟨45141321141898605793268689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60188428189198141057691585 45141321141898605793268689)
          ·
            refine ⟨33855990856423954344951517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45141321141898605793268689 33855990856423954344951517)
            ·
              refine ⟨12695996571158982879356819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33855990856423954344951517 12695996571158982879356819)
              ·
                refine ⟨19043994856738474319035229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12695996571158982879356819 19043994856738474319035229)
                ·
                  refine ⟨7141498071276927869638211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19043994856738474319035229 7141498071276927869638211)
                  ·
                    refine ⟨10712247106915391804457317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7141498071276927869638211 10712247106915391804457317)
                    ·
                      refine ⟨2008546332546635963335747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10712247106915391804457317 2008546332546635963335747)
                      ·
                        rfl

theorem cell23_3911630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_3911630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911630 prefixEnd_3911630 := by exact prefixLift 3911630
  have htrace : WordTrace (prefixWord ++ tailWord_3911630) baseStart_3911630 baseEnd_3911630 := by
    simpa [prefixWord, tailWord_3911630, baseEnd_3911630] using wordTrace_append hprefix tailTrace_3911630
  have hstable : (prefixWord ++ tailWord_3911630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911630).length < 2 ^ (prefixWord ++ tailWord_3911630).sum := by decide
  have hdescent : baseEnd_3911630 < baseStart_3911630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911701 : List Nat := [1, 3, 2, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_3911701 : Nat := 118140960795 + 3911701 * 2 ^ 59
def prefixEnd_3911701 : Nat := 4983230072969 + 3 ^ 40 * 3911701 * 2
def baseEnd_3911701 : Nat := 2008582789673105185547921

theorem tailTrace_3911701 : CollatzResearch.WordTrace tailWord_3911701 prefixEnd_3911701 2008582789673105185547921 := by
  unfold tailWord_3911701
  simp only [CollatzResearch.WordTrace]
  refine ⟨142671456401582817188510957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95114304267721878125673971 142671456401582817188510957)
  ·
    refine ⟨53501796150593556445691609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142671456401582817188510957 53501796150593556445691609)
    ·
      refine ⟨40126347112945167334268707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53501796150593556445691609 40126347112945167334268707)
      ·
        refine ⟨60189520669417751001403061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40126347112945167334268707 60189520669417751001403061)
        ·
          refine ⟨5642767562757914156381537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60189520669417751001403061 5642767562757914156381537)
          ·
            refine ⟨4232075672068435617286153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5642767562757914156381537 4232075672068435617286153)
            ·
              refine ⟨3174056754051326712964615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232075672068435617286153 3174056754051326712964615)
              ·
                refine ⟨4761085131076990069446923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174056754051326712964615 4761085131076990069446923)
                ·
                  refine ⟨7141627696615485104170385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761085131076990069446923 7141627696615485104170385)
                  ·
                    refine ⟨5356220772461613828127789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7141627696615485104170385 5356220772461613828127789)
                    ·
                      refine ⟨2008582789673105185547921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5356220772461613828127789 2008582789673105185547921)
                      ·
                        rfl

theorem cell23_3911701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_3911701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911701 prefixEnd_3911701 := by exact prefixLift 3911701
  have htrace : WordTrace (prefixWord ++ tailWord_3911701) baseStart_3911701 baseEnd_3911701 := by
    simpa [prefixWord, tailWord_3911701, baseEnd_3911701] using wordTrace_append hprefix tailTrace_3911701
  have hstable : (prefixWord ++ tailWord_3911701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911701).length < 2 ^ (prefixWord ++ tailWord_3911701).sum := by decide
  have hdescent : baseEnd_3911701 < baseStart_3911701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911723 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 5]
def baseStart_3911723 : Nat := 118140960795 + 3911723 * 2 ^ 59
def prefixEnd_3911723 : Nat := 4983230072969 + 3 ^ 40 * 3911723 * 2
def baseEnd_3911723 : Nat := 2008594086247504099472819

theorem tailTrace_3911723 : CollatzResearch.WordTrace tailWord_3911723 prefixEnd_3911723 2008594086247504099472819 := by
  unfold tailWord_3911723
  simp only [CollatzResearch.WordTrace]
  refine ⟨142672258807503114945811823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95114839205002076630541215 142672258807503114945811823)
  ·
    refine ⟨214008388211254672418717735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142672258807503114945811823 214008388211254672418717735)
    ·
      refine ⟨321012582316882008628076603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214008388211254672418717735 321012582316882008628076603)
      ·
        refine ⟨481518873475323012942114905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321012582316882008628076603 481518873475323012942114905)
        ·
          refine ⟨361139155106492259706586179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481518873475323012942114905 361139155106492259706586179)
          ·
            refine ⟨541708732659738389559879269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361139155106492259706586179 541708732659738389559879269)
            ·
              refine ⟨101570387373700948042477363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 541708732659738389559879269 101570387373700948042477363)
              ·
                refine ⟨152355581060551422063716045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101570387373700948042477363 152355581060551422063716045)
                ·
                  refine ⟨57133342897706783273893517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152355581060551422063716045 57133342897706783273893517)
                  ·
                    refine ⟨21425003586640043727710069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57133342897706783273893517 21425003586640043727710069)
                    ·
                      refine ⟨2008594086247504099472819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21425003586640043727710069 2008594086247504099472819)
                      ·
                        rfl

theorem cell23_3911723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_3911723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911723 prefixEnd_3911723 := by exact prefixLift 3911723
  have htrace : WordTrace (prefixWord ++ tailWord_3911723) baseStart_3911723 baseEnd_3911723 := by
    simpa [prefixWord, tailWord_3911723, baseEnd_3911723] using wordTrace_append hprefix tailTrace_3911723
  have hstable : (prefixWord ++ tailWord_3911723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911723).length < 2 ^ (prefixWord ++ tailWord_3911723).sum := by decide
  have hdescent : baseEnd_3911723 < baseStart_3911723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911730 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 2, 6]
def baseStart_3911730 : Nat := 118140960795 + 3911730 * 2 ^ 59
def prefixEnd_3911730 : Nat := 4983230072969 + 3 ^ 40 * 3911730 * 2
def baseEnd_3911730 : Nat := 669532560204028524028429

theorem tailTrace_3911730 : CollatzResearch.WordTrace tailWord_3911730 prefixEnd_3911730 669532560204028524028429 := by
  unfold tailWord_3911730
  simp only [CollatzResearch.WordTrace]
  refine ⟨35668128529619438785329161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95115009412318503427544429 35668128529619438785329161)
  ·
    refine ⟨26751096397214579088996871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35668128529619438785329161 26751096397214579088996871)
    ·
      refine ⟨40126644595821868633495307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26751096397214579088996871 40126644595821868633495307)
      ·
        refine ⟨60189966893732802950242961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40126644595821868633495307 60189966893732802950242961)
        ·
          refine ⟨45142475170299602212682221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60189966893732802950242961 45142475170299602212682221)
          ·
            refine ⟨16928428188862350829755833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45142475170299602212682221 16928428188862350829755833)
            ·
              refine ⟨12696321141646763122316875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16928428188862350829755833 12696321141646763122316875)
              ·
                refine ⟨19044481712470144683475313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12696321141646763122316875 19044481712470144683475313)
                ·
                  refine ⟨14283361284352608512606485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19044481712470144683475313 14283361284352608512606485)
                  ·
                    refine ⟨669532560204028524028429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14283361284352608512606485 669532560204028524028429)
                    ·
                      rfl

theorem cell23_3911730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_3911730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911730 prefixEnd_3911730 := by exact prefixLift 3911730
  have htrace : WordTrace (prefixWord ++ tailWord_3911730) baseStart_3911730 baseEnd_3911730 := by
    simpa [prefixWord, tailWord_3911730, baseEnd_3911730] using wordTrace_append hprefix tailTrace_3911730
  have hstable : (prefixWord ++ tailWord_3911730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911730).length < 2 ^ (prefixWord ++ tailWord_3911730).sum := by decide
  have hdescent : baseEnd_3911730 < baseStart_3911730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911740 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 5]
def baseStart_3911740 : Nat := 118140960795 + 3911740 * 2 ^ 59
def prefixEnd_3911740 : Nat := 4983230072969 + 3 ^ 40 * 3911740 * 2
def baseEnd_3911740 : Nat := 2008602815418630532960241

theorem tailTrace_3911740 : CollatzResearch.WordTrace tailWord_3911740 prefixEnd_3911740 2008602815418630532960241 := by
  unfold tailWord_3911740
  simp only [CollatzResearch.WordTrace]
  refine ⟨71336439424220763424590337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95115252565627684566120449 71336439424220763424590337)
  ·
    refine ⟨53502329568165572568442753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71336439424220763424590337 53502329568165572568442753)
    ·
      refine ⟨40126747176124179426332065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53502329568165572568442753 40126747176124179426332065)
      ·
        refine ⟨30095060382093134569749049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40126747176124179426332065 30095060382093134569749049)
        ·
          refine ⟨22571295286569850927311787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30095060382093134569749049 22571295286569850927311787)
          ·
            refine ⟨33856942929854776390967681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22571295286569850927311787 33856942929854776390967681)
            ·
              refine ⟨25392707197391082293225761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33856942929854776390967681 25392707197391082293225761)
              ·
                refine ⟨19044530398043311719919321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25392707197391082293225761 19044530398043311719919321)
                ·
                  refine ⟨14283397798532483789939491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19044530398043311719919321 14283397798532483789939491)
                  ·
                    refine ⟨21425096697798725684909237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14283397798532483789939491 21425096697798725684909237)
                    ·
                      refine ⟨2008602815418630532960241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21425096697798725684909237 2008602815418630532960241)
                      ·
                        rfl

theorem cell23_3911740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_3911740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911740 prefixEnd_3911740 := by exact prefixLift 3911740
  have htrace : WordTrace (prefixWord ++ tailWord_3911740) baseStart_3911740 baseEnd_3911740 := by
    simpa [prefixWord, tailWord_3911740, baseEnd_3911740] using wordTrace_append hprefix tailTrace_3911740
  have hstable : (prefixWord ++ tailWord_3911740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911740).length < 2 ^ (prefixWord ++ tailWord_3911740).sum := by decide
  have hdescent : baseEnd_3911740 < baseStart_3911740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911757 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_3911757 : Nat := 118140960795 + 3911757 * 2 ^ 59
def prefixEnd_3911757 : Nat := 4983230072969 + 3 ^ 40 * 3911757 * 2
def baseEnd_3911757 : Nat := 2008611544589756966447663

theorem tailTrace_3911757 : CollatzResearch.WordTrace tailWord_3911757 prefixEnd_3911757 2008611544589756966447663 := by
  unfold tailWord_3911757
  simp only [CollatzResearch.WordTrace]
  refine ⟨142673498889379938752549525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95115665926253292501699683 142673498889379938752549525)
  ·
    refine ⟨6687820260439684629025759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 142673498889379938752549525 6687820260439684629025759)
    ·
      refine ⟨10031730390659526943538639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6687820260439684629025759 10031730390659526943538639)
      ·
        refine ⟨15047595585989290415307959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10031730390659526943538639 15047595585989290415307959)
        ·
          refine ⟨22571393378983935622961939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15047595585989290415307959 22571393378983935622961939)
          ·
            refine ⟨33857090068475903434442909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22571393378983935622961939 33857090068475903434442909)
            ·
              refine ⟨12696408775678463787916091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33857090068475903434442909 12696408775678463787916091)
              ·
                refine ⟨19044613163517695681874137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12696408775678463787916091 19044613163517695681874137)
                ·
                  refine ⟨14283459872638271761405603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19044613163517695681874137 14283459872638271761405603)
                  ·
                    refine ⟨21425189808957407642108405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14283459872638271761405603 21425189808957407642108405)
                    ·
                      refine ⟨2008611544589756966447663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21425189808957407642108405 2008611544589756966447663)
                      ·
                        rfl

theorem cell23_3911757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_3911757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911757 prefixEnd_3911757 := by exact prefixLift 3911757
  have htrace : WordTrace (prefixWord ++ tailWord_3911757) baseStart_3911757 baseEnd_3911757 := by
    simpa [prefixWord, tailWord_3911757, baseEnd_3911757] using wordTrace_append hprefix tailTrace_3911757
  have hstable : (prefixWord ++ tailWord_3911757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911757).length < 2 ^ (prefixWord ++ tailWord_3911757).sum := by decide
  have hdescent : baseEnd_3911757 < baseStart_3911757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911763 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 8]
def baseStart_3911763 : Nat := 118140960795 + 3911763 * 2 ^ 59
def prefixEnd_3911763 : Nat := 4983230072969 + 3 ^ 40 * 3911763 * 2
def baseEnd_3911763 : Nat := 2008614625473683942972635

theorem tailTrace_3911763 : CollatzResearch.WordTrace tailWord_3911763 prefixEnd_3911763 2008614625473683942972635 := by
  unfold tailWord_3911763
  simp only [CollatzResearch.WordTrace]
  refine ⟨142673717727358201777267943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95115811818238801184845295 142673717727358201777267943)
  ·
    refine ⟨214010576591037302665901915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142673717727358201777267943 214010576591037302665901915)
    ·
      refine ⟨321015864886555953998852873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214010576591037302665901915 321015864886555953998852873)
      ·
        refine ⟨240761898664916965499139655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321015864886555953998852873 240761898664916965499139655)
        ·
          refine ⟨361142847997375448248709483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240761898664916965499139655 361142847997375448248709483)
          ·
            refine ⟨541714271996063172373064225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361142847997375448248709483 541714271996063172373064225)
            ·
              refine ⟨406285703997047379279798169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541714271996063172373064225 406285703997047379279798169)
              ·
                refine ⟨304714277997785534459848627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406285703997047379279798169 304714277997785534459848627)
                ·
                  refine ⟨457071416996678301689772941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 304714277997785534459848627 457071416996678301689772941)
                  ·
                    refine ⟨171401781373754363133664853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 457071416996678301689772941 171401781373754363133664853)
                    ·
                      refine ⟨2008614625473683942972635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 171401781373754363133664853 2008614625473683942972635)
                      ·
                        rfl

theorem cell23_3911763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_3911763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911763 prefixEnd_3911763 := by exact prefixLift 3911763
  have htrace : WordTrace (prefixWord ++ tailWord_3911763) baseStart_3911763 baseEnd_3911763 := by
    simpa [prefixWord, tailWord_3911763, baseEnd_3911763] using wordTrace_append hprefix tailTrace_3911763
  have hstable : (prefixWord ++ tailWord_3911763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911763).length < 2 ^ (prefixWord ++ tailWord_3911763).sum := by decide
  have hdescent : baseEnd_3911763 < baseStart_3911763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911788 : List Nat := [2, 2, 1, 1, 3, 5, 2, 1, 2, 2, 2]
def baseStart_3911788 : Nat := 118140960795 + 3911788 * 2 ^ 59
def prefixEnd_3911788 : Nat := 4983230072969 + 3 ^ 40 * 3911788 * 2
def baseEnd_3911788 : Nat := 2008627462490046345160021

theorem tailTrace_3911788 : CollatzResearch.WordTrace tailWord_3911788 prefixEnd_3911788 2008627462490046345160021 := by
  unfold tailWord_3911788
  simp only [CollatzResearch.WordTrace]
  refine ⟨71337314776133815523464009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95116419701511754031285345 71337314776133815523464009)
  ·
    refine ⟨53502986082100361642598007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71337314776133815523464009 53502986082100361642598007)
    ·
      refine ⟨80254479123150542463897011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53502986082100361642598007 80254479123150542463897011)
      ·
        refine ⟨120381718684725813695845517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80254479123150542463897011 120381718684725813695845517)
        ·
          refine ⟨45143144506772180135942069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120381718684725813695845517 45143144506772180135942069)
          ·
            refine ⟨4232169797509891887744569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 45143144506772180135942069 4232169797509891887744569)
            ·
              refine ⟨3174127348132418915808427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232169797509891887744569 3174127348132418915808427)
              ·
                refine ⟨4761191022198628373712641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174127348132418915808427 4761191022198628373712641)
                ·
                  refine ⟨3570893266648971280284481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4761191022198628373712641 3570893266648971280284481)
                  ·
                    refine ⟨2678169949986728460213361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3570893266648971280284481 2678169949986728460213361)
                    ·
                      refine ⟨2008627462490046345160021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678169949986728460213361 2008627462490046345160021)
                      ·
                        rfl

theorem cell23_3911788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 2, 2].length) (baseStart_3911788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911788 prefixEnd_3911788 := by exact prefixLift 3911788
  have htrace : WordTrace (prefixWord ++ tailWord_3911788) baseStart_3911788 baseEnd_3911788 := by
    simpa [prefixWord, tailWord_3911788, baseEnd_3911788] using wordTrace_append hprefix tailTrace_3911788
  have hstable : (prefixWord ++ tailWord_3911788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911788).length < 2 ^ (prefixWord ++ tailWord_3911788).sum := by decide
  have hdescent : baseEnd_3911788 < baseStart_3911788 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911827 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 2, 4, 2]
def baseStart_3911827 : Nat := 118140960795 + 3911827 * 2 ^ 59
def prefixEnd_3911827 : Nat := 4983230072969 + 3 ^ 40 * 3911827 * 2
def baseEnd_3911827 : Nat := 2008647488235571692572341

theorem tailTrace_3911827 : CollatzResearch.WordTrace tailWord_3911827 prefixEnd_3911827 2008647488235571692572341 := by
  unfold tailWord_3911827
  simp only [CollatzResearch.WordTrace]
  refine ⟨142676051999126340707597735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95117367999417560471731823 142676051999126340707597735)
  ·
    refine ⟨214014077998689511061396603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142676051999126340707597735 214014077998689511061396603)
    ·
      refine ⟨321021116998034266592094905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214014077998689511061396603 321021116998034266592094905)
      ·
        refine ⟨240765837748525699944071179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321021116998034266592094905 240765837748525699944071179)
        ·
          refine ⟨361148756622788549916106769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240765837748525699944071179 361148756622788549916106769)
          ·
            refine ⟨270861567467091412437080077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361148756622788549916106769 270861567467091412437080077)
            ·
              refine ⟨101573087800159279663905029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 270861567467091412437080077 101573087800159279663905029)
              ·
                refine ⟨19044953962529864936982193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101573087800159279663905029 19044953962529864936982193)
                ·
                  refine ⟨14283715471897398702736645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19044953962529864936982193 14283715471897398702736645)
                  ·
                    refine ⟨2678196650980762256763121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14283715471897398702736645 2678196650980762256763121)
                    ·
                      refine ⟨2008647488235571692572341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678196650980762256763121 2008647488235571692572341)
                      ·
                        rfl

theorem cell23_3911827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 4, 2].length) (baseStart_3911827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911827 prefixEnd_3911827 := by exact prefixLift 3911827
  have htrace : WordTrace (prefixWord ++ tailWord_3911827) baseStart_3911827 baseEnd_3911827 := by
    simpa [prefixWord, tailWord_3911827, baseEnd_3911827] using wordTrace_append hprefix tailTrace_3911827
  have hstable : (prefixWord ++ tailWord_3911827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911827).length < 2 ^ (prefixWord ++ tailWord_3911827).sum := by decide
  have hdescent : baseEnd_3911827 < baseStart_3911827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911884 : List Nat := [2, 2, 1, 6, 1, 1, 1, 1, 8]
def baseStart_3911884 : Nat := 118140960795 + 3911884 * 2 ^ 59
def prefixEnd_3911884 : Nat := 4983230072969 + 3 ^ 40 * 3911884 * 2
def baseEnd_3911884 : Nat := 223186306292541996617731

theorem tailTrace_3911884 : CollatzResearch.WordTrace tailWord_3911884 prefixEnd_3911884 223186306292541996617731 := by
  unfold tailWord_3911884
  simp only [CollatzResearch.WordTrace]
  refine ⟨71339065479959919721211353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95118753973279892961615137 71339065479959919721211353)
  ·
    refine ⟨53504299109969939790908515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71339065479959919721211353 53504299109969939790908515)
    ·
      refine ⟨80256448664954909686362773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53504299109969939790908515 80256448664954909686362773)
      ·
        refine ⟨3762021031169761391548255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 80256448664954909686362773 3762021031169761391548255)
        ·
          refine ⟨5643031546754642087322383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762021031169761391548255 5643031546754642087322383)
          ·
            refine ⟨8464547320131963130983575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5643031546754642087322383 8464547320131963130983575)
            ·
              refine ⟨12696820980197944696475363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464547320131963130983575 12696820980197944696475363)
              ·
                refine ⟨19045231470296917044713045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12696820980197944696475363 19045231470296917044713045)
                ·
                  refine ⟨223186306292541996617731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 19045231470296917044713045 223186306292541996617731)
                  ·
                    rfl

theorem cell23_3911884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 8].length) (baseStart_3911884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911884 prefixEnd_3911884 := by exact prefixLift 3911884
  have htrace : WordTrace (prefixWord ++ tailWord_3911884) baseStart_3911884 baseEnd_3911884 := by
    simpa [prefixWord, tailWord_3911884, baseEnd_3911884] using wordTrace_append hprefix tailTrace_3911884
  have hstable : (prefixWord ++ tailWord_3911884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911884).length < 2 ^ (prefixWord ++ tailWord_3911884).sum := by decide
  have hdescent : baseEnd_3911884 < baseStart_3911884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911901 : List Nat := [1, 4, 3, 2, 1, 2, 3, 1, 6]
def baseStart_3911901 : Nat := 118140960795 + 3911901 * 2 ^ 59
def prefixEnd_3911901 : Nat := 4983230072969 + 3 ^ 40 * 3911901 * 2
def baseEnd_3911901 : Nat := 223187276200444933671889

theorem tailTrace_3911901 : CollatzResearch.WordTrace tailWord_3911901 prefixEnd_3911901 223187276200444933671889 := by
  unfold tailWord_3911901
  simp only [CollatzResearch.WordTrace]
  refine ⟨142678751000858251345791557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95119167333905500897194371 142678751000858251345791557)
  ·
    refine ⟨26752265812660922127335917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142678751000858251345791557 26752265812660922127335917)
    ·
      refine ⟨10032099679747845797750969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26752265812660922127335917 10032099679747845797750969)
      ·
        refine ⟨7524074759810884348313227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10032099679747845797750969 7524074759810884348313227)
        ·
          refine ⟨11286112139716326522469841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7524074759810884348313227 11286112139716326522469841)
          ·
            refine ⟨8464584104787244891852381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11286112139716326522469841 8464584104787244891852381)
            ·
              refine ⟨3174219039295216834444643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8464584104787244891852381 3174219039295216834444643)
              ·
                refine ⟨4761328558942825251666965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174219039295216834444643 4761328558942825251666965)
                ·
                  refine ⟨223187276200444933671889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4761328558942825251666965 223187276200444933671889)
                  ·
                    rfl

theorem cell23_3911901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 1, 6].length) (baseStart_3911901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911901 prefixEnd_3911901 := by exact prefixLift 3911901
  have htrace : WordTrace (prefixWord ++ tailWord_3911901) baseStart_3911901 baseEnd_3911901 := by
    simpa [prefixWord, tailWord_3911901, baseEnd_3911901] using wordTrace_append hprefix tailTrace_3911901
  have hstable : (prefixWord ++ tailWord_3911901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911901).length < 2 ^ (prefixWord ++ tailWord_3911901).sum := by decide
  have hdescent : baseEnd_3911901 < baseStart_3911901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911911 : List Nat := [1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_3911911 : Nat := 118140960795 + 3911911 * 2 ^ 59
def prefixEnd_3911911 : Nat := 4983230072969 + 3 ^ 40 * 3911911 * 2
def baseEnd_3911911 : Nat := 2008690620610549363921955

theorem tailTrace_3911911 : CollatzResearch.WordTrace tailWord_3911911 prefixEnd_3911911 2008690620610549363921955 := by
  unfold tailWord_3911911
  simp only [CollatzResearch.WordTrace]
  refine ⟨142679115730822023053655587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95119410487214682035770391 142679115730822023053655587)
  ·
    refine ⟨214018673596233034580483381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142679115730822023053655587 214018673596233034580483381)
    ·
      refine ⟨20064250649646846991920317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214018673596233034580483381 20064250649646846991920317)
      ·
        refine ⟨7524093993617567621970119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20064250649646846991920317 7524093993617567621970119)
        ·
          refine ⟨11286140990426351432955179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7524093993617567621970119 11286140990426351432955179)
          ·
            refine ⟨16929211485639527149432769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11286140990426351432955179 16929211485639527149432769)
            ·
              refine ⟨12696908614229645362074577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16929211485639527149432769 12696908614229645362074577)
              ·
                refine ⟨9522681460672234021555933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12696908614229645362074577 9522681460672234021555933)
                ·
                  refine ⟨3571005547752087758083475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9522681460672234021555933 3571005547752087758083475)
                  ·
                    refine ⟨5356508321628131637125213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3571005547752087758083475 5356508321628131637125213)
                    ·
                      refine ⟨2008690620610549363921955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5356508321628131637125213 2008690620610549363921955)
                      ·
                        rfl

theorem cell23_3911911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_3911911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911911 prefixEnd_3911911 := by exact prefixLift 3911911
  have htrace : WordTrace (prefixWord ++ tailWord_3911911) baseStart_3911911 baseEnd_3911911 := by
    simpa [prefixWord, tailWord_3911911, baseEnd_3911911] using wordTrace_append hprefix tailTrace_3911911
  have hstable : (prefixWord ++ tailWord_3911911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911911).length < 2 ^ (prefixWord ++ tailWord_3911911).sum := by decide
  have hdescent : baseEnd_3911911 < baseStart_3911911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911914 : List Nat := [3, 1, 3, 1, 1, 2, 4, 2, 1, 5]
def baseStart_3911914 : Nat := 118140960795 + 3911914 * 2 ^ 59
def prefixEnd_3911914 : Nat := 4983230072969 + 3 ^ 40 * 3911914 * 2
def baseEnd_3911914 : Nat := 669564053684170950728147

theorem tailTrace_3911914 : CollatzResearch.WordTrace tailWord_3911914 prefixEnd_3911914 669564053684170950728147 := by
  unfold tailWord_3911914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35669806287452788641503699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95119483433207436377343197 35669806287452788641503699)
  ·
    refine ⟨53504709431179182962255549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35669806287452788641503699 53504709431179182962255549)
    ·
      refine ⟨20064266036692193610845831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53504709431179182962255549 20064266036692193610845831)
      ·
        refine ⟨30096399055038290416268747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20064266036692193610845831 30096399055038290416268747)
        ·
          refine ⟨45144598582557435624403121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30096399055038290416268747 45144598582557435624403121)
          ·
            refine ⟨33858448936918076718302341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45144598582557435624403121 33858448936918076718302341)
            ·
              refine ⟨6348459175672139384681689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33858448936918076718302341 6348459175672139384681689)
              ·
                refine ⟨4761344381754104538511267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6348459175672139384681689 4761344381754104538511267)
                ·
                  refine ⟨7142016572631156807766901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761344381754104538511267 7142016572631156807766901)
                  ·
                    refine ⟨669564053684170950728147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7142016572631156807766901 669564053684170950728147)
                    ·
                      rfl

theorem cell23_3911914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 1, 5].length) (baseStart_3911914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911914 prefixEnd_3911914 := by exact prefixLift 3911914
  have htrace : WordTrace (prefixWord ++ tailWord_3911914) baseStart_3911914 baseEnd_3911914 := by
    simpa [prefixWord, tailWord_3911914, baseEnd_3911914] using wordTrace_append hprefix tailTrace_3911914
  have hstable : (prefixWord ++ tailWord_3911914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911914).length < 2 ^ (prefixWord ++ tailWord_3911914).sum := by decide
  have hdescent : baseEnd_3911914 < baseStart_3911914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911938 : List Nat := [3, 4, 1, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_3911938 : Nat := 118140960795 + 3911938 * 2 ^ 59
def prefixEnd_3911938 : Nat := 4983230072969 + 3 ^ 40 * 3911938 * 2
def baseEnd_3911938 : Nat := 2008704484588220758284331

theorem tailTrace_3911938 : CollatzResearch.WordTrace tailWord_3911938 prefixEnd_3911938 2008704484588220758284331 := by
  unfold tailWord_3911938
  simp only [CollatzResearch.WordTrace]
  refine ⟨35670025125431051666222117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95120067001149471109925645 35670025125431051666222117)
  ·
    refine ⟨6688129711018322187416647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 35670025125431051666222117 6688129711018322187416647)
    ·
      refine ⟨10032194566527483281124971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6688129711018322187416647 10032194566527483281124971)
      ·
        refine ⟨15048291849791224921687457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10032194566527483281124971 15048291849791224921687457)
        ·
          refine ⟨11286218887343418691265593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15048291849791224921687457 11286218887343418691265593)
          ·
            refine ⟨8464664165507564018449195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11286218887343418691265593 8464664165507564018449195)
            ·
              refine ⟨12696996248261346027673793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8464664165507564018449195 12696996248261346027673793)
              ·
                refine ⟨9522747186196009520755345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12696996248261346027673793 9522747186196009520755345)
                ·
                  refine ⟨7142060389647007140566509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9522747186196009520755345 7142060389647007140566509)
                  ·
                    refine ⟨2678272646117627677712441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7142060389647007140566509 2678272646117627677712441)
                    ·
                      refine ⟨2008704484588220758284331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678272646117627677712441 2008704484588220758284331)
                      ·
                        rfl

theorem cell23_3911938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_3911938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911938 prefixEnd_3911938 := by exact prefixLift 3911938
  have htrace : WordTrace (prefixWord ++ tailWord_3911938) baseStart_3911938 baseEnd_3911938 := by
    simpa [prefixWord, tailWord_3911938, baseEnd_3911938] using wordTrace_append hprefix tailTrace_3911938
  have hstable : (prefixWord ++ tailWord_3911938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911938).length < 2 ^ (prefixWord ++ tailWord_3911938).sum := by decide
  have hdescent : baseEnd_3911938 < baseStart_3911938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911944 : List Nat := [2, 1, 3, 2, 3, 1, 2, 1, 4, 4]
def baseStart_3911944 : Nat := 118140960795 + 3911944 * 2 ^ 59
def prefixEnd_3911944 : Nat := 4983230072969 + 3 ^ 40 * 3911944 * 2
def baseEnd_3911944 : Nat := 669569188490715911603101

theorem tailTrace_3911944 : CollatzResearch.WordTrace tailWord_3911944 prefixEnd_3911944 669569188490715911603101 := by
  unfold tailWord_3911944
  simp only [CollatzResearch.WordTrace]
  refine ⟨71340159669851234844803443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95120212893134979793071257 71340159669851234844803443)
  ·
    refine ⟨107010239504776852267205165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71340159669851234844803443 107010239504776852267205165)
    ·
      refine ⟨40128839814291319600201937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107010239504776852267205165 40128839814291319600201937)
      ·
        refine ⟨30096629860718489700151453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40128839814291319600201937 30096629860718489700151453)
        ·
          refine ⟨11286236197769433637556795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30096629860718489700151453 11286236197769433637556795)
          ·
            refine ⟨16929354296654150456335193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11286236197769433637556795 16929354296654150456335193)
            ·
              refine ⟨12697015722490612842251395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16929354296654150456335193 12697015722490612842251395)
              ·
                refine ⟨19045523583735919263377093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12697015722490612842251395 19045523583735919263377093)
                ·
                  refine ⟨3571035671950484861883205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19045523583735919263377093 3571035671950484861883205)
                  ·
                    refine ⟨669569188490715911603101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3571035671950484861883205 669569188490715911603101)
                    ·
                      rfl

theorem cell23_3911944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_3911944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911944 prefixEnd_3911944 := by exact prefixLift 3911944
  have htrace : WordTrace (prefixWord ++ tailWord_3911944) baseStart_3911944 baseEnd_3911944 := by
    simpa [prefixWord, tailWord_3911944, baseEnd_3911944] using wordTrace_append hprefix tailTrace_3911944
  have hstable : (prefixWord ++ tailWord_3911944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911944).length < 2 ^ (prefixWord ++ tailWord_3911944).sum := by decide
  have hdescent : baseEnd_3911944 < baseStart_3911944 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3911984 : List Nat := [2, 1, 1, 1, 2, 2, 2, 4, 4, 1, 3]
def baseStart_3911984 : Nat := 118140960795 + 3911984 * 2 ^ 59
def prefixEnd_3911984 : Nat := 4983230072969 + 3 ^ 40 * 3911984 * 2
def baseEnd_3911984 : Nat := 2008728104698327578309119

theorem tailTrace_3911984 : CollatzResearch.WordTrace tailWord_3911984 prefixEnd_3911984 2008728104698327578309119 := by
  unfold tailWord_3911984
  simp only [CollatzResearch.WordTrace]
  refine ⟨71340889129778778260531503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95121185506371704347375337 71340889129778778260531503)
  ·
    refine ⟨107011333694668167390797255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71340889129778778260531503 107011333694668167390797255)
    ·
      refine ⟨160517000542002251086195883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107011333694668167390797255 160517000542002251086195883)
      ·
        refine ⟨240775500813003376629293825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160517000542002251086195883 240775500813003376629293825)
        ·
          refine ⟨180581625609752532471970369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240775500813003376629293825 180581625609752532471970369)
          ·
            refine ⟨135436219207314399353977777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180581625609752532471970369 135436219207314399353977777)
            ·
              refine ⟨101577164405485799515483333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135436219207314399353977777 101577164405485799515483333)
              ·
                refine ⟨19045718326028587409153125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101577164405485799515483333 19045718326028587409153125)
                ·
                  refine ⟨3571072186130360139216211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19045718326028587409153125 3571072186130360139216211)
                  ·
                    refine ⟨5356608279195540208824317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3571072186130360139216211 5356608279195540208824317)
                    ·
                      refine ⟨2008728104698327578309119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5356608279195540208824317 2008728104698327578309119)
                      ·
                        rfl

theorem cell23_3911984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 4, 1, 3].length) (baseStart_3911984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3911984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3911984 prefixEnd_3911984 := by exact prefixLift 3911984
  have htrace : WordTrace (prefixWord ++ tailWord_3911984) baseStart_3911984 baseEnd_3911984 := by
    simpa [prefixWord, tailWord_3911984, baseEnd_3911984] using wordTrace_append hprefix tailTrace_3911984
  have hstable : (prefixWord ++ tailWord_3911984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3911984).length < 2 ^ (prefixWord ++ tailWord_3911984).sum := by decide
  have hdescent : baseEnd_3911984 < baseStart_3911984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3911984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912007 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_3912007 : Nat := 118140960795 + 3912007 * 2 ^ 59
def prefixEnd_3912007 : Nat := 4983230072969 + 3 ^ 40 * 3912007 * 2
def baseEnd_3912007 : Nat := 2008739914753380988321513

theorem tailTrace_3912007 : CollatzResearch.WordTrace tailWord_3912007 prefixEnd_3912007 2008739914753380988321513 := by
  unfold tailWord_3912007
  simp only [CollatzResearch.WordTrace]
  refine ⟨142682617138474231449150275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95121744758982820966100183 142682617138474231449150275)
  ·
    refine ⟨214023925707711347173725413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142682617138474231449150275 214023925707711347173725413)
    ·
      refine ⟨40129486070195877595073515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214023925707711347173725413 40129486070195877595073515)
      ·
        refine ⟨60194229105293816392610273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40129486070195877595073515 60194229105293816392610273)
        ·
          refine ⟨45145671828970362294457705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60194229105293816392610273 45145671828970362294457705)
          ·
            refine ⟨33859253871727771720843279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45145671828970362294457705 33859253871727771720843279)
            ·
              refine ⟨50788880807591657581264919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33859253871727771720843279 50788880807591657581264919)
              ·
                refine ⟨76183321211387486371897379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50788880807591657581264919 76183321211387486371897379)
                ·
                  refine ⟨114274981817081229557846069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76183321211387486371897379 114274981817081229557846069)
                  ·
                    refine ⟨10713279545351365271048069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114274981817081229557846069 10713279545351365271048069)
                    ·
                      refine ⟨2008739914753380988321513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10713279545351365271048069 2008739914753380988321513)
                      ·
                        rfl

theorem cell23_3912007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_3912007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912007 prefixEnd_3912007 := by exact prefixLift 3912007
  have htrace : WordTrace (prefixWord ++ tailWord_3912007) baseStart_3912007 baseEnd_3912007 := by
    simpa [prefixWord, tailWord_3912007, baseEnd_3912007] using wordTrace_append hprefix tailTrace_3912007
  have hstable : (prefixWord ++ tailWord_3912007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912007).length < 2 ^ (prefixWord ++ tailWord_3912007).sum := by decide
  have hdescent : baseEnd_3912007 < baseStart_3912007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912017 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 1, 8]
def baseStart_3912017 : Nat := 118140960795 + 3912017 * 2 ^ 59
def prefixEnd_3912017 : Nat := 4983230072969 + 3 ^ 40 * 3912017 * 2
def baseEnd_3912017 : Nat := 669581683186641983065489

theorem tailTrace_3912017 : CollatzResearch.WordTrace tailWord_3912017 prefixEnd_3912017 669581683186641983065489 := by
  unfold tailWord_3912017
  simp only [CollatzResearch.WordTrace]
  refine ⟨142682981868438003157014305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95121987912292002104676203 142682981868438003157014305)
  ·
    refine ⟨107012236401328502367760729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142682981868438003157014305 107012236401328502367760729)
    ·
      refine ⟨80259177300996376775820547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107012236401328502367760729 80259177300996376775820547)
      ·
        refine ⟨120388765951494565163730821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80259177300996376775820547 120388765951494565163730821)
        ·
          refine ⟨22572893615905230968199529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120388765951494565163730821 22572893615905230968199529)
          ·
            refine ⟨16929670211928923226149647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22572893615905230968199529 16929670211928923226149647)
            ·
              refine ⟨25394505317893384839224471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16929670211928923226149647 25394505317893384839224471)
              ·
                refine ⟨38091757976840077258836707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25394505317893384839224471 38091757976840077258836707)
                ·
                  refine ⟨57137636965260115888255061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38091757976840077258836707 57137636965260115888255061)
                  ·
                    refine ⟨669581683186641983065489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57137636965260115888255061 669581683186641983065489)
                    ·
                      rfl

theorem cell23_3912017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_3912017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912017 prefixEnd_3912017 := by exact prefixLift 3912017
  have htrace : WordTrace (prefixWord ++ tailWord_3912017) baseStart_3912017 baseEnd_3912017 := by
    simpa [prefixWord, tailWord_3912017, baseEnd_3912017] using wordTrace_append hprefix tailTrace_3912017
  have hstable : (prefixWord ++ tailWord_3912017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912017).length < 2 ^ (prefixWord ++ tailWord_3912017).sum := by decide
  have hdescent : baseEnd_3912017 < baseStart_3912017 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912027 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 3]
def baseStart_3912027 : Nat := 118140960795 + 3912027 * 2 ^ 59
def prefixEnd_3912027 : Nat := 4983230072969 + 3 ^ 40 * 3912027 * 2
def baseEnd_3912027 : Nat := 2008750184366470910071421

theorem tailTrace_3912027 : CollatzResearch.WordTrace tailWord_3912027 prefixEnd_3912027 2008750184366470910071421 := by
  unfold tailWord_3912027
  simp only [CollatzResearch.WordTrace]
  refine ⟨142683346598401774864878335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95122231065601183243252223 142683346598401774864878335)
  ·
    refine ⟨214025019897602662297317503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142683346598401774864878335 214025019897602662297317503)
    ·
      refine ⟨321037529846403993445976255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214025019897602662297317503 321037529846403993445976255)
      ·
        refine ⟨481556294769605990168964383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321037529846403993445976255 481556294769605990168964383)
        ·
          refine ⟨722334442154408985253446575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 481556294769605990168964383 722334442154408985253446575)
          ·
            refine ⟨1083501663231613477880169863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 722334442154408985253446575 1083501663231613477880169863)
            ·
              refine ⟨1625252494847420216820254795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1083501663231613477880169863 1625252494847420216820254795)
              ·
                refine ⟨2437878742271130325230382193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1625252494847420216820254795 2437878742271130325230382193)
                ·
                  refine ⟨1828409056703347743922786645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2437878742271130325230382193 1828409056703347743922786645)
                  ·
                    refine ⟨5356667158310589093523789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1828409056703347743922786645 5356667158310589093523789)
                    ·
                      refine ⟨2008750184366470910071421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5356667158310589093523789 2008750184366470910071421)
                      ·
                        rfl

theorem cell23_3912027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 3].length) (baseStart_3912027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912027 prefixEnd_3912027 := by exact prefixLift 3912027
  have htrace : WordTrace (prefixWord ++ tailWord_3912027) baseStart_3912027 baseEnd_3912027 := by
    simpa [prefixWord, tailWord_3912027, baseEnd_3912027] using wordTrace_append hprefix tailTrace_3912027
  have hstable : (prefixWord ++ tailWord_3912027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912027).length < 2 ^ (prefixWord ++ tailWord_3912027).sum := by decide
  have hdescent : baseEnd_3912027 < baseStart_3912027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912041 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 4, 2, 2]
def baseStart_3912041 : Nat := 118140960795 + 3912041 * 2 ^ 59
def prefixEnd_3912041 : Nat := 4983230072969 + 3 ^ 40 * 3912041 * 2
def baseEnd_3912041 : Nat := 2008757373095633855296357

theorem tailTrace_3912041 : CollatzResearch.WordTrace tailWord_3912041 prefixEnd_3912041 2008757373095633855296357 := by
  unfold tailWord_3912041
  simp only [CollatzResearch.WordTrace]
  refine ⟨142683857220351055255887977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95122571480234036837258651 142683857220351055255887977)
  ·
    refine ⟨107012892915263291441915983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142683857220351055255887977 107012892915263291441915983)
    ·
      refine ⟨160519339372894937162873975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107012892915263291441915983 160519339372894937162873975)
      ·
        refine ⟨240779009059342405744310963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160519339372894937162873975 240779009059342405744310963)
        ·
          refine ⟨361168513589013608616466445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240779009059342405744310963 361168513589013608616466445)
          ·
            refine ⟨135438192595880103231174917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361168513589013608616466445 135438192595880103231174917)
            ·
              refine ⟨25394661111727519355845297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135438192595880103231174917 25394661111727519355845297)
              ·
                refine ⟨19045995833795639516883973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25394661111727519355845297 19045995833795639516883973)
                ·
                  refine ⟨3571124218836682409415745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19045995833795639516883973 3571124218836682409415745)
                  ·
                    refine ⟨2678343164127511807061809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3571124218836682409415745 2678343164127511807061809)
                    ·
                      refine ⟨2008757373095633855296357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678343164127511807061809 2008757373095633855296357)
                      ·
                        rfl

theorem cell23_3912041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 4, 2, 2].length) (baseStart_3912041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912041 prefixEnd_3912041 := by exact prefixLift 3912041
  have htrace : WordTrace (prefixWord ++ tailWord_3912041) baseStart_3912041 baseEnd_3912041 := by
    simpa [prefixWord, tailWord_3912041, baseEnd_3912041] using wordTrace_append hprefix tailTrace_3912041
  have hstable : (prefixWord ++ tailWord_3912041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912041).length < 2 ^ (prefixWord ++ tailWord_3912041).sum := by decide
  have hdescent : baseEnd_3912041 < baseStart_3912041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912075 : List Nat := [1, 1, 1, 1, 4, 5, 3, 1, 2, 2, 2]
def baseStart_3912075 : Nat := 118140960795 + 3912075 * 2 ^ 59
def prefixEnd_3912075 : Nat := 4983230072969 + 3 ^ 40 * 3912075 * 2
def baseEnd_3912075 : Nat := 2008774831437886722271201

theorem tailTrace_3912075 : CollatzResearch.WordTrace tailWord_3912075 prefixEnd_3912075 2008774831437886722271201 := by
  unfold tailWord_3912075
  simp only [CollatzResearch.WordTrace]
  refine ⟨142685097302227879062625679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95123398201485252708417119 142685097302227879062625679)
  ·
    refine ⟨214027645953341818593938519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142685097302227879062625679 214027645953341818593938519)
    ·
      refine ⟨321041468930012727890907779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214027645953341818593938519 321041468930012727890907779)
      ·
        refine ⟨481562203395019091836361669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321041468930012727890907779 481562203395019091836361669)
        ·
          refine ⟨90292913136566079719317813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 481562203395019091836361669 90292913136566079719317813)
          ·
            refine ⟨8464960606553069973686045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90292913136566079719317813 8464960606553069973686045)
            ·
              refine ⟨3174360227457401240132267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8464960606553069973686045 3174360227457401240132267)
              ·
                refine ⟨4761540341186101860198401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174360227457401240132267 4761540341186101860198401)
                ·
                  refine ⟨3571155255889576395148801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4761540341186101860198401 3571155255889576395148801)
                  ·
                    refine ⟨2678366441917182296361601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3571155255889576395148801 2678366441917182296361601)
                    ·
                      refine ⟨2008774831437886722271201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678366441917182296361601 2008774831437886722271201)
                      ·
                        rfl

theorem cell23_3912075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 3, 1, 2, 2, 2].length) (baseStart_3912075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912075 prefixEnd_3912075 := by exact prefixLift 3912075
  have htrace : WordTrace (prefixWord ++ tailWord_3912075) baseStart_3912075 baseEnd_3912075 := by
    simpa [prefixWord, tailWord_3912075, baseEnd_3912075] using wordTrace_append hprefix tailTrace_3912075
  have hstable : (prefixWord ++ tailWord_3912075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912075).length < 2 ^ (prefixWord ++ tailWord_3912075).sum := by decide
  have hdescent : baseEnd_3912075 < baseStart_3912075 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912148 : List Nat := [2, 4, 1, 2, 2, 2, 2, 1, 2, 1, 4]
def baseStart_3912148 : Nat := 118140960795 + 3912148 * 2 ^ 59
def prefixEnd_3912148 : Nat := 4983230072969 + 3 ^ 40 * 3912148 * 2
def baseEnd_3912148 : Nat := 2008812315525664936658365

theorem tailTrace_3912148 : CollatzResearch.WordTrace tailWord_3912148 prefixEnd_3912148 2008812315525664936658365 := by
  unfold tailWord_3912148
  simp only [CollatzResearch.WordTrace]
  refine ⟨71343879915481706265016549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95125173220642275020022065 71343879915481706265016549)
  ·
    refine ⟨13376977484152819924690603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71343879915481706265016549 13376977484152819924690603)
    ·
      refine ⟨20065466226229229887035905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13376977484152819924690603 20065466226229229887035905)
      ·
        refine ⟨15049099669671922415276929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20065466226229229887035905 15049099669671922415276929)
        ·
          refine ⟨11286824752253941811457697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15049099669671922415276929 11286824752253941811457697)
          ·
            refine ⟨8465118564190456358593273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11286824752253941811457697 8465118564190456358593273)
            ·
              refine ⟨6348838923142842268944955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8465118564190456358593273 6348838923142842268944955)
              ·
                refine ⟨9523258384714263403417433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6348838923142842268944955 9523258384714263403417433)
                ·
                  refine ⟨7142443788535697552563075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9523258384714263403417433 7142443788535697552563075)
                  ·
                    refine ⟨10713665682803546328844613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7142443788535697552563075 10713665682803546328844613)
                    ·
                      refine ⟨2008812315525664936658365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10713665682803546328844613 2008812315525664936658365)
                      ·
                        rfl

theorem cell23_3912148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_3912148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912148 prefixEnd_3912148 := by exact prefixLift 3912148
  have htrace : WordTrace (prefixWord ++ tailWord_3912148) baseStart_3912148 baseEnd_3912148 := by
    simpa [prefixWord, tailWord_3912148, baseEnd_3912148] using wordTrace_append hprefix tailTrace_3912148
  have hstable : (prefixWord ++ tailWord_3912148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912148).length < 2 ^ (prefixWord ++ tailWord_3912148).sum := by decide
  have hdescent : baseEnd_3912148 < baseStart_3912148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912184 : List Nat := [2, 1, 2, 1, 1, 4, 1, 1, 5, 5]
def baseStart_3912184 : Nat := 118140960795 + 3912184 * 2 ^ 59
def prefixEnd_3912184 : Nat := 4983230072969 + 3 ^ 40 * 3912184 * 2
def baseEnd_3912184 : Nat := 669610266943075598602733

theorem tailTrace_3912184 : CollatzResearch.WordTrace tailWord_3912184 prefixEnd_3912184 669610266943075598602733 := by
  unfold tailWord_3912184
  simp only [CollatzResearch.WordTrace]
  refine ⟨71344536429416495339171803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95126048572555327118895737 71344536429416495339171803)
  ·
    refine ⟨107016804644124743008757705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71344536429416495339171803 107016804644124743008757705)
    ·
      refine ⟨80262603483093557256568279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107016804644124743008757705 80262603483093557256568279)
      ·
        refine ⟨120393905224640335884852419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80262603483093557256568279 120393905224640335884852419)
        ·
          refine ⟨180590857836960503827278629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120393905224640335884852419 180590857836960503827278629)
          ·
            refine ⟨33860785844430094467614743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180590857836960503827278629 33860785844430094467614743)
            ·
              refine ⟨50791178766645141701422115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33860785844430094467614743 50791178766645141701422115)
              ·
                refine ⟨76186768149967712552133173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50791178766645141701422115 76186768149967712552133173)
                ·
                  refine ⟨7142509514059473051762485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76186768149967712552133173 7142509514059473051762485)
                  ·
                    refine ⟨669610266943075598602733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7142509514059473051762485 669610266943075598602733)
                    ·
                      rfl

theorem cell23_3912184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_3912184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912184 prefixEnd_3912184 := by exact prefixLift 3912184
  have htrace : WordTrace (prefixWord ++ tailWord_3912184) baseStart_3912184 baseEnd_3912184 := by
    simpa [prefixWord, tailWord_3912184, baseEnd_3912184] using wordTrace_append hprefix tailTrace_3912184
  have hstable : (prefixWord ++ tailWord_3912184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912184).length < 2 ^ (prefixWord ++ tailWord_3912184).sum := by decide
  have hdescent : baseEnd_3912184 < baseStart_3912184 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912191 : List Nat := [1, 1, 2, 2, 1, 2, 4, 2, 1, 5, 2]
def baseStart_3912191 : Nat := 118140960795 + 3912191 * 2 ^ 59
def prefixEnd_3912191 : Nat := 4983230072969 + 3 ^ 40 * 3912191 * 2
def baseEnd_3912191 : Nat := 2008834395193808268420667

theorem tailTrace_3912191 : CollatzResearch.WordTrace tailWord_3912191 prefixEnd_3912191 2008834395193808268420667 := by
  unfold tailWord_3912191
  simp only [CollatzResearch.WordTrace]
  refine ⟨142689328169807630873848427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95126218779871753915898951 142689328169807630873848427)
  ·
    refine ⟨214033992254711446310772641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142689328169807630873848427 214033992254711446310772641)
    ·
      refine ⟨160525494191033584733079481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214033992254711446310772641 160525494191033584733079481)
      ·
        refine ⟨120394120643275188549809611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160525494191033584733079481 120394120643275188549809611)
        ·
          refine ⟨180591180964912782824714417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120394120643275188549809611 180591180964912782824714417)
          ·
            refine ⟨135443385723684587118535813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180591180964912782824714417 135443385723684587118535813)
            ·
              refine ⟨25395634823190860084725465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135443385723684587118535813 25395634823190860084725465)
              ·
                refine ⟨19046726117393145063544099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25395634823190860084725465 19046726117393145063544099)
                ·
                  refine ⟨28570089176089717595316149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19046726117393145063544099 28570089176089717595316149)
                  ·
                    refine ⟨2678445860258411024560889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 28570089176089717595316149 2678445860258411024560889)
                    ·
                      refine ⟨2008834395193808268420667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678445860258411024560889 2008834395193808268420667)
                      ·
                        rfl

theorem cell23_3912191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_3912191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912191 prefixEnd_3912191 := by exact prefixLift 3912191
  have htrace : WordTrace (prefixWord ++ tailWord_3912191) baseStart_3912191 baseEnd_3912191 := by
    simpa [prefixWord, tailWord_3912191, baseEnd_3912191] using wordTrace_append hprefix tailTrace_3912191
  have hstable : (prefixWord ++ tailWord_3912191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912191).length < 2 ^ (prefixWord ++ tailWord_3912191).sum := by decide
  have hdescent : baseEnd_3912191 < baseStart_3912191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912218 : List Nat := [3, 1, 1, 3, 1, 1, 6, 1, 1, 5]
def baseStart_3912218 : Nat := 118140960795 + 3912218 * 2 ^ 59
def prefixEnd_3912218 : Nat := 4983230072969 + 3 ^ 40 * 3912218 * 2
def baseEnd_3912218 : Nat := 669616086390493220927681

theorem tailTrace_3912218 : CollatzResearch.WordTrace tailWord_3912218 prefixEnd_3912218 669616086390493220927681 := by
  unfold tailWord_3912218
  simp only [CollatzResearch.WordTrace]
  refine ⟨35672578235177453621270327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95126875293806542990054205 35672578235177453621270327)
  ·
    refine ⟨53508867352766180431905491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35672578235177453621270327 53508867352766180431905491)
    ·
      refine ⟨80263301029149270647858237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53508867352766180431905491 80263301029149270647858237)
      ·
        refine ⟨30098737885930976492946839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80263301029149270647858237 30098737885930976492946839)
        ·
          refine ⟨45148106828896464739420259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30098737885930976492946839 45148106828896464739420259)
          ·
            refine ⟨67722160243344697109130389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45148106828896464739420259 67722160243344697109130389)
            ·
              refine ⟨3174476261406782676990487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 67722160243344697109130389 3174476261406782676990487)
              ·
                refine ⟨4761714392110174015485731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3174476261406782676990487 4761714392110174015485731)
                ·
                  refine ⟨7142571588165261023228597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761714392110174015485731 7142571588165261023228597)
                  ·
                    refine ⟨669616086390493220927681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7142571588165261023228597 669616086390493220927681)
                    ·
                      rfl

theorem cell23_3912218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 1, 1, 5].length) (baseStart_3912218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912218 prefixEnd_3912218 := by exact prefixLift 3912218
  have htrace : WordTrace (prefixWord ++ tailWord_3912218) baseStart_3912218 baseEnd_3912218 := by
    simpa [prefixWord, tailWord_3912218, baseEnd_3912218] using wordTrace_append hprefix tailTrace_3912218
  have hstable : (prefixWord ++ tailWord_3912218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912218).length < 2 ^ (prefixWord ++ tailWord_3912218).sum := by decide
  have hdescent : baseEnd_3912218 < baseStart_3912218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912232 : List Nat := [2, 1, 5, 2, 1, 1, 2, 4, 1, 1, 3]
def baseStart_3912232 : Nat := 118140960795 + 3912232 * 2 ^ 59
def prefixEnd_3912232 : Nat := 4983230072969 + 3 ^ 40 * 3912232 * 2
def baseEnd_3912232 : Nat := 2008855447900642608007979

theorem tailTrace_3912232 : CollatzResearch.WordTrace tailWord_3912232 prefixEnd_3912232 2008855447900642608007979 := by
  unfold tailWord_3912232
  simp only [CollatzResearch.WordTrace]
  refine ⟨71345411781329547438045475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95127215708439396584060633 71345411781329547438045475)
  ·
    refine ⟨107018117671994321157068213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71345411781329547438045475 107018117671994321157068213)
    ·
      refine ⟨10032948531749467608475145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107018117671994321157068213 10032948531749467608475145)
      ·
        refine ⟨7524711398812100706356359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10032948531749467608475145 7524711398812100706356359)
        ·
          refine ⟨11287067098218151059534539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7524711398812100706356359 11287067098218151059534539)
          ·
            refine ⟨16930600647327226589301809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11287067098218151059534539 16930600647327226589301809)
            ·
              refine ⟨12697950485495419941976357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16930600647327226589301809 12697950485495419941976357)
              ·
                refine ⟨2380865716030391239120567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12697950485495419941976357 2380865716030391239120567)
                ·
                  refine ⟨3571298574045586858680851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380865716030391239120567 3571298574045586858680851)
                  ·
                    refine ⟨5356947861068380288021277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3571298574045586858680851 5356947861068380288021277)
                    ·
                      refine ⟨2008855447900642608007979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5356947861068380288021277 2008855447900642608007979)
                      ·
                        rfl

theorem cell23_3912232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_3912232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912232 prefixEnd_3912232 := by exact prefixLift 3912232
  have htrace : WordTrace (prefixWord ++ tailWord_3912232) baseStart_3912232 baseEnd_3912232 := by
    simpa [prefixWord, tailWord_3912232, baseEnd_3912232] using wordTrace_append hprefix tailTrace_3912232
  have hstable : (prefixWord ++ tailWord_3912232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912232).length < 2 ^ (prefixWord ++ tailWord_3912232).sum := by decide
  have hdescent : baseEnd_3912232 < baseStart_3912232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912241 : List Nat := [1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_3912241 : Nat := 118140960795 + 3912241 * 2 ^ 59
def prefixEnd_3912241 : Nat := 4983230072969 + 3 ^ 40 * 3912241 * 2
def baseEnd_3912241 : Nat := 2008860069226533072795437

theorem tailTrace_3912241 : CollatzResearch.WordTrace tailWord_3912241 prefixEnd_3912241 2008860069226533072795437 := by
  unfold tailWord_3912241
  simp only [CollatzResearch.WordTrace]
  refine ⟨142691151819626489413168577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95127434546417659608779051 142691151819626489413168577)
  ·
    refine ⟨107018363864719867059876433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142691151819626489413168577 107018363864719867059876433)
    ·
      refine ⟨80263772898539900294907325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107018363864719867059876433 80263772898539900294907325)
      ·
        refine ⟨30098914836952462610590247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80263772898539900294907325 30098914836952462610590247)
        ·
          refine ⟨45148372255428693915885371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30098914836952462610590247 45148372255428693915885371)
          ·
            refine ⟨67722558383143040873828057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45148372255428693915885371 67722558383143040873828057)
            ·
              refine ⟨50791918787357280655371043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67722558383143040873828057 50791918787357280655371043)
              ·
                refine ⟨76187878181035920983056565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50791918787357280655371043 76187878181035920983056565)
                ·
                  refine ⟨7142613579472117592161553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76187878181035920983056565 7142613579472117592161553)
                  ·
                    refine ⟨5356960184604088194121165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7142613579472117592161553 5356960184604088194121165)
                    ·
                      refine ⟨2008860069226533072795437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5356960184604088194121165 2008860069226533072795437)
                      ·
                        rfl

theorem cell23_3912241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_3912241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912241 prefixEnd_3912241 := by exact prefixLift 3912241
  have htrace : WordTrace (prefixWord ++ tailWord_3912241) baseStart_3912241 baseEnd_3912241 := by
    simpa [prefixWord, tailWord_3912241, baseEnd_3912241] using wordTrace_append hprefix tailTrace_3912241
  have hstable : (prefixWord ++ tailWord_3912241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912241).length < 2 ^ (prefixWord ++ tailWord_3912241).sum := by decide
  have hdescent : baseEnd_3912241 < baseStart_3912241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912261 : List Nat := [1, 3, 1, 1, 1, 5, 4, 7]
def baseStart_3912261 : Nat := 118140960795 + 3912261 * 2 ^ 59
def prefixEnd_3912261 : Nat := 4983230072969 + 3 ^ 40 * 3912261 * 2
def baseEnd_3912261 : Nat := 74402605142208259057235

theorem tailTrace_3912261 : CollatzResearch.WordTrace tailWord_3912261 prefixEnd_3912261 74402605142208259057235 := by
  unfold tailWord_3912261
  simp only [CollatzResearch.WordTrace]
  refine ⟨142691881279554032828896637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95127920853036021885931091 142691881279554032828896637)
  ·
    refine ⟨53509455479832762310836239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142691881279554032828896637 53509455479832762310836239)
    ·
      refine ⟨80264183219749143466254359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53509455479832762310836239 80264183219749143466254359)
      ·
        refine ⟨120396274829623715199381539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80264183219749143466254359 120396274829623715199381539)
        ·
          refine ⟨180594412244435572799072309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120396274829623715199381539 180594412244435572799072309)
          ·
            refine ⟨16930726147915834949913029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180594412244435572799072309 16930726147915834949913029)
            ·
              refine ⟨3174511152734219053108693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16930726147915834949913029 3174511152734219053108693)
              ·
                refine ⟨74402605142208259057235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3174511152734219053108693 74402605142208259057235)
                ·
                  rfl

theorem cell23_3912261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 7].length) (baseStart_3912261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912261 prefixEnd_3912261 := by exact prefixLift 3912261
  have htrace : WordTrace (prefixWord ++ tailWord_3912261) baseStart_3912261 baseEnd_3912261 := by
    simpa [prefixWord, tailWord_3912261, baseEnd_3912261] using wordTrace_append hprefix tailTrace_3912261
  have hstable : (prefixWord ++ tailWord_3912261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912261).length < 2 ^ (prefixWord ++ tailWord_3912261).sum := by decide
  have hdescent : baseEnd_3912261 < baseStart_3912261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912264 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_3912264 : Nat := 118140960795 + 3912264 * 2 ^ 59
def prefixEnd_3912264 : Nat := 4983230072969 + 3 ^ 40 * 3912264 * 2
def baseEnd_3912264 : Nat := 2008871879281586482807831

theorem tailTrace_3912264 : CollatzResearch.WordTrace tailWord_3912264 prefixEnd_3912264 2008871879281586482807831 := by
  unfold tailWord_3912264
  simp only [CollatzResearch.WordTrace]
  refine ⟨71345995349271582170627923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95127993799028776227503897 71345995349271582170627923)
  ·
    refine ⟨107018993023907373255941885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71345995349271582170627923 107018993023907373255941885)
    ·
      refine ⟨40132122383965264970978207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107018993023907373255941885 40132122383965264970978207)
      ·
        refine ⟨60198183575947897456467311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40132122383965264970978207 60198183575947897456467311)
        ·
          refine ⟨90297275363921846184700967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60198183575947897456467311 90297275363921846184700967)
          ·
            refine ⟨135445913045882769277051451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90297275363921846184700967 135445913045882769277051451)
            ·
              refine ⟨203168869568824153915577177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135445913045882769277051451 203168869568824153915577177)
              ·
                refine ⟨152376652176618115436682883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203168869568824153915577177 152376652176618115436682883)
                ·
                  refine ⟨228564978264927173155024325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152376652176618115436682883 228564978264927173155024325)
                  ·
                    refine ⟨42855933424673844966567061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228564978264927173155024325 42855933424673844966567061)
                    ·
                      refine ⟨2008871879281586482807831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42855933424673844966567061 2008871879281586482807831)
                      ·
                        rfl

theorem cell23_3912264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_3912264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912264 prefixEnd_3912264 := by exact prefixLift 3912264
  have htrace : WordTrace (prefixWord ++ tailWord_3912264) baseStart_3912264 baseEnd_3912264 := by
    simpa [prefixWord, tailWord_3912264, baseEnd_3912264] using wordTrace_append hprefix tailTrace_3912264
  have hstable : (prefixWord ++ tailWord_3912264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912264).length < 2 ^ (prefixWord ++ tailWord_3912264).sum := by decide
  have hdescent : baseEnd_3912264 < baseStart_3912264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912271 : List Nat := [1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 3]
def baseStart_3912271 : Nat := 118140960795 + 3912271 * 2 ^ 59
def prefixEnd_3912271 : Nat := 4983230072969 + 3 ^ 40 * 3912271 * 2
def baseEnd_3912271 : Nat := 2008875473646167955420299

theorem tailTrace_3912271 : CollatzResearch.WordTrace tailWord_3912271 prefixEnd_3912271 2008875473646167955420299 := by
  unfold tailWord_3912271
  simp only [CollatzResearch.WordTrace]
  refine ⟨142692246009517804536760667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95128164006345203024507111 142692246009517804536760667)
  ·
    refine ⟨214038369014276706805141001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142692246009517804536760667 214038369014276706805141001)
    ·
      refine ⟨160528776760707530103855751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214038369014276706805141001 160528776760707530103855751)
      ·
        refine ⟨240793165141061295155783627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160528776760707530103855751 240793165141061295155783627)
        ·
          refine ⟨361189747711591942733675441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240793165141061295155783627 361189747711591942733675441)
          ·
            refine ⟨270892310783693957050256581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361189747711591942733675441 270892310783693957050256581)
            ·
              refine ⟨50792308271942616946923109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 270892310783693957050256581 50792308271942616946923109)
              ·
                refine ⟨9523557800989240677548083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50792308271942616946923109 9523557800989240677548083)
                ·
                  refine ⟨14285336701483861016322125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9523557800989240677548083 14285336701483861016322125)
                  ·
                    refine ⟨5357001263056447881120797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14285336701483861016322125 5357001263056447881120797)
                    ·
                      refine ⟨2008875473646167955420299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5357001263056447881120797 2008875473646167955420299)
                      ·
                        rfl

theorem cell23_3912271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_3912271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912271 prefixEnd_3912271 := by exact prefixLift 3912271
  have htrace : WordTrace (prefixWord ++ tailWord_3912271) baseStart_3912271 baseEnd_3912271 := by
    simpa [prefixWord, tailWord_3912271, baseEnd_3912271] using wordTrace_append hprefix tailTrace_3912271
  have hstable : (prefixWord ++ tailWord_3912271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912271).length < 2 ^ (prefixWord ++ tailWord_3912271).sum := by decide
  have hdescent : baseEnd_3912271 < baseStart_3912271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912288 : List Nat := [2, 1, 1, 3, 2, 1, 4, 1, 4, 1, 3]
def baseStart_3912288 : Nat := 118140960795 + 3912288 * 2 ^ 59
def prefixEnd_3912288 : Nat := 4983230072969 + 3 ^ 40 * 3912288 * 2
def baseEnd_3912288 : Nat := 2008884202817294388907721

theorem tailTrace_3912288 : CollatzResearch.WordTrace tailWord_3912288 prefixEnd_3912288 2008884202817294388907721 := by
  unfold tailWord_3912288
  simp only [CollatzResearch.WordTrace]
  refine ⟨71346433025228108220064759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95128577366970810960086345 71346433025228108220064759)
  ·
    refine ⟨107019649537842162330097139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71346433025228108220064759 107019649537842162330097139)
    ·
      refine ⟨160529474306763243495145709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107019649537842162330097139 160529474306763243495145709)
      ·
        refine ⟨60198552865036216310679641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160529474306763243495145709 60198552865036216310679641)
        ·
          refine ⟨45148914648777162233009731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60198552865036216310679641 45148914648777162233009731)
          ·
            refine ⟨67723371973165743349514597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45148914648777162233009731 67723371973165743349514597)
            ·
              refine ⟨12698132244968576878033987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67723371973165743349514597 12698132244968576878033987)
              ·
                refine ⟨19047198367452865317050981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12698132244968576878033987 19047198367452865317050981)
                ·
                  refine ⟨3571349693897412246947059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19047198367452865317050981 3571349693897412246947059)
                  ·
                    refine ⟨5357024540846118370420589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3571349693897412246947059 5357024540846118370420589)
                    ·
                      refine ⟨2008884202817294388907721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5357024540846118370420589 2008884202817294388907721)
                      ·
                        rfl

theorem cell23_3912288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_3912288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912288 prefixEnd_3912288 := by exact prefixLift 3912288
  have htrace : WordTrace (prefixWord ++ tailWord_3912288) baseStart_3912288 baseEnd_3912288 := by
    simpa [prefixWord, tailWord_3912288, baseEnd_3912288] using wordTrace_append hprefix tailTrace_3912288
  have hstable : (prefixWord ++ tailWord_3912288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912288).length < 2 ^ (prefixWord ++ tailWord_3912288).sum := by decide
  have hdescent : baseEnd_3912288 < baseStart_3912288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912289 : List Nat := [1, 2, 3, 1, 1, 5, 3, 2, 1, 2, 2]
def baseStart_3912289 : Nat := 118140960795 + 3912289 * 2 ^ 59
def prefixEnd_3912289 : Nat := 4983230072969 + 3 ^ 40 * 3912289 * 2
def baseEnd_3912289 : Nat := 2008884716297948884995217

theorem tailTrace_3912289 : CollatzResearch.WordTrace tailWord_3912289 prefixEnd_3912289 2008884716297948884995217 := by
  unfold tailWord_3912289
  simp only [CollatzResearch.WordTrace]
  refine ⟨142692902523452593610915921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95128601682301729073943947 142692902523452593610915921)
  ·
    refine ⟨107019676892589445208186941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142692902523452593610915921 107019676892589445208186941)
    ·
      refine ⟨40132378834721041953070103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107019676892589445208186941 40132378834721041953070103)
      ·
        refine ⟨60198568252081562929605155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40132378834721041953070103 60198568252081562929605155)
        ·
          refine ⟨90297852378122344394407733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60198568252081562929605155 90297852378122344394407733)
          ·
            refine ⟨8465423660448969786975725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90297852378122344394407733 8465423660448969786975725)
            ·
              refine ⟨3174533872668363670115897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8465423660448969786975725 3174533872668363670115897)
              ·
                refine ⟨2380900404501272752586923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174533872668363670115897 2380900404501272752586923)
                ·
                  refine ⟨3571350606751909128880385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2380900404501272752586923 3571350606751909128880385)
                  ·
                    refine ⟨2678512955063931846660289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3571350606751909128880385 2678512955063931846660289)
                    ·
                      refine ⟨2008884716297948884995217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678512955063931846660289 2008884716297948884995217)
                      ·
                        rfl

theorem cell23_3912289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 2, 1, 2, 2].length) (baseStart_3912289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912289 prefixEnd_3912289 := by exact prefixLift 3912289
  have htrace : WordTrace (prefixWord ++ tailWord_3912289) baseStart_3912289 baseEnd_3912289 := by
    simpa [prefixWord, tailWord_3912289, baseEnd_3912289] using wordTrace_append hprefix tailTrace_3912289
  have hstable : (prefixWord ++ tailWord_3912289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912289).length < 2 ^ (prefixWord ++ tailWord_3912289).sum := by decide
  have hdescent : baseEnd_3912289 < baseStart_3912289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912309 : List Nat := [1, 3, 4, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_3912309 : Nat := 118140960795 + 3912309 * 2 ^ 59
def prefixEnd_3912309 : Nat := 4983230072969 + 3 ^ 40 * 3912309 * 2
def baseEnd_3912309 : Nat := 2008894985911038806745125

theorem tailTrace_3912309 : CollatzResearch.WordTrace tailWord_3912309 prefixEnd_3912309 2008894985911038806745125 := by
  unfold tailWord_3912309
  simp only [CollatzResearch.WordTrace]
  refine ⟨142693631983380137026643981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95129087988920091351095987 142693631983380137026643981)
  ·
    refine ⟨53510111993767551384991493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142693631983380137026643981 53510111993767551384991493)
    ·
      refine ⟨10033145998831415884685905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53510111993767551384991493 10033145998831415884685905)
      ·
        refine ⟨7524859499123561913514429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10033145998831415884685905 7524859499123561913514429)
        ·
          refine ⟨2821822312171335717567911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7524859499123561913514429 2821822312171335717567911)
          ·
            refine ⟨4232733468257003576351867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2821822312171335717567911 4232733468257003576351867)
            ·
              refine ⟨6349100202385505364527801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4232733468257003576351867 6349100202385505364527801)
              ·
                refine ⟨4761825151789129023395851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6349100202385505364527801 4761825151789129023395851)
                ·
                  refine ⟨7142737727683693535093777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4761825151789129023395851 7142737727683693535093777)
                  ·
                    refine ⟨5357053295762770151320333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7142737727683693535093777 5357053295762770151320333)
                    ·
                      refine ⟨2008894985911038806745125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5357053295762770151320333 2008894985911038806745125)
                      ·
                        rfl

theorem cell23_3912309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_3912309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912309 prefixEnd_3912309 := by exact prefixLift 3912309
  have htrace : WordTrace (prefixWord ++ tailWord_3912309) baseStart_3912309 baseEnd_3912309 := by
    simpa [prefixWord, tailWord_3912309, baseEnd_3912309] using wordTrace_append hprefix tailTrace_3912309
  have hstable : (prefixWord ++ tailWord_3912309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912309).length < 2 ^ (prefixWord ++ tailWord_3912309).sum := by decide
  have hdescent : baseEnd_3912309 < baseStart_3912309 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912348 : List Nat := [2, 2, 3, 2, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3912348 : Nat := 118140960795 + 3912348 * 2 ^ 59
def prefixEnd_3912348 : Nat := 4983230072969 + 3 ^ 40 * 3912348 * 2
def baseEnd_3912348 : Nat := 2008915011656564154157445

theorem tailTrace_3912348 : CollatzResearch.WordTrace tailWord_3912348 prefixEnd_3912348 2008915011656564154157445 := by
  unfold tailWord_3912348
  simp only [CollatzResearch.WordTrace]
  refine ⟨71347527215119423343656849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95130036286825897791542465 71347527215119423343656849)
  ·
    refine ⟨53510645411339567507742637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71347527215119423343656849 53510645411339567507742637)
    ·
      refine ⟨20066492029252337815403489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53510645411339567507742637 20066492029252337815403489)
      ·
        refine ⟨15049869021939253361552617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20066492029252337815403489 15049869021939253361552617)
        ·
          refine ⟨11287401766454440021164463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15049869021939253361552617 11287401766454440021164463)
          ·
            refine ⟨16931102649681660031746695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11287401766454440021164463 16931102649681660031746695)
            ·
              refine ⟨25396653974522490047620043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16931102649681660031746695 25396653974522490047620043)
              ·
                refine ⟨38094980961783735071430065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25396653974522490047620043 38094980961783735071430065)
                ·
                  refine ⟨28571235721337801303572549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38094980961783735071430065 28571235721337801303572549)
                  ·
                    refine ⟨5357106697750837744419853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28571235721337801303572549 5357106697750837744419853)
                    ·
                      refine ⟨2008915011656564154157445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5357106697750837744419853 2008915011656564154157445)
                      ·
                        rfl

theorem cell23_3912348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3912348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912348 prefixEnd_3912348 := by exact prefixLift 3912348
  have htrace : WordTrace (prefixWord ++ tailWord_3912348) baseStart_3912348 baseEnd_3912348 := by
    simpa [prefixWord, tailWord_3912348, baseEnd_3912348] using wordTrace_append hprefix tailTrace_3912348
  have hstable : (prefixWord ++ tailWord_3912348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912348).length < 2 ^ (prefixWord ++ tailWord_3912348).sum := by decide
  have hdescent : baseEnd_3912348 < baseStart_3912348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912361 : List Nat := [1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 3]
def baseStart_3912361 : Nat := 118140960795 + 3912361 * 2 ^ 59
def prefixEnd_3912361 : Nat := 4983230072969 + 3 ^ 40 * 3912361 * 2
def baseEnd_3912361 : Nat := 2008921686905072603294885

theorem tailTrace_3912361 : CollatzResearch.WordTrace tailWord_3912361 prefixEnd_3912361 2008921686905072603294885 := by
  unfold tailWord_3912361
  simp only [CollatzResearch.WordTrace]
  refine ⟨142695528579191749907536937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95130352386127833271691291 142695528579191749907536937)
  ·
    refine ⟨107021646434393812430652703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142695528579191749907536937 107021646434393812430652703)
    ·
      refine ⟨160532469651590718645979055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107021646434393812430652703 160532469651590718645979055)
      ·
        refine ⟨240798704477386077968968583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160532469651590718645979055 240798704477386077968968583)
        ·
          refine ⟨361198056716079116953452875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240798704477386077968968583 361198056716079116953452875)
          ·
            refine ⟨541797085074118675430179313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361198056716079116953452875 541797085074118675430179313)
            ·
              refine ⟨406347813805589006572634485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 541797085074118675430179313 406347813805589006572634485)
              ·
                refine ⟨38095107544273969366184483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 406347813805589006572634485 38095107544273969366184483)
                ·
                  refine ⟨57142661316410954049276725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38095107544273969366184483 57142661316410954049276725)
                  ·
                    refine ⟨5357124498413526942119693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57142661316410954049276725 5357124498413526942119693)
                    ·
                      refine ⟨2008921686905072603294885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5357124498413526942119693 2008921686905072603294885)
                      ·
                        rfl

theorem cell23_3912361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_3912361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912361 prefixEnd_3912361 := by exact prefixLift 3912361
  have htrace : WordTrace (prefixWord ++ tailWord_3912361) baseStart_3912361 baseEnd_3912361 := by
    simpa [prefixWord, tailWord_3912361, baseEnd_3912361] using wordTrace_append hprefix tailTrace_3912361
  have hstable : (prefixWord ++ tailWord_3912361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912361).length < 2 ^ (prefixWord ++ tailWord_3912361).sum := by decide
  have hdescent : baseEnd_3912361 < baseStart_3912361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912391 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_3912391 : Nat := 118140960795 + 3912391 * 2 ^ 59
def prefixEnd_3912391 : Nat := 4983230072969 + 3 ^ 40 * 3912391 * 2
def baseEnd_3912391 : Nat := 2008937091324707485919747

theorem tailTrace_3912391 : CollatzResearch.WordTrace tailWord_3912391 prefixEnd_3912391 2008937091324707485919747 := by
  unfold tailWord_3912391
  simp only [CollatzResearch.WordTrace]
  refine ⟨142696622769083065031129027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95131081846055376687419351 142696622769083065031129027)
  ·
    refine ⟨214044934153624597546693541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142696622769083065031129027 214044934153624597546693541)
    ·
      refine ⟨40133425153804612040005039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214044934153624597546693541 40133425153804612040005039)
      ·
        refine ⟨60200137730706918060007559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40133425153804612040005039 60200137730706918060007559)
        ·
          refine ⟨90300206596060377090011339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60200137730706918060007559 90300206596060377090011339)
          ·
            refine ⟨135450309894090565635017009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90300206596060377090011339 135450309894090565635017009)
            ·
              refine ⟨101587732420567924226262757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135450309894090565635017009 101587732420567924226262757)
              ·
                refine ⟨19047699828856485792424267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101587732420567924226262757 19047699828856485792424267)
                ·
                  refine ⟨28571549743284728688636401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19047699828856485792424267 28571549743284728688636401)
                  ·
                    refine ⟨21428662307463546516477301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28571549743284728688636401 21428662307463546516477301)
                    ·
                      refine ⟨2008937091324707485919747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21428662307463546516477301 2008937091324707485919747)
                      ·
                        rfl

theorem cell23_3912391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_3912391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912391 prefixEnd_3912391 := by exact prefixLift 3912391
  have htrace : WordTrace (prefixWord ++ tailWord_3912391) baseStart_3912391 baseEnd_3912391 := by
    simpa [prefixWord, tailWord_3912391, baseEnd_3912391] using wordTrace_append hprefix tailTrace_3912391
  have hstable : (prefixWord ++ tailWord_3912391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912391).length < 2 ^ (prefixWord ++ tailWord_3912391).sum := by decide
  have hdescent : baseEnd_3912391 < baseStart_3912391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912436 : List Nat := [2, 6, 1, 1, 2, 2, 1, 3, 5]
def baseStart_3912436 : Nat := 118140960795 + 3912436 * 2 ^ 59
def prefixEnd_3912436 : Nat := 4983230072969 + 3 ^ 40 * 3912436 * 2
def baseEnd_3912436 : Nat := 223217799772684423317449

theorem tailTrace_3912436 : CollatzResearch.WordTrace tailWord_3912436 prefixEnd_3912436 223217799772684423317449 := by
  unfold tailWord_3912436
  simp only [CollatzResearch.WordTrace]
  refine ⟨71349132026960018858258581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95132176035946691811011441 71349132026960018858258581)
  ·
    refine ⟨3344490563763750883980871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71349132026960018858258581 3344490563763750883980871)
    ·
      refine ⟨5016735845645626325971307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3344490563763750883980871 5016735845645626325971307)
      ·
        refine ⟨7525103768468439488956961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5016735845645626325971307 7525103768468439488956961)
        ·
          refine ⟨5643827826351329616717721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7525103768468439488956961 5643827826351329616717721)
          ·
            refine ⟨4232870869763497212538291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5643827826351329616717721 4232870869763497212538291)
            ·
              refine ⟨6349306304645245818807437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4232870869763497212538291 6349306304645245818807437)
              ·
                refine ⟨2380989864241967182052789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6349306304645245818807437 2380989864241967182052789)
                ·
                  refine ⟨223217799772684423317449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2380989864241967182052789 223217799772684423317449)
                  ·
                    rfl

theorem cell23_3912436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_3912436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912436 prefixEnd_3912436 := by exact prefixLift 3912436
  have htrace : WordTrace (prefixWord ++ tailWord_3912436) baseStart_3912436 baseEnd_3912436 := by
    simpa [prefixWord, tailWord_3912436, baseEnd_3912436] using wordTrace_append hprefix tailTrace_3912436
  have hstable : (prefixWord ++ tailWord_3912436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912436).length < 2 ^ (prefixWord ++ tailWord_3912436).sum := by decide
  have hdescent : baseEnd_3912436 < baseStart_3912436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912455 : List Nat := [1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3912455 : Nat := 118140960795 + 3912455 * 2 ^ 59
def prefixEnd_3912455 : Nat := 4983230072969 + 3 ^ 40 * 3912455 * 2
def baseEnd_3912455 : Nat := 2008969954086595235519453

theorem tailTrace_3912455 : CollatzResearch.WordTrace tailWord_3912455 prefixEnd_3912455 2008969954086595235519453 := by
  unfold tailWord_3912455
  simp only [CollatzResearch.WordTrace]
  refine ⟨142698957040851203961458819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95132638027234135974305879 142698957040851203961458819)
  ·
    refine ⟨214048435561276805942188229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142698957040851203961458819 214048435561276805942188229)
    ·
      refine ⟨40134081667739401114160293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214048435561276805942188229 40134081667739401114160293)
      ·
        refine ⟨7525140312701137708905055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40134081667739401114160293 7525140312701137708905055)
        ·
          refine ⟨11287710469051706563357583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525140312701137708905055 11287710469051706563357583)
          ·
            refine ⟨16931565703577559845036375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11287710469051706563357583 16931565703577559845036375)
            ·
              refine ⟨25397348555366339767554563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16931565703577559845036375 25397348555366339767554563)
              ·
                refine ⟨38096022833049509651331845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25397348555366339767554563 38096022833049509651331845)
                ·
                  refine ⟨7143004281196783059624721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38096022833049509651331845 7143004281196783059624721)
                  ·
                    refine ⟨5357253210897587294718541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7143004281196783059624721 5357253210897587294718541)
                    ·
                      refine ⟨2008969954086595235519453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5357253210897587294718541 2008969954086595235519453)
                      ·
                        rfl

theorem cell23_3912455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3912455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912455 prefixEnd_3912455 := by exact prefixLift 3912455
  have htrace : WordTrace (prefixWord ++ tailWord_3912455) baseStart_3912455 baseEnd_3912455 := by
    simpa [prefixWord, tailWord_3912455, baseEnd_3912455] using wordTrace_append hprefix tailTrace_3912455
  have hstable : (prefixWord ++ tailWord_3912455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912455).length < 2 ^ (prefixWord ++ tailWord_3912455).sum := by decide
  have hdescent : baseEnd_3912455 < baseStart_3912455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912458 : List Nat := [3, 1, 2, 2, 1, 2, 2, 4, 6]
def baseStart_3912458 : Nat := 118140960795 + 3912458 * 2 ^ 59
def prefixEnd_3912458 : Nat := 4983230072969 + 3 ^ 40 * 3912458 * 2
def baseEnd_3912458 : Nat := 223219054947617635975771

theorem tailTrace_3912458 : CollatzResearch.WordTrace tailWord_3912458 prefixEnd_3912458 223219054947617635975771 := by
  unfold tailWord_3912458
  simp only [CollatzResearch.WordTrace]
  refine ⟨35674766614960083868454507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95132710973226890315878685 35674766614960083868454507)
  ·
    refine ⟨53512149922440125802681761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35674766614960083868454507 53512149922440125802681761)
    ·
      refine ⟨40134112441830094352011321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53512149922440125802681761 40134112441830094352011321)
      ·
        refine ⟨30100584331372570764008491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40134112441830094352011321 30100584331372570764008491)
        ·
          refine ⟨45150876497058856146012737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30100584331372570764008491 45150876497058856146012737)
          ·
            refine ⟨33863157372794142109509553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45150876497058856146012737 33863157372794142109509553)
            ·
              refine ⟨25397368029595606582132165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33863157372794142109509553 25397368029595606582132165)
              ·
                refine ⟨4762006505549176234149781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25397368029595606582132165 4762006505549176234149781)
                ·
                  refine ⟨223219054947617635975771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4762006505549176234149781 223219054947617635975771)
                  ·
                    rfl

theorem cell23_3912458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 6].length) (baseStart_3912458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912458 prefixEnd_3912458 := by exact prefixLift 3912458
  have htrace : WordTrace (prefixWord ++ tailWord_3912458) baseStart_3912458 baseEnd_3912458 := by
    simpa [prefixWord, tailWord_3912458, baseEnd_3912458] using wordTrace_append hprefix tailTrace_3912458
  have hstable : (prefixWord ++ tailWord_3912458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912458).length < 2 ^ (prefixWord ++ tailWord_3912458).sum := by decide
  have hdescent : baseEnd_3912458 < baseStart_3912458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912485 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 3]
def baseStart_3912485 : Nat := 118140960795 + 3912485 * 2 ^ 59
def prefixEnd_3912485 : Nat := 4983230072969 + 3 ^ 40 * 3912485 * 2
def baseEnd_3912485 : Nat := 2008985358506230118144315

theorem tailTrace_3912485 : CollatzResearch.WordTrace tailWord_3912485 prefixEnd_3912485 2008985358506230118144315 := by
  unfold tailWord_3912485
  simp only [CollatzResearch.WordTrace]
  refine ⟨142700051230742519085050909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95133367487161679390033939 142700051230742519085050909)
  ·
    refine ⟨53512519211528444656894091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142700051230742519085050909 53512519211528444656894091)
    ·
      refine ⟨80268778817292666985341137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53512519211528444656894091 80268778817292666985341137)
      ·
        refine ⟨60201584112969500239005853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80268778817292666985341137 60201584112969500239005853)
        ·
          refine ⟨22575594042363562589627195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60201584112969500239005853 22575594042363562589627195)
          ·
            refine ⟨33863391063545343884440793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22575594042363562589627195 33863391063545343884440793)
            ·
              refine ⟨25397543297659007913330595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33863391063545343884440793 25397543297659007913330595)
              ·
                refine ⟨38096314946488511869995893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25397543297659007913330595 38096314946488511869995893)
                ·
                  refine ⟨3571529526233297987812115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38096314946488511869995893 3571529526233297987812115)
                  ·
                    refine ⟨5357294289349946981718173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3571529526233297987812115 5357294289349946981718173)
                    ·
                      refine ⟨2008985358506230118144315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5357294289349946981718173 2008985358506230118144315)
                      ·
                        rfl

theorem cell23_3912485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_3912485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912485 prefixEnd_3912485 := by exact prefixLift 3912485
  have htrace : WordTrace (prefixWord ++ tailWord_3912485) baseStart_3912485 baseEnd_3912485 := by
    simpa [prefixWord, tailWord_3912485, baseEnd_3912485] using wordTrace_append hprefix tailTrace_3912485
  have hstable : (prefixWord ++ tailWord_3912485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912485).length < 2 ^ (prefixWord ++ tailWord_3912485).sum := by decide
  have hdescent : baseEnd_3912485 < baseStart_3912485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912513 : List Nat := [1, 2, 5, 3, 1, 2, 2, 2, 1, 4]
def baseStart_3912513 : Nat := 118140960795 + 3912513 * 2 ^ 59
def prefixEnd_3912513 : Nat := 4983230072969 + 3 ^ 40 * 3912513 * 2
def baseEnd_3912513 : Nat := 669666578654852002864729

theorem tailTrace_3912513 : CollatzResearch.WordTrace tailWord_3912513 prefixEnd_3912513 669666578654852002864729 := by
  unfold tailWord_3912513
  simp only [CollatzResearch.WordTrace]
  refine ⟨142701072474641079867070193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95134048316427386578046795 142701072474641079867070193)
  ·
    refine ⟨107025804355980809900302645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142701072474641079867070193 107025804355980809900302645)
    ·
      refine ⟨10033669158373200928153373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107025804355980809900302645 10033669158373200928153373)
      ·
        refine ⟨3762625934389950348057515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10033669158373200928153373 3762625934389950348057515)
        ·
          refine ⟨5643938901584925522086273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3762625934389950348057515 5643938901584925522086273)
          ·
            refine ⟨4232954176188694141564705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5643938901584925522086273 4232954176188694141564705)
            ·
              refine ⟨3174715632141520606173529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4232954176188694141564705 3174715632141520606173529)
              ·
                refine ⟨2381036724106140454630147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174715632141520606173529 2381036724106140454630147)
                ·
                  refine ⟨3571555086159210681945221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381036724106140454630147 3571555086159210681945221)
                  ·
                    refine ⟨669666578654852002864729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3571555086159210681945221 669666578654852002864729)
                    ·
                      rfl

theorem cell23_3912513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_3912513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912513 prefixEnd_3912513 := by exact prefixLift 3912513
  have htrace : WordTrace (prefixWord ++ tailWord_3912513) baseStart_3912513 baseEnd_3912513 := by
    simpa [prefixWord, tailWord_3912513, baseEnd_3912513] using wordTrace_append hprefix tailTrace_3912513
  have hstable : (prefixWord ++ tailWord_3912513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912513).length < 2 ^ (prefixWord ++ tailWord_3912513).sum := by decide
  have hdescent : baseEnd_3912513 < baseStart_3912513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912528 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_3912528 : Nat := 118140960795 + 3912528 * 2 ^ 59
def prefixEnd_3912528 : Nat := 4983230072969 + 3 ^ 40 * 3912528 * 2
def baseEnd_3912528 : Nat := 2009007438174373449906617

theorem tailTrace_3912528 : CollatzResearch.WordTrace tailWord_3912528 prefixEnd_3912528 2009007438174373449906617 := by
  unfold tailWord_3912528
  simp only [CollatzResearch.WordTrace]
  refine ⟨71350809784793368714433119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95134413046391158285910825 71350809784793368714433119)
  ·
    refine ⟨107026214677190053071649679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71350809784793368714433119 107026214677190053071649679)
    ·
      refine ⟨160539322015785079607474519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107026214677190053071649679 160539322015785079607474519)
      ·
        refine ⟨240808983023677619411211779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160539322015785079607474519 240808983023677619411211779)
        ·
          refine ⟨361213474535516429116817669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240808983023677619411211779 361213474535516429116817669)
          ·
            refine ⟨67727526475409330459403313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361213474535516429116817669 67727526475409330459403313)
            ·
              refine ⟨50795644856556997844552485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67727526475409330459403313 50795644856556997844552485)
              ·
                refine ⟨9524183410604437095853591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50795644856556997844552485 9524183410604437095853591)
                ·
                  refine ⟨14286275115906655643780387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9524183410604437095853591 14286275115906655643780387)
                  ·
                    refine ⟨21429412673859983465670581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14286275115906655643780387 21429412673859983465670581)
                    ·
                      refine ⟨2009007438174373449906617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21429412673859983465670581 2009007438174373449906617)
                      ·
                        rfl

theorem cell23_3912528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_3912528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912528 prefixEnd_3912528 := by exact prefixLift 3912528
  have htrace : WordTrace (prefixWord ++ tailWord_3912528) baseStart_3912528 baseEnd_3912528 := by
    simpa [prefixWord, tailWord_3912528, baseEnd_3912528] using wordTrace_append hprefix tailTrace_3912528
  have hstable : (prefixWord ++ tailWord_3912528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912528).length < 2 ^ (prefixWord ++ tailWord_3912528).sum := by decide
  have hdescent : baseEnd_3912528 < baseStart_3912528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912535 : List Nat := [1, 1, 3, 2, 4, 2, 2, 1, 1, 6]
def baseStart_3912535 : Nat := 118140960795 + 3912535 * 2 ^ 59
def prefixEnd_3912535 : Nat := 4983230072969 + 3 ^ 40 * 3912535 * 2
def baseEnd_3912535 : Nat := 669670344179651640839695

theorem tailTrace_3912535 : CollatzResearch.WordTrace tailWord_3912535 prefixEnd_3912535 669670344179651640839695 := by
  unfold tailWord_3912535
  simp only [CollatzResearch.WordTrace]
  refine ⟨142701874880561377624371059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95134583253707585082914039 142701874880561377624371059)
  ·
    refine ⟨214052812320842066436556589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142701874880561377624371059 214052812320842066436556589)
    ·
      refine ⟨80269804620315774913708721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214052812320842066436556589 80269804620315774913708721)
      ·
        refine ⟨60202353465236831185281541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80269804620315774913708721 60202353465236831185281541)
        ·
          refine ⟨11287941274731905847240289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60202353465236831185281541 11287941274731905847240289)
          ·
            refine ⟨8465955956048929385430217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11287941274731905847240289 8465955956048929385430217)
            ·
              refine ⟨6349466967036697039072663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8465955956048929385430217 6349466967036697039072663)
              ·
                refine ⟨9524200450555045558608995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349466967036697039072663 9524200450555045558608995)
                ·
                  refine ⟨14286300675832568337913493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9524200450555045558608995 14286300675832568337913493)
                  ·
                    refine ⟨669670344179651640839695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 14286300675832568337913493 669670344179651640839695)
                    ·
                      rfl

theorem cell23_3912535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_3912535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912535 prefixEnd_3912535 := by exact prefixLift 3912535
  have htrace : WordTrace (prefixWord ++ tailWord_3912535) baseStart_3912535 baseEnd_3912535 := by
    simpa [prefixWord, tailWord_3912535, baseEnd_3912535] using wordTrace_append hprefix tailTrace_3912535
  have hstable : (prefixWord ++ tailWord_3912535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912535).length < 2 ^ (prefixWord ++ tailWord_3912535).sum := by decide
  have hdescent : baseEnd_3912535 < baseStart_3912535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912546 : List Nat := [3, 3, 2, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_3912546 : Nat := 118140960795 + 3912546 * 2 ^ 59
def prefixEnd_3912546 : Nat := 4983230072969 + 3 ^ 40 * 3912546 * 2
def baseEnd_3912546 : Nat := 2009016680826154379481535

theorem tailTrace_3912546 : CollatzResearch.WordTrace tailWord_3912546 prefixEnd_3912546 2009016680826154379481535 := by
  unfold tailWord_3912546
  simp only [CollatzResearch.WordTrace]
  refine ⟨35675569020880381625755373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95134850722347684335347661 35675569020880381625755373)
  ·
    refine ⟨13378338382830143109658265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35675569020880381625755373 13378338382830143109658265)
    ·
      refine ⟨10033753787122607332243699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13378338382830143109658265 10033753787122607332243699)
      ·
        refine ⟨15050630680683910998365549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10033753787122607332243699 15050630680683910998365549)
        ·
          refine ⟨5643986505256466624387081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15050630680683910998365549 5643986505256466624387081)
          ·
            refine ⟨4232989878942349968290311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5643986505256466624387081 4232989878942349968290311)
            ·
              refine ⟨6349484818413524952435467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4232989878942349968290311 6349484818413524952435467)
              ·
                refine ⟨9524227227620287428653201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6349484818413524952435467 9524227227620287428653201)
                ·
                  refine ⟨7143170420715215571489901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9524227227620287428653201 7143170420715215571489901)
                  ·
                    refine ⟨2678688907768205839308713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7143170420715215571489901 2678688907768205839308713)
                    ·
                      refine ⟨2009016680826154379481535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678688907768205839308713 2009016680826154379481535)
                      ·
                        rfl

theorem cell23_3912546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_3912546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912546 prefixEnd_3912546 := by exact prefixLift 3912546
  have htrace : WordTrace (prefixWord ++ tailWord_3912546) baseStart_3912546 baseEnd_3912546 := by
    simpa [prefixWord, tailWord_3912546, baseEnd_3912546] using wordTrace_append hprefix tailTrace_3912546
  have hstable : (prefixWord ++ tailWord_3912546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912546).length < 2 ^ (prefixWord ++ tailWord_3912546).sum := by decide
  have hdescent : baseEnd_3912546 < baseStart_3912546 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912608 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 1, 8]
def baseStart_3912608 : Nat := 118140960795 + 3912608 * 2 ^ 59
def prefixEnd_3912608 : Nat := 4983230072969 + 3 ^ 40 * 3912608 * 2
def baseEnd_3912608 : Nat := 669682838875577712302083

theorem tailTrace_3912608 : CollatzResearch.WordTrace tailWord_3912608 prefixEnd_3912608 669682838875577712302083 := by
  unfold tailWord_3912608
  simp only [CollatzResearch.WordTrace]
  refine ⟨71352268704648455545889239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95136358272864607394518985 71352268704648455545889239)
  ·
    refine ⟨107028403056972683318833859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71352268704648455545889239 107028403056972683318833859)
    ·
      refine ⟨160542604585459024978250789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107028403056972683318833859 160542604585459024978250789)
      ·
        refine ⟨30101738359773567183422023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160542604585459024978250789 30101738359773567183422023)
        ·
          refine ⟨45152607539660350775133035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30101738359773567183422023 45152607539660350775133035)
          ·
            refine ⟨67728911309490526162699553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45152607539660350775133035 67728911309490526162699553)
            ·
              refine ⟨50796683482117894622024665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67728911309490526162699553 50796683482117894622024665)
              ·
                refine ⟨38097512611588420966518499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50796683482117894622024665 38097512611588420966518499)
                ·
                  refine ⟨57146268917382631449777749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38097512611588420966518499 57146268917382631449777749)
                  ·
                    refine ⟨669682838875577712302083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57146268917382631449777749 669682838875577712302083)
                    ·
                      rfl

theorem cell23_3912608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_3912608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912608 prefixEnd_3912608 := by exact prefixLift 3912608
  have htrace : WordTrace (prefixWord ++ tailWord_3912608) baseStart_3912608 baseEnd_3912608 := by
    simpa [prefixWord, tailWord_3912608, baseEnd_3912608] using wordTrace_append hprefix tailTrace_3912608
  have hstable : (prefixWord ++ tailWord_3912608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912608).length < 2 ^ (prefixWord ++ tailWord_3912608).sum := by decide
  have hdescent : baseEnd_3912608 < baseStart_3912608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912689 : List Nat := [1, 2, 2, 2, 4, 1, 4, 2, 5]
def baseStart_3912689 : Nat := 118140960795 + 3912689 * 2 ^ 59
def prefixEnd_3912689 : Nat := 4983230072969 + 3 ^ 40 * 3912689 * 2
def baseEnd_3912689 : Nat := 223232234284416368888153

theorem tailTrace_3912689 : CollatzResearch.WordTrace tailWord_3912689 prefixEnd_3912689 223232234284416368888153 := by
  unfold tailWord_3912689
  simp only [CollatzResearch.WordTrace]
  refine ⟨142707491722003461925477121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95138327814668974616984747 142707491722003461925477121)
  ·
    refine ⟨107030618791502596444107841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142707491722003461925477121 107030618791502596444107841)
    ·
      refine ⟨80272964093626947333080881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107030618791502596444107841 80272964093626947333080881)
      ·
        refine ⟨60204723070220210499810661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80272964093626947333080881 60204723070220210499810661)
        ·
          refine ⟨11288385575666289468714499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60204723070220210499810661 11288385575666289468714499)
          ·
            refine ⟨16932578363499434203071749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288385575666289468714499 16932578363499434203071749)
            ·
              refine ⟨3174858443156143913075953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16932578363499434203071749 3174858443156143913075953)
              ·
                refine ⟨2381143832367107934806965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3174858443156143913075953 2381143832367107934806965)
                ·
                  refine ⟨223232234284416368888153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2381143832367107934806965 223232234284416368888153)
                  ·
                    rfl

theorem cell23_3912689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 4, 2, 5].length) (baseStart_3912689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912689 prefixEnd_3912689 := by exact prefixLift 3912689
  have htrace : WordTrace (prefixWord ++ tailWord_3912689) baseStart_3912689 baseEnd_3912689 := by
    simpa [prefixWord, tailWord_3912689, baseEnd_3912689] using wordTrace_append hprefix tailTrace_3912689
  have hstable : (prefixWord ++ tailWord_3912689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912689).length < 2 ^ (prefixWord ++ tailWord_3912689).sum := by decide
  have hdescent : baseEnd_3912689 < baseStart_3912689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912735 : List Nat := [1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_3912735 : Nat := 118140960795 + 3912735 * 2 ^ 59
def prefixEnd_3912735 : Nat := 4983230072969 + 3 ^ 40 * 3912735 * 2
def baseEnd_3912735 : Nat := 2009113728669854140018165

theorem tailTrace_3912735 : CollatzResearch.WordTrace tailWord_3912735 prefixEnd_3912735 2009113728669854140018165 := by
  unfold tailWord_3912735
  simp only [CollatzResearch.WordTrace]
  refine ⟨142709169479836811781651659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95139446319891207854434439 142709169479836811781651659)
  ·
    refine ⟨214063754219755217672477489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142709169479836811781651659 214063754219755217672477489)
    ·
      refine ⟨160547815664816413254358117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214063754219755217672477489 160547815664816413254358117)
      ·
        refine ⟨30102715437153077485192147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160547815664816413254358117 30102715437153077485192147)
        ·
          refine ⟨45154073155729616227788221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30102715437153077485192147 45154073155729616227788221)
          ·
            refine ⟨16932777433398606085420583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45154073155729616227788221 16932777433398606085420583)
            ·
              refine ⟨25399166150097909128130875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16932777433398606085420583 25399166150097909128130875)
              ·
                refine ⟨38098749225146863692196313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25399166150097909128130875 38098749225146863692196313)
                ·
                  refine ⟨28574061918860147769147235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38098749225146863692196313 28574061918860147769147235)
                  ·
                    refine ⟨42861092878290221653720853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28574061918860147769147235 42861092878290221653720853)
                    ·
                      refine ⟨2009113728669854140018165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42861092878290221653720853 2009113728669854140018165)
                      ·
                        rfl

theorem cell23_3912735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_3912735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912735 prefixEnd_3912735 := by exact prefixLift 3912735
  have htrace : WordTrace (prefixWord ++ tailWord_3912735) baseStart_3912735 baseEnd_3912735 := by
    simpa [prefixWord, tailWord_3912735, baseEnd_3912735] using wordTrace_append hprefix tailTrace_3912735
  have hstable : (prefixWord ++ tailWord_3912735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912735).length < 2 ^ (prefixWord ++ tailWord_3912735).sum := by decide
  have hdescent : baseEnd_3912735 < baseStart_3912735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912756 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 2, 4, 2]
def baseStart_3912756 : Nat := 118140960795 + 3912756 * 2 ^ 59
def prefixEnd_3912756 : Nat := 4983230072969 + 3 ^ 40 * 3912756 * 2
def baseEnd_3912756 : Nat := 2009124511763598557855569

theorem tailTrace_3912756 : CollatzResearch.WordTrace tailWord_3912756 prefixEnd_3912756 2009124511763598557855569 := by
  unfold tailWord_3912756
  simp only [CollatzResearch.WordTrace]
  refine ⟨71354967706380366184083061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95139956941840488245444081 71354967706380366184083061)
  ·
    refine ⟨6689528222473159329757787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71354967706380366184083061 6689528222473159329757787)
    ·
      refine ⟨10034292333709738994636681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6689528222473159329757787 10034292333709738994636681)
      ·
        refine ⟨7525719250282304245977511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10034292333709738994636681 7525719250282304245977511)
        ·
          refine ⟨11288578875423456368966267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525719250282304245977511 11288578875423456368966267)
          ·
            refine ⟨16932868313135184553449401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11288578875423456368966267 16932868313135184553449401)
            ·
              refine ⟨12699651234851388415087051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16932868313135184553449401 12699651234851388415087051)
              ·
                refine ⟨19049476852277082622630577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12699651234851388415087051 19049476852277082622630577)
                ·
                  refine ⟨14287107639207811966972933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19049476852277082622630577 14287107639207811966972933)
                  ·
                    refine ⟨2678832682351464743807425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14287107639207811966972933 2678832682351464743807425)
                    ·
                      refine ⟨2009124511763598557855569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678832682351464743807425 2009124511763598557855569)
                      ·
                        rfl

theorem cell23_3912756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_3912756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912756 prefixEnd_3912756 := by exact prefixLift 3912756
  have htrace : WordTrace (prefixWord ++ tailWord_3912756) baseStart_3912756 baseEnd_3912756 := by
    simpa [prefixWord, tailWord_3912756, baseEnd_3912756] using wordTrace_append hprefix tailTrace_3912756
  have hstable : (prefixWord ++ tailWord_3912756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912756).length < 2 ^ (prefixWord ++ tailWord_3912756).sum := by decide
  have hdescent : baseEnd_3912756 < baseStart_3912756 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912792 : List Nat := [2, 1, 2, 2, 1, 3, 1, 5, 1, 5]
def baseStart_3912792 : Nat := 118140960795 + 3912792 * 2 ^ 59
def prefixEnd_3912792 : Nat := 4983230072969 + 3 ^ 40 * 3912792 * 2
def baseEnd_3912792 : Nat := 669714332355720139001801

theorem tailTrace_3912792 : CollatzResearch.WordTrace tailWord_3912792 prefixEnd_3912792 669714332355720139001801 := by
  unfold tailWord_3912792
  simp only [CollatzResearch.WordTrace]
  refine ⟨71355624220315155258238315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95140832293753540344317753 71355624220315155258238315)
  ·
    refine ⟨107033436330472732887357473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71355624220315155258238315 107033436330472732887357473)
    ·
      refine ⟨80275077247854549665518105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107033436330472732887357473 80275077247854549665518105)
      ·
        refine ⟨60206307935890912249138579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80275077247854549665518105 60206307935890912249138579)
        ·
          refine ⟨90309461903836368373707869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60206307935890912249138579 90309461903836368373707869)
          ·
            refine ⟨33866048213938638140140451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90309461903836368373707869 33866048213938638140140451)
            ·
              refine ⟨50799072320907957210210677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33866048213938638140140451 50799072320907957210210677)
              ·
                refine ⟨4762413030085120988457251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50799072320907957210210677 4762413030085120988457251)
                ·
                  refine ⟨7143619545127681482685877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762413030085120988457251 7143619545127681482685877)
                  ·
                    refine ⟨669714332355720139001801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7143619545127681482685877 669714332355720139001801)
                    ·
                      rfl

theorem cell23_3912792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 1, 5].length) (baseStart_3912792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912792 prefixEnd_3912792 := by exact prefixLift 3912792
  have htrace : WordTrace (prefixWord ++ tailWord_3912792) baseStart_3912792 baseEnd_3912792 := by
    simpa [prefixWord, tailWord_3912792, baseEnd_3912792] using wordTrace_append hprefix tailTrace_3912792
  have hstable : (prefixWord ++ tailWord_3912792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912792).length < 2 ^ (prefixWord ++ tailWord_3912792).sum := by decide
  have hdescent : baseEnd_3912792 < baseStart_3912792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912799 : List Nat := [1, 1, 2, 3, 1, 1, 5, 2, 2, 3, 2]
def baseStart_3912799 : Nat := 118140960795 + 3912799 * 2 ^ 59
def prefixEnd_3912799 : Nat := 4983230072969 + 3 ^ 40 * 3912799 * 2
def baseEnd_3912799 : Nat := 2009146591431741889617871

theorem tailTrace_3912799 : CollatzResearch.WordTrace tailWord_3912799 prefixEnd_3912799 2009146591431741889617871 := by
  unfold tailWord_3912799
  simp only [CollatzResearch.WordTrace]
  refine ⟨142711503751604950711981451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95141002501069967141320967 142711503751604950711981451)
  ·
    refine ⟨214067255627407426067972177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142711503751604950711981451 214067255627407426067972177)
    ·
      refine ⟨160550441720555569550979133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214067255627407426067972177 160550441720555569550979133)
      ·
        refine ⟨60206415645208338581617175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160550441720555569550979133 60206415645208338581617175)
        ·
          refine ⟨90309623467812507872425763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60206415645208338581617175 90309623467812507872425763)
          ·
            refine ⟨135464435201718761808638645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90309623467812507872425763 135464435201718761808638645)
            ·
              refine ⟨12699790800161133919559873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135464435201718761808638645 12699790800161133919559873)
              ·
                refine ⟨9524843100120850439669905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12699790800161133919559873 9524843100120850439669905)
                ·
                  refine ⟨7143632325090637829752429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9524843100120850439669905 7143632325090637829752429)
                  ·
                    refine ⟨2678862121908989186157161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7143632325090637829752429 2678862121908989186157161)
                    ·
                      refine ⟨2009146591431741889617871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678862121908989186157161 2009146591431741889617871)
                      ·
                        rfl

theorem cell23_3912799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_3912799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912799 prefixEnd_3912799 := by exact prefixLift 3912799
  have htrace : WordTrace (prefixWord ++ tailWord_3912799) baseStart_3912799 baseEnd_3912799 := by
    simpa [prefixWord, tailWord_3912799, baseEnd_3912799] using wordTrace_append hprefix tailTrace_3912799
  have hstable : (prefixWord ++ tailWord_3912799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912799).length < 2 ^ (prefixWord ++ tailWord_3912799).sum := by decide
  have hdescent : baseEnd_3912799 < baseStart_3912799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912812 : List Nat := [2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 4]
def baseStart_3912812 : Nat := 118140960795 + 3912812 * 2 ^ 59
def prefixEnd_3912812 : Nat := 4983230072969 + 3 ^ 40 * 3912812 * 2
def baseEnd_3912812 : Nat := 2009153266680250338755311

theorem tailTrace_3912812 : CollatzResearch.WordTrace tailWord_3912812 prefixEnd_3912812 2009153266680250338755311 := by
  unfold tailWord_3912812
  simp only [CollatzResearch.WordTrace]
  refine ⟨71355988950278926966102345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95141318600371902621469793 71355988950278926966102345)
  ·
    refine ⟨53516991712709195224576759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71355988950278926966102345 53516991712709195224576759)
    ·
      refine ⟨80275487569063792836865139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53516991712709195224576759 80275487569063792836865139)
      ·
        refine ⟨120413231353595689255297709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80275487569063792836865139 120413231353595689255297709)
        ·
          refine ⟨45154961757598383470736641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120413231353595689255297709 45154961757598383470736641)
          ·
            refine ⟨33866221318198787603052481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45154961757598383470736641 33866221318198787603052481)
            ·
              refine ⟨25399665988649090702289361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33866221318198787603052481 25399665988649090702289361)
              ·
                refine ⟨19049749491486818026717021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25399665988649090702289361 19049749491486818026717021)
                ·
                  refine ⟨7143656059307556760018883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19049749491486818026717021 7143656059307556760018883)
                  ·
                    refine ⟨10715484088961335140028325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7143656059307556760018883 10715484088961335140028325)
                    ·
                      refine ⟨2009153266680250338755311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10715484088961335140028325 2009153266680250338755311)
                      ·
                        rfl

theorem cell23_3912812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 4].length) (baseStart_3912812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912812 prefixEnd_3912812 := by exact prefixLift 3912812
  have htrace : WordTrace (prefixWord ++ tailWord_3912812) baseStart_3912812 baseEnd_3912812 := by
    simpa [prefixWord, tailWord_3912812, baseEnd_3912812] using wordTrace_append hprefix tailTrace_3912812
  have hstable : (prefixWord ++ tailWord_3912812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912812).length < 2 ^ (prefixWord ++ tailWord_3912812).sum := by decide
  have hdescent : baseEnd_3912812 < baseStart_3912812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912835 : List Nat := [1, 1, 1, 3, 3, 2, 1, 11]
def baseStart_3912835 : Nat := 118140960795 + 3912835 * 2 ^ 59
def prefixEnd_3912835 : Nat := 4983230072969 + 3 ^ 40 * 3912835 * 2
def baseEnd_3912835 : Nat := 74413521360566805509915

theorem tailTrace_3912835 : CollatzResearch.WordTrace tailWord_3912835 prefixEnd_3912835 74413521360566805509915 := by
  unfold tailWord_3912835
  simp only [CollatzResearch.WordTrace]
  refine ⟨142712816779474528860291959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95141877852983019240194639 142712816779474528860291959)
  ·
    refine ⟨214069225169211793290437939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142712816779474528860291959 214069225169211793290437939)
    ·
      refine ⟨321103837753817689935656909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214069225169211793290437939 321103837753817689935656909)
      ·
        refine ⟨120413939157681633725871341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321103837753817689935656909 120413939157681633725871341)
        ·
          refine ⟨45155227184130612647201753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120413939157681633725871341 45155227184130612647201753)
          ·
            refine ⟨33866420388097959485401315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45155227184130612647201753 33866420388097959485401315)
            ·
              refine ⟨50799630582146939228101973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33866420388097959485401315 50799630582146939228101973)
              ·
                refine ⟨74413521360566805509915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 50799630582146939228101973 74413521360566805509915)
                ·
                  rfl

theorem cell23_3912835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 11].length) (baseStart_3912835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912835 prefixEnd_3912835 := by exact prefixLift 3912835
  have htrace : WordTrace (prefixWord ++ tailWord_3912835) baseStart_3912835 baseEnd_3912835 := by
    simpa [prefixWord, tailWord_3912835, baseEnd_3912835] using wordTrace_append hprefix tailTrace_3912835
  have hstable : (prefixWord ++ tailWord_3912835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912835).length < 2 ^ (prefixWord ++ tailWord_3912835).sum := by decide
  have hdescent : baseEnd_3912835 < baseStart_3912835 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912856 : List Nat := [2, 1, 2, 4, 2, 2, 2, 2, 2, 4]
def baseStart_3912856 : Nat := 118140960795 + 3912856 * 2 ^ 59
def prefixEnd_3912856 : Nat := 4983230072969 + 3 ^ 40 * 3912856 * 2
def baseEnd_3912856 : Nat := 669725286609682722201703

theorem tailTrace_3912856 : CollatzResearch.WordTrace tailWord_3912856 prefixEnd_3912856 669725286609682722201703 := by
  unfold tailWord_3912856
  simp only [CollatzResearch.WordTrace]
  refine ⟨71356791356199224723403211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95142388474932299631204281 71356791356199224723403211)
  ·
    refine ⟨107035187034298837085104817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71356791356199224723403211 107035187034298837085104817)
    ·
      refine ⟨80276390275724127813828613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107035187034298837085104817 80276390275724127813828613)
      ·
        refine ⟨15051823176698273965092865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80276390275724127813828613 15051823176698273965092865)
        ·
          refine ⟨11288867382523705473819649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15051823176698273965092865 11288867382523705473819649)
          ·
            refine ⟨8466650536892779105364737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11288867382523705473819649 8466650536892779105364737)
            ·
              refine ⟨6349987902669584329023553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8466650536892779105364737 6349987902669584329023553)
              ·
                refine ⟨4762490927002188246767665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6349987902669584329023553 4762490927002188246767665)
                ·
                  refine ⟨3571868195251641185075749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4762490927002188246767665 3571868195251641185075749)
                  ·
                    refine ⟨669725286609682722201703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3571868195251641185075749 669725286609682722201703)
                    ·
                      rfl

theorem cell23_3912856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 2, 4].length) (baseStart_3912856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912856 prefixEnd_3912856 := by exact prefixLift 3912856
  have htrace : WordTrace (prefixWord ++ tailWord_3912856) baseStart_3912856 baseEnd_3912856 := by
    simpa [prefixWord, tailWord_3912856, baseEnd_3912856] using wordTrace_append hprefix tailTrace_3912856
  have hstable : (prefixWord ++ tailWord_3912856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912856).length < 2 ^ (prefixWord ++ tailWord_3912856).sum := by decide
  have hdescent : baseEnd_3912856 < baseStart_3912856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912897 : List Nat := [1, 2, 6, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_3912897 : Nat := 118140960795 + 3912897 * 2 ^ 59
def prefixEnd_3912897 : Nat := 4983230072969 + 3 ^ 40 * 3912897 * 2
def baseEnd_3912897 : Nat := 2009196912535882506192421

theorem tailTrace_3912897 : CollatzResearch.WordTrace tailWord_3912897 prefixEnd_3912897 2009196912535882506192421 := by
  unfold tailWord_3912897
  simp only [CollatzResearch.WordTrace]
  refine ⟨142715078105249913449048945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95143385403499942299365963 142715078105249913449048945)
  ·
    refine ⟨107036308578937435086786709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142715078105249913449048945 107036308578937435086786709)
    ·
      refine ⟨5017326964637692269693127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107036308578937435086786709 5017326964637692269693127)
      ·
        refine ⟨7525990446956538404539691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5017326964637692269693127 7525990446956538404539691)
        ·
          refine ⟨11288985670434807606809537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7525990446956538404539691 11288985670434807606809537)
          ·
            refine ⟨8466739252826105705107153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11288985670434807606809537 8466739252826105705107153)
            ·
              refine ⟨6350054439619579278830365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8466739252826105705107153 6350054439619579278830365)
              ·
                refine ⟨2381270414857342229561387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6350054439619579278830365 2381270414857342229561387)
                ·
                  refine ⟨3571905622286013344342081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381270414857342229561387 3571905622286013344342081)
                  ·
                    refine ⟨2678929216714510008256561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3571905622286013344342081 2678929216714510008256561)
                    ·
                      refine ⟨2009196912535882506192421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678929216714510008256561 2009196912535882506192421)
                      ·
                        rfl

theorem cell23_3912897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_3912897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912897 prefixEnd_3912897 := by exact prefixLift 3912897
  have htrace : WordTrace (prefixWord ++ tailWord_3912897) baseStart_3912897 baseEnd_3912897 := by
    simpa [prefixWord, tailWord_3912897, baseEnd_3912897] using wordTrace_append hprefix tailTrace_3912897
  have hstable : (prefixWord ++ tailWord_3912897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912897).length < 2 ^ (prefixWord ++ tailWord_3912897).sum := by decide
  have hdescent : baseEnd_3912897 < baseStart_3912897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912900 : List Nat := [2, 3, 3, 1, 3, 2, 2, 1, 1, 2, 3]
def baseStart_3912900 : Nat := 118140960795 + 3912900 * 2 ^ 59
def prefixEnd_3912900 : Nat := 4983230072969 + 3 ^ 40 * 3912900 * 2
def baseEnd_3912900 : Nat := 2009198452977845994454907

theorem tailTrace_3912900 : CollatzResearch.WordTrace tailWord_3912900 prefixEnd_3912900 2009198452977845994454907 := by
  unfold tailWord_3912900
  simp only [CollatzResearch.WordTrace]
  refine ⟨71357593762119522480704077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95143458349492696640938769 71357593762119522480704077)
  ·
    refine ⟨26759097660794820930264029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71357593762119522480704077 26759097660794820930264029)
    ·
      refine ⟨10034661622798057848849011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26759097660794820930264029 10034661622798057848849011)
      ·
        refine ⟨15051992434197086773273517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10034661622798057848849011 15051992434197086773273517)
        ·
          refine ⟨5644497162823907539977569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15051992434197086773273517 5644497162823907539977569)
          ·
            refine ⟨4233372872117930654983177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5644497162823907539977569 4233372872117930654983177)
            ·
              refine ⟨3175029654088447991237383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4233372872117930654983177 3175029654088447991237383)
              ·
                refine ⟨4762544481132671986856075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3175029654088447991237383 4762544481132671986856075)
                ·
                  refine ⟨7143816721699007980284113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4762544481132671986856075 7143816721699007980284113)
                  ·
                    refine ⟨5357862541274255985213085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7143816721699007980284113 5357862541274255985213085)
                    ·
                      refine ⟨2009198452977845994454907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5357862541274255985213085 2009198452977845994454907)
                      ·
                        rfl

theorem cell23_3912900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_3912900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912900 prefixEnd_3912900 := by exact prefixLift 3912900
  have htrace : WordTrace (prefixWord ++ tailWord_3912900) baseStart_3912900 baseEnd_3912900 := by
    simpa [prefixWord, tailWord_3912900, baseEnd_3912900] using wordTrace_append hprefix tailTrace_3912900
  have hstable : (prefixWord ++ tailWord_3912900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912900).length < 2 ^ (prefixWord ++ tailWord_3912900).sum := by decide
  have hdescent : baseEnd_3912900 < baseStart_3912900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912919 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 3, 4, 2]
def baseStart_3912919 : Nat := 118140960795 + 3912919 * 2 ^ 59
def prefixEnd_3912919 : Nat := 4983230072969 + 3 ^ 40 * 3912919 * 2
def baseEnd_3912919 : Nat := 2009208209110281420117319

theorem tailTrace_3912919 : CollatzResearch.WordTrace tailWord_3912919 prefixEnd_3912919 2009208209110281420117319 := by
  unfold tailWord_3912919
  simp only [CollatzResearch.WordTrace]
  refine ⟨142715880511170211206349811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95143920340780140804233207 142715880511170211206349811)
  ·
    refine ⟨214073820766755316809524717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142715880511170211206349811 214073820766755316809524717)
    ·
      refine ⟨80277682787533243803571769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214073820766755316809524717 80277682787533243803571769)
      ·
        refine ⟨60208262090649932852678827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80277682787533243803571769 60208262090649932852678827)
        ·
          refine ⟨90312393135974899279018241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60208262090649932852678827 90312393135974899279018241)
          ·
            refine ⟨67734294851981174459263681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90312393135974899279018241 67734294851981174459263681)
            ·
              refine ⟨50800721138985880844447761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67734294851981174459263681 50800721138985880844447761)
              ·
                refine ⟨38100540854239410633335821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50800721138985880844447761 38100540854239410633335821)
                ·
                  refine ⟨14287702820339778987500933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38100540854239410633335821 14287702820339778987500933)
                  ·
                    refine ⟨2678944278813708560156425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14287702820339778987500933 2678944278813708560156425)
                    ·
                      refine ⟨2009208209110281420117319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678944278813708560156425 2009208209110281420117319)
                      ·
                        rfl

theorem cell23_3912919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 3, 4, 2].length) (baseStart_3912919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912919 prefixEnd_3912919 := by exact prefixLift 3912919
  have htrace : WordTrace (prefixWord ++ tailWord_3912919) baseStart_3912919 baseEnd_3912919 := by
    simpa [prefixWord, tailWord_3912919, baseEnd_3912919] using wordTrace_append hprefix tailTrace_3912919
  have hstable : (prefixWord ++ tailWord_3912919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912919).length < 2 ^ (prefixWord ++ tailWord_3912919).sum := by decide
  have hdescent : baseEnd_3912919 < baseStart_3912919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912922 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5]
def baseStart_3912922 : Nat := 118140960795 + 3912922 * 2 ^ 59
def prefixEnd_3912922 : Nat := 4983230072969 + 3 ^ 40 * 3912922 * 2
def baseEnd_3912922 : Nat := 2009209749552244908379805

theorem tailTrace_3912922 : CollatzResearch.WordTrace tailWord_3912922 prefixEnd_3912922 2009209749552244908379805 := by
  unfold tailWord_3912922
  simp only [CollatzResearch.WordTrace]
  refine ⟨35678997482539835679677255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95143993286772895145806013 35678997482539835679677255)
  ·
    refine ⟨53518496223809753519515883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35678997482539835679677255 53518496223809753519515883)
    ·
      refine ⟨80277744335714630279273825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53518496223809753519515883 80277744335714630279273825)
      ·
        refine ⟨60208308251785972709455369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80277744335714630279273825 60208308251785972709455369)
        ·
          refine ⟨45156231188839479532091527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60208308251785972709455369 45156231188839479532091527)
          ·
            refine ⟨67734346783259219298137291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45156231188839479532091527 67734346783259219298137291)
            ·
              refine ⟨101601520174888828947205937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67734346783259219298137291 101601520174888828947205937)
              ·
                refine ⟨76201140131166621710404453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101601520174888828947205937 76201140131166621710404453)
                ·
                  refine ⟨14287713774593741570700835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76201140131166621710404453 14287713774593741570700835)
                  ·
                    refine ⟨21431570661890612356051253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14287713774593741570700835 21431570661890612356051253)
                    ·
                      refine ⟨2009209749552244908379805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21431570661890612356051253 2009209749552244908379805)
                      ·
                        rfl

theorem cell23_3912922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5].length) (baseStart_3912922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912922 prefixEnd_3912922 := by exact prefixLift 3912922
  have htrace : WordTrace (prefixWord ++ tailWord_3912922) baseStart_3912922 baseEnd_3912922 := by
    simpa [prefixWord, tailWord_3912922, baseEnd_3912922] using wordTrace_append hprefix tailTrace_3912922
  have hstable : (prefixWord ++ tailWord_3912922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912922).length < 2 ^ (prefixWord ++ tailWord_3912922).sum := by decide
  have hdescent : baseEnd_3912922 < baseStart_3912922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3912948 : List Nat := [2, 6, 1, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_3912948 : Nat := 118140960795 + 3912948 * 2 ^ 59
def prefixEnd_3912948 : Nat := 4983230072969 + 3 ^ 40 * 3912948 * 2
def baseEnd_3912948 : Nat := 2009223100049261806654687

theorem tailTrace_3912948 : CollatzResearch.WordTrace tailWord_3912948 prefixEnd_3912948 2009223100049261806654687 := by
  unfold tailWord_3912948
  simp only [CollatzResearch.WordTrace]
  refine ⟨71358469114032574579577749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95144625485376766106103665 71358469114032574579577749)
  ·
    refine ⟨3344928239720276933417707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 71358469114032574579577749 3344928239720276933417707)
    ·
      refine ⟨5017392359580415400126561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3344928239720276933417707 5017392359580415400126561)
      ·
        refine ⟨3763044269685311550094921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5017392359580415400126561 3763044269685311550094921)
        ·
          refine ⟨2822283202263983662571191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3763044269685311550094921 2822283202263983662571191)
          ·
            refine ⟨4233424803395975493856787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2822283202263983662571191 4233424803395975493856787)
            ·
              refine ⟨6350137205093963240785181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4233424803395975493856787 6350137205093963240785181)
              ·
                refine ⟨2381301451910236215294443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6350137205093963240785181 2381301451910236215294443)
                ·
                  refine ⟨3571952177865354322941665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381301451910236215294443 3571952177865354322941665)
                  ·
                    refine ⟨2678964133399015742206249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3571952177865354322941665 2678964133399015742206249)
                    ·
                      refine ⟨2009223100049261806654687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2678964133399015742206249 2009223100049261806654687)
                      ·
                        rfl

theorem cell23_3912948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_3912948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3912948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3912948 prefixEnd_3912948 := by exact prefixLift 3912948
  have htrace : WordTrace (prefixWord ++ tailWord_3912948) baseStart_3912948 baseEnd_3912948 := by
    simpa [prefixWord, tailWord_3912948, baseEnd_3912948] using wordTrace_append hprefix tailTrace_3912948
  have hstable : (prefixWord ++ tailWord_3912948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3912948).length < 2 ^ (prefixWord ++ tailWord_3912948).sum := by decide
  have hdescent : baseEnd_3912948 < baseStart_3912948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3912948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913049 : List Nat := [1, 2, 1, 2, 2, 2, 4, 3, 6]
def baseStart_3913049 : Nat := 118140960795 + 3913049 * 2 ^ 59
def prefixEnd_3913049 : Nat := 4983230072969 + 3 ^ 40 * 3913049 * 2
def baseEnd_3913049 : Nat := 223252773510596212387969

theorem tailTrace_3913049 : CollatzResearch.WordTrace tailWord_3913049 prefixEnd_3913049 223252773510596212387969 := by
  unfold tailWord_3913049
  simp only [CollatzResearch.WordTrace]
  refine ⟨142720622000699243408582201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95147081333799495605721467 142720622000699243408582201)
  ·
    refine ⟨107040466500524432556436651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142720622000699243408582201 107040466500524432556436651)
    ·
      refine ⟨160560699750786648834654977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107040466500524432556436651 160560699750786648834654977)
      ·
        refine ⟨120420524813089986625991233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160560699750786648834654977 120420524813089986625991233)
        ·
          refine ⟨90315393609817489969493425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120420524813089986625991233 90315393609817489969493425)
          ·
            refine ⟨67736545207363117477120069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90315393609817489969493425 67736545207363117477120069)
            ·
              refine ⟨12700602226380584526960013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67736545207363117477120069 12700602226380584526960013)
              ·
                refine ⟨4762725834892719197610005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12700602226380584526960013 4762725834892719197610005)
                ·
                  refine ⟨223252773510596212387969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4762725834892719197610005 223252773510596212387969)
                  ·
                    rfl

theorem cell23_3913049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 3, 6].length) (baseStart_3913049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913049 prefixEnd_3913049 := by exact prefixLift 3913049
  have htrace : WordTrace (prefixWord ++ tailWord_3913049) baseStart_3913049 baseEnd_3913049 := by
    simpa [prefixWord, tailWord_3913049, baseEnd_3913049] using wordTrace_append hprefix tailTrace_3913049
  have hstable : (prefixWord ++ tailWord_3913049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913049).length < 2 ^ (prefixWord ++ tailWord_3913049).sum := by decide
  have hdescent : baseEnd_3913049 < baseStart_3913049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913156 : List Nat := [2, 3, 3, 2, 1, 1, 1, 10]
def baseStart_3913156 : Nat := 118140960795 + 3913156 * 2 ^ 59
def prefixEnd_3913156 : Nat := 4983230072969 + 3 ^ 40 * 3913156 * 2
def baseEnd_3913156 : Nat := 74419626075014703439027

theorem tailTrace_3913156 : CollatzResearch.WordTrace tailWord_3913156 prefixEnd_3913156 74419626075014703439027 := by
  unfold tailWord_3913156
  simp only [CollatzResearch.WordTrace]
  refine ⟨71362262305655800341363661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95149683074207733788484881 71362262305655800341363661)
  ·
    refine ⟨26760848364620925128011373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71362262305655800341363661 26760848364620925128011373)
    ·
      refine ⟨10035318136732846923004265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26760848364620925128011373 10035318136732846923004265)
      ·
        refine ⟨7526488602549635192253199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10035318136732846923004265 7526488602549635192253199)
        ·
          refine ⟨11289732903824452788379799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7526488602549635192253199 11289732903824452788379799)
          ·
            refine ⟨16934599355736679182569699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11289732903824452788379799 16934599355736679182569699)
            ·
              refine ⟨25401899033605018773854549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16934599355736679182569699 25401899033605018773854549)
              ·
                refine ⟨74419626075014703439027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 25401899033605018773854549 74419626075014703439027)
                ·
                  rfl

theorem cell23_3913156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 10].length) (baseStart_3913156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913156 prefixEnd_3913156 := by exact prefixLift 3913156
  have htrace : WordTrace (prefixWord ++ tailWord_3913156) baseStart_3913156 baseEnd_3913156 := by
    simpa [prefixWord, tailWord_3913156, baseEnd_3913156] using wordTrace_append hprefix tailTrace_3913156
  have hstable : (prefixWord ++ tailWord_3913156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913156).length < 2 ^ (prefixWord ++ tailWord_3913156).sum := by decide
  have hdescent : baseEnd_3913156 < baseStart_3913156 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913159 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_3913159 : Nat := 118140960795 + 3913159 * 2 ^ 59
def prefixEnd_3913159 : Nat := 4983230072969 + 3 ^ 40 * 3913159 * 2
def baseEnd_3913159 : Nat := 2009331444467360481116215

theorem tailTrace_3913159 : CollatzResearch.WordTrace tailWord_3913159 prefixEnd_3913159 2009331444467360481116215 := by
  unfold tailWord_3913159
  simp only [CollatzResearch.WordTrace]
  refine ⟨142724634030300732195086531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95149756020200488130057687 142724634030300732195086531)
  ·
    refine ⟨214086951045451098292629797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142724634030300732195086531 214086951045451098292629797)
    ·
      refine ⟨40141303321022080929868087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214086951045451098292629797 40141303321022080929868087)
      ·
        refine ⟨60211954981533121394802131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40141303321022080929868087 60211954981533121394802131)
        ·
          refine ⟨90317932472299682092203197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60211954981533121394802131 90317932472299682092203197)
          ·
            refine ⟨33869224677112380784576199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90317932472299682092203197 33869224677112380784576199)
            ·
              refine ⟨50803837015668571176864299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33869224677112380784576199 50803837015668571176864299)
              ·
                refine ⟨76205755523502856765296449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50803837015668571176864299 76205755523502856765296449)
                ·
                  refine ⟨57154316642627142573972337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76205755523502856765296449 57154316642627142573972337)
                  ·
                    refine ⟨42865737481970356930479253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57154316642627142573972337 42865737481970356930479253)
                    ·
                      refine ⟨2009331444467360481116215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42865737481970356930479253 2009331444467360481116215)
                      ·
                        rfl

theorem cell23_3913159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_3913159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913159 prefixEnd_3913159 := by exact prefixLift 3913159
  have htrace : WordTrace (prefixWord ++ tailWord_3913159) baseStart_3913159 baseEnd_3913159 := by
    simpa [prefixWord, tailWord_3913159, baseEnd_3913159] using wordTrace_append hprefix tailTrace_3913159
  have hstable : (prefixWord ++ tailWord_3913159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913159).length < 2 ^ (prefixWord ++ tailWord_3913159).sum := by decide
  have hdescent : baseEnd_3913159 < baseStart_3913159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913200 : List Nat := [2, 1, 1, 1, 3, 5, 2, 2, 2, 1, 3]
def baseStart_3913200 : Nat := 118140960795 + 3913200 * 2 ^ 59
def prefixEnd_3913200 : Nat := 4983230072969 + 3 ^ 40 * 3913200 * 2
def baseEnd_3913200 : Nat := 2009352497174194820703527

theorem tailTrace_3913200 : CollatzResearch.WordTrace tailWord_3913200 prefixEnd_3913200 2009352497174194820703527 := by
  unfold tailWord_3913200
  simp only [CollatzResearch.WordTrace]
  refine ⟨71363064711576098098664527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95150752948768130798219369 71363064711576098098664527)
  ·
    refine ⟨107044597067364147147996791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71363064711576098098664527 107044597067364147147996791)
    ·
      refine ⟨160566895601046220721995187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107044597067364147147996791 160566895601046220721995187)
      ·
        refine ⟨240850343401569331082992781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160566895601046220721995187 240850343401569331082992781)
        ·
          refine ⟨90318878775588499156122293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 240850343401569331082992781 90318878775588499156122293)
          ·
            refine ⟨8467394885211421795886465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90318878775588499156122293 8467394885211421795886465)
            ·
              refine ⟨6350546163908566346914849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8467394885211421795886465 6350546163908566346914849)
              ·
                refine ⟨4762909622931424760186137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6350546163908566346914849 4762909622931424760186137)
                ·
                  refine ⟨3572182217198568570139603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4762909622931424760186137 3572182217198568570139603)
                  ·
                    refine ⟨5358273325797852855209405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3572182217198568570139603 5358273325797852855209405)
                    ·
                      refine ⟨2009352497174194820703527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5358273325797852855209405 2009352497174194820703527)
                      ·
                        rfl

theorem cell23_3913200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 2, 2, 1, 3].length) (baseStart_3913200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913200 prefixEnd_3913200 := by exact prefixLift 3913200
  have htrace : WordTrace (prefixWord ++ tailWord_3913200) baseStart_3913200 baseEnd_3913200 := by
    simpa [prefixWord, tailWord_3913200, baseEnd_3913200] using wordTrace_append hprefix tailTrace_3913200
  have hstable : (prefixWord ++ tailWord_3913200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913200).length < 2 ^ (prefixWord ++ tailWord_3913200).sum := by decide
  have hdescent : baseEnd_3913200 < baseStart_3913200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913273 : List Nat := [1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3913273 : Nat := 118140960795 + 3913273 * 2 ^ 59
def prefixEnd_3913273 : Nat := 4983230072969 + 3 ^ 40 * 3913273 * 2
def baseEnd_3913273 : Nat := 2009389981261973035090691

theorem tailTrace_3913273 : CollatzResearch.WordTrace tailWord_3913273 prefixEnd_3913273 2009389981261973035090691 := by
  unfold tailWord_3913273
  simp only [CollatzResearch.WordTrace]
  refine ⟨142728791951887729664736473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95152527967925153109824315 142728791951887729664736473)
  ·
    refine ⟨107046593963915797248552355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142728791951887729664736473 107046593963915797248552355)
    ·
      refine ⟨160569890945873695872828533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107046593963915797248552355 160569890945873695872828533)
      ·
        refine ⟨15053427276175658988077675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160569890945873695872828533 15053427276175658988077675)
        ·
          refine ⟨22580140914263488482116513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15053427276175658988077675 22580140914263488482116513)
          ·
            refine ⟨16935105685697616361587385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22580140914263488482116513 16935105685697616361587385)
            ·
              refine ⟨12701329264273212271190539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16935105685697616361587385 12701329264273212271190539)
              ·
                refine ⟨19051993896409818406785809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12701329264273212271190539 19051993896409818406785809)
                ·
                  refine ⟨14288995422307363805089357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19051993896409818406785809 14288995422307363805089357)
                  ·
                    refine ⟨5358373283365261426908509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14288995422307363805089357 5358373283365261426908509)
                    ·
                      refine ⟨2009389981261973035090691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5358373283365261426908509 2009389981261973035090691)
                      ·
                        rfl

theorem cell23_3913273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3913273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913273 prefixEnd_3913273 := by exact prefixLift 3913273
  have htrace : WordTrace (prefixWord ++ tailWord_3913273) baseStart_3913273 baseEnd_3913273 := by
    simpa [prefixWord, tailWord_3913273, baseEnd_3913273] using wordTrace_append hprefix tailTrace_3913273
  have hstable : (prefixWord ++ tailWord_3913273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913273).length < 2 ^ (prefixWord ++ tailWord_3913273).sum := by decide
  have hdescent : baseEnd_3913273 < baseStart_3913273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913296 : List Nat := [2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_3913296 : Nat := 118140960795 + 3913296 * 2 ^ 59
def prefixEnd_3913296 : Nat := 4983230072969 + 3 ^ 40 * 3913296 * 2
def baseEnd_3913296 : Nat := 2009401791317026445103085

theorem tailTrace_3913296 : CollatzResearch.WordTrace tailWord_3913296 prefixEnd_3913296 2009401791317026445103085 := by
  unfold tailWord_3913296
  simp only [CollatzResearch.WordTrace]
  refine ⟨71364815415402202296411871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95153087220536269728549161 71364815415402202296411871)
  ·
    refine ⟨107047223123103303444617807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71364815415402202296411871 107047223123103303444617807)
    ·
      refine ⟨160570834684654955166926711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107047223123103303444617807 160570834684654955166926711)
      ·
        refine ⟨240856252026982432750390067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160570834684654955166926711 240856252026982432750390067)
        ·
          refine ⟨361284378040473649125585101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 240856252026982432750390067 361284378040473649125585101)
          ·
            refine ⟨135481641765177618422094413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361284378040473649125585101 135481641765177618422094413)
            ·
              refine ⟨50805615661941606908285405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135481641765177618422094413 50805615661941606908285405)
              ·
                refine ⟨19052105873228102590607027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50805615661941606908285405 19052105873228102590607027)
                ·
                  refine ⟨28578158809842153885910541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19052105873228102590607027 28578158809842153885910541)
                  ·
                    refine ⟨10716809553690807707216453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28578158809842153885910541 10716809553690807707216453)
                    ·
                      refine ⟨2009401791317026445103085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10716809553690807707216453 2009401791317026445103085)
                      ·
                        rfl

theorem cell23_3913296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_3913296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913296 prefixEnd_3913296 := by exact prefixLift 3913296
  have htrace : WordTrace (prefixWord ++ tailWord_3913296) baseStart_3913296 baseEnd_3913296 := by
    simpa [prefixWord, tailWord_3913296, baseEnd_3913296] using wordTrace_append hprefix tailTrace_3913296
  have hstable : (prefixWord ++ tailWord_3913296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913296).length < 2 ^ (prefixWord ++ tailWord_3913296).sum := by decide
  have hdescent : baseEnd_3913296 < baseStart_3913296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913313 : List Nat := [1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3913313 : Nat := 118140960795 + 3913313 * 2 ^ 59
def prefixEnd_3913313 : Nat := 4983230072969 + 3 ^ 40 * 3913313 * 2
def baseEnd_3913313 : Nat := 2009410520488152878590507

theorem tailTrace_3913313 : CollatzResearch.WordTrace tailWord_3913313 prefixEnd_3913313 2009410520488152878590507 := by
  unfold tailWord_3913313
  simp only [CollatzResearch.WordTrace]
  refine ⟨142730250871742816496192593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95153500581161877664128395 142730250871742816496192593)
  ·
    refine ⟨107047688153807112372144445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142730250871742816496192593 107047688153807112372144445)
    ·
      refine ⟨40142883057677667139554167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107047688153807112372144445 40142883057677667139554167)
      ·
        refine ⟨60214324586516500709331251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40142883057677667139554167 60214324586516500709331251)
        ·
          refine ⟨90321486879774751063996877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60214324586516500709331251 90321486879774751063996877)
          ·
            refine ⟨33870557579915531648998829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90321486879774751063996877 33870557579915531648998829)
            ·
              refine ⟨12701459092468324368374561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33870557579915531648998829 12701459092468324368374561)
              ·
                refine ⟨9526094319351243276280921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12701459092468324368374561 9526094319351243276280921)
                ·
                  refine ⟨7144570739513432457210691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9526094319351243276280921 7144570739513432457210691)
                  ·
                    refine ⟨10716856109270148685816037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7144570739513432457210691 10716856109270148685816037)
                    ·
                      refine ⟨2009410520488152878590507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10716856109270148685816037 2009410520488152878590507)
                      ·
                        rfl

theorem cell23_3913313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3913313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913313 prefixEnd_3913313 := by exact prefixLift 3913313
  have htrace : WordTrace (prefixWord ++ tailWord_3913313) baseStart_3913313 baseEnd_3913313 := by
    simpa [prefixWord, tailWord_3913313, baseEnd_3913313] using wordTrace_append hprefix tailTrace_3913313
  have hstable : (prefixWord ++ tailWord_3913313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913313).length < 2 ^ (prefixWord ++ tailWord_3913313).sum := by decide
  have hdescent : baseEnd_3913313 < baseStart_3913313 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913374 : List Nat := [4, 3, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_3913374 : Nat := 118140960795 + 3913374 * 2 ^ 59
def prefixEnd_3913374 : Nat := 4983230072969 + 3 ^ 40 * 3913374 * 2
def baseEnd_3913374 : Nat := 669813947602692379975909

theorem tailTrace_3913374 : CollatzResearch.WordTrace tailWord_3913374 prefixEnd_3913374 669813947602692379975909 := by
  unfold tailWord_3913374
  simp only [CollatzResearch.WordTrace]
  refine ⟨17841559465565227989270397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 95154983816347882609442117 17841559465565227989270397)
  ·
    refine ⟨6690584799586960495976399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17841559465565227989270397 6690584799586960495976399)
    ·
      refine ⟨10035877199380440743964599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6690584799586960495976399 10035877199380440743964599)
      ·
        refine ⟨15053815799070661115946899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10035877199380440743964599 15053815799070661115946899)
        ·
          refine ⟨22580723698605991673920349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15053815799070661115946899 22580723698605991673920349)
          ·
            refine ⟨8467771386977246877720131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22580723698605991673920349 8467771386977246877720131)
            ·
              refine ⟨12701657080465870316580197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8467771386977246877720131 12701657080465870316580197)
              ·
                refine ⟨2381560702587350684358787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12701657080465870316580197 2381560702587350684358787)
                ·
                  refine ⟨3572341053881026026538181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2381560702587350684358787 3572341053881026026538181)
                  ·
                    refine ⟨669813947602692379975909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3572341053881026026538181 669813947602692379975909)
                    ·
                      rfl

theorem cell23_3913374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_3913374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913374 prefixEnd_3913374 := by exact prefixLift 3913374
  have htrace : WordTrace (prefixWord ++ tailWord_3913374) baseStart_3913374 baseEnd_3913374 := by
    simpa [prefixWord, tailWord_3913374, baseEnd_3913374] using wordTrace_append hprefix tailTrace_3913374
  have hstable : (prefixWord ++ tailWord_3913374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913374).length < 2 ^ (prefixWord ++ tailWord_3913374).sum := by decide
  have hdescent : baseEnd_3913374 < baseStart_3913374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913413 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_3913413 : Nat := 118140960795 + 3913413 * 2 ^ 59
def prefixEnd_3913413 : Nat := 4983230072969 + 3 ^ 40 * 3913413 * 2
def baseEnd_3913413 : Nat := 669820622851200829113349

theorem tailTrace_3913413 : CollatzResearch.WordTrace tailWord_3913413 prefixEnd_3913413 669820622851200829113349 := by
  unfold tailWord_3913413
  simp only [CollatzResearch.WordTrace]
  refine ⟨142733898171380533574832893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95155932114253689049888595 142733898171380533574832893)
  ·
    refine ⟨53525211814267700090562335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142733898171380533574832893 53525211814267700090562335)
    ·
      refine ⟨80287817721401550135843503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53525211814267700090562335 80287817721401550135843503)
      ·
        refine ⟨120431726582102325203765255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80287817721401550135843503 120431726582102325203765255)
        ·
          refine ⟨180647589873153487805647883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120431726582102325203765255 180647589873153487805647883)
          ·
            refine ⟨270971384809730231708471825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180647589873153487805647883 270971384809730231708471825)
            ·
              refine ⟨203228538607297673781353869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 270971384809730231708471825 203228538607297673781353869)
              ·
                refine ⟨76210701977736627668007701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203228538607297673781353869 76210701977736627668007701)
                ·
                  refine ⟨3572376655206404421937861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 76210701977736627668007701 3572376655206404421937861)
                  ·
                    refine ⟨669820622851200829113349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3572376655206404421937861 669820622851200829113349)
                    ·
                      rfl

theorem cell23_3913413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_3913413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913413 prefixEnd_3913413 := by exact prefixLift 3913413
  have htrace : WordTrace (prefixWord ++ tailWord_3913413) baseStart_3913413 baseEnd_3913413 := by
    simpa [prefixWord, tailWord_3913413, baseEnd_3913413] using wordTrace_append hprefix tailTrace_3913413
  have hstable : (prefixWord ++ tailWord_3913413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913413).length < 2 ^ (prefixWord ++ tailWord_3913413).sum := by decide
  have hdescent : baseEnd_3913413 < baseStart_3913413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913450 : List Nat := [3, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4]
def baseStart_3913450 : Nat := 118140960795 + 3913450 * 2 ^ 59
def prefixEnd_3913450 : Nat := 4983230072969 + 3 ^ 40 * 3913450 * 2
def baseEnd_3913450 : Nat := 2009480867337818842577377

theorem tailTrace_3913450 : CollatzResearch.WordTrace tailWord_3913450 prefixEnd_3913450 2009480867337818842577377 := by
  unfold tailWord_3913450
  simp only [CollatzResearch.WordTrace]
  refine ⟨35683811918061622223482451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95156831781497659262619869 35683811918061622223482451)
  ·
    refine ⟨53525717877092433335223677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35683811918061622223482451 53525717877092433335223677)
    ·
      refine ⟨20072144203909662500708879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53525717877092433335223677 20072144203909662500708879)
      ·
        refine ⟨30108216305864493751063319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20072144203909662500708879 30108216305864493751063319)
        ·
          refine ⟨45162324458796740626594979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30108216305864493751063319 45162324458796740626594979)
          ·
            refine ⟨67743486688195110939892469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45162324458796740626594979 67743486688195110939892469)
            ·
              refine ⟨6350951877018291650614919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67743486688195110939892469 6350951877018291650614919)
              ·
                refine ⟨9526427815527437475922379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6350951877018291650614919 9526427815527437475922379)
                ·
                  refine ⟨14289641723291156213883569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9526427815527437475922379 14289641723291156213883569)
                  ·
                    refine ⟨10717231292468367160412677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14289641723291156213883569 10717231292468367160412677)
                    ·
                      refine ⟨2009480867337818842577377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10717231292468367160412677 2009480867337818842577377)
                      ·
                        rfl

theorem cell23_3913450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_3913450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913450 prefixEnd_3913450 := by exact prefixLift 3913450
  have htrace : WordTrace (prefixWord ++ tailWord_3913450) baseStart_3913450 baseEnd_3913450 := by
    simpa [prefixWord, tailWord_3913450, baseEnd_3913450] using wordTrace_append hprefix tailTrace_3913450
  have hstable : (prefixWord ++ tailWord_3913450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913450).length < 2 ^ (prefixWord ++ tailWord_3913450).sum := by decide
  have hdescent : baseEnd_3913450 < baseStart_3913450 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913457 : List Nat := [1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 3]
def baseStart_3913457 : Nat := 118140960795 + 3913457 * 2 ^ 59
def prefixEnd_3913457 : Nat := 4983230072969 + 3 ^ 40 * 3913457 * 2
def baseEnd_3913457 : Nat := 2009484461702400315189845

theorem tailTrace_3913457 : CollatzResearch.WordTrace tailWord_3913457 prefixEnd_3913457 2009484461702400315189845 := by
  unfold tailWord_3913457
  simp only [CollatzResearch.WordTrace]
  refine ⟨142735502983221129089434625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95157001988814086059623083 142735502983221129089434625)
  ·
    refine ⟨107051627237415846817075969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142735502983221129089434625 107051627237415846817075969)
    ·
      refine ⟨80288720428061885112806977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107051627237415846817075969 80288720428061885112806977)
      ·
        refine ⟨60216540321046413834605233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80288720428061885112806977 60216540321046413834605233)
        ·
          refine ⟨45162405240784810375953925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60216540321046413834605233 45162405240784810375953925)
          ·
            refine ⟨8467950982647151945491361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45162405240784810375953925 8467950982647151945491361)
            ·
              refine ⟨6350963236985363959118521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8467950982647151945491361 6350963236985363959118521)
              ·
                refine ⟨4763222427739022969338891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6350963236985363959118521 4763222427739022969338891)
                ·
                  refine ⟨7144833641608534454008337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763222427739022969338891 7144833641608534454008337)
                  ·
                    refine ⟨5358625231206400840506253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7144833641608534454008337 5358625231206400840506253)
                    ·
                      refine ⟨2009484461702400315189845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5358625231206400840506253 2009484461702400315189845)
                      ·
                        rfl

theorem cell23_3913457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_3913457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913457 prefixEnd_3913457 := by exact prefixLift 3913457
  have htrace : WordTrace (prefixWord ++ tailWord_3913457) baseStart_3913457 baseEnd_3913457 := by
    simpa [prefixWord, tailWord_3913457, baseEnd_3913457] using wordTrace_append hprefix tailTrace_3913457
  have hstable : (prefixWord ++ tailWord_3913457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913457).length < 2 ^ (prefixWord ++ tailWord_3913457).sum := by decide
  have hdescent : baseEnd_3913457 < baseStart_3913457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913503 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 1, 8]
def baseStart_3913503 : Nat := 118140960795 + 3913503 * 2 ^ 59
def prefixEnd_3913503 : Nat := 4983230072969 + 3 ^ 40 * 3913503 * 2
def baseEnd_3913503 : Nat := 669836027270835711738211

theorem tailTrace_3913503 : CollatzResearch.WordTrace tailWord_3913503 prefixEnd_3913503 669836027270835711738211 := by
  unfold tailWord_3913503
  simp only [CollatzResearch.WordTrace]
  refine ⟨142737180741054478945609163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95158120494036319297072775 142737180741054478945609163)
  ·
    refine ⟨214105771111581718418413745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142737180741054478945609163 214105771111581718418413745)
    ·
      refine ⟨160579328333686288813810309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214105771111581718418413745 160579328333686288813810309)
      ·
        refine ⟨30108624062566179152589433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160579328333686288813810309 30108624062566179152589433)
        ·
          refine ⟨22581468046924634364442075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30108624062566179152589433 22581468046924634364442075)
          ·
            refine ⟨33872202070386951546663113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22581468046924634364442075 33872202070386951546663113)
            ·
              refine ⟨25404151552790213659997335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33872202070386951546663113 25404151552790213659997335)
              ·
                refine ⟨38106227329185320489996003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25404151552790213659997335 38106227329185320489996003)
                ·
                  refine ⟨57159340993777980734994005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38106227329185320489996003 57159340993777980734994005)
                  ·
                    refine ⟨669836027270835711738211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 57159340993777980734994005 669836027270835711738211)
                    ·
                      rfl

theorem cell23_3913503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_3913503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913503 prefixEnd_3913503 := by exact prefixLift 3913503
  have htrace : WordTrace (prefixWord ++ tailWord_3913503) baseStart_3913503 baseEnd_3913503 := by
    simpa [prefixWord, tailWord_3913503, baseEnd_3913503] using wordTrace_append hprefix tailTrace_3913503
  have hstable : (prefixWord ++ tailWord_3913503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913503).length < 2 ^ (prefixWord ++ tailWord_3913503).sum := by decide
  have hdescent : baseEnd_3913503 < baseStart_3913503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913527 : List Nat := [1, 1, 3, 1, 2, 1, 2, 4, 4, 2, 2]
def baseStart_3913527 : Nat := 118140960795 + 3913527 * 2 ^ 59
def prefixEnd_3913527 : Nat := 4983230072969 + 3 ^ 40 * 3913527 * 2
def baseEnd_3913527 : Nat := 2009520405348215041314523

theorem tailTrace_3913527 : CollatzResearch.WordTrace tailWord_3913527 prefixEnd_3913527 2009520405348215041314523 := by
  unfold tailWord_3913527
  simp only [CollatzResearch.WordTrace]
  refine ⟨142738056092967531044482835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95158704061978354029655223 142738056092967531044482835)
  ·
    refine ⟨214107084139451296566724253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142738056092967531044482835 214107084139451296566724253)
    ·
      refine ⟨80290156552294236212521595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214107084139451296566724253 80290156552294236212521595)
      ·
        refine ⟨120435234828441354318782393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80290156552294236212521595 120435234828441354318782393)
        ·
          refine ⟨90326426121331015739086795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120435234828441354318782393 90326426121331015739086795)
          ·
            refine ⟨135489639181996523608630193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90326426121331015739086795 135489639181996523608630193)
            ·
              refine ⟨101617229386497392706472645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135489639181996523608630193 101617229386497392706472645)
              ·
                refine ⟨19053230509968261132463621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101617229386497392706472645 19053230509968261132463621)
                ·
                  refine ⟨3572480720619048962336929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19053230509968261132463621 3572480720619048962336929)
                  ·
                    refine ⟨2679360540464286721752697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3572480720619048962336929 2679360540464286721752697)
                    ·
                      refine ⟨2009520405348215041314523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679360540464286721752697 2009520405348215041314523)
                      ·
                        rfl

theorem cell23_3913527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 4, 4, 2, 2].length) (baseStart_3913527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913527 prefixEnd_3913527 := by exact prefixLift 3913527
  have htrace : WordTrace (prefixWord ++ tailWord_3913527) baseStart_3913527 baseEnd_3913527 := by
    simpa [prefixWord, tailWord_3913527, baseEnd_3913527] using wordTrace_append hprefix tailTrace_3913527
  have hstable : (prefixWord ++ tailWord_3913527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913527).length < 2 ^ (prefixWord ++ tailWord_3913527).sum := by decide
  have hdescent : baseEnd_3913527 < baseStart_3913527 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913530 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5]
def baseStart_3913530 : Nat := 118140960795 + 3913530 * 2 ^ 59
def prefixEnd_3913530 : Nat := 4983230072969 + 3 ^ 40 * 3913530 * 2
def baseEnd_3913530 : Nat := 2009521945790178529577009

theorem tailTrace_3913530 : CollatzResearch.WordTrace tailWord_3913530 prefixEnd_3913530 2009521945790178529577009 := by
  unfold tailWord_3913530
  simp only [CollatzResearch.WordTrace]
  refine ⟨35684541377989165639210511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95158777007971108371228029 35684541377989165639210511)
  ·
    refine ⟨53526812066983748458815767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35684541377989165639210511 53526812066983748458815767)
    ·
      refine ⟨80290218100475622688223651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53526812066983748458815767 80290218100475622688223651)
      ·
        refine ⟨120435327150713434032335477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80290218100475622688223651 120435327150713434032335477)
        ·
          refine ⟨11290811920379384440531451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120435327150713434032335477 11290811920379384440531451)
          ·
            refine ⟨16936217880569076660797177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11290811920379384440531451 16936217880569076660797177)
            ·
              refine ⟨12702163410426807495597883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16936217880569076660797177 12702163410426807495597883)
              ·
                refine ⟨19053245115640211243396825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12702163410426807495597883 19053245115640211243396825)
                ·
                  refine ⟨14289933836730158432547619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19053245115640211243396825 14289933836730158432547619)
                  ·
                    refine ⟨21434900755095237648821429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14289933836730158432547619 21434900755095237648821429)
                    ·
                      refine ⟨2009521945790178529577009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21434900755095237648821429 2009521945790178529577009)
                      ·
                        rfl

theorem cell23_3913530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 2, 1, 5].length) (baseStart_3913530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913530 prefixEnd_3913530 := by exact prefixLift 3913530
  have htrace : WordTrace (prefixWord ++ tailWord_3913530) baseStart_3913530 baseEnd_3913530 := by
    simpa [prefixWord, tailWord_3913530, baseEnd_3913530] using wordTrace_append hprefix tailTrace_3913530
  have hstable : (prefixWord ++ tailWord_3913530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913530).length < 2 ^ (prefixWord ++ tailWord_3913530).sum := by decide
  have hdescent : baseEnd_3913530 < baseStart_3913530 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913543 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_3913543 : Nat := 118140960795 + 3913543 * 2 ^ 59
def prefixEnd_3913543 : Nat := 4983230072969 + 3 ^ 40 * 3913543 * 2
def baseEnd_3913543 : Nat := 2009528621038686978714449

theorem tailTrace_3913543 : CollatzResearch.WordTrace tailWord_3913543 prefixEnd_3913543 2009528621038686978714449 := by
  unfold tailWord_3913543
  simp only [CollatzResearch.WordTrace]
  refine ⟨142738639660909565777065283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95159093107273043851376855 142738639660909565777065283)
  ·
    refine ⟨214107959491364348665597925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142738639660909565777065283 214107959491364348665597925)
    ·
      refine ⟨40145242404630815374799611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214107959491364348665597925 40145242404630815374799611)
      ·
        refine ⟨60217863606946223062199417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40145242404630815374799611 60217863606946223062199417)
        ·
          refine ⟨45163397705209667296649563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60217863606946223062199417 45163397705209667296649563)
          ·
            refine ⟨67745096557814500944974345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45163397705209667296649563 67745096557814500944974345)
            ·
              refine ⟨50808822418360875708730759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67745096557814500944974345 50808822418360875708730759)
              ·
                refine ⟨76213233627541313563096139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50808822418360875708730759 76213233627541313563096139)
                ·
                  refine ⟨114319850441311970344644209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76213233627541313563096139 114319850441311970344644209)
                  ·
                    refine ⟨85739887830983977758483157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114319850441311970344644209 85739887830983977758483157)
                    ·
                      refine ⟨2009528621038686978714449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 85739887830983977758483157 2009528621038686978714449)
                      ·
                        rfl

theorem cell23_3913543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_3913543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913543 prefixEnd_3913543 := by exact prefixLift 3913543
  have htrace : WordTrace (prefixWord ++ tailWord_3913543) baseStart_3913543 baseEnd_3913543 := by
    simpa [prefixWord, tailWord_3913543, baseEnd_3913543] using wordTrace_append hprefix tailTrace_3913543
  have hstable : (prefixWord ++ tailWord_3913543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913543).length < 2 ^ (prefixWord ++ tailWord_3913543).sum := by decide
  have hdescent : baseEnd_3913543 < baseStart_3913543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913544 : List Nat := [2, 1, 3, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_3913544 : Nat := 118140960795 + 3913544 * 2 ^ 59
def prefixEnd_3913544 : Nat := 4983230072969 + 3 ^ 40 * 3913544 * 2
def baseEnd_3913544 : Nat := 2009529134519341474801945

theorem tailTrace_3913544 : CollatzResearch.WordTrace tailWord_3913544 prefixEnd_3913544 2009529134519341474801945 := by
  unfold tailWord_3913544
  simp only [CollatzResearch.WordTrace]
  refine ⟨71369338066952971473925843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95159117422603961965234457 71369338066952971473925843)
  ·
    refine ⟨107054007100429457210888765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71369338066952971473925843 107054007100429457210888765)
    ·
      refine ⟨40145252662661046454083287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107054007100429457210888765 40145252662661046454083287)
      ·
        refine ⟨60217878993991569681124931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40145252662661046454083287 60217878993991569681124931)
        ·
          refine ⟨90326818490987354521687397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60217878993991569681124931 90326818490987354521687397)
          ·
            refine ⟨16936278467060128972816387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90326818490987354521687397 16936278467060128972816387)
            ·
              refine ⟨25404417700590193459224581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16936278467060128972816387 25404417700590193459224581)
              ·
                refine ⟨4763328318860661273604609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25404417700590193459224581 4763328318860661273604609)
                ·
                  refine ⟨3572496239145495955203457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4763328318860661273604609 3572496239145495955203457)
                  ·
                    refine ⟨2679372179359121966402593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3572496239145495955203457 2679372179359121966402593)
                    ·
                      refine ⟨2009529134519341474801945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679372179359121966402593 2009529134519341474801945)
                      ·
                        rfl

theorem cell23_3913544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_3913544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913544 prefixEnd_3913544 := by exact prefixLift 3913544
  have htrace : WordTrace (prefixWord ++ tailWord_3913544) baseStart_3913544 baseEnd_3913544 := by
    simpa [prefixWord, tailWord_3913544, baseEnd_3913544] using wordTrace_append hprefix tailTrace_3913544
  have hstable : (prefixWord ++ tailWord_3913544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913544).length < 2 ^ (prefixWord ++ tailWord_3913544).sum := by decide
  have hdescent : baseEnd_3913544 < baseStart_3913544 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913580 : List Nat := [2, 2, 1, 1, 4, 3, 1, 1, 1, 7]
def baseStart_3913580 : Nat := 118140960795 + 3913580 * 2 ^ 59
def prefixEnd_3913580 : Nat := 4983230072969 + 3 ^ 40 * 3913580 * 2
def baseEnd_3913580 : Nat := 669849206607634444650593

theorem tailTrace_3913580 : CollatzResearch.WordTrace tailWord_3913580 prefixEnd_3913580 669849206607634444650593 := by
  unfold tailWord_3913580
  simp only [CollatzResearch.WordTrace]
  refine ⟨71369994580887760548081097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95159992774517014064108129 71369994580887760548081097)
  ·
    refine ⟨53527495935665820411060823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71369994580887760548081097 53527495935665820411060823)
    ·
      refine ⟨80291243903498730616591235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53527495935665820411060823 80291243903498730616591235)
      ·
        refine ⟨120436865855248095924886853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80291243903498730616591235 120436865855248095924886853)
        ·
          refine ⟨22581912347859017985916285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120436865855248095924886853 22581912347859017985916285)
          ·
            refine ⟨8468217130447131744718607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22581912347859017985916285 8468217130447131744718607)
            ·
              refine ⟨12702325695670697617077911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468217130447131744718607 12702325695670697617077911)
              ·
                refine ⟨19053488543506046425616867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12702325695670697617077911 19053488543506046425616867)
                ·
                  refine ⟨28580232815259069638425301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19053488543506046425616867 28580232815259069638425301)
                  ·
                    refine ⟨669849206607634444650593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 28580232815259069638425301 669849206607634444650593)
                    ·
                      rfl

theorem cell23_3913580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 7].length) (baseStart_3913580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913580 prefixEnd_3913580 := by exact prefixLift 3913580
  have htrace : WordTrace (prefixWord ++ tailWord_3913580) baseStart_3913580 baseEnd_3913580 := by
    simpa [prefixWord, tailWord_3913580, baseEnd_3913580] using wordTrace_append hprefix tailTrace_3913580
  have hstable : (prefixWord ++ tailWord_3913580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913580).length < 2 ^ (prefixWord ++ tailWord_3913580).sum := by decide
  have hdescent : baseEnd_3913580 < baseStart_3913580 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913600 : List Nat := [2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_3913600 : Nat := 118140960795 + 3913600 * 2 ^ 59
def prefixEnd_3913600 : Nat := 4983230072969 + 3 ^ 40 * 3913600 * 2
def baseEnd_3913600 : Nat := 2009557889435993255701687

theorem tailTrace_3913600 : CollatzResearch.WordTrace tailWord_3913600 prefixEnd_3913600 2009557889435993255701687 := by
  unfold tailWord_3913600
  simp only [CollatzResearch.WordTrace]
  refine ⟨71370359310851532255945127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95160479081135376341260169 71370359310851532255945127)
  ·
    refine ⟨107055538966277298383917691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71370359310851532255945127 107055538966277298383917691)
    ·
      refine ⟨160583308449415947575876537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107055538966277298383917691 160583308449415947575876537)
      ·
        refine ⟨120437481337061960681907403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160583308449415947575876537 120437481337061960681907403)
        ·
          refine ⟨180656222005592941022861105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120437481337061960681907403 180656222005592941022861105)
          ·
            refine ⟨135492166504194705767145829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180656222005592941022861105 135492166504194705767145829)
            ·
              refine ⟨25404781219536507331339843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135492166504194705767145829 25404781219536507331339843)
              ·
                refine ⟨38107171829304760997009765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25404781219536507331339843 38107171829304760997009765)
                ·
                  refine ⟨7145094717994642686939331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38107171829304760997009765 7145094717994642686939331)
                  ·
                    refine ⟨10717642076991964030408997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7145094717994642686939331 10717642076991964030408997)
                    ·
                      refine ⟨2009557889435993255701687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10717642076991964030408997 2009557889435993255701687)
                      ·
                        rfl

theorem cell23_3913600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_3913600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913600 prefixEnd_3913600 := by exact prefixLift 3913600
  have htrace : WordTrace (prefixWord ++ tailWord_3913600) baseStart_3913600 baseEnd_3913600 := by
    simpa [prefixWord, tailWord_3913600, baseEnd_3913600] using wordTrace_append hprefix tailTrace_3913600
  have hstable : (prefixWord ++ tailWord_3913600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913600).length < 2 ^ (prefixWord ++ tailWord_3913600).sum := by decide
  have hdescent : baseEnd_3913600 < baseStart_3913600 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913617 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 2, 4, 2]
def baseStart_3913617 : Nat := 118140960795 + 3913617 * 2 ^ 59
def prefixEnd_3913617 : Nat := 4983230072969 + 3 ^ 40 * 3913617 * 2
def baseEnd_3913617 : Nat := 2009566618607119689189109

theorem tailTrace_3913617 : CollatzResearch.WordTrace tailWord_3913617 prefixEnd_3913617 2009566618607119689189109 := by
  unfold tailWord_3913617
  simp only [CollatzResearch.WordTrace]
  refine ⟨142741338662641476415259105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95160892441760984276839403 142741338662641476415259105)
  ·
    refine ⟨107056003996981107311444329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142741338662641476415259105 107056003996981107311444329)
    ·
      refine ⟨80292002997735830483583247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107056003996981107311444329 80292002997735830483583247)
      ·
        refine ⟨120438004496603745725374871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80292002997735830483583247 120438004496603745725374871)
        ·
          refine ⟨180657006744905618588062307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120438004496603745725374871 180657006744905618588062307)
          ·
            refine ⟨270985510117358427882093461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180657006744905618588062307 270985510117358427882093461)
            ·
              refine ⟨12702445786751176306973131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 270985510117358427882093461 12702445786751176306973131)
              ·
                refine ⟨19053668680126764460459697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12702445786751176306973131 19053668680126764460459697)
                ·
                  refine ⟨14290251510095073345344773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19053668680126764460459697 14290251510095073345344773)
                  ·
                    refine ⟨2679422158142826252252145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 14290251510095073345344773 2679422158142826252252145)
                    ·
                      refine ⟨2009566618607119689189109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679422158142826252252145 2009566618607119689189109)
                      ·
                        rfl

theorem cell23_3913617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 4, 2].length) (baseStart_3913617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913617 prefixEnd_3913617 := by exact prefixLift 3913617
  have htrace : WordTrace (prefixWord ++ tailWord_3913617) baseStart_3913617 baseEnd_3913617 := by
    simpa [prefixWord, tailWord_3913617, baseEnd_3913617] using wordTrace_append hprefix tailTrace_3913617
  have hstable : (prefixWord ++ tailWord_3913617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913617).length < 2 ^ (prefixWord ++ tailWord_3913617).sum := by decide
  have hdescent : baseEnd_3913617 < baseStart_3913617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913684 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3913684 : Nat := 118140960795 + 3913684 * 2 ^ 59
def prefixEnd_3913684 : Nat := 4983230072969 + 3 ^ 40 * 3913684 * 2
def baseEnd_3913684 : Nat := 2009601021810970927051301

theorem tailTrace_3913684 : CollatzResearch.WordTrace tailWord_3913684 prefixEnd_3913684 2009601021810970927051301 := by
  unfold tailWord_3913684
  simp only [CollatzResearch.WordTrace]
  refine ⟨71371891176699373428974053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95162521568932497905298737 71371891176699373428974053)
  ·
    refine ⟨13382229595631132517932635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71371891176699373428974053 13382229595631132517932635)
    ·
      refine ⟨20073344393446698776898953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13382229595631132517932635 20073344393446698776898953)
      ·
        refine ⟨15055008295085024082674215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20073344393446698776898953 15055008295085024082674215)
        ·
          refine ⟨22582512442627536124011323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055008295085024082674215 22582512442627536124011323)
          ·
            refine ⟨33873768663941304186016985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22582512442627536124011323 33873768663941304186016985)
            ·
              refine ⟨25405326497955978139512739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33873768663941304186016985 25405326497955978139512739)
              ·
                refine ⟨38107989746933967209269109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25405326497955978139512739 38107989746933967209269109)
                ·
                  refine ⟨3572624038775059425868979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38107989746933967209269109 3572624038775059425868979)
                  ·
                    refine ⟨5358936058162589138803469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3572624038775059425868979 5358936058162589138803469)
                    ·
                      refine ⟨2009601021810970927051301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5358936058162589138803469 2009601021810970927051301)
                      ·
                        rfl

theorem cell23_3913684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3913684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913684 prefixEnd_3913684 := by exact prefixLift 3913684
  have htrace : WordTrace (prefixWord ++ tailWord_3913684) baseStart_3913684 baseEnd_3913684 := by
    simpa [prefixWord, tailWord_3913684, baseEnd_3913684] using wordTrace_append hprefix tailTrace_3913684
  have hstable : (prefixWord ++ tailWord_3913684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913684).length < 2 ^ (prefixWord ++ tailWord_3913684).sum := by decide
  have hdescent : baseEnd_3913684 < baseStart_3913684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913707 : List Nat := [1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 4]
def baseStart_3913707 : Nat := 118140960795 + 3913707 * 2 ^ 59
def prefixEnd_3913707 : Nat := 4983230072969 + 3 ^ 40 * 3913707 * 2
def baseEnd_3913707 : Nat := 2009612831866024337063695

theorem tailTrace_3913707 : CollatzResearch.WordTrace tailWord_3913707 prefixEnd_3913707 2009612831866024337063695 := by
  unfold tailWord_3913707
  simp only [CollatzResearch.WordTrace]
  refine ⟨142744621232315421786035375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95163080821543614524023583 142744621232315421786035375)
  ·
    refine ⟨214116931848473132679053063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142744621232315421786035375 214116931848473132679053063)
    ·
      refine ⟨321175397772709699018579595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214116931848473132679053063 321175397772709699018579595)
      ·
        refine ⟨481763096659064548527869393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321175397772709699018579595 481763096659064548527869393)
        ·
          refine ⟨361322322494298411395902045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 481763096659064548527869393 361322322494298411395902045)
          ·
            refine ⟨135495870935361904273463267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361322322494298411395902045 135495870935361904273463267)
            ·
              refine ⟨203243806403042856410194901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135495870935361904273463267 203243806403042856410194901)
              ·
                refine ⟨4763526712571316947113943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 203243806403042856410194901 4763526712571316947113943)
                ·
                  refine ⟨7145290068856975420670915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763526712571316947113943 7145290068856975420670915)
                  ·
                    refine ⟨10717935103285463131006373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7145290068856975420670915 10717935103285463131006373)
                    ·
                      refine ⟨2009612831866024337063695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10717935103285463131006373 2009612831866024337063695)
                      ·
                        rfl

theorem cell23_3913707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 7, 1, 1, 4].length) (baseStart_3913707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913707 prefixEnd_3913707 := by exact prefixLift 3913707
  have htrace : WordTrace (prefixWord ++ tailWord_3913707) baseStart_3913707 baseEnd_3913707 := by
    simpa [prefixWord, tailWord_3913707, baseEnd_3913707] using wordTrace_append hprefix tailTrace_3913707
  have hstable : (prefixWord ++ tailWord_3913707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913707).length < 2 ^ (prefixWord ++ tailWord_3913707).sum := by decide
  have hdescent : baseEnd_3913707 < baseStart_3913707 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913720 : List Nat := [2, 1, 2, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_3913720 : Nat := 118140960795 + 3913720 * 2 ^ 59
def prefixEnd_3913720 : Nat := 4983230072969 + 3 ^ 40 * 3913720 * 2
def baseEnd_3913720 : Nat := 2009619507114532786201135

theorem tailTrace_3913720 : CollatzResearch.WordTrace tailWord_3913720 prefixEnd_3913720 2009619507114532786201135 := by
  unfold tailWord_3913720
  simp only [CollatzResearch.WordTrace]
  refine ⟨71372547690634162503129307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95163396920845550004172409 71372547690634162503129307)
  ·
    refine ⟨107058821535951243754693961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71372547690634162503129307 107058821535951243754693961)
    ·
      refine ⟨80294116151963432816020471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107058821535951243754693961 80294116151963432816020471)
      ·
        refine ⟨120441174227945149224030707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80294116151963432816020471 120441174227945149224030707)
        ·
          refine ⟨180661761341917723836046061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120441174227945149224030707 180661761341917723836046061)
          ·
            refine ⟨67748160503219146438517273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180661761341917723836046061 67748160503219146438517273)
            ·
              refine ⟨50811120377414359828887955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67748160503219146438517273 50811120377414359828887955)
              ·
                refine ⟨76216680566121539743331933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50811120377414359828887955 76216680566121539743331933)
                ·
                  refine ⟨28581255212295577403749475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76216680566121539743331933 28581255212295577403749475)
                  ·
                    refine ⟨42871882818443366105624213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28581255212295577403749475 42871882818443366105624213)
                    ·
                      refine ⟨2009619507114532786201135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 42871882818443366105624213 2009619507114532786201135)
                      ·
                        rfl

theorem cell23_3913720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_3913720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913720 prefixEnd_3913720 := by exact prefixLift 3913720
  have htrace : WordTrace (prefixWord ++ tailWord_3913720) baseStart_3913720 baseEnd_3913720 := by
    simpa [prefixWord, tailWord_3913720, baseEnd_3913720] using wordTrace_append hprefix tailTrace_3913720
  have hstable : (prefixWord ++ tailWord_3913720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913720).length < 2 ^ (prefixWord ++ tailWord_3913720).sum := by decide
  have hdescent : baseEnd_3913720 < baseStart_3913720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913761 : List Nat := [1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3913761 : Nat := 118140960795 + 3913761 * 2 ^ 59
def prefixEnd_3913761 : Nat := 4983230072969 + 3 ^ 40 * 3913761 * 2
def baseEnd_3913761 : Nat := 2009640559821367125788447

theorem tailTrace_3913761 : CollatzResearch.WordTrace tailWord_3913761 prefixEnd_3913761 2009640559821367125788447 := by
  unfold tailWord_3913761
  simp only [CollatzResearch.WordTrace]
  refine ⟨142746590774119789008501137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95164393849413192672334091 142746590774119789008501137)
  ·
    refine ⟨107059943080589841756375853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142746590774119789008501137 107059943080589841756375853)
    ·
      refine ⟨40147478655221190658640945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107059943080589841756375853 40147478655221190658640945)
      ·
        refine ⟨30110608991415892993980709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40147478655221190658640945 30110608991415892993980709)
        ·
          refine ⟨5645739185890479936371383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30110608991415892993980709 5645739185890479936371383)
          ·
            refine ⟨8468608778835719904557075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5645739185890479936371383 8468608778835719904557075)
            ·
              refine ⟨12702913168253579856835613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468608778835719904557075 12702913168253579856835613)
              ·
                refine ⟨4763592438095092446313355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12702913168253579856835613 4763592438095092446313355)
                ·
                  refine ⟨7145388657142638669470033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763592438095092446313355 7145388657142638669470033)
                  ·
                    refine ⟨5359041492856979002102525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7145388657142638669470033 5359041492856979002102525)
                    ·
                      refine ⟨2009640559821367125788447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5359041492856979002102525 2009640559821367125788447)
                      ·
                        rfl

theorem cell23_3913761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3913761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913761 prefixEnd_3913761 := by exact prefixLift 3913761
  have htrace : WordTrace (prefixWord ++ tailWord_3913761) baseStart_3913761 baseEnd_3913761 := by
    simpa [prefixWord, tailWord_3913761, baseEnd_3913761] using wordTrace_append hprefix tailTrace_3913761
  have hstable : (prefixWord ++ tailWord_3913761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913761).length < 2 ^ (prefixWord ++ tailWord_3913761).sum := by decide
  have hdescent : baseEnd_3913761 < baseStart_3913761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913801 : List Nat := [1, 2, 1, 1, 2, 2, 6, 2, 1, 3, 2]
def baseStart_3913801 : Nat := 118140960795 + 3913801 * 2 ^ 59
def prefixEnd_3913801 : Nat := 4983230072969 + 3 ^ 40 * 3913801 * 2
def baseEnd_3913801 : Nat := 2009661099047546969288263

theorem tailTrace_3913801 : CollatzResearch.WordTrace tailWord_3913801 prefixEnd_3913801 2009661099047546969288263 := by
  unfold tailWord_3913801
  simp only [CollatzResearch.WordTrace]
  refine ⟨142748049693974875839957257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95165366462649917226638171 142748049693974875839957257)
  ·
    refine ⟨107061037270481156879967943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142748049693974875839957257 107061037270481156879967943)
    ·
      refine ⟨160591555905721735319951915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107061037270481156879967943 160591555905721735319951915)
      ·
        refine ⟨240887333858582602979927873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160591555905721735319951915 240887333858582602979927873)
        ·
          refine ⟨180665500393936952234945905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 240887333858582602979927873 180665500393936952234945905)
          ·
            refine ⟨135499125295452714176209429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180665500393936952234945905 135499125295452714176209429)
            ·
              refine ⟨6351521498224345977009817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 135499125295452714176209429 6351521498224345977009817)
              ·
                refine ⟨4763641123668259482757363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6351521498224345977009817 4763641123668259482757363)
                ·
                  refine ⟨7145461685502389224136045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4763641123668259482757363 7145461685502389224136045)
                  ·
                    refine ⟨2679548132063395959051017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7145461685502389224136045 2679548132063395959051017)
                    ·
                      refine ⟨2009661099047546969288263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679548132063395959051017 2009661099047546969288263)
                      ·
                        rfl

theorem cell23_3913801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 6, 2, 1, 3, 2].length) (baseStart_3913801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913801 prefixEnd_3913801 := by exact prefixLift 3913801
  have htrace : WordTrace (prefixWord ++ tailWord_3913801) baseStart_3913801 baseEnd_3913801 := by
    simpa [prefixWord, tailWord_3913801, baseEnd_3913801] using wordTrace_append hprefix tailTrace_3913801
  have hstable : (prefixWord ++ tailWord_3913801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913801).length < 2 ^ (prefixWord ++ tailWord_3913801).sum := by decide
  have hdescent : baseEnd_3913801 < baseStart_3913801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913817 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 5]
def baseStart_3913817 : Nat := 118140960795 + 3913817 * 2 ^ 59
def prefixEnd_3913817 : Nat := 4983230072969 + 3 ^ 40 * 3913817 * 2
def baseEnd_3913817 : Nat := 2009669314738018906688189

theorem tailTrace_3913817 : CollatzResearch.WordTrace tailWord_3913817 prefixEnd_3913817 2009669314738018906688189 := by
  unfold tailWord_3913817
  simp only [CollatzResearch.WordTrace]
  refine ⟨142748633261916910572539705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95165755507944607048359803 142748633261916910572539705)
  ·
    refine ⟨107061474946437682929404779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142748633261916910572539705 107061474946437682929404779)
    ·
      refine ⟨160592212419656524394107169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107061474946437682929404779 160592212419656524394107169)
      ·
        refine ⟨120444159314742393295580377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160592212419656524394107169 120444159314742393295580377)
        ·
          refine ⟨90333119486056794971685283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120444159314742393295580377 90333119486056794971685283)
          ·
            refine ⟨135499679229085192457527925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90333119486056794971685283 135499679229085192457527925)
            ·
              refine ⟨12703094927726736792893243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135499679229085192457527925 12703094927726736792893243)
              ·
                refine ⟨19054642391590105189339865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12703094927726736792893243 19054642391590105189339865)
                ·
                  refine ⟨14290981793692578892004899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19054642391590105189339865 14290981793692578892004899)
                  ·
                    refine ⟨21436472690538868338007349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14290981793692578892004899 21436472690538868338007349)
                    ·
                      refine ⟨2009669314738018906688189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21436472690538868338007349 2009669314738018906688189)
                      ·
                        rfl

theorem cell23_3913817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_3913817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913817 prefixEnd_3913817 := by exact prefixLift 3913817
  have htrace : WordTrace (prefixWord ++ tailWord_3913817) baseStart_3913817 baseEnd_3913817 := by
    simpa [prefixWord, tailWord_3913817, baseEnd_3913817] using wordTrace_append hprefix tailTrace_3913817
  have hstable : (prefixWord ++ tailWord_3913817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913817).length < 2 ^ (prefixWord ++ tailWord_3913817).sum := by decide
  have hdescent : baseEnd_3913817 < baseStart_3913817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913827 : List Nat := [1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3913827 : Nat := 118140960795 + 3913827 * 2 ^ 59
def prefixEnd_3913827 : Nat := 4983230072969 + 3 ^ 40 * 3913827 * 2
def baseEnd_3913827 : Nat := 2009674449544563867563143

theorem tailTrace_3913827 : CollatzResearch.WordTrace tailWord_3913827 prefixEnd_3913827 2009674449544563867563143 := by
  unfold tailWord_3913827
  simp only [CollatzResearch.WordTrace]
  refine ⟨142748997991880682280403735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95165998661253788186935823 142748997991880682280403735)
  ·
    refine ⟨214123496987821023420605603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142748997991880682280403735 214123496987821023420605603)
    ·
      refine ⟨321185245481731535130908405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214123496987821023420605603 321185245481731535130908405)
      ·
        refine ⟨30111116763912331418522663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321185245481731535130908405 30111116763912331418522663)
        ·
          refine ⟨45166675145868497127783995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30111116763912331418522663 45166675145868497127783995)
          ·
            refine ⟨67750012718802745691675993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45166675145868497127783995 67750012718802745691675993)
            ·
              refine ⟨50812509539102059268756995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67750012718802745691675993 50812509539102059268756995)
              ·
                refine ⟨76218764308653088903135493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50812509539102059268756995 76218764308653088903135493)
                ·
                  refine ⟨14291018307872454169337905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76218764308653088903135493 14291018307872454169337905)
                  ·
                    refine ⟨10718263730904340627003429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14291018307872454169337905 10718263730904340627003429)
                    ·
                      refine ⟨2009674449544563867563143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 10718263730904340627003429 2009674449544563867563143)
                      ·
                        rfl

theorem cell23_3913827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3913827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913827 prefixEnd_3913827 := by exact prefixLift 3913827
  have htrace : WordTrace (prefixWord ++ tailWord_3913827) baseStart_3913827 baseEnd_3913827 := by
    simpa [prefixWord, tailWord_3913827, baseEnd_3913827] using wordTrace_append hprefix tailTrace_3913827
  have hstable : (prefixWord ++ tailWord_3913827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913827).length < 2 ^ (prefixWord ++ tailWord_3913827).sum := by decide
  have hdescent : baseEnd_3913827 < baseStart_3913827 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913831 : List Nat := [1, 1, 5, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_3913831 : Nat := 118140960795 + 3913831 * 2 ^ 59
def prefixEnd_3913831 : Nat := 4983230072969 + 3 ^ 40 * 3913831 * 2
def baseEnd_3913831 : Nat := 2009676503467181851913125

theorem tailTrace_3913831 : CollatzResearch.WordTrace tailWord_3913831 prefixEnd_3913831 2009676503467181851913125 := by
  unfold tailWord_3913831
  simp only [CollatzResearch.WordTrace]
  refine ⟨142749143883866190963549347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95166095922577460642366231 142749143883866190963549347)
  ·
    refine ⟨214123715825799286445324021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142749143883866190963549347 214123715825799286445324021)
    ·
      refine ⟨20074098358668683104249127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214123715825799286445324021 20074098358668683104249127)
      ·
        refine ⟨30111147538003024656373691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20074098358668683104249127 30111147538003024656373691)
        ·
          refine ⟨45166721307004536984560537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30111147538003024656373691 45166721307004536984560537)
          ·
            refine ⟨33875040980253402738420403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45166721307004536984560537 33875040980253402738420403)
            ·
              refine ⟨50812561470380104107630605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33875040980253402738420403 50812561470380104107630605)
              ·
                refine ⟨19054710551392539040361477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50812561470380104107630605 19054710551392539040361477)
                ·
                  refine ⟨3572758228386101070067777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19054710551392539040361477 3572758228386101070067777)
                  ·
                    refine ⟨2679568671289575802550833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3572758228386101070067777 2679568671289575802550833)
                    ·
                      refine ⟨2009676503467181851913125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2679568671289575802550833 2009676503467181851913125)
                      ·
                        rfl

theorem cell23_3913831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_3913831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913831 prefixEnd_3913831 := by exact prefixLift 3913831
  have htrace : WordTrace (prefixWord ++ tailWord_3913831) baseStart_3913831 baseEnd_3913831 := by
    simpa [prefixWord, tailWord_3913831, baseEnd_3913831] using wordTrace_append hprefix tailTrace_3913831
  have hstable : (prefixWord ++ tailWord_3913831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913831).length < 2 ^ (prefixWord ++ tailWord_3913831).sum := by decide
  have hdescent : baseEnd_3913831 < baseStart_3913831 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913877 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_3913877 : Nat := 118140960795 + 3913877 * 2 ^ 59
def prefixEnd_3913877 : Nat := 4983230072969 + 3 ^ 40 * 3913877 * 2
def baseEnd_3913877 : Nat := 2009700123577288671937913

theorem tailTrace_3913877 : CollatzResearch.WordTrace tailWord_3913877 prefixEnd_3913877 2009700123577288671937913 := by
  unfold tailWord_3913877
  simp only [CollatzResearch.WordTrace]
  refine ⟨142750821641699540819723885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 95167214427799693879815923 142750821641699540819723885)
  ·
    refine ⟨53531558115637327807396457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142750821641699540819723885 53531558115637327807396457)
    ·
      refine ⟨40148668586727995855547343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53531558115637327807396457 40148668586727995855547343)
      ·
        refine ⟨60223002880091993783321015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40148668586727995855547343 60223002880091993783321015)
        ·
          refine ⟨90334504320137990674981523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60223002880091993783321015 90334504320137990674981523)
          ·
            refine ⟨135501756480206986012472285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90334504320137990674981523 135501756480206986012472285)
            ·
              refine ⟨50813158680077619754677107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135501756480206986012472285 50813158680077619754677107)
              ·
                refine ⟨76219738020116429632015661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50813158680077619754677107 76219738020116429632015661)
                ·
                  refine ⟨28582401757543661112005873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76219738020116429632015661 28582401757543661112005873)
                  ·
                    refine ⟨21436801318157745834004405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28582401757543661112005873 21436801318157745834004405)
                    ·
                      refine ⟨2009700123577288671937913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 21436801318157745834004405 2009700123577288671937913)
                      ·
                        rfl

theorem cell23_3913877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_3913877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913877 prefixEnd_3913877 := by exact prefixLift 3913877
  have htrace : WordTrace (prefixWord ++ tailWord_3913877) baseStart_3913877 baseEnd_3913877 := by
    simpa [prefixWord, tailWord_3913877, baseEnd_3913877] using wordTrace_append hprefix tailTrace_3913877
  have hstable : (prefixWord ++ tailWord_3913877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913877).length < 2 ^ (prefixWord ++ tailWord_3913877).sum := by decide
  have hdescent : baseEnd_3913877 < baseStart_3913877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913884 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 2, 5]
def baseStart_3913884 : Nat := 118140960795 + 3913884 * 2 ^ 59
def prefixEnd_3913884 : Nat := 4983230072969 + 3 ^ 40 * 3913884 * 2
def baseEnd_3913884 : Nat := 669901239313956714850127

theorem tailTrace_3913884 : CollatzResearch.WordTrace tailWord_3913884 prefixEnd_3913884 669901239313956714850127 := by
  unfold tailWord_3913884
  simp only [CollatzResearch.WordTrace]
  refine ⟨71375538476337090507614353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95167384635116120676819137 71375538476337090507614353)
  ·
    refine ⟨53531653857252817880710765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71375538476337090507614353 53531653857252817880710765)
    ·
      refine ⟨20074370196469806705266537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53531653857252817880710765 20074370196469806705266537)
      ·
        refine ⟨15055777647352355028949903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20074370196469806705266537 15055777647352355028949903)
        ·
          refine ⟨22583666471028532543424855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15055777647352355028949903 22583666471028532543424855)
          ·
            refine ⟨33875499706542798815137283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22583666471028532543424855 33875499706542798815137283)
            ·
              refine ⟨50813249559814198222705925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33875499706542798815137283 50813249559814198222705925)
              ·
                refine ⟨9527484292465162166757361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50813249559814198222705925 9527484292465162166757361)
                ·
                  refine ⟨7145613219348871625068021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9527484292465162166757361 7145613219348871625068021)
                  ·
                    refine ⟨669901239313956714850127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7145613219348871625068021 669901239313956714850127)
                    ·
                      rfl

theorem cell23_3913884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_3913884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913884 prefixEnd_3913884 := by exact prefixLift 3913884
  have htrace : WordTrace (prefixWord ++ tailWord_3913884) baseStart_3913884 baseEnd_3913884 := by
    simpa [prefixWord, tailWord_3913884, baseEnd_3913884] using wordTrace_append hprefix tailTrace_3913884
  have hstable : (prefixWord ++ tailWord_3913884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913884).length < 2 ^ (prefixWord ++ tailWord_3913884).sum := by decide
  have hdescent : baseEnd_3913884 < baseStart_3913884 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913888 : List Nat := [2, 1, 1, 4, 2, 4, 2, 2, 5]
def baseStart_3913888 : Nat := 118140960795 + 3913888 * 2 ^ 59
def prefixEnd_3913888 : Nat := 4983230072969 + 3 ^ 40 * 3913888 * 2
def baseEnd_3913888 : Nat := 223300641318276458766707

theorem tailTrace_3913888 : CollatzResearch.WordTrace tailWord_3913888 prefixEnd_3913888 223300641318276458766707 := by
  unfold tailWord_3913888
  simp only [CollatzResearch.WordTrace]
  refine ⟨71375611422329844849187159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 95167481896439793132249545 71375611422329844849187159)
  ·
    refine ⟨107063417133494767273780739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71375611422329844849187159 107063417133494767273780739)
    ·
      refine ⟨160595125700242150910671109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107063417133494767273780739 160595125700242150910671109)
      ·
        refine ⟨30111586068795403295750833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160595125700242150910671109 30111586068795403295750833)
        ·
          refine ⟨22583689551596552471813125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30111586068795403295750833 22583689551596552471813125)
          ·
            refine ⟨4234441790924353588464961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 22583689551596552471813125 4234441790924353588464961)
            ·
              refine ⟨3175831343193265191348721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4234441790924353588464961 3175831343193265191348721)
              ·
                refine ⟨2381873507394948893511541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3175831343193265191348721 2381873507394948893511541)
                ·
                  refine ⟨223300641318276458766707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2381873507394948893511541 223300641318276458766707)
                  ·
                    rfl

theorem cell23_3913888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 5].length) (baseStart_3913888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913888 prefixEnd_3913888 := by exact prefixLift 3913888
  have htrace : WordTrace (prefixWord ++ tailWord_3913888) baseStart_3913888 baseEnd_3913888 := by
    simpa [prefixWord, tailWord_3913888, baseEnd_3913888] using wordTrace_append hprefix tailTrace_3913888
  have hstable : (prefixWord ++ tailWord_3913888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913888).length < 2 ^ (prefixWord ++ tailWord_3913888).sum := by decide
  have hdescent : baseEnd_3913888 < baseStart_3913888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913898 : List Nat := [3, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3913898 : Nat := 118140960795 + 3913898 * 2 ^ 59
def prefixEnd_3913898 : Nat := 4983230072969 + 3 ^ 40 * 3913898 * 2
def baseEnd_3913898 : Nat := 2009710906671033089775317

theorem tailTrace_3913898 : CollatzResearch.WordTrace tailWord_3913898 prefixEnd_3913898 2009710906671033089775317 := by
  unfold tailWord_3913898
  simp only [CollatzResearch.WordTrace]
  refine ⟨35687896893655865351559587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95167725049748974270825565 35687896893655865351559587)
  ·
    refine ⟨53531845340483798027339381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35687896893655865351559587 53531845340483798027339381)
    ·
      refine ⟨5018610500670356065063067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 53531845340483798027339381 5018610500670356065063067)
      ·
        refine ⟨7527915751005534097594601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5018610500670356065063067 7527915751005534097594601)
        ·
          refine ⟨5645936813254150573195951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7527915751005534097594601 5645936813254150573195951)
          ·
            refine ⟨8468905219881225859793927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5645936813254150573195951 8468905219881225859793927)
            ·
              refine ⟨12703357829821838789690891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8468905219881225859793927 12703357829821838789690891)
              ·
                refine ⟨19055036744732758184536337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12703357829821838789690891 19055036744732758184536337)
                ·
                  refine ⟨14291277558549568638402253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19055036744732758184536337 14291277558549568638402253)
                  ·
                    refine ⟨5359229084456088239400845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14291277558549568638402253 5359229084456088239400845)
                    ·
                      refine ⟨2009710906671033089775317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5359229084456088239400845 2009710906671033089775317)
                      ·
                        rfl

theorem cell23_3913898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3913898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913898 prefixEnd_3913898 := by exact prefixLift 3913898
  have htrace : WordTrace (prefixWord ++ tailWord_3913898) baseStart_3913898 baseEnd_3913898 := by
    simpa [prefixWord, tailWord_3913898, baseEnd_3913898] using wordTrace_append hprefix tailTrace_3913898
  have hstable : (prefixWord ++ tailWord_3913898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913898).length < 2 ^ (prefixWord ++ tailWord_3913898).sum := by decide
  have hdescent : baseEnd_3913898 < baseStart_3913898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3913914 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 5, 4]
def baseStart_3913914 : Nat := 118140960795 + 3913914 * 2 ^ 59
def prefixEnd_3913914 : Nat := 4983230072969 + 3 ^ 40 * 3913914 * 2
def baseEnd_3913914 : Nat := 669906374120501675725081

theorem tailTrace_3913914 : CollatzResearch.WordTrace tailWord_3913914 prefixEnd_3913914 669906374120501675725081 := by
  unfold tailWord_3913914
  simp only [CollatzResearch.WordTrace]
  refine ⟨35688042785641374034705199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 95168114095043664092547197 35688042785641374034705199)
  ·
    refine ⟨53532064178462061052057799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35688042785641374034705199 53532064178462061052057799)
    ·
      refine ⟨80298096267693091578086699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53532064178462061052057799 80298096267693091578086699)
      ·
        refine ⟨120447144401539637367130049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80298096267693091578086699 120447144401539637367130049)
        ·
          refine ⟨90335358301154728025347537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120447144401539637367130049 90335358301154728025347537)
          ·
            refine ⟨67751518725866046019010653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90335358301154728025347537 67751518725866046019010653)
            ·
              refine ⟨25406819522199767257128995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67751518725866046019010653 25406819522199767257128995)
              ·
                refine ⟨38110229283299650885693493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25406819522199767257128995 38110229283299650885693493)
                ·
                  refine ⟨3572833995309342270533765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 38110229283299650885693493 3572833995309342270533765)
                  ·
                    refine ⟨669906374120501675725081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3572833995309342270533765 669906374120501675725081)
                    ·
                      rfl

theorem cell23_3913914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 5, 4].length) (baseStart_3913914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3913914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3913914 prefixEnd_3913914 := by exact prefixLift 3913914
  have htrace : WordTrace (prefixWord ++ tailWord_3913914) baseStart_3913914 baseEnd_3913914 := by
    simpa [prefixWord, tailWord_3913914, baseEnd_3913914] using wordTrace_append hprefix tailTrace_3913914
  have hstable : (prefixWord ++ tailWord_3913914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3913914).length < 2 ^ (prefixWord ++ tailWord_3913914).sum := by decide
  have hdescent : baseEnd_3913914 < baseStart_3913914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3913914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
