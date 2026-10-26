import V185TrunkScan23Chunk0975

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5777413 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 8]
def baseStart_5777413 : Nat := 118140960795 + 5777413 * 2 ^ 59
def prefixEnd_5777413 : Nat := 4983230072969 + 3 ^ 40 * 5777413 * 2
def baseEnd_5777413 : Nat := 329621089837145508751963

theorem tailTrace_5777413 : CollatzResearch.WordTrace tailWord_5777413 prefixEnd_5777413 329621089837145508751963 := by
  unfold tailWord_5777413
  simp only [CollatzResearch.WordTrace]
  refine ⟨210719563418426879430024893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140479708945617919620016595 210719563418426879430024893)
  ·
    refine ⟨79019836281910079786259335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210719563418426879430024893 79019836281910079786259335)
    ·
      refine ⟨118529754422865119679389003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79019836281910079786259335 118529754422865119679389003)
      ·
        refine ⟨177794631634297679519083505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118529754422865119679389003 177794631634297679519083505)
        ·
          refine ⟨133345973725723259639312629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177794631634297679519083505 133345973725723259639312629)
          ·
            refine ⟨12501185036786555591185559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133345973725723259639312629 12501185036786555591185559)
            ·
              refine ⟨18751777555179833386778339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12501185036786555591185559 18751777555179833386778339)
              ·
                refine ⟨28127666332769750080167509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18751777555179833386778339 28127666332769750080167509)
                ·
                  refine ⟨329621089837145508751963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28127666332769750080167509 329621089837145508751963)
                  ·
                    rfl

theorem cell23_5777413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 8].length) (baseStart_5777413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777413 prefixEnd_5777413 := by exact prefixLift 5777413
  have htrace : WordTrace (prefixWord ++ tailWord_5777413) baseStart_5777413 baseEnd_5777413 := by
    simpa [prefixWord, tailWord_5777413, baseEnd_5777413] using wordTrace_append hprefix tailTrace_5777413
  have hstable : (prefixWord ++ tailWord_5777413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777413).length < 2 ^ (prefixWord ++ tailWord_5777413).sum := by decide
  have hdescent : baseEnd_5777413 < baseStart_5777413 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777480 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 2, 6, 2]
def baseStart_5777480 : Nat := 118140960795 + 5777480 * 2 ^ 59
def prefixEnd_5777480 : Nat := 4983230072969 + 3 ^ 40 * 5777480 * 2
def baseEnd_5777480 : Nat := 2966624211738160816629859

theorem tailTrace_5777480 : CollatzResearch.WordTrace tailWord_5777480 prefixEnd_5777480 2966624211738160816629859 := by
  unfold tailWord_5777480
  simp only [CollatzResearch.WordTrace]
  refine ⟨105361003554592074936356947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140481338072789433248475929 105361003554592074936356947)
  ·
    refine ⟨158041505331888112404535421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105361003554592074936356947 158041505331888112404535421)
    ·
      refine ⟨59265564499458042151700783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158041505331888112404535421 59265564499458042151700783)
      ·
        refine ⟨88898346749187063227551175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59265564499458042151700783 88898346749187063227551175)
        ·
          refine ⟨133347520123780594841326763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88898346749187063227551175 133347520123780594841326763)
          ·
            refine ⟨200021280185670892261990145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133347520123780594841326763 200021280185670892261990145)
            ·
              refine ⟨150015960139253169196492609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200021280185670892261990145 150015960139253169196492609)
              ·
                refine ⟨112511970104439876897369457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150015960139253169196492609 112511970104439876897369457)
                ·
                  refine ⟨84383977578329907673027093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112511970104439876897369457 84383977578329907673027093)
                  ·
                    refine ⟨3955498948984214422173145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 84383977578329907673027093 3955498948984214422173145)
                    ·
                      refine ⟨2966624211738160816629859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955498948984214422173145 2966624211738160816629859)
                      ·
                        rfl

theorem cell23_5777480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 2, 6, 2].length) (baseStart_5777480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777480 prefixEnd_5777480 := by exact prefixLift 5777480
  have htrace : WordTrace (prefixWord ++ tailWord_5777480) baseStart_5777480 baseEnd_5777480 := by
    simpa [prefixWord, tailWord_5777480, baseEnd_5777480] using wordTrace_append hprefix tailTrace_5777480
  have hstable : (prefixWord ++ tailWord_5777480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777480).length < 2 ^ (prefixWord ++ tailWord_5777480).sum := by decide
  have hdescent : baseEnd_5777480 < baseStart_5777480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777494 : List Nat := [5, 2, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5777494 : Nat := 118140960795 + 5777494 * 2 ^ 59
def prefixEnd_5777494 : Nat := 4983230072969 + 3 ^ 40 * 5777494 * 2
def baseEnd_5777494 : Nat := 988877133489107920618265

theorem tailTrace_5777494 : CollatzResearch.WordTrace tailWord_5777494 prefixEnd_5777494 988877133489107920618265 := by
  unfold tailWord_5777494
  simp only [CollatzResearch.WordTrace]
  refine ⟨13170157358195839391482721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140481678487422286842482357 13170157358195839391482721)
  ·
    refine ⟨9877618018646879543612041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13170157358195839391482721 9877618018646879543612041)
    ·
      refine ⟨7408213513985159657709031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9877618018646879543612041 7408213513985159657709031)
      ·
        refine ⟨11112320270977739486563547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7408213513985159657709031 11112320270977739486563547)
        ·
          refine ⟨16668480406466609229845321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11112320270977739486563547 16668480406466609229845321)
          ·
            refine ⟨12501360304849956922383991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16668480406466609229845321 12501360304849956922383991)
            ·
              refine ⟨18752040457274935383575987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12501360304849956922383991 18752040457274935383575987)
              ·
                refine ⟨28128060685912403075363981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18752040457274935383575987 28128060685912403075363981)
                ·
                  refine ⟨10548022757217151153261493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28128060685912403075363981 10548022757217151153261493)
                  ·
                    refine ⟨988877133489107920618265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10548022757217151153261493 988877133489107920618265)
                    ·
                      rfl

theorem cell23_5777494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5777494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777494 prefixEnd_5777494 := by exact prefixLift 5777494
  have htrace : WordTrace (prefixWord ++ tailWord_5777494) baseStart_5777494 baseEnd_5777494 := by
    simpa [prefixWord, tailWord_5777494, baseEnd_5777494] using wordTrace_append hprefix tailTrace_5777494
  have hstable : (prefixWord ++ tailWord_5777494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777494).length < 2 ^ (prefixWord ++ tailWord_5777494).sum := by decide
  have hdescent : baseEnd_5777494 < baseStart_5777494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777497 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 5, 2, 2]
def baseStart_5777497 : Nat := 118140960795 + 5777497 * 2 ^ 59
def prefixEnd_5777497 : Nat := 4983230072969 + 3 ^ 40 * 5777497 * 2
def baseEnd_5777497 : Nat := 2966632940909287250117281

theorem tailTrace_5777497 : CollatzResearch.WordTrace tailWord_5777497 prefixEnd_5777497 2966632940909287250117281 := by
  unfold tailWord_5777497
  simp only [CollatzResearch.WordTrace]
  refine ⟨210722627150122561776082745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140481751433415041184055163 210722627150122561776082745)
  ·
    refine ⟨158041970362591921332062059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210722627150122561776082745 158041970362591921332062059)
    ·
      refine ⟨237062955543887881998093089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158041970362591921332062059 237062955543887881998093089)
      ·
        refine ⟨177797216657915911498569817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237062955543887881998093089 177797216657915911498569817)
        ·
          refine ⟨133347912493436933623927363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177797216657915911498569817 133347912493436933623927363)
          ·
            refine ⟨200021868740155400435891045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133347912493436933623927363 200021868740155400435891045)
            ·
              refine ⟨37504100388779137581729571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200021868740155400435891045 37504100388779137581729571)
              ·
                refine ⟨56256150583168706372594357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37504100388779137581729571 56256150583168706372594357)
                ·
                  refine ⟨5274014117172066222430721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56256150583168706372594357 5274014117172066222430721)
                  ·
                    refine ⟨3955510587879049666823041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5274014117172066222430721 3955510587879049666823041)
                    ·
                      refine ⟨2966632940909287250117281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955510587879049666823041 2966632940909287250117281)
                      ·
                        rfl

theorem cell23_5777497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 2, 2].length) (baseStart_5777497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777497 prefixEnd_5777497 := by exact prefixLift 5777497
  have htrace : WordTrace (prefixWord ++ tailWord_5777497) baseStart_5777497 baseEnd_5777497 := by
    simpa [prefixWord, tailWord_5777497, baseEnd_5777497] using wordTrace_append hprefix tailTrace_5777497
  have hstable : (prefixWord ++ tailWord_5777497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777497).length < 2 ^ (prefixWord ++ tailWord_5777497).sum := by decide
  have hdescent : baseEnd_5777497 < baseStart_5777497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777501 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5777501 : Nat := 118140960795 + 5777501 * 2 ^ 59
def prefixEnd_5777501 : Nat := 4983230072969 + 3 ^ 40 * 5777501 * 2
def baseEnd_5777501 : Nat := 2966634994831905234467263

theorem tailTrace_5777501 : CollatzResearch.WordTrace tailWord_5777501 prefixEnd_5777501 2966634994831905234467263 := by
  unfold tailWord_5777501
  simp only [CollatzResearch.WordTrace]
  refine ⟨210722773042108070459228357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140481848694738713639485571 210722773042108070459228357)
  ·
    refine ⟨39510519945395263211105317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210722773042108070459228357 39510519945395263211105317)
    ·
      refine ⟨7408222489761611852082247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39510519945395263211105317 7408222489761611852082247)
      ·
        refine ⟨11112333734642417778123371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7408222489761611852082247 11112333734642417778123371)
        ·
          refine ⟨16668500601963626667185057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11112333734642417778123371 16668500601963626667185057)
          ·
            refine ⟨12501375451472720000388793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16668500601963626667185057 12501375451472720000388793)
            ·
              refine ⟨9376031588604540000291595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12501375451472720000388793 9376031588604540000291595)
              ·
                refine ⟨14064047382906810000437393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9376031588604540000291595 14064047382906810000437393)
                ·
                  refine ⟨10548035537180107500328045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14064047382906810000437393 10548035537180107500328045)
                  ·
                    refine ⟨3955513326442540312623017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10548035537180107500328045 3955513326442540312623017)
                    ·
                      refine ⟨2966634994831905234467263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955513326442540312623017 2966634994831905234467263)
                      ·
                        rfl

theorem cell23_5777501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5777501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777501 prefixEnd_5777501 := by exact prefixLift 5777501
  have htrace : WordTrace (prefixWord ++ tailWord_5777501) baseStart_5777501 baseEnd_5777501 := by
    simpa [prefixWord, tailWord_5777501, baseEnd_5777501] using wordTrace_append hprefix tailTrace_5777501
  have hstable : (prefixWord ++ tailWord_5777501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777501).length < 2 ^ (prefixWord ++ tailWord_5777501).sum := by decide
  have hdescent : baseEnd_5777501 < baseStart_5777501 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777537 : List Nat := [1, 2, 4, 2, 3, 2, 1, 8]
def baseStart_5777537 : Nat := 118140960795 + 5777537 * 2 ^ 59
def prefixEnd_5777537 : Nat := 4983230072969 + 3 ^ 40 * 5777537 * 2
def baseEnd_5777537 : Nat := 109876054819832114578411

theorem tailTrace_5777537 : CollatzResearch.WordTrace tailWord_5777537 prefixEnd_5777537 109876054819832114578411 := by
  unfold tailWord_5777537
  simp only [CollatzResearch.WordTrace]
  refine ⟨210724086069977648607538865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140482724046651765738359243 210724086069977648607538865)
  ·
    refine ⟨158043064552483236455654149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210724086069977648607538865 158043064552483236455654149)
    ·
      refine ⟨29633074603590606835435153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158043064552483236455654149 29633074603590606835435153)
      ·
        refine ⟨22224805952692955126576365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29633074603590606835435153 22224805952692955126576365)
        ·
          refine ⟨8334302232259858172466137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22224805952692955126576365 8334302232259858172466137)
          ·
            refine ⟨6250726674194893629349603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8334302232259858172466137 6250726674194893629349603)
            ·
              refine ⟨9376090011292340444024405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6250726674194893629349603 9376090011292340444024405)
              ·
                refine ⟨109876054819832114578411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9376090011292340444024405 109876054819832114578411)
                ·
                  rfl

theorem cell23_5777537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 8].length) (baseStart_5777537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777537 prefixEnd_5777537 := by exact prefixLift 5777537
  have htrace : WordTrace (prefixWord ++ tailWord_5777537) baseStart_5777537 baseEnd_5777537 := by
    simpa [prefixWord, tailWord_5777537, baseEnd_5777537] using wordTrace_append hprefix tailTrace_5777537
  have hstable : (prefixWord ++ tailWord_5777537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777537).length < 2 ^ (prefixWord ++ tailWord_5777537).sum := by decide
  have hdescent : baseEnd_5777537 < baseStart_5777537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777557 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_5777557 : Nat := 118140960795 + 5777557 * 2 ^ 59
def prefixEnd_5777557 : Nat := 4983230072969 + 3 ^ 40 * 5777557 * 2
def baseEnd_5777557 : Nat := 2966663749748557015367005

theorem tailTrace_5777557 : CollatzResearch.WordTrace tailWord_5777557 prefixEnd_5777557 2966663749748557015367005 := by
  unfold tailWord_5777557
  simp only [CollatzResearch.WordTrace]
  refine ⟨210724815529905192023266925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140483210353270128015511283 210724815529905192023266925)
  ·
    refine ⟨79021805823714447008725097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210724815529905192023266925 79021805823714447008725097)
    ·
      refine ⟨59266354367785835256543823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79021805823714447008725097 59266354367785835256543823)
      ·
        refine ⟨88899531551678752884815735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59266354367785835256543823 88899531551678752884815735)
        ·
          refine ⟨133349297327518129327223603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88899531551678752884815735 133349297327518129327223603)
          ·
            refine ⟨200023945991277193990835405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133349297327518129327223603 200023945991277193990835405)
            ·
              refine ⟨75008979746728947746563277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200023945991277193990835405 75008979746728947746563277)
              ·
                refine ⟨28128367405023355404961229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75008979746728947746563277 28128367405023355404961229)
                ·
                  refine ⟨10548137776883758276860461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28128367405023355404961229 10548137776883758276860461)
                  ·
                    refine ⟨3955551666331409353822673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10548137776883758276860461 3955551666331409353822673)
                    ·
                      refine ⟨2966663749748557015367005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955551666331409353822673 2966663749748557015367005)
                      ·
                        rfl

theorem cell23_5777557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_5777557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777557 prefixEnd_5777557 := by exact prefixLift 5777557
  have htrace : WordTrace (prefixWord ++ tailWord_5777557) baseStart_5777557 baseEnd_5777557 := by
    simpa [prefixWord, tailWord_5777557, baseEnd_5777557] using wordTrace_append hprefix tailTrace_5777557
  have hstable : (prefixWord ++ tailWord_5777557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777557).length < 2 ^ (prefixWord ++ tailWord_5777557).sum := by decide
  have hdescent : baseEnd_5777557 < baseStart_5777557 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777563 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 1, 8]
def baseStart_5777563 : Nat := 118140960795 + 5777563 * 2 ^ 59
def prefixEnd_5777563 : Nat := 4983230072969 + 3 ^ 40 * 5777563 * 2
def baseEnd_5777563 : Nat := 988888943544161330630659

theorem tailTrace_5777563 : CollatzResearch.WordTrace tailWord_5777563 prefixEnd_5777563 988888943544161330630659 := by
  unfold tailWord_5777563
  simp only [CollatzResearch.WordTrace]
  refine ⟨210725034367883455047985343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140483356245255636698656895 210725034367883455047985343)
  ·
    refine ⟨316087551551825182571978015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210725034367883455047985343 316087551551825182571978015)
    ·
      refine ⟨474131327327737773857967023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316087551551825182571978015 474131327327737773857967023)
      ·
        refine ⟨711196990991606660786950535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474131327327737773857967023 711196990991606660786950535)
        ·
          refine ⟨1066795486487409991180425803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711196990991606660786950535 1066795486487409991180425803)
          ·
            refine ⟨1600193229731114986770638705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1066795486487409991180425803 1600193229731114986770638705)
            ·
              refine ⟨1200144922298336240077979029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1600193229731114986770638705 1200144922298336240077979029)
              ·
                refine ⟨56256793232734511253655267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1200144922298336240077979029 56256793232734511253655267)
                ·
                  refine ⟨84385189849101766880482901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56256793232734511253655267 84385189849101766880482901)
                  ·
                    refine ⟨988888943544161330630659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84385189849101766880482901 988888943544161330630659)
                    ·
                      rfl

theorem cell23_5777563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 8].length) (baseStart_5777563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777563 prefixEnd_5777563 := by exact prefixLift 5777563
  have htrace : WordTrace (prefixWord ++ tailWord_5777563) baseStart_5777563 baseEnd_5777563 := by
    simpa [prefixWord, tailWord_5777563, baseEnd_5777563] using wordTrace_append hprefix tailTrace_5777563
  have hstable : (prefixWord ++ tailWord_5777563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777563).length < 2 ^ (prefixWord ++ tailWord_5777563).sum := by decide
  have hdescent : baseEnd_5777563 < baseStart_5777563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777581 : List Nat := [1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_5777581 : Nat := 118140960795 + 5777581 * 2 ^ 59
def prefixEnd_5777581 : Nat := 4983230072969 + 3 ^ 40 * 5777581 * 2
def baseEnd_5777581 : Nat := 2966676073284264921466895

theorem tailTrace_5777581 : CollatzResearch.WordTrace tailWord_5777581 prefixEnd_5777581 2966676073284264921466895 := by
  unfold tailWord_5777581
  simp only [CollatzResearch.WordTrace]
  refine ⟨210725690881818244122140597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140483793921212162748093731 210725690881818244122140597)
  ·
    refine ⟨19755533520170460386450681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210725690881818244122140597 19755533520170460386450681)
    ·
      refine ⟨14816650140127845289838011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19755533520170460386450681 14816650140127845289838011)
      ·
        refine ⟨22224975210191767934757017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14816650140127845289838011 22224975210191767934757017)
        ·
          refine ⟨16668731407643825951067763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22224975210191767934757017 16668731407643825951067763)
          ·
            refine ⟨25003097111465738926601645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16668731407643825951067763 25003097111465738926601645)
            ·
              refine ⟨9376161416799652097475617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25003097111465738926601645 9376161416799652097475617)
              ·
                refine ⟨7032121062599739073106713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9376161416799652097475617 7032121062599739073106713)
                ·
                  refine ⟨5274090796949804304830035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7032121062599739073106713 5274090796949804304830035)
                  ·
                    refine ⟨7911136195424706457245053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5274090796949804304830035 7911136195424706457245053)
                    ·
                      refine ⟨2966676073284264921466895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7911136195424706457245053 2966676073284264921466895)
                      ·
                        rfl

theorem cell23_5777581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_5777581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777581 prefixEnd_5777581 := by exact prefixLift 5777581
  have htrace : WordTrace (prefixWord ++ tailWord_5777581) baseStart_5777581 baseEnd_5777581 := by
    simpa [prefixWord, tailWord_5777581, baseEnd_5777581] using wordTrace_append hprefix tailTrace_5777581
  have hstable : (prefixWord ++ tailWord_5777581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777581).length < 2 ^ (prefixWord ++ tailWord_5777581).sum := by decide
  have hdescent : baseEnd_5777581 < baseStart_5777581 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777598 : List Nat := [4, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_5777598 : Nat := 118140960795 + 5777598 * 2 ^ 59
def prefixEnd_5777598 : Nat := 4983230072969 + 3 ^ 40 * 5777598 * 2
def baseEnd_5777598 : Nat := 2966684802455391354954317

theorem tailTrace_5777598 : CollatzResearch.WordTrace tailWord_5777598 prefixEnd_5777598 2966684802455391354954317 := by
  unfold tailWord_5777598
  simp only [CollatzResearch.WordTrace]
  refine ⟨26340788865344582003188681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140484207281837770683672965 26340788865344582003188681)
  ·
    refine ⟨19755591649008436502391511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26340788865344582003188681 19755591649008436502391511)
    ·
      refine ⟨29633387473512654753587267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19755591649008436502391511 29633387473512654753587267)
      ·
        refine ⟨44450081210268982130380901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29633387473512654753587267 44450081210268982130380901)
        ·
          refine ⟨8334390226925434149446419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44450081210268982130380901 8334390226925434149446419)
          ·
            refine ⟨12501585340388151224169629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334390226925434149446419 12501585340388151224169629)
            ·
              refine ⟨4688094502645556709063611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12501585340388151224169629 4688094502645556709063611)
              ·
                refine ⟨7032141753968335063595417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688094502645556709063611 7032141753968335063595417)
                ·
                  refine ⟨5274106315476251297696563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7032141753968335063595417 5274106315476251297696563)
                  ·
                    refine ⟨7911159473214376946544845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5274106315476251297696563 7911159473214376946544845)
                    ·
                      refine ⟨2966684802455391354954317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7911159473214376946544845 2966684802455391354954317)
                      ·
                        rfl

theorem cell23_5777598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_5777598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777598 prefixEnd_5777598 := by exact prefixLift 5777598
  have htrace : WordTrace (prefixWord ++ tailWord_5777598) baseStart_5777598 baseEnd_5777598 := by
    simpa [prefixWord, tailWord_5777598, baseEnd_5777598] using wordTrace_append hprefix tailTrace_5777598
  have hstable : (prefixWord ++ tailWord_5777598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777598).length < 2 ^ (prefixWord ++ tailWord_5777598).sum := by decide
  have hdescent : baseEnd_5777598 < baseStart_5777598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777610 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 7]
def baseStart_5777610 : Nat := 118140960795 + 5777610 * 2 ^ 59
def prefixEnd_5777610 : Nat := 4983230072969 + 3 ^ 40 * 5777610 * 2
def baseEnd_5777610 : Nat := 329632329358138367556029

theorem tailTrace_5777610 : CollatzResearch.WordTrace tailWord_5777610 prefixEnd_5777610 329632329358138367556029 := by
  unfold tailWord_5777610
  simp only [CollatzResearch.WordTrace]
  refine ⟨52681687149678295518736571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140484499065808788049964189 52681687149678295518736571)
  ·
    refine ⟨79022530724517443278104857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52681687149678295518736571 79022530724517443278104857)
    ·
      refine ⟨59266898043388082458578643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79022530724517443278104857 59266898043388082458578643)
      ·
        refine ⟨88900347065082123687867965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59266898043388082458578643 88900347065082123687867965)
        ·
          refine ⟨33337630149405796382950487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88900347065082123687867965 33337630149405796382950487)
          ·
            refine ⟨50006445224108694574425731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33337630149405796382950487 50006445224108694574425731)
            ·
              refine ⟨75009667836163041861638597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50006445224108694574425731 75009667836163041861638597)
              ·
                refine ⟨14064312719280570349057237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75009667836163041861638597 14064312719280570349057237)
                ·
                  refine ⟨329632329358138367556029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14064312719280570349057237 329632329358138367556029)
                  ·
                    rfl

theorem cell23_5777610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_5777610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777610 prefixEnd_5777610 := by exact prefixLift 5777610
  have htrace : WordTrace (prefixWord ++ tailWord_5777610) baseStart_5777610 baseEnd_5777610 := by
    simpa [prefixWord, tailWord_5777610, baseEnd_5777610] using wordTrace_append hprefix tailTrace_5777610
  have hstable : (prefixWord ++ tailWord_5777610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777610).length < 2 ^ (prefixWord ++ tailWord_5777610).sum := by decide
  have hdescent : baseEnd_5777610 < baseStart_5777610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777644 : List Nat := [2, 2, 1, 1, 2, 3, 5, 2, 5]
def baseStart_5777644 : Nat := 118140960795 + 5777644 * 2 ^ 59
def prefixEnd_5777644 : Nat := 4983230072969 + 3 ^ 40 * 5777644 * 2
def baseEnd_5777644 : Nat := 329634269173944241664345

theorem tailTrace_5777644 : CollatzResearch.WordTrace tailWord_5777644 prefixEnd_5777644 329634269173944241664345 := by
  unfold tailWord_5777644
  simp only [CollatzResearch.WordTrace]
  refine ⟨105363994340295002940841993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140485325787060003921122657 105363994340295002940841993)
  ·
    refine ⟨79022995755221252205631495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105363994340295002940841993 79022995755221252205631495)
    ·
      refine ⟨118534493632831878308447243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79022995755221252205631495 118534493632831878308447243)
      ·
        refine ⟨177801740449247817462670865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118534493632831878308447243 177801740449247817462670865)
        ·
          refine ⟨133351305336935863097003149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177801740449247817462670865 133351305336935863097003149)
          ·
            refine ⟨50006739501350948661376181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133351305336935863097003149 50006739501350948661376181)
            ·
              refine ⟨4688131828251651437004017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50006739501350948661376181 4688131828251651437004017)
              ·
                refine ⟨3516098871188738577753013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688131828251651437004017 3516098871188738577753013)
                ·
                  refine ⟨329634269173944241664345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3516098871188738577753013 329634269173944241664345)
                  ·
                    rfl

theorem cell23_5777644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 5].length) (baseStart_5777644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777644 prefixEnd_5777644 := by exact prefixLift 5777644
  have htrace : WordTrace (prefixWord ++ tailWord_5777644) baseStart_5777644 baseEnd_5777644 := by
    simpa [prefixWord, tailWord_5777644, baseEnd_5777644] using wordTrace_append hprefix tailTrace_5777644
  have hstable : (prefixWord ++ tailWord_5777644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777644).length < 2 ^ (prefixWord ++ tailWord_5777644).sum := by decide
  have hdescent : baseEnd_5777644 < baseStart_5777644 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777717 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 6]
def baseStart_5777717 : Nat := 118140960795 + 5777717 * 2 ^ 59
def prefixEnd_5777717 : Nat := 4983230072969 + 3 ^ 40 * 5777717 * 2
def baseEnd_5777717 : Nat := 329638434072586265485141

theorem tailTrace_5777717 : CollatzResearch.WordTrace tailWord_5777717 prefixEnd_5777717 329638434072586265485141 := by
  unfold tailWord_5777717
  simp only [CollatzResearch.WordTrace]
  refine ⟨210730651209325539349091405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140487100806217026232727603 210730651209325539349091405)
  ·
    refine ⟨79023994203497077255909277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210730651209325539349091405 79023994203497077255909277)
    ·
      refine ⟨29633997826311403970965979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79023994203497077255909277 29633997826311403970965979)
      ·
        refine ⟨44450996739467105956448969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29633997826311403970965979 44450996739467105956448969)
        ·
          refine ⟨33338247554600329467336727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44450996739467105956448969 33338247554600329467336727)
          ·
            refine ⟨50007371331900494201005091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33338247554600329467336727 50007371331900494201005091)
            ·
              refine ⟨75011056997850741301507637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50007371331900494201005091 75011056997850741301507637)
              ·
                refine ⟨7032286593548506997016341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75011056997850741301507637 7032286593548506997016341)
                ·
                  refine ⟨329638434072586265485141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7032286593548506997016341 329638434072586265485141)
                  ·
                    rfl

theorem cell23_5777717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_5777717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777717 prefixEnd_5777717 := by exact prefixLift 5777717
  have htrace : WordTrace (prefixWord ++ tailWord_5777717) baseStart_5777717 baseEnd_5777717 := by
    simpa [prefixWord, tailWord_5777717, baseEnd_5777717] using wordTrace_append hprefix tailTrace_5777717
  have hstable : (prefixWord ++ tailWord_5777717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777717).length < 2 ^ (prefixWord ++ tailWord_5777717).sum := by decide
  have hdescent : baseEnd_5777717 < baseStart_5777717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777754 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2]
def baseStart_5777754 : Nat := 118140960795 + 5777754 * 2 ^ 59
def prefixEnd_5777754 : Nat := 4983230072969 + 3 ^ 40 * 5777754 * 2
def baseEnd_5777754 : Nat := 2966764905437492744603599

theorem tailTrace_5777754 : CollatzResearch.WordTrace tailWord_5777754 prefixEnd_5777754 2966764905437492744603599 := by
  unfold tailWord_5777754
  simp only [CollatzResearch.WordTrace]
  refine ⟨52683000177547873667047079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140488000473460996445458877 52683000177547873667047079)
  ·
    refine ⟨79024500266321810500570619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52683000177547873667047079 79024500266321810500570619)
    ·
      refine ⟨118536750399482715750855929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79024500266321810500570619 118536750399482715750855929)
      ·
        refine ⟨88902562799612036813141947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118536750399482715750855929 88902562799612036813141947)
        ·
          refine ⟨133353844199418055219712921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88902562799612036813141947 133353844199418055219712921)
          ·
            refine ⟨100015383149563541414784691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133353844199418055219712921 100015383149563541414784691)
            ·
              refine ⟨150023074724345312122177037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100015383149563541414784691 150023074724345312122177037)
              ·
                refine ⟨56258653021629492045816389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150023074724345312122177037 56258653021629492045816389)
                ·
                  refine ⟨10548497441555529758590573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56258653021629492045816389 10548497441555529758590573)
                  ·
                    refine ⟨3955686540583323659471465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10548497441555529758590573 3955686540583323659471465)
                    ·
                      refine ⟨2966764905437492744603599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955686540583323659471465 2966764905437492744603599)
                      ·
                        rfl

theorem cell23_5777754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2].length) (baseStart_5777754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777754 prefixEnd_5777754 := by exact prefixLift 5777754
  have htrace : WordTrace (prefixWord ++ tailWord_5777754) baseStart_5777754 baseEnd_5777754 := by
    simpa [prefixWord, tailWord_5777754, baseEnd_5777754] using wordTrace_append hprefix tailTrace_5777754
  have hstable : (prefixWord ++ tailWord_5777754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777754).length < 2 ^ (prefixWord ++ tailWord_5777754).sum := by decide
  have hdescent : baseEnd_5777754 < baseStart_5777754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777781 : List Nat := [1, 3, 4, 1, 2, 2, 2, 2, 1, 5]
def baseStart_5777781 : Nat := 118140960795 + 5777781 * 2 ^ 59
def prefixEnd_5777781 : Nat := 4983230072969 + 3 ^ 40 * 5777781 * 2
def baseEnd_5777781 : Nat := 988926256471721379655325

theorem tailTrace_5777781 : CollatzResearch.WordTrace tailWord_5777781 prefixEnd_5777781 988926256471721379655325 := by
  unfold tailWord_5777781
  simp only [CollatzResearch.WordTrace]
  refine ⟨210732985481093678279421197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140488656987395785519614131 210732985481093678279421197)
  ·
    refine ⟨79024869555410129354782949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210732985481093678279421197 79024869555410129354782949)
    ·
      refine ⟨14817163041639399254021803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79024869555410129354782949 14817163041639399254021803)
      ·
        refine ⟨22225744562459098881032705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14817163041639399254021803 22225744562459098881032705)
        ·
          refine ⟨16669308421844324160774529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22225744562459098881032705 16669308421844324160774529)
          ·
            refine ⟨12501981316383243120580897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16669308421844324160774529 12501981316383243120580897)
            ·
              refine ⟨9376485987287432340435673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12501981316383243120580897 9376485987287432340435673)
              ·
                refine ⟨7032364490465574255326755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9376485987287432340435673 7032364490465574255326755)
                ·
                  refine ⟨10548546735698361382990133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7032364490465574255326755 10548546735698361382990133)
                  ·
                    refine ⟨988926256471721379655325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10548546735698361382990133 988926256471721379655325)
                    ·
                      rfl

theorem cell23_5777781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_5777781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777781 prefixEnd_5777781 := by exact prefixLift 5777781
  have htrace : WordTrace (prefixWord ++ tailWord_5777781) baseStart_5777781 baseEnd_5777781 := by
    simpa [prefixWord, tailWord_5777781, baseEnd_5777781] using wordTrace_append hprefix tailTrace_5777781
  have hstable : (prefixWord ++ tailWord_5777781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777781).length < 2 ^ (prefixWord ++ tailWord_5777781).sum := by decide
  have hdescent : baseEnd_5777781 < baseStart_5777781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777795 : List Nat := [1, 1, 1, 3, 6, 2, 1, 3, 1, 1, 3]
def baseStart_5777795 : Nat := 118140960795 + 5777795 * 2 ^ 59
def prefixEnd_5777795 : Nat := 4983230072969 + 3 ^ 40 * 5777795 * 2
def baseEnd_5777795 : Nat := 2966785958144327084190911

theorem tailTrace_5777795 : CollatzResearch.WordTrace tailWord_5777795 prefixEnd_5777795 2966785958144327084190911 := by
  unfold tailWord_5777795
  simp only [CollatzResearch.WordTrace]
  refine ⟨210733496103042958670430839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140488997402028639113620559 210733496103042958670430839)
  ·
    refine ⟨316100244154564438005646259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210733496103042958670430839 316100244154564438005646259)
    ·
      refine ⟨474150366231846657008469389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316100244154564438005646259 474150366231846657008469389)
      ·
        refine ⟨177806387336942496378176021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474150366231846657008469389 177806387336942496378176021)
        ·
          refine ⟨8334674406419179517727001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 177806387336942496378176021 8334674406419179517727001)
          ·
            refine ⟨6251005804814384638295251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8334674406419179517727001 6251005804814384638295251)
            ·
              refine ⟨9376508707221576957442877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6251005804814384638295251 9376508707221576957442877)
              ·
                refine ⟨3516190765208091359041079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9376508707221576957442877 3516190765208091359041079)
                ·
                  refine ⟨5274286147812137038561619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516190765208091359041079 5274286147812137038561619)
                  ·
                    refine ⟨7911429221718205557842429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5274286147812137038561619 7911429221718205557842429)
                    ·
                      refine ⟨2966785958144327084190911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7911429221718205557842429 2966785958144327084190911)
                      ·
                        rfl

theorem cell23_5777795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 3, 1, 1, 3].length) (baseStart_5777795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777795 prefixEnd_5777795 := by exact prefixLift 5777795
  have htrace : WordTrace (prefixWord ++ tailWord_5777795) baseStart_5777795 baseEnd_5777795 := by
    simpa [prefixWord, tailWord_5777795, baseEnd_5777795] using wordTrace_append hprefix tailTrace_5777795
  have hstable : (prefixWord ++ tailWord_5777795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777795).length < 2 ^ (prefixWord ++ tailWord_5777795).sum := by decide
  have hdescent : baseEnd_5777795 < baseStart_5777795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777797 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 4]
def baseStart_5777797 : Nat := 118140960795 + 5777797 * 2 ^ 59
def prefixEnd_5777797 : Nat := 4983230072969 + 3 ^ 40 * 5777797 * 2
def baseEnd_5777797 : Nat := 2966786985105636076365901

theorem tailTrace_5777797 : CollatzResearch.WordTrace tailWord_5777797 prefixEnd_5777797 2966786985105636076365901 := by
  unfold tailWord_5777797
  simp only [CollatzResearch.WordTrace]
  refine ⟨210733569049035713012003645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140489046032690475341335763 210733569049035713012003645)
  ·
    refine ⟨79025088393388392379501367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210733569049035713012003645 79025088393388392379501367)
    ·
      refine ⟨118537632590082588569252051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79025088393388392379501367 118537632590082588569252051)
      ·
        refine ⟨177806448885123882853878077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118537632590082588569252051 177806448885123882853878077)
        ·
          refine ⟨66677418331921456070204279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177806448885123882853878077 66677418331921456070204279)
          ·
            refine ⟨100016127497882184105306419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66677418331921456070204279 100016127497882184105306419)
            ·
              refine ⟨150024191246823276157959629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100016127497882184105306419 150024191246823276157959629)
              ·
                refine ⟨56259071717558728559234861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150024191246823276157959629 56259071717558728559234861)
                ·
                  refine ⟨21097151894084523209713073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56259071717558728559234861 21097151894084523209713073)
                  ·
                    refine ⟨15822863920563392407284805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21097151894084523209713073 15822863920563392407284805)
                    ·
                      refine ⟨2966786985105636076365901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15822863920563392407284805 2966786985105636076365901)
                      ·
                        rfl

theorem cell23_5777797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_5777797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777797 prefixEnd_5777797 := by exact prefixLift 5777797
  have htrace : WordTrace (prefixWord ++ tailWord_5777797) baseStart_5777797 baseEnd_5777797 := by
    simpa [prefixWord, tailWord_5777797, baseEnd_5777797] using wordTrace_append hprefix tailTrace_5777797
  have hstable : (prefixWord ++ tailWord_5777797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777797).length < 2 ^ (prefixWord ++ tailWord_5777797).sum := by decide
  have hdescent : baseEnd_5777797 < baseStart_5777797 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777804 : List Nat := [2, 2, 1, 2, 1, 5, 2, 1, 1, 1, 5]
def baseStart_5777804 : Nat := 118140960795 + 5777804 * 2 ^ 59
def prefixEnd_5777804 : Nat := 4983230072969 + 3 ^ 40 * 5777804 * 2
def baseEnd_5777804 : Nat := 2966790579470217548978369

theorem tailTrace_5777804 : CollatzResearch.WordTrace tailWord_5777804 prefixEnd_5777804 2966790579470217548978369 := by
  unfold tailWord_5777804
  simp only [CollatzResearch.WordTrace]
  refine ⟨105366912180005176603754233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140489216240006902138338977 105366912180005176603754233)
  ·
    refine ⟨79025184135003882452815675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105366912180005176603754233 79025184135003882452815675)
    ·
      refine ⟨118537776202505823679223513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79025184135003882452815675 118537776202505823679223513)
      ·
        refine ⟨88903332151879367759417635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118537776202505823679223513 88903332151879367759417635)
        ·
          refine ⟨133354998227819051639126453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88903332151879367759417635 133354998227819051639126453)
          ·
            refine ⟨12502031083858036091168105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133354998227819051639126453 12502031083858036091168105)
            ·
              refine ⟨9376523312893527068376079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12502031083858036091168105 9376523312893527068376079)
              ·
                refine ⟨14064784969340290602564119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9376523312893527068376079 14064784969340290602564119)
                ·
                  refine ⟨21097177454010435903846179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14064784969340290602564119 21097177454010435903846179)
                  ·
                    refine ⟨31645766181015653855769269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21097177454010435903846179 31645766181015653855769269)
                    ·
                      refine ⟨2966790579470217548978369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31645766181015653855769269 2966790579470217548978369)
                      ·
                        rfl

theorem cell23_5777804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_5777804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777804 prefixEnd_5777804 := by exact prefixLift 5777804
  have htrace : WordTrace (prefixWord ++ tailWord_5777804) baseStart_5777804 baseEnd_5777804 := by
    simpa [prefixWord, tailWord_5777804, baseEnd_5777804] using wordTrace_append hprefix tailTrace_5777804
  have hstable : (prefixWord ++ tailWord_5777804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777804).length < 2 ^ (prefixWord ++ tailWord_5777804).sum := by decide
  have hdescent : baseEnd_5777804 < baseStart_5777804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777812 : List Nat := [2, 4, 2, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_5777812 : Nat := 118140960795 + 5777812 * 2 ^ 59
def prefixEnd_5777812 : Nat := 4983230072969 + 3 ^ 40 * 5777812 * 2
def baseEnd_5777812 : Nat := 2966794687315453517678333

theorem tailTrace_5777812 : CollatzResearch.WordTrace tailWord_5777812 prefixEnd_5777812 2966794687315453517678333 := by
  unfold tailWord_5777812
  simp only [CollatzResearch.WordTrace]
  refine ⟨105367058071990685286899845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140489410762654247049199793 105367058071990685286899845)
  ·
    refine ⟨19756323388498253491293721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105367058071990685286899845 19756323388498253491293721)
    ·
      refine ⟨14817242541373690118470291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19756323388498253491293721 14817242541373690118470291)
      ·
        refine ⟨22225863812060535177705437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14817242541373690118470291 22225863812060535177705437)
        ·
          refine ⟨8334698929522700691639539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22225863812060535177705437 8334698929522700691639539)
          ·
            refine ⟨12502048394284051037459309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334698929522700691639539 12502048394284051037459309)
            ·
              refine ⟨4688268147856519139047241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12502048394284051037459309 4688268147856519139047241)
              ·
                refine ⟨3516201110892389354285431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688268147856519139047241 3516201110892389354285431)
                ·
                  refine ⟨5274301666338584031428147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516201110892389354285431 5274301666338584031428147)
                  ·
                    refine ⟨7911452499507876047142221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5274301666338584031428147 7911452499507876047142221)
                    ·
                      refine ⟨2966794687315453517678333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7911452499507876047142221 2966794687315453517678333)
                      ·
                        rfl

theorem cell23_5777812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_5777812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777812 prefixEnd_5777812 := by exact prefixLift 5777812
  have htrace : WordTrace (prefixWord ++ tailWord_5777812) baseStart_5777812 baseEnd_5777812 := by
    simpa [prefixWord, tailWord_5777812, baseEnd_5777812] using wordTrace_append hprefix tailTrace_5777812
  have hstable : (prefixWord ++ tailWord_5777812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777812).length < 2 ^ (prefixWord ++ tailWord_5777812).sum := by decide
  have hdescent : baseEnd_5777812 < baseStart_5777812 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777818 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2]
def baseStart_5777818 : Nat := 118140960795 + 5777818 * 2 ^ 59
def prefixEnd_5777818 : Nat := 4983230072969 + 3 ^ 40 * 5777818 * 2
def baseEnd_5777818 : Nat := 2966797768199380494203305

theorem tailTrace_5777818 : CollatzResearch.WordTrace tailWord_5777818 prefixEnd_5777818 2966797768199380494203305 := by
  unfold tailWord_5777818
  simp only [CollatzResearch.WordTrace]
  refine ⟨52683583745489908399629527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140489556654639755732345405 52683583745489908399629527)
  ·
    refine ⟨79025375618234862599444291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52683583745489908399629527 79025375618234862599444291)
    ·
      refine ⟨118538063427352293899166437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79025375618234862599444291 118538063427352293899166437)
      ·
        refine ⟨22225886892628555106093707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118538063427352293899166437 22225886892628555106093707)
        ·
          refine ⟨33338830338942832659140561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22225886892628555106093707 33338830338942832659140561)
          ·
            refine ⟨25004122754207124494355421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33338830338942832659140561 25004122754207124494355421)
            ·
              refine ⟨9376546032827671685383283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25004122754207124494355421 9376546032827671685383283)
              ·
                refine ⟨14064819049241507528074925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9376546032827671685383283 14064819049241507528074925)
                ·
                  refine ⟨5274307143465565323028097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14064819049241507528074925 5274307143465565323028097)
                  ·
                    refine ⟨3955730357599173992271073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5274307143465565323028097 3955730357599173992271073)
                    ·
                      refine ⟨2966797768199380494203305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955730357599173992271073 2966797768199380494203305)
                      ·
                        rfl

theorem cell23_5777818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_5777818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777818 prefixEnd_5777818 := by exact prefixLift 5777818
  have htrace : WordTrace (prefixWord ++ tailWord_5777818) baseStart_5777818 baseEnd_5777818 := by
    simpa [prefixWord, tailWord_5777818, baseEnd_5777818] using wordTrace_append hprefix tailTrace_5777818
  have hstable : (prefixWord ++ tailWord_5777818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777818).length < 2 ^ (prefixWord ++ tailWord_5777818).sum := by decide
  have hdescent : baseEnd_5777818 < baseStart_5777818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777867 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 2, 6]
def baseStart_5777867 : Nat := 118140960795 + 5777867 * 2 ^ 59
def prefixEnd_5777867 : Nat := 4983230072969 + 3 ^ 40 * 5777867 * 2
def baseEnd_5777867 : Nat := 988940976250483600830193

theorem tailTrace_5777867 : CollatzResearch.WordTrace tailWord_5777867 prefixEnd_5777867 988940976250483600830193 := by
  unfold tailWord_5777867
  simp only [CollatzResearch.WordTrace]
  refine ⟨210736122158782114967051855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140490748105854743311367903 210736122158782114967051855)
  ·
    refine ⟨316104183238173172450577783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210736122158782114967051855 316104183238173172450577783)
    ·
      refine ⟨474156274857259758675866675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316104183238173172450577783 474156274857259758675866675)
      ·
        refine ⟨711234412285889638013800013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474156274857259758675866675 711234412285889638013800013)
        ·
          refine ⟨266712904607208614255175005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 711234412285889638013800013 266712904607208614255175005)
          ·
            refine ⟨100017339227703230345690627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266712904607208614255175005 100017339227703230345690627)
            ·
              refine ⟨150026008841554845518535941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100017339227703230345690627 150026008841554845518535941)
              ·
                refine ⟨28129876657791533534725489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150026008841554845518535941 28129876657791533534725489)
                ·
                  refine ⟨21097407493343650151044117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28129876657791533534725489 21097407493343650151044117)
                  ·
                    refine ⟨988940976250483600830193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21097407493343650151044117 988940976250483600830193)
                    ·
                      rfl

theorem cell23_5777867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 2, 6].length) (baseStart_5777867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777867 prefixEnd_5777867 := by exact prefixLift 5777867
  have htrace : WordTrace (prefixWord ++ tailWord_5777867) baseStart_5777867 baseEnd_5777867 := by
    simpa [prefixWord, tailWord_5777867, baseEnd_5777867] using wordTrace_append hprefix tailTrace_5777867
  have hstable : (prefixWord ++ tailWord_5777867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777867).length < 2 ^ (prefixWord ++ tailWord_5777867).sum := by decide
  have hdescent : baseEnd_5777867 < baseStart_5777867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777878 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_5777878 : Nat := 118140960795 + 5777878 * 2 ^ 59
def prefixEnd_5777878 : Nat := 4983230072969 + 3 ^ 40 * 5777878 * 2
def baseEnd_5777878 : Nat := 2966828577038650259453029

theorem tailTrace_5777878 : CollatzResearch.WordTrace tailWord_5777878 prefixEnd_5777878 2966828577038650259453029 := by
  unfold tailWord_5777878
  simp only [CollatzResearch.WordTrace]
  refine ⟨13171032710108891490356393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140491015574494842563801525 13171032710108891490356393)
  ·
    refine ⟨9878274532581668617767295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13171032710108891490356393 9878274532581668617767295)
    ·
      refine ⟨14817411798872502926650943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9878274532581668617767295 14817411798872502926650943)
      ·
        refine ⟨22226117698308754389976415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14817411798872502926650943 22226117698308754389976415)
        ·
          refine ⟨33339176547463131584964623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22226117698308754389976415 33339176547463131584964623)
          ·
            refine ⟨50008764821194697377446935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33339176547463131584964623 50008764821194697377446935)
            ·
              refine ⟨75013147231792046066170403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50008764821194697377446935 75013147231792046066170403)
              ·
                refine ⟨112519720847688069099255605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75013147231792046066170403 112519720847688069099255605)
                ·
                  refine ⟨10548723829470756478055213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112519720847688069099255605 10548723829470756478055213)
                  ·
                    refine ⟨3955771436051533679270705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10548723829470756478055213 3955771436051533679270705)
                    ·
                      refine ⟨2966828577038650259453029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955771436051533679270705 2966828577038650259453029)
                      ·
                        rfl

theorem cell23_5777878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_5777878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777878 prefixEnd_5777878 := by exact prefixLift 5777878
  have htrace : WordTrace (prefixWord ++ tailWord_5777878) baseStart_5777878 baseEnd_5777878 := by
    simpa [prefixWord, tailWord_5777878, baseEnd_5777878] using wordTrace_append hprefix tailTrace_5777878
  have hstable : (prefixWord ++ tailWord_5777878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777878).length < 2 ^ (prefixWord ++ tailWord_5777878).sum := by decide
  have hdescent : baseEnd_5777878 < baseStart_5777878 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777931 : List Nat := [1, 1, 1, 1, 7, 1, 2, 4, 5]
def baseStart_5777931 : Nat := 118140960795 + 5777931 * 2 ^ 59
def prefixEnd_5777931 : Nat := 4983230072969 + 3 ^ 40 * 5777931 * 2
def baseEnd_5777931 : Nat := 329650643501482061343365

theorem tailTrace_5777931 : CollatzResearch.WordTrace tailWord_5777931 prefixEnd_5777931 329650643501482061343365 := by
  unfold tailWord_5777931
  simp only [CollatzResearch.WordTrace]
  refine ⟨210738456430550253897381647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140492304287033502598254431 210738456430550253897381647)
  ·
    refine ⟨316107684645825380846072471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210738456430550253897381647 316107684645825380846072471)
    ·
      refine ⟨474161526968738071269108707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316107684645825380846072471 474161526968738071269108707)
      ·
        refine ⟨711242290453107106903663061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474161526968738071269108707 711242290453107106903663061)
        ·
          refine ⟨16669741182494697818054603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 711242290453107106903663061 16669741182494697818054603)
          ·
            refine ⟨25004611773742046727081905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16669741182494697818054603 25004611773742046727081905)
            ·
              refine ⟨18753458830306535045311429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25004611773742046727081905 18753458830306535045311429)
              ·
                refine ⟨3516273530682475320995893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18753458830306535045311429 3516273530682475320995893)
                ·
                  refine ⟨329650643501482061343365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3516273530682475320995893 329650643501482061343365)
                  ·
                    rfl

theorem cell23_5777931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 5].length) (baseStart_5777931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777931 prefixEnd_5777931 := by exact prefixLift 5777931
  have htrace : WordTrace (prefixWord ++ tailWord_5777931) baseStart_5777931 baseEnd_5777931 := by
    simpa [prefixWord, tailWord_5777931, baseEnd_5777931] using wordTrace_append hprefix tailTrace_5777931
  have hstable : (prefixWord ++ tailWord_5777931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777931).length < 2 ^ (prefixWord ++ tailWord_5777931).sum := by decide
  have hdescent : baseEnd_5777931 < baseStart_5777931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777944 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 1, 7]
def baseStart_5777944 : Nat := 118140960795 + 5777944 * 2 ^ 59
def prefixEnd_5777944 : Nat := 4983230072969 + 3 ^ 40 * 5777944 * 2
def baseEnd_5777944 : Nat := 988954155587282333742575

theorem tailTrace_5777944 : CollatzResearch.WordTrace tailWord_5777944 prefixEnd_5777944 988954155587282333742575 := by
  unfold tailWord_5777944
  simp only [CollatzResearch.WordTrace]
  refine ⟨105369465289751578558802443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140492620386335438078403257 105369465289751578558802443)
  ·
    refine ⟨158054197934627367838203665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105369465289751578558802443 158054197934627367838203665)
    ·
      refine ⟨118540648450970525878652749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158054197934627367838203665 118540648450970525878652749)
      ·
        refine ⟨44452743169113947204494781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118540648450970525878652749 44452743169113947204494781)
        ·
          refine ⟨16669778688417730201685543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44452743169113947204494781 16669778688417730201685543)
          ·
            refine ⟨25004668032626595302528315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16669778688417730201685543 25004668032626595302528315)
            ·
              refine ⟨37507002048939892953792473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25004668032626595302528315 37507002048939892953792473)
              ·
                refine ⟨28130251536704919715344355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37507002048939892953792473 28130251536704919715344355)
                ·
                  refine ⟨42195377305057379573016533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28130251536704919715344355 42195377305057379573016533)
                  ·
                    refine ⟨988954155587282333742575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42195377305057379573016533 988954155587282333742575)
                    ·
                      rfl

theorem cell23_5777944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_5777944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777944 prefixEnd_5777944 := by exact prefixLift 5777944
  have htrace : WordTrace (prefixWord ++ tailWord_5777944) baseStart_5777944 baseEnd_5777944 := by
    simpa [prefixWord, tailWord_5777944, baseEnd_5777944] using wordTrace_append hprefix tailTrace_5777944
  have hstable : (prefixWord ++ tailWord_5777944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777944).length < 2 ^ (prefixWord ++ tailWord_5777944).sum := by decide
  have hdescent : baseEnd_5777944 < baseStart_5777944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777954 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_5777954 : Nat := 118140960795 + 5777954 * 2 ^ 59
def prefixEnd_5777954 : Nat := 4983230072969 + 3 ^ 40 * 5777954 * 2
def baseEnd_5777954 : Nat := 2966867601568391962102679

theorem tailTrace_5777954 : CollatzResearch.WordTrace tailWord_5777954 prefixEnd_5777954 2966867601568391962102679 := by
  unfold tailWord_5777954
  simp only [CollatzResearch.WordTrace]
  refine ⟨52684823827366732206367229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140492863539644619216979277 52684823827366732206367229)
  ·
    refine ⟨19756808935262524577387711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52684823827366732206367229 19756808935262524577387711)
    ·
      refine ⟨29635213402893786866081567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19756808935262524577387711 29635213402893786866081567)
      ·
        refine ⟨44452820104340680299122351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29635213402893786866081567 44452820104340680299122351)
        ·
          refine ⟨66679230156511020448683527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44452820104340680299122351 66679230156511020448683527)
          ·
            refine ⟨100018845234766530673025291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66679230156511020448683527 100018845234766530673025291)
            ·
              refine ⟨150028267852149796009537937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100018845234766530673025291 150028267852149796009537937)
              ·
                refine ⟨112521200889112347007153453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150028267852149796009537937 112521200889112347007153453)
                ·
                  refine ⟨42195450333417130127682545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112521200889112347007153453 42195450333417130127682545)
                  ·
                    refine ⟨31646587750062847595761909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42195450333417130127682545 31646587750062847595761909)
                    ·
                      refine ⟨2966867601568391962102679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31646587750062847595761909 2966867601568391962102679)
                      ·
                        rfl

theorem cell23_5777954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_5777954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777954 prefixEnd_5777954 := by exact prefixLift 5777954
  have htrace : WordTrace (prefixWord ++ tailWord_5777954) baseStart_5777954 baseEnd_5777954 := by
    simpa [prefixWord, tailWord_5777954, baseEnd_5777954] using wordTrace_append hprefix tailTrace_5777954
  have hstable : (prefixWord ++ tailWord_5777954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777954).length < 2 ^ (prefixWord ++ tailWord_5777954).sum := by decide
  have hdescent : baseEnd_5777954 < baseStart_5777954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777964 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 4]
def baseStart_5777964 : Nat := 118140960795 + 5777964 * 2 ^ 59
def prefixEnd_5777964 : Nat := 4983230072969 + 3 ^ 40 * 5777964 * 2
def baseEnd_5777964 : Nat := 2966872736374936922977633

theorem tailTrace_5777964 : CollatzResearch.WordTrace tailWord_5777964 prefixEnd_5777964 2966872736374936922977633 := by
  unfold tailWord_5777964
  simp only [CollatzResearch.WordTrace]
  refine ⟨105369830019715350266666473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140493106692953800355555297 105369830019715350266666473)
  ·
    refine ⟨79027372514786512699999855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105369830019715350266666473 79027372514786512699999855)
    ·
      refine ⟨118541058772179769049999783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79027372514786512699999855 118541058772179769049999783)
      ·
        refine ⟨177811588158269653574999675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118541058772179769049999783 177811588158269653574999675)
        ·
          refine ⟨266717382237404480362499513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177811588158269653574999675 266717382237404480362499513)
          ·
            refine ⟨200038036678053360271874635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266717382237404480362499513 200038036678053360271874635)
            ·
              refine ⟨300057055017080040407811953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200038036678053360271874635 300057055017080040407811953)
              ·
                refine ⟨225042791262810030305858965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 300057055017080040407811953 225042791262810030305858965)
                ·
                  refine ⟨10548880840444220170587139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 225042791262810030305858965 10548880840444220170587139)
                  ·
                    refine ⟨15823321260666330255880709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10548880840444220170587139 15823321260666330255880709)
                    ·
                      refine ⟨2966872736374936922977633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15823321260666330255880709 2966872736374936922977633)
                      ·
                        rfl

theorem cell23_5777964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 4].length) (baseStart_5777964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777964 prefixEnd_5777964 := by exact prefixLift 5777964
  have htrace : WordTrace (prefixWord ++ tailWord_5777964) baseStart_5777964 baseEnd_5777964 := by
    simpa [prefixWord, tailWord_5777964, baseEnd_5777964] using wordTrace_append hprefix tailTrace_5777964
  have hstable : (prefixWord ++ tailWord_5777964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777964).length < 2 ^ (prefixWord ++ tailWord_5777964).sum := by decide
  have hdescent : baseEnd_5777964 < baseStart_5777964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777981 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_5777981 : Nat := 118140960795 + 5777981 * 2 ^ 59
def prefixEnd_5777981 : Nat := 4983230072969 + 3 ^ 40 * 5777981 * 2
def baseEnd_5777981 : Nat := 2966881465546063356465055

theorem tailTrace_5777981 : CollatzResearch.WordTrace tailWord_5777981 prefixEnd_5777981 2966881465546063356465055 := by
  unfold tailWord_5777981
  simp only [CollatzResearch.WordTrace]
  refine ⟨210740280080369112436701797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140493520053579408291134531 210740280080369112436701797)
  ·
    refine ⟨39513802515069208581881587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210740280080369112436701797 39513802515069208581881587)
    ·
      refine ⟨59270703772603812872822381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39513802515069208581881587 59270703772603812872822381)
      ·
        refine ⟨22226513914726429827308393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59270703772603812872822381 22226513914726429827308393)
        ·
          refine ⟨16669885436044822370481295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22226513914726429827308393 16669885436044822370481295)
          ·
            refine ⟨25004828154067233555721943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16669885436044822370481295 25004828154067233555721943)
            ·
              refine ⟨37507242231100850333582915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25004828154067233555721943 37507242231100850333582915)
              ·
                refine ⟨56260863346651275500374373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37507242231100850333582915 56260863346651275500374373)
                ·
                  refine ⟨10548911877497114156320195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56260863346651275500374373 10548911877497114156320195)
                  ·
                    refine ⟨15823367816245671234480293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10548911877497114156320195 15823367816245671234480293)
                    ·
                      refine ⟨2966881465546063356465055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15823367816245671234480293 2966881465546063356465055)
                      ·
                        rfl

theorem cell23_5777981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_5777981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777981 prefixEnd_5777981 := by exact prefixLift 5777981
  have htrace : WordTrace (prefixWord ++ tailWord_5777981) baseStart_5777981 baseEnd_5777981 := by
    simpa [prefixWord, tailWord_5777981, baseEnd_5777981] using wordTrace_append hprefix tailTrace_5777981
  have hstable : (prefixWord ++ tailWord_5777981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777981).length < 2 ^ (prefixWord ++ tailWord_5777981).sum := by decide
  have hdescent : baseEnd_5777981 < baseStart_5777981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5777982 : List Nat := [4, 2, 1, 4, 1, 1, 3, 2, 5]
def baseStart_5777982 : Nat := 118140960795 + 5777982 * 2 ^ 59
def prefixEnd_5777982 : Nat := 4983230072969 + 3 ^ 40 * 5777982 * 2
def baseEnd_5777982 : Nat := 329653553225190872505839

theorem tailTrace_5777982 : CollatzResearch.WordTrace tailWord_5777982 prefixEnd_5777982 329653553225190872505839 := by
  unfold tailWord_5777982
  simp only [CollatzResearch.WordTrace]
  refine ⟨26342539569170686200936025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140493544368910326404992133 26342539569170686200936025)
  ·
    refine ⟨19756904676878014650702019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26342539569170686200936025 19756904676878014650702019)
    ·
      refine ⟨29635357015317021976053029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19756904676878014650702019 29635357015317021976053029)
      ·
        refine ⟨5556629440371941620509943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29635357015317021976053029 5556629440371941620509943)
        ·
          refine ⟨8334944160557912430764915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5556629440371941620509943 8334944160557912430764915)
          ·
            refine ⟨12502416240836868646147373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8334944160557912430764915 12502416240836868646147373)
            ·
              refine ⟨4688406090313825742305265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12502416240836868646147373 4688406090313825742305265)
              ·
                refine ⟨3516304567735369306728949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688406090313825742305265 3516304567735369306728949)
                ·
                  refine ⟨329653553225190872505839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3516304567735369306728949 329653553225190872505839)
                  ·
                    rfl

theorem cell23_5777982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 5].length) (baseStart_5777982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5777982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5777982 prefixEnd_5777982 := by exact prefixLift 5777982
  have htrace : WordTrace (prefixWord ++ tailWord_5777982) baseStart_5777982 baseEnd_5777982 := by
    simpa [prefixWord, tailWord_5777982, baseEnd_5777982] using wordTrace_append hprefix tailTrace_5777982
  have hstable : (prefixWord ++ tailWord_5777982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5777982).length < 2 ^ (prefixWord ++ tailWord_5777982).sum := by decide
  have hdescent : baseEnd_5777982 < baseStart_5777982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5777982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778068 : List Nat := [2, 4, 2, 2, 1, 1, 2, 1, 3, 5]
def baseStart_5778068 : Nat := 118140960795 + 5778068 * 2 ^ 59
def prefixEnd_5778068 : Nat := 4983230072969 + 3 ^ 40 * 5778068 * 2
def baseEnd_5778068 : Nat := 988975379454334838692385

theorem tailTrace_5778068 : CollatzResearch.WordTrace tailWord_5778068 prefixEnd_5778068 988975379454334838692385 := by
  unfold tailWord_5778068
  simp only [CollatzResearch.WordTrace]
  refine ⟨105371726615526963147559429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140495635487369284196745905 105371726615526963147559429)
  ·
    refine ⟨19757198740411305590167393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105371726615526963147559429 19757198740411305590167393)
    ·
      refine ⟨14817899055308479192625545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19757198740411305590167393 14817899055308479192625545)
      ·
        refine ⟨11113424291481359394469159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14817899055308479192625545 11113424291481359394469159)
        ·
          refine ⟨16670136437222039091703739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11113424291481359394469159 16670136437222039091703739)
          ·
            refine ⟨25005204655833058637555609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16670136437222039091703739 25005204655833058637555609)
            ·
              refine ⟨18753903491874793978166707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25005204655833058637555609 18753903491874793978166707)
              ·
                refine ⟨28130855237812190967250061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18753903491874793978166707 28130855237812190967250061)
                ·
                  refine ⟨10549070714179571612718773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28130855237812190967250061 10549070714179571612718773)
                  ·
                    refine ⟨988975379454334838692385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10549070714179571612718773 988975379454334838692385)
                    ·
                      rfl

theorem cell23_5778068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_5778068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778068 prefixEnd_5778068 := by exact prefixLift 5778068
  have htrace : WordTrace (prefixWord ++ tailWord_5778068) baseStart_5778068 baseEnd_5778068 := by
    simpa [prefixWord, tailWord_5778068, baseEnd_5778068] using wordTrace_append hprefix tailTrace_5778068
  have hstable : (prefixWord ++ tailWord_5778068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778068).length < 2 ^ (prefixWord ++ tailWord_5778068).sum := by decide
  have hdescent : baseEnd_5778068 < baseStart_5778068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778071 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 4]
def baseStart_5778071 : Nat := 118140960795 + 5778071 * 2 ^ 59
def prefixEnd_5778071 : Nat := 4983230072969 + 3 ^ 40 * 5778071 * 2
def baseEnd_5778071 : Nat := 2966927678804968004339641

theorem tailTrace_5778071 : CollatzResearch.WordTrace tailWord_5778071 prefixEnd_5778071 2966927678804968004339641 := by
  unfold tailWord_5778071
  simp only [CollatzResearch.WordTrace]
  refine ⟨210743562650043057807478067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140495708433362038538318711 210743562650043057807478067)
  ·
    refine ⟨316115343975064586711217101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210743562650043057807478067 316115343975064586711217101)
    ·
      refine ⟨118543253990649220016706413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316115343975064586711217101 118543253990649220016706413)
      ·
        refine ⟨44453720246493457506264905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118543253990649220016706413 44453720246493457506264905)
        ·
          refine ⟨33340290184870093129698679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44453720246493457506264905 33340290184870093129698679)
          ·
            refine ⟨50010435277305139694548019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33340290184870093129698679 50010435277305139694548019)
            ·
              refine ⟨75015652915957709541822029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50010435277305139694548019 75015652915957709541822029)
              ·
                refine ⟨28130869843484141078183261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75015652915957709541822029 28130869843484141078183261)
                ·
                  refine ⟨10549076191306552904318723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28130869843484141078183261 10549076191306552904318723)
                  ·
                    refine ⟨15823614286959829356478085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10549076191306552904318723 15823614286959829356478085)
                    ·
                      refine ⟨2966927678804968004339641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15823614286959829356478085 2966927678804968004339641)
                      ·
                        rfl

theorem cell23_5778071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_5778071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778071 prefixEnd_5778071 := by exact prefixLift 5778071
  have htrace : WordTrace (prefixWord ++ tailWord_5778071) baseStart_5778071 baseEnd_5778071 := by
    simpa [prefixWord, tailWord_5778071, baseEnd_5778071] using wordTrace_append hprefix tailTrace_5778071
  have hstable : (prefixWord ++ tailWord_5778071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778071).length < 2 ^ (prefixWord ++ tailWord_5778071).sum := by decide
  have hdescent : baseEnd_5778071 < baseStart_5778071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778104 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_5778104 : Nat := 118140960795 + 5778104 * 2 ^ 59
def prefixEnd_5778104 : Nat := 4983230072969 + 3 ^ 40 * 5778104 * 2
def baseEnd_5778104 : Nat := 2966944623666566375226989

theorem tailTrace_5778104 : CollatzResearch.WordTrace tailWord_5778104 prefixEnd_5778104 2966944623666566375226989 := by
  unfold tailWord_5778104
  simp only [CollatzResearch.WordTrace]
  refine ⟨105372383129461752221714683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140496510839282336295619577 105372383129461752221714683)
  ·
    refine ⟨158058574694192628332572025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105372383129461752221714683 158058574694192628332572025)
    ·
      refine ⟨118543931020644471249429019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158058574694192628332572025 118543931020644471249429019)
      ·
        refine ⟨177815896530966706874143529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118543931020644471249429019 177815896530966706874143529)
        ·
          refine ⟨133361922398225030155607647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177815896530966706874143529 133361922398225030155607647)
          ·
            refine ⟨200042883597337545233411471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133361922398225030155607647 200042883597337545233411471)
            ·
              refine ⟨300064325396006317850117207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200042883597337545233411471 300064325396006317850117207)
              ·
                refine ⟨450096488094009476775175811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300064325396006317850117207 450096488094009476775175811)
                ·
                  refine ⟨675144732141014215162763717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450096488094009476775175811 675144732141014215162763717)
                  ·
                    refine ⟨126589637276440165343018197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 675144732141014215162763717 126589637276440165343018197)
                    ·
                      refine ⟨2966944623666566375226989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126589637276440165343018197 2966944623666566375226989)
                      ·
                        rfl

theorem cell23_5778104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_5778104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778104 prefixEnd_5778104 := by exact prefixLift 5778104
  have htrace : WordTrace (prefixWord ++ tailWord_5778104) baseStart_5778104 baseEnd_5778104 := by
    simpa [prefixWord, tailWord_5778104, baseEnd_5778104] using wordTrace_append hprefix tailTrace_5778104
  have hstable : (prefixWord ++ tailWord_5778104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778104).length < 2 ^ (prefixWord ++ tailWord_5778104).sum := by decide
  have hdescent : baseEnd_5778104 < baseStart_5778104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778138 : List Nat := [3, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3]
def baseStart_5778138 : Nat := 118140960795 + 5778138 * 2 ^ 59
def prefixEnd_5778138 : Nat := 4983230072969 + 3 ^ 40 * 5778138 * 2
def baseEnd_5778138 : Nat := 2966962082008819242201833

theorem tailTrace_5778138 : CollatzResearch.WordTrace tailWord_5778138 prefixEnd_5778138 2966962082008819242201833 := by
  unfold tailWord_5778138
  simp only [CollatzResearch.WordTrace]
  refine ⟨52686501585200082062541767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140497337560533552166778045 52686501585200082062541767)
  ·
    refine ⟨79029752377800123093812651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52686501585200082062541767 79029752377800123093812651)
    ·
      refine ⟨118544628566700184640718977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79029752377800123093812651 118544628566700184640718977)
      ·
        refine ⟨88908471425025138480539233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118544628566700184640718977 88908471425025138480539233)
        ·
          refine ⟨66681353568768853860404425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88908471425025138480539233 66681353568768853860404425)
          ·
            refine ⟨50011015176576640395303319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66681353568768853860404425 50011015176576640395303319)
            ·
              refine ⟨75016522764864960592954979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50011015176576640395303319 75016522764864960592954979)
              ·
                refine ⟨112524784147297440889432469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75016522764864960592954979 112524784147297440889432469)
                ·
                  refine ⟨5274599256904567541692147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112524784147297440889432469 5274599256904567541692147)
                  ·
                    refine ⟨7911898885356851312538221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5274599256904567541692147 7911898885356851312538221)
                    ·
                      refine ⟨2966962082008819242201833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7911898885356851312538221 2966962082008819242201833)
                      ·
                        rfl

theorem cell23_5778138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 1, 6, 1, 3].length) (baseStart_5778138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778138 prefixEnd_5778138 := by exact prefixLift 5778138
  have htrace : WordTrace (prefixWord ++ tailWord_5778138) baseStart_5778138 baseEnd_5778138 := by
    simpa [prefixWord, tailWord_5778138, baseEnd_5778138] using wordTrace_append hprefix tailTrace_5778138
  have hstable : (prefixWord ++ tailWord_5778138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778138).length < 2 ^ (prefixWord ++ tailWord_5778138).sum := by decide
  have hdescent : baseEnd_5778138 < baseStart_5778138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778161 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 4]
def baseStart_5778161 : Nat := 118140960795 + 5778161 * 2 ^ 59
def prefixEnd_5778161 : Nat := 4983230072969 + 3 ^ 40 * 5778161 * 2
def baseEnd_5778161 : Nat := 2966973892063872652214227

theorem tailTrace_5778161 : CollatzResearch.WordTrace tailWord_5778161 prefixEnd_5778161 2966973892063872652214227 := by
  unfold tailWord_5778161
  simp only [CollatzResearch.WordTrace]
  refine ⟨210746845219717003178254337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140497896813144668785502891 210746845219717003178254337)
  ·
    refine ⟨158060133914787752383690753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210746845219717003178254337 158060133914787752383690753)
    ·
      refine ⟨118545100436090814287768065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158060133914787752383690753 118545100436090814287768065)
      ·
        refine ⟨88908825327068110715826049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118545100436090814287768065 88908825327068110715826049)
        ·
          refine ⟨66681618995301083036869537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88908825327068110715826049 66681618995301083036869537)
          ·
            refine ⟨50011214246475812277652153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66681618995301083036869537 50011214246475812277652153)
            ·
              refine ⟨37508410684856859208239115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50011214246475812277652153 37508410684856859208239115)
              ·
                refine ⟨56262616027285288812358673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37508410684856859208239115 56262616027285288812358673)
                ·
                  refine ⟨42196962020463966609269005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56262616027285288812358673 42196962020463966609269005)
                  ·
                    refine ⟨15823860757673987478475877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42196962020463966609269005 15823860757673987478475877)
                    ·
                      refine ⟨2966973892063872652214227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15823860757673987478475877 2966973892063872652214227)
                      ·
                        rfl

theorem cell23_5778161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 3, 4].length) (baseStart_5778161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778161 prefixEnd_5778161 := by exact prefixLift 5778161
  have htrace : WordTrace (prefixWord ++ tailWord_5778161) baseStart_5778161 baseEnd_5778161 := by
    simpa [prefixWord, tailWord_5778161, baseEnd_5778161] using wordTrace_append hprefix tailTrace_5778161
  have hstable : (prefixWord ++ tailWord_5778161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778161).length < 2 ^ (prefixWord ++ tailWord_5778161).sum := by decide
  have hdescent : baseEnd_5778161 < baseStart_5778161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778172 : List Nat := [2, 2, 2, 1, 3, 2, 4, 1, 2, 1, 3]
def baseStart_5778172 : Nat := 118140960795 + 5778172 * 2 ^ 59
def prefixEnd_5778172 : Nat := 4983230072969 + 3 ^ 40 * 5778172 * 2
def baseEnd_5778172 : Nat := 2966979540351072109176677

theorem tailTrace_5778172 : CollatzResearch.WordTrace tailWord_5778172 prefixEnd_5778172 2966979540351072109176677 := by
  unfold tailWord_5778172
  simp only [CollatzResearch.WordTrace]
  refine ⟨105373623211338576028452385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140498164281784768037936513 105373623211338576028452385)
  ·
    refine ⟨79030217408503932021339289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105373623211338576028452385 79030217408503932021339289)
    ·
      refine ⟨59272663056377949016004467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79030217408503932021339289 59272663056377949016004467)
      ·
        refine ⟨88908994584566923524006701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59272663056377949016004467 88908994584566923524006701)
        ·
          refine ⟨33340872969212596321502513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88908994584566923524006701 33340872969212596321502513)
          ·
            refine ⟨25005654726909447241126885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33340872969212596321502513 25005654726909447241126885)
            ·
              refine ⟨4688560261295521357711291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25005654726909447241126885 4688560261295521357711291)
              ·
                refine ⟨7032840391943282036566937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688560261295521357711291 7032840391943282036566937)
                ·
                  refine ⟨5274630293957461527425203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7032840391943282036566937 5274630293957461527425203)
                  ·
                    refine ⟨7911945440936192291137805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5274630293957461527425203 7911945440936192291137805)
                    ·
                      refine ⟨2966979540351072109176677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7911945440936192291137805 2966979540351072109176677)
                      ·
                        rfl

theorem cell23_5778172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 4, 1, 2, 1, 3].length) (baseStart_5778172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778172 prefixEnd_5778172 := by exact prefixLift 5778172
  have htrace : WordTrace (prefixWord ++ tailWord_5778172) baseStart_5778172 baseEnd_5778172 := by
    simpa [prefixWord, tailWord_5778172, baseEnd_5778172] using wordTrace_append hprefix tailTrace_5778172
  have hstable : (prefixWord ++ tailWord_5778172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778172).length < 2 ^ (prefixWord ++ tailWord_5778172).sum := by decide
  have hdescent : baseEnd_5778172 < baseStart_5778172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778199 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 1, 3, 2]
def baseStart_5778199 : Nat := 118140960795 + 5778199 * 2 ^ 59
def prefixEnd_5778199 : Nat := 4983230072969 + 3 ^ 40 * 5778199 * 2
def baseEnd_5778199 : Nat := 2966993404328743503539053

theorem tailTrace_5778199 : CollatzResearch.WordTrace tailWord_5778199 prefixEnd_5778199 2966993404328743503539053 := by
  unfold tailWord_5778199
  simp only [CollatzResearch.WordTrace]
  refine ⟨210748231193579335668137651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140498820795719557112091767 210748231193579335668137651)
  ·
    refine ⟨316122346790369003502206477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210748231193579335668137651 316122346790369003502206477)
    ·
      refine ⟨118545880046388376313327429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316122346790369003502206477 118545880046388376313327429)
      ·
        refine ⟨22227352508697820558748893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118545880046388376313327429 22227352508697820558748893)
        ·
          refine ⟨8335257190761682709530835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22227352508697820558748893 8335257190761682709530835)
          ·
            refine ⟨12502885786142524064296253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8335257190761682709530835 12502885786142524064296253)
            ·
              refine ⟨4688582169803446524111095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12502885786142524064296253 4688582169803446524111095)
              ·
                refine ⟨7032873254705169786166643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688582169803446524111095 7032873254705169786166643)
                ·
                  refine ⟨10549309882057754679249965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7032873254705169786166643 10549309882057754679249965)
                  ·
                    refine ⟨3955991205771658004718737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10549309882057754679249965 3955991205771658004718737)
                    ·
                      refine ⟨2966993404328743503539053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3955991205771658004718737 2966993404328743503539053)
                      ·
                        rfl

theorem cell23_5778199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_5778199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778199 prefixEnd_5778199 := by exact prefixLift 5778199
  have htrace : WordTrace (prefixWord ++ tailWord_5778199) baseStart_5778199 baseEnd_5778199 := by
    simpa [prefixWord, tailWord_5778199, baseEnd_5778199] using wordTrace_append hprefix tailTrace_5778199
  have hstable : (prefixWord ++ tailWord_5778199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778199).length < 2 ^ (prefixWord ++ tailWord_5778199).sum := by decide
  have hdescent : baseEnd_5778199 < baseStart_5778199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778231 : List Nat := [1, 1, 3, 1, 2, 1, 4, 2, 1, 7]
def baseStart_5778231 : Nat := 118140960795 + 5778231 * 2 ^ 59
def prefixEnd_5778231 : Nat := 4983230072969 + 3 ^ 40 * 5778231 * 2
def baseEnd_5778231 : Nat := 989003278569895792779635

theorem tailTrace_5778231 : CollatzResearch.WordTrace tailWord_5778231 prefixEnd_5778231 989003278569895792779635 := by
  unfold tailWord_5778231
  simp only [CollatzResearch.WordTrace]
  refine ⟨210749398329463405133302547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140499598886308936755535031 210749398329463405133302547)
  ·
    refine ⟨316124097494195107699953821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210749398329463405133302547 316124097494195107699953821)
    ·
      refine ⟨118546536560323165387482683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316124097494195107699953821 118546536560323165387482683)
      ·
        refine ⟨177819804840484748081224025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118546536560323165387482683 177819804840484748081224025)
        ·
          refine ⟨133364853630363561060918019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177819804840484748081224025 133364853630363561060918019)
          ·
            refine ⟨200047280445545341591377029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133364853630363561060918019 200047280445545341591377029)
            ·
              refine ⟨37508865083539751548383193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200047280445545341591377029 37508865083539751548383193)
              ·
                refine ⟨28131648812654813661287395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37508865083539751548383193 28131648812654813661287395)
                ·
                  refine ⟨42197473218982220491931093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28131648812654813661287395 42197473218982220491931093)
                  ·
                    refine ⟨989003278569895792779635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42197473218982220491931093 989003278569895792779635)
                    ·
                      rfl

theorem cell23_5778231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 7].length) (baseStart_5778231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778231 prefixEnd_5778231 := by exact prefixLift 5778231
  have htrace : WordTrace (prefixWord ++ tailWord_5778231) baseStart_5778231 baseEnd_5778231 := by
    simpa [prefixWord, tailWord_5778231, baseEnd_5778231] using wordTrace_append hprefix tailTrace_5778231
  have hstable : (prefixWord ++ tailWord_5778231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778231).length < 2 ^ (prefixWord ++ tailWord_5778231).sum := by decide
  have hdescent : baseEnd_5778231 < baseStart_5778231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778288 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 3]
def baseStart_5778288 : Nat := 118140960795 + 5778288 * 2 ^ 59
def prefixEnd_5778288 : Nat := 4983230072969 + 3 ^ 40 * 5778288 * 2
def baseEnd_5778288 : Nat := 2967039104106993655326143

theorem tailTrace_5778288 : CollatzResearch.WordTrace tailWord_5778288 prefixEnd_5778288 2967039104106993655326143 := by
  unfold tailWord_5778288
  simp only [CollatzResearch.WordTrace]
  refine ⟨105375738645128451934063759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140500984860171269245418345 105375738645128451934063759)
  ·
    refine ⟨158063607967692677901095639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105375738645128451934063759 158063607967692677901095639)
    ·
      refine ⟨237095411951539016851643459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158063607967692677901095639 237095411951539016851643459)
      ·
        refine ⟨355643117927308525277465189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237095411951539016851643459 355643117927308525277465189)
        ·
          refine ⟨66683084611370348489524723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 355643117927308525277465189 66683084611370348489524723)
          ·
            refine ⟨100024626917055522734287085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66683084611370348489524723 100024626917055522734287085)
            ·
              refine ⟨37509235093895821025357657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100024626917055522734287085 37509235093895821025357657)
              ·
                refine ⟨28131926320421865769018243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37509235093895821025357657 28131926320421865769018243)
                ·
                  refine ⟨42197889480632798653527365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28131926320421865769018243 42197889480632798653527365)
                  ·
                    refine ⟨7912104277618649747536381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42197889480632798653527365 7912104277618649747536381)
                    ·
                      refine ⟨2967039104106993655326143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7912104277618649747536381 2967039104106993655326143)
                      ·
                        rfl

theorem cell23_5778288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_5778288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778288 prefixEnd_5778288 := by exact prefixLift 5778288
  have htrace : WordTrace (prefixWord ++ tailWord_5778288) baseStart_5778288 baseEnd_5778288 := by
    simpa [prefixWord, tailWord_5778288, baseEnd_5778288] using wordTrace_append hprefix tailTrace_5778288
  have hstable : (prefixWord ++ tailWord_5778288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778288).length < 2 ^ (prefixWord ++ tailWord_5778288).sum := by decide
  have hdescent : baseEnd_5778288 < baseStart_5778288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778345 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 4, 3, 2]
def baseStart_5778345 : Nat := 118140960795 + 5778345 * 2 ^ 59
def prefixEnd_5778345 : Nat := 4983230072969 + 3 ^ 40 * 5778345 * 2
def baseEnd_5778345 : Nat := 2967068372504299932313381

theorem tailTrace_5778345 : CollatzResearch.WordTrace tailWord_5778345 prefixEnd_5778345 2967068372504299932313381 := by
  unfold tailWord_5778345
  simp only [CollatzResearch.WordTrace]
  refine ⟨210753556251050402602952489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140502370834033601735301659 210753556251050402602952489)
  ·
    refine ⟨158065167188287801952214367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210753556251050402602952489 158065167188287801952214367)
    ·
      refine ⟨237097750782431702928321551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158065167188287801952214367 237097750782431702928321551)
      ·
        refine ⟨355646626173647554392482327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237097750782431702928321551 355646626173647554392482327)
        ·
          refine ⟨533469939260471331588723491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355646626173647554392482327 533469939260471331588723491)
          ·
            refine ⟨800204908890706997383085237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533469939260471331588723491 800204908890706997383085237)
            ·
              refine ⟨75019210208503781004664241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 800204908890706997383085237 75019210208503781004664241)
              ·
                refine ⟨56264407656377835753498181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75019210208503781004664241 56264407656377835753498181)
                ·
                  refine ⟨10549576435570844203780909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56264407656377835753498181 10549576435570844203780909)
                  ·
                    refine ⟨3956091163339066576417841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10549576435570844203780909 3956091163339066576417841)
                    ·
                      refine ⟨2967068372504299932313381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956091163339066576417841 2967068372504299932313381)
                      ·
                        rfl

theorem cell23_5778345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 3, 2].length) (baseStart_5778345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778345 prefixEnd_5778345 := by exact prefixLift 5778345
  have htrace : WordTrace (prefixWord ++ tailWord_5778345) baseStart_5778345 baseEnd_5778345 := by
    simpa [prefixWord, tailWord_5778345, baseEnd_5778345] using wordTrace_append hprefix tailTrace_5778345
  have hstable : (prefixWord ++ tailWord_5778345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778345).length < 2 ^ (prefixWord ++ tailWord_5778345).sum := by decide
  have hdescent : baseEnd_5778345 < baseStart_5778345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778362 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2]
def baseStart_5778362 : Nat := 118140960795 + 5778362 * 2 ^ 59
def prefixEnd_5778362 : Nat := 4983230072969 + 3 ^ 40 * 5778362 * 2
def baseEnd_5778362 : Nat := 2967077101675426365800803

theorem tailTrace_5778362 : CollatzResearch.WordTrace tailWord_5778362 prefixEnd_5778362 2967077101675426365800803 := by
  unfold tailWord_5778362
  simp only [CollatzResearch.WordTrace]
  refine ⟨52688544072997203626580335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140502784194659209670880893 52688544072997203626580335)
  ·
    refine ⟨79032816109495805439870503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52688544072997203626580335 79032816109495805439870503)
    ·
      refine ⟨118549224164243708159805755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79032816109495805439870503 118549224164243708159805755)
      ·
        refine ⟨177823836246365562239708633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118549224164243708159805755 177823836246365562239708633)
        ·
          refine ⟨133367877184774171679781475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177823836246365562239708633 133367877184774171679781475)
          ·
            refine ⟨200051815777161257519672213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133367877184774171679781475 200051815777161257519672213)
            ·
              refine ⟨9377428864554433946234635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200051815777161257519672213 9377428864554433946234635)
              ·
                refine ⟨14066143296831650919351953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9377428864554433946234635 14066143296831650919351953)
                ·
                  refine ⟨10549607472623738189513965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14066143296831650919351953 10549607472623738189513965)
                  ·
                    refine ⟨3956102802233901821067737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10549607472623738189513965 3956102802233901821067737)
                    ·
                      refine ⟨2967077101675426365800803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956102802233901821067737 2967077101675426365800803)
                      ·
                        rfl

theorem cell23_5778362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2].length) (baseStart_5778362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778362 prefixEnd_5778362 := by exact prefixLift 5778362
  have htrace : WordTrace (prefixWord ++ tailWord_5778362) baseStart_5778362 baseEnd_5778362 := by
    simpa [prefixWord, tailWord_5778362, baseEnd_5778362] using wordTrace_append hprefix tailTrace_5778362
  have hstable : (prefixWord ++ tailWord_5778362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778362).length < 2 ^ (prefixWord ++ tailWord_5778362).sum := by decide
  have hdescent : baseEnd_5778362 < baseStart_5778362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778368 : List Nat := [2, 1, 1, 2, 3, 3, 1, 1, 3, 6]
def baseStart_5778368 : Nat := 118140960795 + 5778368 * 2 ^ 59
def prefixEnd_5778368 : Nat := 4983230072969 + 3 ^ 40 * 5778368 * 2
def baseEnd_5778368 : Nat := 989026727519784447441925

theorem tailTrace_5778368 : CollatzResearch.WordTrace tailWord_5778368 prefixEnd_5778368 989026727519784447441925 := by
  unfold tailWord_5778368
  simp only [CollatzResearch.WordTrace]
  refine ⟨105377197564983538765519879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140502930086644718354026505 105377197564983538765519879)
  ·
    refine ⟨158065796347475308148279819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105377197564983538765519879 158065796347475308148279819)
    ·
      refine ⟨237098694521212962222419729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158065796347475308148279819 237098694521212962222419729)
      ·
        refine ⟨177824020890909721666814797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237098694521212962222419729 177824020890909721666814797)
        ·
          refine ⟨66684007834091145625055549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177824020890909721666814797 66684007834091145625055549)
          ·
            refine ⟨25006502937784179609395831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66684007834091145625055549 25006502937784179609395831)
            ·
              refine ⟨37509754406676269414093747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25006502937784179609395831 37509754406676269414093747)
              ·
                refine ⟨56264631610014404121140621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37509754406676269414093747 56264631610014404121140621)
                ·
                  refine ⟨21099236853755401545427733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56264631610014404121140621 21099236853755401545427733)
                  ·
                    refine ⟨989026727519784447441925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21099236853755401545427733 989026727519784447441925)
                    ·
                      rfl

theorem cell23_5778368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_5778368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778368 prefixEnd_5778368 := by exact prefixLift 5778368
  have htrace : WordTrace (prefixWord ++ tailWord_5778368) baseStart_5778368 baseEnd_5778368 := by
    simpa [prefixWord, tailWord_5778368, baseEnd_5778368] using wordTrace_append hprefix tailTrace_5778368
  have hstable : (prefixWord ++ tailWord_5778368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778368).length < 2 ^ (prefixWord ++ tailWord_5778368).sum := by decide
  have hdescent : baseEnd_5778368 < baseStart_5778368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778375 : List Nat := [1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_5778375 : Nat := 118140960795 + 5778375 * 2 ^ 59
def prefixEnd_5778375 : Nat := 4983230072969 + 3 ^ 40 * 5778375 * 2
def baseEnd_5778375 : Nat := 2967083776923934814938243

theorem tailTrace_5778375 : CollatzResearch.WordTrace tailWord_5778375 prefixEnd_5778375 2967083776923934814938243 := by
  unfold tailWord_5778375
  simp only [CollatzResearch.WordTrace]
  refine ⟨210754650440941717726544579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140503100293961145151029719 210754650440941717726544579)
  ·
    refine ⟨316131975661412576589816869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210754650440941717726544579 316131975661412576589816869)
    ·
      refine ⟨59274745436514858110590663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316131975661412576589816869 59274745436514858110590663)
      ·
        refine ⟨88912118154772287165885995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59274745436514858110590663 88912118154772287165885995)
        ·
          refine ⟨133368177232158430748828993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88912118154772287165885995 133368177232158430748828993)
          ·
            refine ⟨100026132924118823061621745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133368177232158430748828993 100026132924118823061621745)
            ·
              refine ⟨75019599693089117296216309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100026132924118823061621745 75019599693089117296216309)
              ·
                refine ⟨7033087471227104746520279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75019599693089117296216309 7033087471227104746520279)
                ·
                  refine ⟨10549631206840657119780419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7033087471227104746520279 10549631206840657119780419)
                  ·
                    refine ⟨15824446810260985679670629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10549631206840657119780419 15824446810260985679670629)
                    ·
                      refine ⟨2967083776923934814938243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15824446810260985679670629 2967083776923934814938243)
                      ·
                        rfl

theorem cell23_5778375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_5778375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778375 prefixEnd_5778375 := by exact prefixLift 5778375
  have htrace : WordTrace (prefixWord ++ tailWord_5778375) baseStart_5778375 baseEnd_5778375 := by
    simpa [prefixWord, tailWord_5778375, baseEnd_5778375] using wordTrace_append hprefix tailTrace_5778375
  have hstable : (prefixWord ++ tailWord_5778375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778375).length < 2 ^ (prefixWord ++ tailWord_5778375).sum := by decide
  have hdescent : baseEnd_5778375 < baseStart_5778375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778386 : List Nat := [3, 2, 2, 3, 1, 2, 1, 4, 1, 1, 3]
def baseStart_5778386 : Nat := 118140960795 + 5778386 * 2 ^ 59
def prefixEnd_5778386 : Nat := 4983230072969 + 3 ^ 40 * 5778386 * 2
def baseEnd_5778386 : Nat := 2967089425211134271900693

theorem tailTrace_5778386 : CollatzResearch.WordTrace tailWord_5778386 prefixEnd_5778386 2967089425211134271900693 := by
  unfold tailWord_5778386
  simp only [CollatzResearch.WordTrace]
  refine ⟨52688762910975466651298753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140503367762601244403463341 52688762910975466651298753)
  ·
    refine ⟨39516572183231599988474065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52688762910975466651298753 39516572183231599988474065)
    ·
      refine ⟨29637429137423699991355549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39516572183231599988474065 29637429137423699991355549)
      ·
        refine ⟨11114035926533887496758331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29637429137423699991355549 11114035926533887496758331)
        ·
          refine ⟨16671053889800831245137497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11114035926533887496758331 16671053889800831245137497)
          ·
            refine ⟨12503290417350623433853123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16671053889800831245137497 12503290417350623433853123)
            ·
              refine ⟨18754935626025935150779685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12503290417350623433853123 18754935626025935150779685)
              ·
                refine ⟨3516550429879862840771191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18754935626025935150779685 3516550429879862840771191)
                ·
                  refine ⟨5274825644819794261156787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516550429879862840771191 5274825644819794261156787)
                  ·
                    refine ⟨7912238467229691391735181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5274825644819794261156787 7912238467229691391735181)
                    ·
                      refine ⟨2967089425211134271900693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7912238467229691391735181 2967089425211134271900693)
                      ·
                        rfl

theorem cell23_5778386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_5778386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778386 prefixEnd_5778386 := by exact prefixLift 5778386
  have htrace : WordTrace (prefixWord ++ tailWord_5778386) baseStart_5778386 baseEnd_5778386 := by
    simpa [prefixWord, tailWord_5778386, baseEnd_5778386] using wordTrace_append hprefix tailTrace_5778386
  have hstable : (prefixWord ++ tailWord_5778386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778386).length < 2 ^ (prefixWord ++ tailWord_5778386).sum := by decide
  have hdescent : baseEnd_5778386 < baseStart_5778386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778402 : List Nat := [3, 3, 3, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5778402 : Nat := 118140960795 + 5778402 * 2 ^ 59
def prefixEnd_5778402 : Nat := 4983230072969 + 3 ^ 40 * 5778402 * 2
def baseEnd_5778402 : Nat := 989032546967202069766873

theorem tailTrace_5778402 : CollatzResearch.WordTrace tailWord_5778402 prefixEnd_5778402 989032546967202069766873 := by
  unfold tailWord_5778402
  simp only [CollatzResearch.WordTrace]
  refine ⟨52688908802960975334444365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140503756807895934225184973 52688908802960975334444365)
  ·
    refine ⟨19758340801110365750416637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52688908802960975334444365 19758340801110365750416637)
    ·
      refine ⟨7409377800416387156406239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19758340801110365750416637 7409377800416387156406239)
      ·
        refine ⟨11114066700624580734609359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7409377800416387156406239 11114066700624580734609359)
        ·
          refine ⟨16671100050936871101914039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11114066700624580734609359 16671100050936871101914039)
          ·
            refine ⟨25006650076405306652871059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16671100050936871101914039 25006650076405306652871059)
            ·
              refine ⟨37509975114607959979306589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25006650076405306652871059 37509975114607959979306589)
              ·
                refine ⟨14066240667977984992239971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37509975114607959979306589 14066240667977984992239971)
                ·
                  refine ⟨21099361001966977488359957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14066240667977984992239971 21099361001966977488359957)
                  ·
                    refine ⟨989032546967202069766873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21099361001966977488359957 989032546967202069766873)
                    ·
                      rfl

theorem cell23_5778402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5778402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778402 prefixEnd_5778402 := by exact prefixLift 5778402
  have htrace : WordTrace (prefixWord ++ tailWord_5778402) baseStart_5778402 baseEnd_5778402 := by
    simpa [prefixWord, tailWord_5778402, baseEnd_5778402] using wordTrace_append hprefix tailTrace_5778402
  have hstable : (prefixWord ++ tailWord_5778402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778402).length < 2 ^ (prefixWord ++ tailWord_5778402).sum := by decide
  have hdescent : baseEnd_5778402 < baseStart_5778402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778415 : List Nat := [1, 1, 2, 1, 4, 4, 3, 7]
def baseStart_5778415 : Nat := 118140960795 + 5778415 * 2 ^ 59
def prefixEnd_5778415 : Nat := 4983230072969 + 3 ^ 40 * 5778415 * 2
def baseEnd_5778415 : Nat := 109892752450004246608817

theorem tailTrace_5778415 : CollatzResearch.WordTrace tailWord_5778415 prefixEnd_5778415 109892752450004246608817 := by
  unfold tailWord_5778415
  simp only [CollatzResearch.WordTrace]
  refine ⟨210756109360796804558000699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140504072907197869705333799 210756109360796804558000699)
  ·
    refine ⟨316134164041195206837001049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210756109360796804558000699 316134164041195206837001049)
    ·
      refine ⟨237100623030896405127750787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316134164041195206837001049 237100623030896405127750787)
      ·
        refine ⟨355650934546344607691626181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237100623030896405127750787 355650934546344607691626181)
        ·
          refine ⟨66684550227439613942179909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 355650934546344607691626181 66684550227439613942179909)
          ·
            refine ⟨12503353167644927614158733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66684550227439613942179909 12503353167644927614158733)
            ·
              refine ⟨4688757437866847855309525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12503353167644927614158733 4688757437866847855309525)
              ·
                refine ⟨109892752450004246608817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4688757437866847855309525 109892752450004246608817)
                ·
                  rfl

theorem cell23_5778415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 3, 7].length) (baseStart_5778415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778415 prefixEnd_5778415 := by exact prefixLift 5778415
  have htrace : WordTrace (prefixWord ++ tailWord_5778415) baseStart_5778415 baseEnd_5778415 := by
    simpa [prefixWord, tailWord_5778415, baseEnd_5778415] using wordTrace_append hprefix tailTrace_5778415
  have hstable : (prefixWord ++ tailWord_5778415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778415).length < 2 ^ (prefixWord ++ tailWord_5778415).sum := by decide
  have hdescent : baseEnd_5778415 < baseStart_5778415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778422 : List Nat := [5, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_5778422 : Nat := 118140960795 + 5778422 * 2 ^ 59
def prefixEnd_5778422 : Nat := 4983230072969 + 3 ^ 40 * 5778422 * 2
def baseEnd_5778422 : Nat := 2967107910514696131050527

theorem tailTrace_5778422 : CollatzResearch.WordTrace tailWord_5778422 prefixEnd_5778422 2967107910514696131050527 := by
  unfold tailWord_5778422
  simp only [CollatzResearch.WordTrace]
  refine ⟨13172272791985715297094095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140504243114514296502337013 13172272791985715297094095)
  ·
    refine ⟨19758409187978572945641143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13172272791985715297094095 19758409187978572945641143)
    ·
      refine ⟨29637613781967859418461715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19758409187978572945641143 29637613781967859418461715)
      ·
        refine ⟨44456420672951789127692573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29637613781967859418461715 44456420672951789127692573)
        ·
          refine ⟨16671157752356920922884715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44456420672951789127692573 16671157752356920922884715)
          ·
            refine ⟨25006736628535381384327073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16671157752356920922884715 25006736628535381384327073)
            ·
              refine ⟨18755052471401536038245305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25006736628535381384327073 18755052471401536038245305)
              ·
                refine ⟨14066289353551152028683979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18755052471401536038245305 14066289353551152028683979)
                ·
                  refine ⟨21099434030326728043025969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14066289353551152028683979 21099434030326728043025969)
                  ·
                    refine ⟨15824575522745046032269477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21099434030326728043025969 15824575522745046032269477)
                    ·
                      refine ⟨2967107910514696131050527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15824575522745046032269477 2967107910514696131050527)
                      ·
                        rfl

theorem cell23_5778422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_5778422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778422 prefixEnd_5778422 := by exact prefixLift 5778422
  have htrace : WordTrace (prefixWord ++ tailWord_5778422) baseStart_5778422 baseEnd_5778422 := by
    simpa [prefixWord, tailWord_5778422, baseEnd_5778422] using wordTrace_append hprefix tailTrace_5778422
  have hstable : (prefixWord ++ tailWord_5778422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778422).length < 2 ^ (prefixWord ++ tailWord_5778422).sum := by decide
  have hdescent : baseEnd_5778422 < baseStart_5778422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778425 : List Nat := [1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 3]
def baseStart_5778425 : Nat := 118140960795 + 5778425 * 2 ^ 59
def prefixEnd_5778425 : Nat := 4983230072969 + 3 ^ 40 * 5778425 * 2
def baseEnd_5778425 : Nat := 2967109450956659619313013

theorem tailTrace_5778425 : CollatzResearch.WordTrace tailWord_5778425 prefixEnd_5778425 2967109450956659619313013 := by
  unfold tailWord_5778425
  simp only [CollatzResearch.WordTrace]
  refine ⟨210756474090760576265864729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140504316060507050843909819 210756474090760576265864729)
  ·
    refine ⟨158067355568070432199398547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210756474090760576265864729 158067355568070432199398547)
    ·
      refine ⟨237101033352105648299097821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158067355568070432199398547 237101033352105648299097821)
      ·
        refine ⟨88912887507039618112161683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237101033352105648299097821 88912887507039618112161683)
        ·
          refine ⟨133369331260559427168242525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88912887507039618112161683 133369331260559427168242525)
          ·
            refine ⟨50013499222709785188090947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133369331260559427168242525 50013499222709785188090947)
            ·
              refine ⟨75020248834064677782136421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50013499222709785188090947 75020248834064677782136421)
              ·
                refine ⟨14066296656387127084150579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75020248834064677782136421 14066296656387127084150579)
                ·
                  refine ⟨21099444984580690626225869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14066296656387127084150579 21099444984580690626225869)
                  ·
                    refine ⟨7912291869217758984834701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21099444984580690626225869 7912291869217758984834701)
                    ·
                      refine ⟨2967109450956659619313013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7912291869217758984834701 2967109450956659619313013)
                      ·
                        rfl

theorem cell23_5778425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 3].length) (baseStart_5778425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778425 prefixEnd_5778425 := by exact prefixLift 5778425
  have htrace : WordTrace (prefixWord ++ tailWord_5778425) baseStart_5778425 baseEnd_5778425 := by
    simpa [prefixWord, tailWord_5778425, baseEnd_5778425] using wordTrace_append hprefix tailTrace_5778425
  have hstable : (prefixWord ++ tailWord_5778425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778425).length < 2 ^ (prefixWord ++ tailWord_5778425).sum := by decide
  have hdescent : baseEnd_5778425 < baseStart_5778425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778469 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 1, 3, 2]
def baseStart_5778469 : Nat := 118140960795 + 5778469 * 2 ^ 59
def prefixEnd_5778469 : Nat := 4983230072969 + 3 ^ 40 * 5778469 * 2
def baseEnd_5778469 : Nat := 2967132044105457447162811

theorem tailTrace_5778469 : CollatzResearch.WordTrace tailWord_5778469 prefixEnd_5778469 2967132044105457447162811 := by
  unfold tailWord_5778469
  simp only [CollatzResearch.WordTrace]
  refine ⟨210758078902601171780466461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140505385935067447853644307 210758078902601171780466461)
  ·
    refine ⟨79034279588475439417674923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210758078902601171780466461 79034279588475439417674923)
    ·
      refine ⟨118551419382713159126512385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79034279588475439417674923 118551419382713159126512385)
      ·
        refine ⟨88913564537034869344884289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118551419382713159126512385 88913564537034869344884289)
        ·
          refine ⟨66685173402776152008663217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88913564537034869344884289 66685173402776152008663217)
          ·
            refine ⟨50013880052082114006497413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66685173402776152008663217 50013880052082114006497413)
            ·
              refine ⟨9377602509765396376218265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50013880052082114006497413 9377602509765396376218265)
              ·
                refine ⟨7033201882324047282163699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9377602509765396376218265 7033201882324047282163699)
                ·
                  refine ⟨10549802823486070923245549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7033201882324047282163699 10549802823486070923245549)
                  ·
                    refine ⟨3956176058807276596217081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10549802823486070923245549 3956176058807276596217081)
                    ·
                      refine ⟨2967132044105457447162811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956176058807276596217081 2967132044105457447162811)
                      ·
                        rfl

theorem cell23_5778469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 1, 3, 2].length) (baseStart_5778469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778469 prefixEnd_5778469 := by exact prefixLift 5778469
  have htrace : WordTrace (prefixWord ++ tailWord_5778469) baseStart_5778469 baseEnd_5778469 := by
    simpa [prefixWord, tailWord_5778469, baseEnd_5778469] using wordTrace_append hprefix tailTrace_5778469
  have hstable : (prefixWord ++ tailWord_5778469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778469).length < 2 ^ (prefixWord ++ tailWord_5778469).sum := by decide
  have hdescent : baseEnd_5778469 < baseStart_5778469 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778482 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2]
def baseStart_5778482 : Nat := 118140960795 + 5778482 * 2 ^ 59
def prefixEnd_5778482 : Nat := 4983230072969 + 3 ^ 40 * 5778482 * 2
def baseEnd_5778482 : Nat := 2967138719353965896300251

theorem tailTrace_5778482 : CollatzResearch.WordTrace tailWord_5778482 prefixEnd_5778482 2967138719353965896300251 := by
  unfold tailWord_5778482
  simp only [CollatzResearch.WordTrace]
  refine ⟨52689638262888518750172425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140505702034369383333793133 52689638262888518750172425)
  ·
    refine ⟨39517228697166389062629319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52689638262888518750172425 39517228697166389062629319)
    ·
      refine ⟨59275843045749583593943979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39517228697166389062629319 59275843045749583593943979)
      ·
        refine ⟨88913764568624375390915969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59275843045749583593943979 88913764568624375390915969)
        ·
          refine ⟨66685323426468281543186977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88913764568624375390915969 66685323426468281543186977)
          ·
            refine ⟨50013992569851211157390233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66685323426468281543186977 50013992569851211157390233)
            ·
              refine ⟨37510494427388408368042675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50013992569851211157390233 37510494427388408368042675)
              ·
                refine ⟨56265741641082612552064013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37510494427388408368042675 56265741641082612552064013)
                ·
                  refine ⟨21099653115405979707024005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56265741641082612552064013 21099653115405979707024005)
                  ·
                    refine ⟨3956184959138621195067001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21099653115405979707024005 3956184959138621195067001)
                    ·
                      refine ⟨2967138719353965896300251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956184959138621195067001 2967138719353965896300251)
                      ·
                        rfl

theorem cell23_5778482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_5778482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778482 prefixEnd_5778482 := by exact prefixLift 5778482
  have htrace : WordTrace (prefixWord ++ tailWord_5778482) baseStart_5778482 baseEnd_5778482 := by
    simpa [prefixWord, tailWord_5778482, baseEnd_5778482] using wordTrace_append hprefix tailTrace_5778482
  have hstable : (prefixWord ++ tailWord_5778482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778482).length < 2 ^ (prefixWord ++ tailWord_5778482).sum := by decide
  have hdescent : baseEnd_5778482 < baseStart_5778482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778485 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_5778485 : Nat := 118140960795 + 5778485 * 2 ^ 59
def prefixEnd_5778485 : Nat := 4983230072969 + 3 ^ 40 * 5778485 * 2
def baseEnd_5778485 : Nat := 2967140259795929384562737

theorem tailTrace_5778485 : CollatzResearch.WordTrace tailWord_5778485 prefixEnd_5778485 2967140259795929384562737 := by
  unfold tailWord_5778485
  simp only [CollatzResearch.WordTrace]
  refine ⟨210758662470543206513048909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140505774980362137675365939 210758662470543206513048909)
  ·
    refine ⟨79034498426453702442393341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210758662470543206513048909 79034498426453702442393341)
    ·
      refine ⟨29637936909920138415897503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79034498426453702442393341 29637936909920138415897503)
      ·
        refine ⟨44456905364880207623846255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29637936909920138415897503 44456905364880207623846255)
        ·
          refine ⟨66685358047320311435769383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44456905364880207623846255 66685358047320311435769383)
          ·
            refine ⟨100028037070980467153654075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66685358047320311435769383 100028037070980467153654075)
            ·
              refine ⟨150042055606470700730481113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100028037070980467153654075 150042055606470700730481113)
              ·
                refine ⟨112531541704853025547860835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150042055606470700730481113 112531541704853025547860835)
                ·
                  refine ⟨168797312557279538321791253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112531541704853025547860835 168797312557279538321791253)
                  ·
                    refine ⟨7912374026122478358833965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 168797312557279538321791253 7912374026122478358833965)
                    ·
                      refine ⟨2967140259795929384562737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7912374026122478358833965 2967140259795929384562737)
                      ·
                        rfl

theorem cell23_5778485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_5778485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778485 prefixEnd_5778485 := by exact prefixLift 5778485
  have htrace : WordTrace (prefixWord ++ tailWord_5778485) baseStart_5778485 baseEnd_5778485 := by
    simpa [prefixWord, tailWord_5778485, baseEnd_5778485] using wordTrace_append hprefix tailTrace_5778485
  have hstable : (prefixWord ++ tailWord_5778485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778485).length < 2 ^ (prefixWord ++ tailWord_5778485).sum := by decide
  have hdescent : baseEnd_5778485 < baseStart_5778485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778486 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_5778486 : Nat := 118140960795 + 5778486 * 2 ^ 59
def prefixEnd_5778486 : Nat := 4983230072969 + 3 ^ 40 * 5778486 * 2
def baseEnd_5778486 : Nat := 2967140773276583880650233

theorem tailTrace_5778486 : CollatzResearch.WordTrace tailWord_5778486 prefixEnd_5778486 2967140773276583880650233 := by
  unfold tailWord_5778486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13172418683971223980239707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140505799295693055789223541 13172418683971223980239707)
  ·
    refine ⟨19758628025956835970359561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13172418683971223980239707 19758628025956835970359561)
    ·
      refine ⟨14818971019467626977769671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19758628025956835970359561 14818971019467626977769671)
      ·
        refine ⟨22228456529201440466654507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14818971019467626977769671 22228456529201440466654507)
        ·
          refine ⟨33342684793802160699981761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22228456529201440466654507 33342684793802160699981761)
          ·
            refine ⟨25007013595351620524986321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33342684793802160699981761 25007013595351620524986321)
            ·
              refine ⟨18755260196513715393739741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25007013595351620524986321 18755260196513715393739741)
              ·
                refine ⟨7033222573692643272652403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18755260196513715393739741 7033222573692643272652403)
                ·
                  refine ⟨10549833860538964908978605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7033222573692643272652403 10549833860538964908978605)
                  ·
                    refine ⟨3956187697702111840866977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10549833860538964908978605 3956187697702111840866977)
                    ·
                      refine ⟨2967140773276583880650233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956187697702111840866977 2967140773276583880650233)
                      ·
                        rfl

theorem cell23_5778486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_5778486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778486 prefixEnd_5778486 := by exact prefixLift 5778486
  have htrace : WordTrace (prefixWord ++ tailWord_5778486) baseStart_5778486 baseEnd_5778486 := by
    simpa [prefixWord, tailWord_5778486, baseEnd_5778486] using wordTrace_append hprefix tailTrace_5778486
  have hstable : (prefixWord ++ tailWord_5778486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778486).length < 2 ^ (prefixWord ++ tailWord_5778486).sum := by decide
  have hdescent : baseEnd_5778486 < baseStart_5778486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778499 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 2, 2, 2]
def baseStart_5778499 : Nat := 118140960795 + 5778499 * 2 ^ 59
def prefixEnd_5778499 : Nat := 4983230072969 + 3 ^ 40 * 5778499 * 2
def baseEnd_5778499 : Nat := 2967147448525092329787673

theorem tailTrace_5778499 : CollatzResearch.WordTrace tailWord_5778499 prefixEnd_5778499 2967147448525092329787673 := by
  unfold tailWord_5778499
  simp only [CollatzResearch.WordTrace]
  refine ⟨210759173092492486904058551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140506115394994991269372367 210759173092492486904058551)
  ·
    refine ⟨316138759638738730356087827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210759173092492486904058551 316138759638738730356087827)
    ·
      refine ⟨474208139458108095534131741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316138759638738730356087827 474208139458108095534131741)
      ·
        refine ⟨177828052296790535825299403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474208139458108095534131741 177828052296790535825299403)
        ·
          refine ⟨266742078445185803737949105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177828052296790535825299403 266742078445185803737949105)
          ·
            refine ⟨200056558833889352803461829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266742078445185803737949105 200056558833889352803461829)
            ·
              refine ⟨37510604781354253650649093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200056558833889352803461829 37510604781354253650649093)
              ·
                refine ⟨7033238396503922559496705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37510604781354253650649093 7033238396503922559496705)
                ·
                  refine ⟨5274928797377941919622529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7033238396503922559496705 5274928797377941919622529)
                  ·
                    refine ⟨3956196598033456439716897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5274928797377941919622529 3956196598033456439716897)
                    ·
                      refine ⟨2967147448525092329787673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956196598033456439716897 2967147448525092329787673)
                      ·
                        rfl

theorem cell23_5778499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 2, 2, 2].length) (baseStart_5778499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778499 prefixEnd_5778499 := by exact prefixLift 5778499
  have htrace : WordTrace (prefixWord ++ tailWord_5778499) baseStart_5778499 baseEnd_5778499 := by
    simpa [prefixWord, tailWord_5778499, baseEnd_5778499] using wordTrace_append hprefix tailTrace_5778499
  have hstable : (prefixWord ++ tailWord_5778499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778499).length < 2 ^ (prefixWord ++ tailWord_5778499).sum := by decide
  have hdescent : baseEnd_5778499 < baseStart_5778499 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778575 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 3]
def baseStart_5778575 : Nat := 118140960795 + 5778575 * 2 ^ 59
def prefixEnd_5778575 : Nat := 4983230072969 + 3 ^ 40 * 5778575 * 2
def baseEnd_5778575 : Nat := 2967186473054834032437323

theorem tailTrace_5778575 : CollatzResearch.WordTrace tailWord_5778575 prefixEnd_5778575 2967186473054834032437323 := by
  unfold tailWord_5778575
  simp only [CollatzResearch.WordTrace]
  refine ⟨210761945040217151883825179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140507963360144767922550119 210761945040217151883825179)
  ·
    refine ⟨316142917560325727825737769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210761945040217151883825179 316142917560325727825737769)
    ·
      refine ⟨237107188170244295869303327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316142917560325727825737769 237107188170244295869303327)
      ·
        refine ⟨355660782255366443803954991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237107188170244295869303327 355660782255366443803954991)
        ·
          refine ⟨533491173383049665705932487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355660782255366443803954991 533491173383049665705932487)
          ·
            refine ⟨800236760074574498558898731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533491173383049665705932487 800236760074574498558898731)
            ·
              refine ⟨1200355140111861747838348097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800236760074574498558898731 1200355140111861747838348097)
              ·
                refine ⟨900266355083896310878761073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1200355140111861747838348097 900266355083896310878761073)
                ·
                  refine ⟨675199766312922233159070805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 900266355083896310878761073 675199766312922233159070805)
                  ·
                    refine ⟨7912497261479557419832861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 675199766312922233159070805 7912497261479557419832861)
                    ·
                      refine ⟨2967186473054834032437323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7912497261479557419832861 2967186473054834032437323)
                      ·
                        rfl

theorem cell23_5778575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 8, 3].length) (baseStart_5778575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778575 prefixEnd_5778575 := by exact prefixLift 5778575
  have htrace : WordTrace (prefixWord ++ tailWord_5778575) baseStart_5778575 baseEnd_5778575 := by
    simpa [prefixWord, tailWord_5778575, baseEnd_5778575] using wordTrace_append hprefix tailTrace_5778575
  have hstable : (prefixWord ++ tailWord_5778575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778575).length < 2 ^ (prefixWord ++ tailWord_5778575).sum := by decide
  have hdescent : baseEnd_5778575 < baseStart_5778575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778592 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 3]
def baseStart_5778592 : Nat := 118140960795 + 5778592 * 2 ^ 59
def prefixEnd_5778592 : Nat := 4983230072969 + 3 ^ 40 * 5778592 * 2
def baseEnd_5778592 : Nat := 2967195202225960465924745

theorem tailTrace_5778592 : CollatzResearch.WordTrace tailWord_5778592 prefixEnd_5778592 2967195202225960465924745 := by
  unfold tailWord_5778592
  simp only [CollatzResearch.WordTrace]
  refine ⟨105381282540577781893597015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140508376720770375858129353 105381282540577781893597015)
  ·
    refine ⟨158071923810866672840395523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105381282540577781893597015 158071923810866672840395523)
    ·
      refine ⟨237107885716300009260593285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158071923810866672840395523 237107885716300009260593285)
      ·
        refine ⟨44457728571806251736361241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237107885716300009260593285 44457728571806251736361241)
        ·
          refine ⟨33343296428854688802270931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44457728571806251736361241 33343296428854688802270931)
          ·
            refine ⟨50014944643282033203406397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33343296428854688802270931 50014944643282033203406397)
            ·
              refine ⟨18755604241230762451277399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50014944643282033203406397 18755604241230762451277399)
              ·
                refine ⟨28133406361846143676916099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18755604241230762451277399 28133406361846143676916099)
                ·
                  refine ⟨42200109542769215515374149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28133406361846143676916099 42200109542769215515374149)
                  ·
                    refine ⟨7912520539269227909132653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42200109542769215515374149 7912520539269227909132653)
                    ·
                      refine ⟨2967195202225960465924745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7912520539269227909132653 2967195202225960465924745)
                      ·
                        rfl

theorem cell23_5778592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_5778592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778592 prefixEnd_5778592 := by exact prefixLift 5778592
  have htrace : WordTrace (prefixWord ++ tailWord_5778592) baseStart_5778592 baseEnd_5778592 := by
    simpa [prefixWord, tailWord_5778592, baseEnd_5778592] using wordTrace_append hprefix tailTrace_5778592
  have hstable : (prefixWord ++ tailWord_5778592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778592).length < 2 ^ (prefixWord ++ tailWord_5778592).sum := by decide
  have hdescent : baseEnd_5778592 < baseStart_5778592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778615 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 8]
def baseStart_5778615 : Nat := 118140960795 + 5778615 * 2 ^ 59
def prefixEnd_5778615 : Nat := 4983230072969 + 3 ^ 40 * 5778615 * 2
def baseEnd_5778615 : Nat := 2967207012281013875937139

theorem tailTrace_5778615 : CollatzResearch.WordTrace tailWord_5778615 prefixEnd_5778615 2967207012281013875937139 := by
  unfold tailWord_5778615
  simp only [CollatzResearch.WordTrace]
  refine ⟨210763403960072238715281299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140508935973381492476854199 210763403960072238715281299)
  ·
    refine ⟨316145105940108358072921949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210763403960072238715281299 316145105940108358072921949)
    ·
      refine ⟨118554414727540634277345731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316145105940108358072921949 118554414727540634277345731)
      ·
        refine ⟨177831622091310951416018597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118554414727540634277345731 177831622091310951416018597)
        ·
          refine ⟨33343429142120803390503487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177831622091310951416018597 33343429142120803390503487)
          ·
            refine ⟨50015143713181205085755231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33343429142120803390503487 50015143713181205085755231)
            ·
              refine ⟨75022715569771807628632847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50015143713181205085755231 75022715569771807628632847)
              ·
                refine ⟨112534073354657711442949271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75022715569771807628632847 112534073354657711442949271)
                ·
                  refine ⟨168801110031986567164423907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112534073354657711442949271 168801110031986567164423907)
                  ·
                    refine ⟨253201665047979850746635861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 168801110031986567164423907 253201665047979850746635861)
                    ·
                      refine ⟨2967207012281013875937139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 253201665047979850746635861 2967207012281013875937139)
                      ·
                        rfl

theorem cell23_5778615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_5778615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778615 prefixEnd_5778615 := by exact prefixLift 5778615
  have htrace : WordTrace (prefixWord ++ tailWord_5778615) baseStart_5778615 baseEnd_5778615 := by
    simpa [prefixWord, tailWord_5778615, baseEnd_5778615] using wordTrace_append hprefix tailTrace_5778615
  have hstable : (prefixWord ++ tailWord_5778615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778615).length < 2 ^ (prefixWord ++ tailWord_5778615).sum := by decide
  have hdescent : baseEnd_5778615 < baseStart_5778615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778649 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 2, 3, 2]
def baseStart_5778649 : Nat := 118140960795 + 5778649 * 2 ^ 59
def prefixEnd_5778649 : Nat := 4983230072969 + 3 ^ 40 * 5778649 * 2
def baseEnd_5778649 : Nat := 2967224470623266742911983

theorem tailTrace_5778649 : CollatzResearch.WordTrace tailWord_5778649 prefixEnd_5778649 2967224470623266742911983 := by
  unfold tailWord_5778649
  simp only [CollatzResearch.WordTrace]
  refine ⟨210764644041949062522019001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140509762694632708348012667 210764644041949062522019001)
  ·
    refine ⟨158073483031461796891514251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210764644041949062522019001 158073483031461796891514251)
    ·
      refine ⟨237110224547192695337271377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158073483031461796891514251 237110224547192695337271377)
      ·
        refine ⟨177832668410394521502953533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237110224547192695337271377 177832668410394521502953533)
        ·
          refine ⟨66687250653897945563607575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177832668410394521502953533 66687250653897945563607575)
          ·
            refine ⟨100030875980846918345411363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66687250653897945563607575 100030875980846918345411363)
            ·
              refine ⟨150046313971270377518117045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100030875980846918345411363 150046313971270377518117045)
              ·
                refine ⟨14066841934806597892323473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150046313971270377518117045 14066841934806597892323473)
                ·
                  refine ⟨10550131451104948419242605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14066841934806597892323473 10550131451104948419242605)
                  ·
                    refine ⟨3956299294164355657215977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10550131451104948419242605 3956299294164355657215977)
                    ·
                      refine ⟨2967224470623266742911983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956299294164355657215977 2967224470623266742911983)
                      ·
                        rfl

theorem cell23_5778649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 2, 3, 2].length) (baseStart_5778649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778649 prefixEnd_5778649 := by exact prefixLift 5778649
  have htrace : WordTrace (prefixWord ++ tailWord_5778649) baseStart_5778649 baseEnd_5778649 := by
    simpa [prefixWord, tailWord_5778649, baseEnd_5778649] using wordTrace_append hprefix tailTrace_5778649
  have hstable : (prefixWord ++ tailWord_5778649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778649).length < 2 ^ (prefixWord ++ tailWord_5778649).sum := by decide
  have hdescent : baseEnd_5778649 < baseStart_5778649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778666 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2]
def baseStart_5778666 : Nat := 118140960795 + 5778666 * 2 ^ 59
def prefixEnd_5778666 : Nat := 4983230072969 + 3 ^ 40 * 5778666 * 2
def baseEnd_5778666 : Nat := 2967233199794393176399405

theorem tailTrace_5778666 : CollatzResearch.WordTrace tailWord_5778666 prefixEnd_5778666 2967233199794393176399405 := by
  unfold tailWord_5778666
  simp only [CollatzResearch.WordTrace]
  refine ⟨52691316020721868606346963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140510176055258316283591901 52691316020721868606346963)
  ·
    refine ⟨79036974031082802909520445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52691316020721868606346963 79036974031082802909520445)
    ·
      refine ⟨29638865261656051091070167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79036974031082802909520445 29638865261656051091070167)
      ·
        refine ⟨44458297892484076636605251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29638865261656051091070167 44458297892484076636605251)
        ·
          refine ⟨66687446838726114954907877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44458297892484076636605251 66687446838726114954907877)
          ·
            refine ⟨12503896282261146554045227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66687446838726114954907877 12503896282261146554045227)
            ·
              refine ⟨18755844423391719831067841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12503896282261146554045227 18755844423391719831067841)
              ·
                refine ⟨14066883317543789873300881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18755844423391719831067841 14066883317543789873300881)
                ·
                  refine ⟨10550162488157842404975661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14066883317543789873300881 10550162488157842404975661)
                  ·
                    refine ⟨3956310933059190901865873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10550162488157842404975661 3956310933059190901865873)
                    ·
                      refine ⟨2967233199794393176399405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956310933059190901865873 2967233199794393176399405)
                      ·
                        rfl

theorem cell23_5778666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_5778666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778666 prefixEnd_5778666 := by exact prefixLift 5778666
  have htrace : WordTrace (prefixWord ++ tailWord_5778666) baseStart_5778666 baseEnd_5778666 := by
    simpa [prefixWord, tailWord_5778666, baseEnd_5778666] using wordTrace_append hprefix tailTrace_5778666
  have hstable : (prefixWord ++ tailWord_5778666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778666).length < 2 ^ (prefixWord ++ tailWord_5778666).sum := by decide
  have hdescent : baseEnd_5778666 < baseStart_5778666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778682 : List Nat := [3, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5]
def baseStart_5778682 : Nat := 118140960795 + 5778682 * 2 ^ 59
def prefixEnd_5778682 : Nat := 4983230072969 + 3 ^ 40 * 5778682 * 2
def baseEnd_5778682 : Nat := 2967241415484865113799331

theorem tailTrace_5778682 : CollatzResearch.WordTrace tailWord_5778682 prefixEnd_5778682 2967241415484865113799331 := by
  unfold tailWord_5778682
  simp only [CollatzResearch.WordTrace]
  refine ⟨52691461912707377289492575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140510565100553006105313533 52691461912707377289492575)
  ·
    refine ⟨79037192869061065934238863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52691461912707377289492575 79037192869061065934238863)
    ·
      refine ⟨118555789303591598901358295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79037192869061065934238863 118555789303591598901358295)
      ·
        refine ⟨177833683955387398352037443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118555789303591598901358295 177833683955387398352037443)
        ·
          refine ⟨266750525933081097528056165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177833683955387398352037443 266750525933081097528056165)
          ·
            refine ⟨50015723612452705786510531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266750525933081097528056165 50015723612452705786510531)
            ·
              refine ⟨75023585418679058679765797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50015723612452705786510531 75023585418679058679765797)
              ·
                refine ⟨14066922266002323502456087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75023585418679058679765797 14066922266002323502456087)
                ·
                  refine ⟨21100383399003485253684131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14066922266002323502456087 21100383399003485253684131)
                  ·
                    refine ⟨31650575098505227880526197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21100383399003485253684131 31650575098505227880526197)
                    ·
                      refine ⟨2967241415484865113799331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31650575098505227880526197 2967241415484865113799331)
                      ·
                        rfl

theorem cell23_5778682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5].length) (baseStart_5778682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778682 prefixEnd_5778682 := by exact prefixLift 5778682
  have htrace : WordTrace (prefixWord ++ tailWord_5778682) baseStart_5778682 baseEnd_5778682 := by
    simpa [prefixWord, tailWord_5778682, baseEnd_5778682] using wordTrace_append hprefix tailTrace_5778682
  have hstable : (prefixWord ++ tailWord_5778682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778682).length < 2 ^ (prefixWord ++ tailWord_5778682).sum := by decide
  have hdescent : baseEnd_5778682 < baseStart_5778682 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778699 : List Nat := [1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 3]
def baseStart_5778699 : Nat := 118140960795 + 5778699 * 2 ^ 59
def prefixEnd_5778699 : Nat := 4983230072969 + 3 ^ 40 * 5778699 * 2
def baseEnd_5778699 : Nat := 2967250144655991547286753

theorem tailTrace_5778699 : CollatzResearch.WordTrace tailWord_5778699 prefixEnd_5778699 2967250144655991547286753 := by
  unfold tailWord_5778699
  simp only [CollatzResearch.WordTrace]
  refine ⟨210766467691767921061339151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140510978461178614040892767 210766467691767921061339151)
  ·
    refine ⟨316149701537651881592008727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210766467691767921061339151 316149701537651881592008727)
    ·
      refine ⟨474224552306477822388013091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316149701537651881592008727 474224552306477822388013091)
      ·
        refine ⟨711336828459716733582019637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474224552306477822388013091 711336828459716733582019637)
        ·
          refine ⟨66687827668098443773314341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 711336828459716733582019637 66687827668098443773314341)
          ·
            refine ⟨12503967687768458207496439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66687827668098443773314341 12503967687768458207496439)
            ·
              refine ⟨18755951531652687311244659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12503967687768458207496439 18755951531652687311244659)
              ·
                refine ⟨28133927297479030966866989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18755951531652687311244659 28133927297479030966866989)
                ·
                  refine ⟨10550222736554636612575121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28133927297479030966866989 10550222736554636612575121)
                  ·
                    refine ⟨7912667052415977459431341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10550222736554636612575121 7912667052415977459431341)
                    ·
                      refine ⟨2967250144655991547286753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7912667052415977459431341 2967250144655991547286753)
                      ·
                        rfl

theorem cell23_5778699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 3].length) (baseStart_5778699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778699 prefixEnd_5778699 := by exact prefixLift 5778699
  have htrace : WordTrace (prefixWord ++ tailWord_5778699) baseStart_5778699 baseEnd_5778699 := by
    simpa [prefixWord, tailWord_5778699, baseEnd_5778699] using wordTrace_append hprefix tailTrace_5778699
  have hstable : (prefixWord ++ tailWord_5778699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778699).length < 2 ^ (prefixWord ++ tailWord_5778699).sum := by decide
  have hdescent : baseEnd_5778699 < baseStart_5778699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778702 : List Nat := [4, 1, 1, 2, 1, 3, 2, 9]
def baseStart_5778702 : Nat := 118140960795 + 5778702 * 2 ^ 59
def prefixEnd_5778702 : Nat := 4983230072969 + 3 ^ 40 * 5778702 * 2
def baseEnd_5778702 : Nat := 109898210559183519835157

theorem tailTrace_5778702 : CollatzResearch.WordTrace tailWord_5778702 prefixEnd_5778702 109898210559183519835157 := by
  unfold tailWord_5778702
  simp only [CollatzResearch.WordTrace]
  refine ⟨26345822138844631571712295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140511051407171368382465573 26345822138844631571712295)
  ·
    refine ⟨39518733208266947357568443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26345822138844631571712295 39518733208266947357568443)
    ·
      refine ⟨59278099812400421036352665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39518733208266947357568443 59278099812400421036352665)
      ·
        refine ⟨44458574859300315777264499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59278099812400421036352665 44458574859300315777264499)
        ·
          refine ⟨66687862288950473665896749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44458574859300315777264499 66687862288950473665896749)
          ·
            refine ⟨25007948358356427624711281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66687862288950473665896749 25007948358356427624711281)
            ·
              refine ⟨18755961268767320718533461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25007948358356427624711281 18755961268767320718533461)
              ·
                refine ⟨109898210559183519835157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18755961268767320718533461 109898210559183519835157)
                ·
                  rfl

theorem cell23_5778702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 9].length) (baseStart_5778702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778702 prefixEnd_5778702 := by exact prefixLift 5778702
  have htrace : WordTrace (prefixWord ++ tailWord_5778702) baseStart_5778702 baseEnd_5778702 := by
    simpa [prefixWord, tailWord_5778702, baseEnd_5778702] using wordTrace_append hprefix tailTrace_5778702
  have hstable : (prefixWord ++ tailWord_5778702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778702).length < 2 ^ (prefixWord ++ tailWord_5778702).sum := by decide
  have hdescent : baseEnd_5778702 < baseStart_5778702 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778746 : List Nat := [3, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3]
def baseStart_5778746 : Nat := 118140960795 + 5778746 * 2 ^ 59
def prefixEnd_5778746 : Nat := 4983230072969 + 3 ^ 40 * 5778746 * 2
def baseEnd_5778746 : Nat := 2967274278246752863399037

theorem tailTrace_5778746 : CollatzResearch.WordTrace tailWord_5778746 prefixEnd_5778746 2967274278246752863399037 := by
  unfold tailWord_5778746
  simp only [CollatzResearch.WordTrace]
  refine ⟨52692045480649412022075023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140512121281731765392200061 52692045480649412022075023)
  ·
    refine ⟨79038068220974118033112535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52692045480649412022075023 79038068220974118033112535)
    ·
      refine ⟨118557102331461177049668803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79038068220974118033112535 118557102331461177049668803)
      ·
        refine ⟨177835653497191765574503205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118557102331461177049668803 177835653497191765574503205)
        ·
          refine ⟨33344185030723456045219351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177835653497191765574503205 33344185030723456045219351)
          ·
            refine ⟨50016277546085184067829027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33344185030723456045219351 50016277546085184067829027)
            ·
              refine ⟨75024416319127776101743541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50016277546085184067829027 75024416319127776101743541)
              ·
                refine ⟨7033539029918229009538457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75024416319127776101743541 7033539029918229009538457)
                ·
                  refine ⟨5275154272438671757153843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7033539029918229009538457 5275154272438671757153843)
                  ·
                    refine ⟨7912731408658007635730765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5275154272438671757153843 7912731408658007635730765)
                    ·
                      refine ⟨2967274278246752863399037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7912731408658007635730765 2967274278246752863399037)
                      ·
                        rfl

theorem cell23_5778746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 5, 2, 1, 3].length) (baseStart_5778746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778746 prefixEnd_5778746 := by exact prefixLift 5778746
  have htrace : WordTrace (prefixWord ++ tailWord_5778746) baseStart_5778746 baseEnd_5778746 := by
    simpa [prefixWord, tailWord_5778746, baseEnd_5778746] using wordTrace_append hprefix tailTrace_5778746
  have hstable : (prefixWord ++ tailWord_5778746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778746).length < 2 ^ (prefixWord ++ tailWord_5778746).sum := by decide
  have hdescent : baseEnd_5778746 < baseStart_5778746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778752 : List Nat := [2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_5778752 : Nat := 118140960795 + 5778752 * 2 ^ 59
def prefixEnd_5778752 : Nat := 4983230072969 + 3 ^ 40 * 5778752 * 2
def baseEnd_5778752 : Nat := 2967277359130679839924009

theorem tailTrace_5778752 : CollatzResearch.WordTrace tailWord_5778752 prefixEnd_5778752 2967277359130679839924009 := by
  unfold tailWord_5778752
  simp only [CollatzResearch.WordTrace]
  refine ⟨105384200380287955556509255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140512267173717274075345673 105384200380287955556509255)
  ·
    refine ⟨158076300570431933334763883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105384200380287955556509255 158076300570431933334763883)
    ·
      refine ⟨237114450855647900002145825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158076300570431933334763883 237114450855647900002145825)
      ·
        refine ⟨177835838141735925001609369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237114450855647900002145825 177835838141735925001609369)
        ·
          refine ⟨133376878606301943751207027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177835838141735925001609369 133376878606301943751207027)
          ·
            refine ⟨200065317909452915626810541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133376878606301943751207027 200065317909452915626810541)
            ·
              refine ⟨75024494216044843360053953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200065317909452915626810541 75024494216044843360053953)
              ·
                refine ⟨56268370662033632520040465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75024494216044843360053953 56268370662033632520040465)
                ·
                  refine ⟨42201277996525224390030349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56268370662033632520040465 42201277996525224390030349)
                  ·
                    refine ⟨15825479248696959146261381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42201277996525224390030349 15825479248696959146261381)
                    ·
                      refine ⟨2967277359130679839924009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15825479248696959146261381 2967277359130679839924009)
                      ·
                        rfl

theorem cell23_5778752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_5778752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778752 prefixEnd_5778752 := by exact prefixLift 5778752
  have htrace : WordTrace (prefixWord ++ tailWord_5778752) baseStart_5778752 baseEnd_5778752 := by
    simpa [prefixWord, tailWord_5778752, baseEnd_5778752] using wordTrace_append hprefix tailTrace_5778752
  have hstable : (prefixWord ++ tailWord_5778752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778752).length < 2 ^ (prefixWord ++ tailWord_5778752).sum := by decide
  have hdescent : baseEnd_5778752 < baseStart_5778752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778773 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_5778773 : Nat := 118140960795 + 5778773 * 2 ^ 59
def prefixEnd_5778773 : Nat := 4983230072969 + 3 ^ 40 * 5778773 * 2
def baseEnd_5778773 : Nat := 2967288142224424257761413

theorem tailTrace_5778773 : CollatzResearch.WordTrace tailWord_5778773 prefixEnd_5778773 2967288142224424257761413 := by
  unfold tailWord_5778773
  simp only [CollatzResearch.WordTrace]
  refine ⟨210769166693499831699532973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140512777795666554466355315 210769166693499831699532973)
  ·
    refine ⟨79038437510062436887324865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210769166693499831699532973 79038437510062436887324865)
    ·
      refine ⟨59278828132546827665493649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79038437510062436887324865 59278828132546827665493649)
      ·
        refine ⟨44459121099410120749120237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59278828132546827665493649 44459121099410120749120237)
        ·
          refine ⟨16672170412278795280920089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44459121099410120749120237 16672170412278795280920089)
          ·
            refine ⟨12504127809209096460690067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16672170412278795280920089 12504127809209096460690067)
            ·
              refine ⟨18756191713813644691035101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12504127809209096460690067 18756191713813644691035101)
              ·
                refine ⟨7033571892680116759138163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18756191713813644691035101 7033571892680116759138163)
                ·
                  refine ⟨10550357839020175138707245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7033571892680116759138163 10550357839020175138707245)
                  ·
                    refine ⟨3956384189632565677015217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10550357839020175138707245 3956384189632565677015217)
                    ·
                      refine ⟨2967288142224424257761413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956384189632565677015217 2967288142224424257761413)
                      ·
                        rfl

theorem cell23_5778773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_5778773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778773 prefixEnd_5778773 := by exact prefixLift 5778773
  have htrace : WordTrace (prefixWord ++ tailWord_5778773) baseStart_5778773 baseEnd_5778773 := by
    simpa [prefixWord, tailWord_5778773, baseEnd_5778773] using wordTrace_append hprefix tailTrace_5778773
  have hstable : (prefixWord ++ tailWord_5778773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778773).length < 2 ^ (prefixWord ++ tailWord_5778773).sum := by decide
  have hdescent : baseEnd_5778773 < baseStart_5778773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778774 : List Nat := [5, 2, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5778774 : Nat := 118140960795 + 5778774 * 2 ^ 59
def prefixEnd_5778774 : Nat := 4983230072969 + 3 ^ 40 * 5778774 * 2
def baseEnd_5778774 : Nat := 989096218568359584616303

theorem tailTrace_5778774 : CollatzResearch.WordTrace tailWord_5778774 prefixEnd_5778774 989096218568359584616303 := by
  unfold tailWord_5778774
  simp only [CollatzResearch.WordTrace]
  refine ⟨13173075197906013054394961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140512802110997472580212917 13173075197906013054394961)
  ·
    refine ⟨9879806398429509790796221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13173075197906013054394961 9879806398429509790796221)
    ·
      refine ⟨3704927399411066171548583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9879806398429509790796221 3704927399411066171548583)
      ·
        refine ⟨5557391099116599257322875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704927399411066171548583 5557391099116599257322875)
        ·
          refine ⟨8336086648674898885984313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5557391099116599257322875 8336086648674898885984313)
          ·
            refine ⟨6252064986506174164488235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8336086648674898885984313 6252064986506174164488235)
            ·
              refine ⟨9378097479759261246732353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6252064986506174164488235 9378097479759261246732353)
              ·
                refine ⟨7033573109819445935049265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9378097479759261246732353 7033573109819445935049265)
                ·
                  refine ⟨5275179832364584451286949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7033573109819445935049265 5275179832364584451286949)
                  ·
                    refine ⟨989096218568359584616303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5275179832364584451286949 989096218568359584616303)
                    ·
                      rfl

theorem cell23_5778774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5778774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778774 prefixEnd_5778774 := by exact prefixLift 5778774
  have htrace : WordTrace (prefixWord ++ tailWord_5778774) baseStart_5778774 baseEnd_5778774 := by
    simpa [prefixWord, tailWord_5778774, baseEnd_5778774] using wordTrace_append hprefix tailTrace_5778774
  have hstable : (prefixWord ++ tailWord_5778774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778774).length < 2 ^ (prefixWord ++ tailWord_5778774).sum := by decide
  have hdescent : baseEnd_5778774 < baseStart_5778774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778879 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 3]
def baseStart_5778879 : Nat := 118140960795 + 5778879 * 2 ^ 59
def prefixEnd_5778879 : Nat := 4983230072969 + 3 ^ 40 * 5778879 * 2
def baseEnd_5778879 : Nat := 2967342571173800843035925

theorem tailTrace_5778879 : CollatzResearch.WordTrace tailWord_5778879 prefixEnd_5778879 2967342571173800843035925 := by
  unfold tailWord_5778879
  simp only [CollatzResearch.WordTrace]
  refine ⟨210773032831115811802891691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140515355220743874535261127 210773032831115811802891691)
  ·
    refine ⟨316159549246673717704337537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210773032831115811802891691 316159549246673717704337537)
    ·
      refine ⟨237119661935005288278253153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316159549246673717704337537 237119661935005288278253153)
      ·
        refine ⟨177839746451253966208689865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237119661935005288278253153 177839746451253966208689865)
        ·
          refine ⟨133379809838440474656517399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177839746451253966208689865 133379809838440474656517399)
          ·
            refine ⟨200069714757660711984776099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133379809838440474656517399 200069714757660711984776099)
            ·
              refine ⟨300104572136491067977164149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200069714757660711984776099 300104572136491067977164149)
              ·
                refine ⟨28134803637796037622859139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 300104572136491067977164149 28134803637796037622859139)
                ·
                  refine ⟨42202205456694056434288709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28134803637796037622859139 42202205456694056434288709)
                  ·
                    refine ⟨7912913523130135581429133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42202205456694056434288709 7912913523130135581429133)
                    ·
                      refine ⟨2967342571173800843035925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7912913523130135581429133 2967342571173800843035925)
                      ·
                        rfl

theorem cell23_5778879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_5778879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778879 prefixEnd_5778879 := by exact prefixLift 5778879
  have htrace : WordTrace (prefixWord ++ tailWord_5778879) baseStart_5778879 baseEnd_5778879 := by
    simpa [prefixWord, tailWord_5778879, baseEnd_5778879] using wordTrace_append hprefix tailTrace_5778879
  have hstable : (prefixWord ++ tailWord_5778879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778879).length < 2 ^ (prefixWord ++ tailWord_5778879).sum := by decide
  have hdescent : baseEnd_5778879 < baseStart_5778879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778930 : List Nat := [3, 2, 1, 4, 1, 3, 1, 1, 2, 2, 3]
def baseStart_5778930 : Nat := 118140960795 + 5778930 * 2 ^ 59
def prefixEnd_5778930 : Nat := 4983230072969 + 3 ^ 40 * 5778930 * 2
def baseEnd_5778930 : Nat := 2967368758687180143498191

theorem tailTrace_5778930 : CollatzResearch.WordTrace tailWord_5778930 prefixEnd_5778930 2967368758687180143498191 := by
  unfold tailWord_5778930
  simp only [CollatzResearch.WordTrace]
  refine ⟨52693723238482761878249561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140516595302620698341998829 52693723238482761878249561)
  ·
    refine ⟨39520292428862071408687171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52693723238482761878249561 39520292428862071408687171)
    ·
      refine ⟨59280438643293107113030757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39520292428862071408687171 59280438643293107113030757)
      ·
        refine ⟨11115082245617457583693267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59280438643293107113030757 11115082245617457583693267)
        ·
          refine ⟨16672623368426186375539901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11115082245617457583693267 16672623368426186375539901)
          ·
            refine ⟨6252233763159819890827463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16672623368426186375539901 6252233763159819890827463)
            ·
              refine ⟨9378350644739729836241195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6252233763159819890827463 9378350644739729836241195)
              ·
                refine ⟨14067525967109594754361793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9378350644739729836241195 14067525967109594754361793)
                ·
                  refine ⟨10550644475332196065771345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14067525967109594754361793 10550644475332196065771345)
                  ·
                    refine ⟨7912983356499147049328509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10550644475332196065771345 7912983356499147049328509)
                    ·
                      refine ⟨2967368758687180143498191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7912983356499147049328509 2967368758687180143498191)
                      ·
                        rfl

theorem cell23_5778930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_5778930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778930 prefixEnd_5778930 := by exact prefixLift 5778930
  have htrace : WordTrace (prefixWord ++ tailWord_5778930) baseStart_5778930 baseEnd_5778930 := by
    simpa [prefixWord, tailWord_5778930, baseEnd_5778930] using wordTrace_append hprefix tailTrace_5778930
  have hstable : (prefixWord ++ tailWord_5778930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778930).length < 2 ^ (prefixWord ++ tailWord_5778930).sum := by decide
  have hdescent : baseEnd_5778930 < baseStart_5778930 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5778986 : List Nat := [3, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5]
def baseStart_5778986 : Nat := 118140960795 + 5778986 * 2 ^ 59
def prefixEnd_5778986 : Nat := 4983230072969 + 3 ^ 40 * 5778986 * 2
def baseEnd_5778986 : Nat := 2967397513603831924397933

theorem tailTrace_5778986 : CollatzResearch.WordTrace tailWord_5778986 prefixEnd_5778986 2967397513603831924397933 := by
  unfold tailWord_5778986
  simp only [CollatzResearch.WordTrace]
  refine ⟨52694233860432042269259203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140517956961152112718024541 52694233860432042269259203)
  ·
    refine ⟨79041350790648063403888805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52694233860432042269259203 79041350790648063403888805)
    ·
      refine ⟨14820253273246511888229151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79041350790648063403888805 14820253273246511888229151)
      ·
        refine ⟨22230379909869767832343727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14820253273246511888229151 22230379909869767832343727)
        ·
          refine ⟨33345569864804651748515591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22230379909869767832343727 33345569864804651748515591)
          ·
            refine ⟨50018354797206977622773387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33345569864804651748515591 50018354797206977622773387)
            ·
              refine ⟨75027532195810466434160081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50018354797206977622773387 75027532195810466434160081)
              ·
                refine ⟨56270649146857849825620061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75027532195810466434160081 56270649146857849825620061)
                ·
                  refine ⟨21101493430071693684607523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56270649146857849825620061 21101493430071693684607523)
                  ·
                    refine ⟨31652240145107540526911285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21101493430071693684607523 31652240145107540526911285)
                    ·
                      refine ⟨2967397513603831924397933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31652240145107540526911285 2967397513603831924397933)
                      ·
                        rfl

theorem cell23_5778986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_5778986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5778986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5778986 prefixEnd_5778986 := by exact prefixLift 5778986
  have htrace : WordTrace (prefixWord ++ tailWord_5778986) baseStart_5778986 baseEnd_5778986 := by
    simpa [prefixWord, tailWord_5778986, baseEnd_5778986] using wordTrace_append hprefix tailTrace_5778986
  have hstable : (prefixWord ++ tailWord_5778986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5778986).length < 2 ^ (prefixWord ++ tailWord_5778986).sum := by decide
  have hdescent : baseEnd_5778986 < baseStart_5778986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5778986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779019 : List Nat := [1, 1, 1, 1, 3, 1, 3, 3, 2, 7]
def baseStart_5779019 : Nat := 118140960795 + 5779019 * 2 ^ 59
def prefixEnd_5779019 : Nat := 4983230072969 + 3 ^ 40 * 5779019 * 2
def baseEnd_5779019 : Nat := 989138152821810098428427

theorem tailTrace_5779019 : CollatzResearch.WordTrace tailWord_5779019 prefixEnd_5779019 989138152821810098428427 := by
  unfold tailWord_5779019
  simp only [CollatzResearch.WordTrace]
  refine ⟨210778139050608615712988111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140518759367072410475325407 210778139050608615712988111)
  ·
    refine ⟨316167208575912923569482167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210778139050608615712988111 316167208575912923569482167)
    ·
      refine ⟨474250812863869385354223251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316167208575912923569482167 474250812863869385354223251)
      ·
        refine ⟨711376219295804078031334877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474250812863869385354223251 711376219295804078031334877)
        ·
          refine ⟨266766082235926529261750579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 711376219295804078031334877 266766082235926529261750579)
          ·
            refine ⟨400149123353889793892625869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266766082235926529261750579 400149123353889793892625869)
            ·
              refine ⟨150055921257708672709734701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 400149123353889793892625869 150055921257708672709734701)
              ·
                refine ⟨56270970471640752266150513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150055921257708672709734701 56270970471640752266150513)
                ·
                  refine ⟨42203227853730564199612885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56270970471640752266150513 42203227853730564199612885)
                  ·
                    refine ⟨989138152821810098428427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42203227853730564199612885 989138152821810098428427)
                    ·
                      rfl

theorem cell23_5779019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 3, 2, 7].length) (baseStart_5779019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779019 prefixEnd_5779019 := by exact prefixLift 5779019
  have htrace : WordTrace (prefixWord ++ tailWord_5779019) baseStart_5779019 baseEnd_5779019 := by
    simpa [prefixWord, tailWord_5779019, baseEnd_5779019] using wordTrace_append hprefix tailTrace_5779019
  have hstable : (prefixWord ++ tailWord_5779019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779019).length < 2 ^ (prefixWord ++ tailWord_5779019).sum := by decide
  have hdescent : baseEnd_5779019 < baseStart_5779019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779037 : List Nat := [1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5779037 : Nat := 118140960795 + 5779037 * 2 ^ 59
def prefixEnd_5779037 : Nat := 4983230072969 + 3 ^ 40 * 5779037 * 2
def baseEnd_5779037 : Nat := 2967423701117211224860199

theorem tailTrace_5779037 : CollatzResearch.WordTrace tailWord_5779037 prefixEnd_5779037 2967423701117211224860199 := by
  unfold tailWord_5779037
  simp only [CollatzResearch.WordTrace]
  refine ⟨210778795564543404787143365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140519197043028936524762243 210778795564543404787143365)
  ·
    refine ⟨39521024168351888397589381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210778795564543404787143365 39521024168351888397589381)
    ·
      refine ⟨7410192031565979074548009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39521024168351888397589381 7410192031565979074548009)
      ·
        refine ⟨5557644023674484305911007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7410192031565979074548009 5557644023674484305911007)
        ·
          refine ⟨8336466035511726458866511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5557644023674484305911007 8336466035511726458866511)
          ·
            refine ⟨12504699053267589688299767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8336466035511726458866511 12504699053267589688299767)
            ·
              refine ⟨18757048579901384532449651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12504699053267589688299767 18757048579901384532449651)
              ·
                refine ⟨28135572869852076798674477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18757048579901384532449651 28135572869852076798674477)
                ·
                  refine ⟨10550839826194528799502929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28135572869852076798674477 10550839826194528799502929)
                  ·
                    refine ⟨7913129869645896599627197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10550839826194528799502929 7913129869645896599627197)
                    ·
                      refine ⟨2967423701117211224860199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7913129869645896599627197 2967423701117211224860199)
                      ·
                        rfl

theorem cell23_5779037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5779037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779037 prefixEnd_5779037 := by exact prefixLift 5779037
  have htrace : WordTrace (prefixWord ++ tailWord_5779037) baseStart_5779037 baseEnd_5779037 := by
    simpa [prefixWord, tailWord_5779037, baseEnd_5779037] using wordTrace_append hprefix tailTrace_5779037
  have hstable : (prefixWord ++ tailWord_5779037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779037).length < 2 ^ (prefixWord ++ tailWord_5779037).sum := by decide
  have hdescent : baseEnd_5779037 < baseStart_5779037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779039 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 10]
def baseStart_5779039 : Nat := 118140960795 + 5779039 * 2 ^ 59
def prefixEnd_5779039 : Nat := 4983230072969 + 3 ^ 40 * 5779039 * 2
def baseEnd_5779039 : Nat := 2967424728078520217035189

theorem tailTrace_5779039 : CollatzResearch.WordTrace tailWord_5779039 prefixEnd_5779039 2967424728078520217035189 := by
  unfold tailWord_5779039
  simp only [CollatzResearch.WordTrace]
  refine ⟨210778868510536159128716171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140519245673690772752477447 210778868510536159128716171)
  ·
    refine ⟨316168302765804238693074257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210778868510536159128716171 316168302765804238693074257)
    ·
      refine ⟨237126227074353179019805693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316168302765804238693074257 237126227074353179019805693)
      ·
        refine ⟨88922335152882442132427135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237126227074353179019805693 88922335152882442132427135)
        ·
          refine ⟨133383502729323663198640703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88922335152882442132427135 133383502729323663198640703)
          ·
            refine ⟨200075254093985494797961055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133383502729323663198640703 200075254093985494797961055)
            ·
              refine ⟨300112881140978242196941583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200075254093985494797961055 300112881140978242196941583)
              ·
                refine ⟨450169321711467363295412375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300112881140978242196941583 450169321711467363295412375)
                ·
                  refine ⟨675253982567201044943118563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450169321711467363295412375 675253982567201044943118563)
                  ·
                    refine ⟨1012880973850801567414677845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 675253982567201044943118563 1012880973850801567414677845)
                    ·
                      refine ⟨2967424728078520217035189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1012880973850801567414677845 2967424728078520217035189)
                      ·
                        rfl

theorem cell23_5779039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_5779039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779039 prefixEnd_5779039 := by exact prefixLift 5779039
  have htrace : WordTrace (prefixWord ++ tailWord_5779039) baseStart_5779039 baseEnd_5779039 := by
    simpa [prefixWord, tailWord_5779039, baseEnd_5779039] using wordTrace_append hprefix tailTrace_5779039
  have hstable : (prefixWord ++ tailWord_5779039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779039).length < 2 ^ (prefixWord ++ tailWord_5779039).sum := by decide
  have hdescent : baseEnd_5779039 < baseStart_5779039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779096 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 9]
def baseStart_5779096 : Nat := 118140960795 + 5779096 * 2 ^ 59
def prefixEnd_5779096 : Nat := 4983230072969 + 3 ^ 40 * 5779096 * 2
def baseEnd_5779096 : Nat := 329717110719536277113603

theorem tailTrace_5779096 : CollatzResearch.WordTrace tailWord_5779096 prefixEnd_5779096 329717110719536277113603 := by
  unfold tailWord_5779096
  simp only [CollatzResearch.WordTrace]
  refine ⟨105390473735664828931770571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140520631647553105242360761 105390473735664828931770571)
  ·
    refine ⟨158085710603497243397655857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105390473735664828931770571 158085710603497243397655857)
    ·
      refine ⟨118564282952622932548241893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158085710603497243397655857 118564282952622932548241893)
      ·
        refine ⟨22230803053616799852795355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118564282952622932548241893 22230803053616799852795355)
        ·
          refine ⟨33346204580425199779193033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22230803053616799852795355 33346204580425199779193033)
          ·
            refine ⟨25009653435318899834394775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33346204580425199779193033 25009653435318899834394775)
            ·
              refine ⟨37514480152978349751592163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25009653435318899834394775 37514480152978349751592163)
              ·
                refine ⟨56271720229467524627388245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37514480152978349751592163 56271720229467524627388245)
                ·
                  refine ⟨329717110719536277113603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56271720229467524627388245 329717110719536277113603)
                  ·
                    rfl

theorem cell23_5779096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 9].length) (baseStart_5779096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779096 prefixEnd_5779096 := by exact prefixLift 5779096
  have htrace : WordTrace (prefixWord ++ tailWord_5779096) baseStart_5779096 baseEnd_5779096 := by
    simpa [prefixWord, tailWord_5779096, baseEnd_5779096] using wordTrace_append hprefix tailTrace_5779096
  have hstable : (prefixWord ++ tailWord_5779096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779096).length < 2 ^ (prefixWord ++ tailWord_5779096).sum := by decide
  have hdescent : baseEnd_5779096 < baseStart_5779096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779136 : List Nat := [2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_5779136 : Nat := 118140960795 + 5779136 * 2 ^ 59
def prefixEnd_5779136 : Nat := 4983230072969 + 3 ^ 40 * 5779136 * 2
def baseEnd_5779136 : Nat := 2967474535702006337522243

theorem tailTrace_5779136 : CollatzResearch.WordTrace tailWord_5779136 prefixEnd_5779136 2967474535702006337522243 := by
  unfold tailWord_5779136
  simp only [CollatzResearch.WordTrace]
  refine ⟨105391203195592372347498631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140521604260789829796664841 105391203195592372347498631)
  ·
    refine ⟨158086804793388558521247947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105391203195592372347498631 158086804793388558521247947)
    ·
      refine ⟨237130207190082837781871921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158086804793388558521247947 237130207190082837781871921)
      ·
        refine ⟨177847655392562128336403941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237130207190082837781871921 177847655392562128336403941)
        ·
          refine ⟨33346435386105399063075739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177847655392562128336403941 33346435386105399063075739)
          ·
            refine ⟨50019653079158098594613609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33346435386105399063075739 50019653079158098594613609)
            ·
              refine ⟨37514739809368573945960207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50019653079158098594613609 37514739809368573945960207)
              ·
                refine ⟨56272109714052860918940311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37514739809368573945960207 56272109714052860918940311)
                ·
                  refine ⟨84408164571079291378410467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56272109714052860918940311 84408164571079291378410467)
                  ·
                    refine ⟨126612246856618937067615701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84408164571079291378410467 126612246856618937067615701)
                    ·
                      refine ⟨2967474535702006337522243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126612246856618937067615701 2967474535702006337522243)
                      ·
                        rfl

theorem cell23_5779136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_5779136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779136 prefixEnd_5779136 := by exact prefixLift 5779136
  have htrace : WordTrace (prefixWord ++ tailWord_5779136) baseStart_5779136 baseEnd_5779136 := by
    simpa [prefixWord, tailWord_5779136, baseEnd_5779136] using wordTrace_append hprefix tailTrace_5779136
  have hstable : (prefixWord ++ tailWord_5779136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779136).length < 2 ^ (prefixWord ++ tailWord_5779136).sum := by decide
  have hdescent : baseEnd_5779136 < baseStart_5779136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779164 : List Nat := [2, 2, 5, 1, 2, 2, 1, 3, 5]
def baseStart_5779164 : Nat := 118140960795 + 5779164 * 2 ^ 59
def prefixEnd_5779164 : Nat := 4983230072969 + 3 ^ 40 * 5779164 * 2
def baseEnd_5779164 : Nat := 329720990351148025330235

theorem tailTrace_5779164 : CollatzResearch.WordTrace tailWord_5779164 prefixEnd_5779164 329720990351148025330235 := by
  unfold tailWord_5779164
  simp only [CollatzResearch.WordTrace]
  refine ⟨105391713817541652738508273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140522285090055536984677697 105391713817541652738508273)
  ·
    refine ⟨79043785363156239553881205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105391713817541652738508273 79043785363156239553881205)
    ·
      refine ⟨7410354877795897458176363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79043785363156239553881205 7410354877795897458176363)
      ·
        refine ⟨11115532316693846187264545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7410354877795897458176363 11115532316693846187264545)
        ·
          refine ⟨8336649237520384640448409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11115532316693846187264545 8336649237520384640448409)
          ·
            refine ⟨6252486928140288480336307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8336649237520384640448409 6252486928140288480336307)
            ·
              refine ⟨9378730392210432720504461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6252486928140288480336307 9378730392210432720504461)
              ·
                refine ⟨3517023897078912270189173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9378730392210432720504461 3517023897078912270189173)
                ·
                  refine ⟨329720990351148025330235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3517023897078912270189173 329720990351148025330235)
                  ·
                    rfl

theorem cell23_5779164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 5].length) (baseStart_5779164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779164 prefixEnd_5779164 := by exact prefixLift 5779164
  have htrace : WordTrace (prefixWord ++ tailWord_5779164) baseStart_5779164 baseEnd_5779164 := by
    simpa [prefixWord, tailWord_5779164, baseEnd_5779164] using wordTrace_append hprefix tailTrace_5779164
  have hstable : (prefixWord ++ tailWord_5779164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779164).length < 2 ^ (prefixWord ++ tailWord_5779164).sum := by decide
  have hdescent : baseEnd_5779164 < baseStart_5779164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779247 : List Nat := [1, 1, 2, 1, 2, 1, 2, 8, 1, 1, 3]
def baseStart_5779247 : Nat := 118140960795 + 5779247 * 2 ^ 59
def prefixEnd_5779247 : Nat := 4983230072969 + 3 ^ 40 * 5779247 * 2
def baseEnd_5779247 : Nat := 2967531532054655403234233

theorem tailTrace_5779247 : CollatzResearch.WordTrace tailWord_5779247 prefixEnd_5779247 2967531532054655403234233 := by
  unfold tailWord_5779247
  simp only [CollatzResearch.WordTrace]
  refine ⟨210786454893782610652287995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140524303262521740434858663 210786454893782610652287995)
  ·
    refine ⟨316179682340673915978431993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210786454893782610652287995 316179682340673915978431993)
    ·
      refine ⟨237134761755505436983823995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316179682340673915978431993 237134761755505436983823995)
      ·
        refine ⟨355702142633258155475735993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237134761755505436983823995 355702142633258155475735993)
        ·
          refine ⟨266776606974943616606801995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355702142633258155475735993 266776606974943616606801995)
          ·
            refine ⟨400164910462415424910202993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266776606974943616606801995 400164910462415424910202993)
            ·
              refine ⟨300123682846811568682652245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400164910462415424910202993 300123682846811568682652245)
              ·
                refine ⟨3517074408361073070499831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 300123682846811568682652245 3517074408361073070499831)
                ·
                  refine ⟨5275611612541609605749747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3517074408361073070499831 5275611612541609605749747)
                  ·
                    refine ⟨7913417418812414408624621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5275611612541609605749747 7913417418812414408624621)
                    ·
                      refine ⟨2967531532054655403234233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7913417418812414408624621 2967531532054655403234233)
                      ·
                        rfl

theorem cell23_5779247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 8, 1, 1, 3].length) (baseStart_5779247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779247 prefixEnd_5779247 := by exact prefixLift 5779247
  have htrace : WordTrace (prefixWord ++ tailWord_5779247) baseStart_5779247 baseEnd_5779247 := by
    simpa [prefixWord, tailWord_5779247, baseEnd_5779247] using wordTrace_append hprefix tailTrace_5779247
  have hstable : (prefixWord ++ tailWord_5779247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779247).length < 2 ^ (prefixWord ++ tailWord_5779247).sum := by decide
  have hdescent : baseEnd_5779247 < baseStart_5779247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779284 : List Nat := [2, 4, 1, 1, 3, 3, 2, 1, 1, 5]
def baseStart_5779284 : Nat := 118140960795 + 5779284 * 2 ^ 59
def prefixEnd_5779284 : Nat := 4983230072969 + 3 ^ 40 * 5779284 * 2
def baseEnd_5779284 : Nat := 989183510279623919490521

theorem tailTrace_5779284 : CollatzResearch.WordTrace tailWord_5779284 prefixEnd_5779284 989183510279623919490521 := by
  unfold tailWord_5779284
  simp only [CollatzResearch.WordTrace]
  refine ⟨105393902197324282985692453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140525202929765710647589937 105393902197324282985692453)
  ·
    refine ⟨19761356661998303059817335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105393902197324282985692453 19761356661998303059817335)
    ·
      refine ⟨29642034992997454589726003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19761356661998303059817335 29642034992997454589726003)
      ·
        refine ⟨44463052489496181884589005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29642034992997454589726003 44463052489496181884589005)
        ·
          refine ⟨16673644683561068206720877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44463052489496181884589005 16673644683561068206720877)
          ·
            refine ⟨6252616756335400577520329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16673644683561068206720877 6252616756335400577520329)
            ·
              refine ⟨4689462567251550433140247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6252616756335400577520329 4689462567251550433140247)
              ·
                refine ⟨7034193850877325649710371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4689462567251550433140247 7034193850877325649710371)
                ·
                  refine ⟨10551290776315988474565557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7034193850877325649710371 10551290776315988474565557)
                  ·
                    refine ⟨989183510279623919490521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10551290776315988474565557 989183510279623919490521)
                    ·
                      rfl

theorem cell23_5779284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_5779284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779284 prefixEnd_5779284 := by exact prefixLift 5779284
  have htrace : WordTrace (prefixWord ++ tailWord_5779284) baseStart_5779284 baseEnd_5779284 := by
    simpa [prefixWord, tailWord_5779284, baseEnd_5779284] using wordTrace_append hprefix tailTrace_5779284
  have hstable : (prefixWord ++ tailWord_5779284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779284).length < 2 ^ (prefixWord ++ tailWord_5779284).sum := by decide
  have hdescent : baseEnd_5779284 < baseStart_5779284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779287 : List Nat := [1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 4]
def baseStart_5779287 : Nat := 118140960795 + 5779287 * 2 ^ 59
def prefixEnd_5779287 : Nat := 4983230072969 + 3 ^ 40 * 5779287 * 2
def baseEnd_5779287 : Nat := 2967552071280835246734049

theorem tailTrace_5779287 : CollatzResearch.WordTrace tailWord_5779287 prefixEnd_5779287 2967552071280835246734049 := by
  unfold tailWord_5779287
  simp only [CollatzResearch.WordTrace]
  refine ⟨210787913813637697483744115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140525275875758464989162743 210787913813637697483744115)
  ·
    refine ⟨316181870720456546225616173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210787913813637697483744115 316181870720456546225616173)
    ·
      refine ⟨118568201520171204834606065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316181870720456546225616173 118568201520171204834606065)
      ·
        refine ⟨88926151140128403625954549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118568201520171204834606065 88926151140128403625954549)
        ·
          refine ⟨8336826669387037839933239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88926151140128403625954549 8336826669387037839933239)
          ·
            refine ⟨12505240004080556759899859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8336826669387037839933239 12505240004080556759899859)
            ·
              refine ⟨18757860006120835139849789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12505240004080556759899859 18757860006120835139849789)
              ·
                refine ⟨7034197502295313177443671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18757860006120835139849789 7034197502295313177443671)
                ·
                  refine ⟨10551296253442969766165507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7034197502295313177443671 10551296253442969766165507)
                  ·
                    refine ⟨15826944380164454649248261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10551296253442969766165507 15826944380164454649248261)
                    ·
                      refine ⟨2967552071280835246734049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15826944380164454649248261 2967552071280835246734049)
                      ·
                        rfl

theorem cell23_5779287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_5779287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779287 prefixEnd_5779287 := by exact prefixLift 5779287
  have htrace : WordTrace (prefixWord ++ tailWord_5779287) baseStart_5779287 baseEnd_5779287 := by
    simpa [prefixWord, tailWord_5779287, baseEnd_5779287] using wordTrace_append hprefix tailTrace_5779287
  have hstable : (prefixWord ++ tailWord_5779287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779287).length < 2 ^ (prefixWord ++ tailWord_5779287).sum := by decide
  have hdescent : baseEnd_5779287 < baseStart_5779287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779304 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 3, 2, 2]
def baseStart_5779304 : Nat := 118140960795 + 5779304 * 2 ^ 59
def prefixEnd_5779304 : Nat := 4983230072969 + 3 ^ 40 * 5779304 * 2
def baseEnd_5779304 : Nat := 2967560800451961680221471

theorem tailTrace_5779304 : CollatzResearch.WordTrace tailWord_5779304 prefixEnd_5779304 2967560800451961680221471 := by
  unfold tailWord_5779304
  simp only [CollatzResearch.WordTrace]
  refine ⟨105394266927288054693556483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140525689236384072924741977 105394266927288054693556483)
  ·
    refine ⟨158091400390932082040334725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105394266927288054693556483 158091400390932082040334725)
    ·
      refine ⟨29642137573299765382562761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158091400390932082040334725 29642137573299765382562761)
      ·
        refine ⟨22231603179974824036922071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29642137573299765382562761 22231603179974824036922071)
        ·
          refine ⟨33347404769962236055383107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22231603179974824036922071 33347404769962236055383107)
          ·
            refine ⟨50021107154943354083074661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33347404769962236055383107 50021107154943354083074661)
            ·
              refine ⟨9378957591551878890576499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50021107154943354083074661 9378957591551878890576499)
              ·
                refine ⟨14068436387327818335864749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9378957591551878890576499 14068436387327818335864749)
                ·
                  refine ⟨5275663645247931875949281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14068436387327818335864749 5275663645247931875949281)
                  ·
                    refine ⟨3956747733935948906961961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5275663645247931875949281 3956747733935948906961961)
                    ·
                      refine ⟨2967560800451961680221471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956747733935948906961961 2967560800451961680221471)
                      ·
                        rfl

theorem cell23_5779304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_5779304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779304 prefixEnd_5779304 := by exact prefixLift 5779304
  have htrace : WordTrace (prefixWord ++ tailWord_5779304) baseStart_5779304 baseEnd_5779304 := by
    simpa [prefixWord, tailWord_5779304, baseEnd_5779304] using wordTrace_append hprefix tailTrace_5779304
  have hstable : (prefixWord ++ tailWord_5779304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779304).length < 2 ^ (prefixWord ++ tailWord_5779304).sum := by decide
  have hdescent : baseEnd_5779304 < baseStart_5779304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779333 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 5]
def baseStart_5779333 : Nat := 118140960795 + 5779333 * 2 ^ 59
def prefixEnd_5779333 : Nat := 4983230072969 + 3 ^ 40 * 5779333 * 2
def baseEnd_5779333 : Nat := 2967575691390942066758837

theorem tailTrace_5779333 : CollatzResearch.WordTrace tailWord_5779333 prefixEnd_5779333 2967575691390942066758837 := by
  unfold tailWord_5779333
  simp only [CollatzResearch.WordTrace]
  refine ⟨210789591571471047339918653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140526394380980698226612435 210789591571471047339918653)
  ·
    refine ⟨79046096839301642752469495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210789591571471047339918653 79046096839301642752469495)
    ·
      refine ⟨118569145258952464128704243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79046096839301642752469495 118569145258952464128704243)
      ·
        refine ⟨177853717888428696193056365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118569145258952464128704243 177853717888428696193056365)
        ·
          refine ⟨66695144208160761072396137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177853717888428696193056365 66695144208160761072396137)
          ·
            refine ⟨50021358156120570804297103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66695144208160761072396137 50021358156120570804297103)
            ·
              refine ⟨75032037234180856206445655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50021358156120570804297103 75032037234180856206445655)
              ·
                refine ⟨112548055851271284309668483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75032037234180856206445655 112548055851271284309668483)
                ·
                  refine ⟨168822083776906926464502725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112548055851271284309668483 168822083776906926464502725)
                  ·
                    refine ⟨31654140708170048712094261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168822083776906926464502725 31654140708170048712094261)
                    ·
                      refine ⟨2967575691390942066758837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31654140708170048712094261 2967575691390942066758837)
                      ·
                        rfl

theorem cell23_5779333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_5779333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779333 prefixEnd_5779333 := by exact prefixLift 5779333
  have htrace : WordTrace (prefixWord ++ tailWord_5779333) baseStart_5779333 baseEnd_5779333 := by
    simpa [prefixWord, tailWord_5779333, baseEnd_5779333] using wordTrace_append hprefix tailTrace_5779333
  have hstable : (prefixWord ++ tailWord_5779333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779333).length < 2 ^ (prefixWord ++ tailWord_5779333).sum := by decide
  have hdescent : baseEnd_5779333 < baseStart_5779333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779353 : List Nat := [1, 2, 1, 2, 1, 3, 2, 1, 4, 6]
def baseStart_5779353 : Nat := 118140960795 + 5779353 * 2 ^ 59
def prefixEnd_5779353 : Nat := 4983230072969 + 3 ^ 40 * 5779353 * 2
def baseEnd_5779353 : Nat := 989195320334677329502915

theorem tailTrace_5779353 : CollatzResearch.WordTrace tailWord_5779353 prefixEnd_5779353 989195320334677329502915 := by
  unfold tailWord_5779353
  simp only [CollatzResearch.WordTrace]
  refine ⟨210790321031398590755646713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140526880687599060503764475 210790321031398590755646713)
  ·
    refine ⟨158092740773548943066735035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210790321031398590755646713 158092740773548943066735035)
    ·
      refine ⟨237139111160323414600102553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158092740773548943066735035 237139111160323414600102553)
      ·
        refine ⟨177854333370242560950076915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237139111160323414600102553 177854333370242560950076915)
        ·
          refine ⟨266781500055363841425115373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177854333370242560950076915 266781500055363841425115373)
          ·
            refine ⟨100043062520761440534418265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266781500055363841425115373 100043062520761440534418265)
            ·
              refine ⟨75032296890571080400813699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100043062520761440534418265 75032296890571080400813699)
              ·
                refine ⟨112548445335856620601220549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75032296890571080400813699 112548445335856620601220549)
                ·
                  refine ⟨21102833500473116362728853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112548445335856620601220549 21102833500473116362728853)
                  ·
                    refine ⟨989195320334677329502915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21102833500473116362728853 989195320334677329502915)
                    ·
                      rfl

theorem cell23_5779353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 1, 4, 6].length) (baseStart_5779353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779353 prefixEnd_5779353 := by exact prefixLift 5779353
  have htrace : WordTrace (prefixWord ++ tailWord_5779353) baseStart_5779353 baseEnd_5779353 := by
    simpa [prefixWord, tailWord_5779353, baseEnd_5779353] using wordTrace_append hprefix tailTrace_5779353
  have hstable : (prefixWord ++ tailWord_5779353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779353).length < 2 ^ (prefixWord ++ tailWord_5779353).sum := by decide
  have hdescent : baseEnd_5779353 < baseStart_5779353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779363 : List Nat := [1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 5]
def baseStart_5779363 : Nat := 118140960795 + 5779363 * 2 ^ 59
def prefixEnd_5779363 : Nat := 4983230072969 + 3 ^ 40 * 5779363 * 2
def baseEnd_5779363 : Nat := 2967591095810576949383699

theorem tailTrace_5779363 : CollatzResearch.WordTrace tailWord_5779363 prefixEnd_5779363 2967591095810576949383699 := by
  unfold tailWord_5779363
  simp only [CollatzResearch.WordTrace]
  refine ⟨210790685761362362463510743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140527123840908241642340495 210790685761362362463510743)
  ·
    refine ⟨316186028642043543695266115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210790685761362362463510743 316186028642043543695266115)
    ·
      refine ⟨474279042963065315542899173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316186028642043543695266115 474279042963065315542899173)
      ·
        refine ⟨88927320555574746664293595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 474279042963065315542899173 88927320555574746664293595)
        ·
          refine ⟨133390980833362119996440393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88927320555574746664293595 133390980833362119996440393)
          ·
            refine ⟨100043235625021589997330295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133390980833362119996440393 100043235625021589997330295)
            ·
              refine ⟨150064853437532384995995443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100043235625021589997330295 150064853437532384995995443)
              ·
                refine ⟨225097280156298577493993165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150064853437532384995995443 225097280156298577493993165)
                ·
                  refine ⟨84411480058611966560247437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225097280156298577493993165 84411480058611966560247437)
                  ·
                    refine ⟨31654305021979487460092789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84411480058611966560247437 31654305021979487460092789)
                    ·
                      refine ⟨2967591095810576949383699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31654305021979487460092789 2967591095810576949383699)
                      ·
                        rfl

theorem cell23_5779363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_5779363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779363 prefixEnd_5779363 := by exact prefixLift 5779363
  have htrace : WordTrace (prefixWord ++ tailWord_5779363) baseStart_5779363 baseEnd_5779363 := by
    simpa [prefixWord, tailWord_5779363, baseEnd_5779363] using wordTrace_append hprefix tailTrace_5779363
  have hstable : (prefixWord ++ tailWord_5779363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779363).length < 2 ^ (prefixWord ++ tailWord_5779363).sum := by decide
  have hdescent : baseEnd_5779363 < baseStart_5779363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779381 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_5779381 : Nat := 118140960795 + 5779381 * 2 ^ 59
def prefixEnd_5779381 : Nat := 4983230072969 + 3 ^ 40 * 5779381 * 2
def baseEnd_5779381 : Nat := 2967600338462357878958617

theorem tailTrace_5779381 : CollatzResearch.WordTrace tailWord_5779381 prefixEnd_5779381 2967600338462357878958617 := by
  unfold tailWord_5779381
  simp only [CollatzResearch.WordTrace]
  refine ⟨210791342275297151537665997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140527561516864767691777331 210791342275297151537665997)
  ·
    refine ⟨79046753353236431826624749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210791342275297151537665997 79046753353236431826624749)
    ·
      refine ⟨29642532507463661934984281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79046753353236431826624749 29642532507463661934984281)
      ·
        refine ⟨22231899380597746451238211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29642532507463661934984281 22231899380597746451238211)
        ·
          refine ⟨33347849070896619676857317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22231899380597746451238211 33347849070896619676857317)
          ·
            refine ⟨6252721700793116189410747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33347849070896619676857317 6252721700793116189410747)
            ·
              refine ⟨9379082551189674284116121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6252721700793116189410747 9379082551189674284116121)
              ·
                refine ⟨7034311913392255713087091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9379082551189674284116121 7034311913392255713087091)
                ·
                  refine ⟨10551467870088383569630637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7034311913392255713087091 10551467870088383569630637)
                  ·
                    refine ⟨3956800451283143838611489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10551467870088383569630637 3956800451283143838611489)
                    ·
                      refine ⟨2967600338462357878958617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956800451283143838611489 2967600338462357878958617)
                      ·
                        rfl

theorem cell23_5779381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_5779381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779381 prefixEnd_5779381 := by exact prefixLift 5779381
  have htrace : WordTrace (prefixWord ++ tailWord_5779381) baseStart_5779381 baseEnd_5779381 := by
    simpa [prefixWord, tailWord_5779381, baseEnd_5779381] using wordTrace_append hprefix tailTrace_5779381
  have hstable : (prefixWord ++ tailWord_5779381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779381).length < 2 ^ (prefixWord ++ tailWord_5779381).sum := by decide
  have hdescent : baseEnd_5779381 < baseStart_5779381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779383 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 9]
def baseStart_5779383 : Nat := 118140960795 + 5779383 * 2 ^ 59
def prefixEnd_5779383 : Nat := 4983230072969 + 3 ^ 40 * 5779383 * 2
def baseEnd_5779383 : Nat := 329733485047074096792623

theorem tailTrace_5779383 : CollatzResearch.WordTrace tailWord_5779383 prefixEnd_5779383 329733485047074096792623 := by
  unfold tailWord_5779383
  simp only [CollatzResearch.WordTrace]
  refine ⟨210791415221289905879238803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140527610147526603919492535 210791415221289905879238803)
  ·
    refine ⟨316187122831934858818858205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210791415221289905879238803 316187122831934858818858205)
    ·
      refine ⟨118570171061975572057071827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316187122831934858818858205 118570171061975572057071827)
      ·
        refine ⟨177855256592963358085607741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118570171061975572057071827 177855256592963358085607741)
        ·
          refine ⟨66695721222361259282102903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177855256592963358085607741 66695721222361259282102903)
          ·
            refine ⟨100043581833541888923154355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66695721222361259282102903 100043581833541888923154355)
            ·
              refine ⟨150065372750312833384731533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100043581833541888923154355 150065372750312833384731533)
              ·
                refine ⟨56274514781367312519274325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150065372750312833384731533 56274514781367312519274325)
                ·
                  refine ⟨329733485047074096792623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 56274514781367312519274325 329733485047074096792623)
                  ·
                    rfl

theorem cell23_5779383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 9].length) (baseStart_5779383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779383 prefixEnd_5779383 := by exact prefixLift 5779383
  have htrace : WordTrace (prefixWord ++ tailWord_5779383) baseStart_5779383 baseEnd_5779383 := by
    simpa [prefixWord, tailWord_5779383, baseEnd_5779383] using wordTrace_append hprefix tailTrace_5779383
  have hstable : (prefixWord ++ tailWord_5779383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779383).length < 2 ^ (prefixWord ++ tailWord_5779383).sum := by decide
  have hdescent : baseEnd_5779383 < baseStart_5779383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779427 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 3]
def baseStart_5779427 : Nat := 118140960795 + 5779427 * 2 ^ 59
def prefixEnd_5779427 : Nat := 4983230072969 + 3 ^ 40 * 5779427 * 2
def baseEnd_5779427 : Nat := 2967623958572464698983405

theorem tailTrace_5779427 : CollatzResearch.WordTrace tailWord_5779427 prefixEnd_5779427 2967623958572464698983405 := by
  unfold tailWord_5779427
  simp only [CollatzResearch.WordTrace]
  refine ⟨210793020033130501393840535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140528680022087000929227023 210793020033130501393840535)
  ·
    refine ⟨316189530049695752090760803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210793020033130501393840535 316189530049695752090760803)
    ·
      refine ⟨474284295074543628136141205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316189530049695752090760803 474284295074543628136141205)
      ·
        refine ⟨22232076331619232568881619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 474284295074543628136141205 22232076331619232568881619)
        ·
          refine ⟨33348114497428848853322429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22232076331619232568881619 33348114497428848853322429)
          ·
            refine ⟨12505542936535818319995911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33348114497428848853322429 12505542936535818319995911)
            ·
              refine ⟨18758314404803727479993867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12505542936535818319995911 18758314404803727479993867)
              ·
                refine ⟨28137471607205591219990801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18758314404803727479993867 28137471607205591219990801)
                ·
                  refine ⟨21103103705404193414993101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28137471607205591219990801 21103103705404193414993101)
                  ·
                    refine ⟨7913663889526572530622413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21103103705404193414993101 7913663889526572530622413)
                    ·
                      refine ⟨2967623958572464698983405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7913663889526572530622413 2967623958572464698983405)
                      ·
                        rfl

theorem cell23_5779427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_5779427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779427 prefixEnd_5779427 := by exact prefixLift 5779427
  have htrace : WordTrace (prefixWord ++ tailWord_5779427) baseStart_5779427 baseEnd_5779427 := by
    simpa [prefixWord, tailWord_5779427, baseEnd_5779427] using wordTrace_append hprefix tailTrace_5779427
  have hstable : (prefixWord ++ tailWord_5779427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779427).length < 2 ^ (prefixWord ++ tailWord_5779427).sum := by decide
  have hdescent : baseEnd_5779427 < baseStart_5779427 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779462 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_5779462 : Nat := 118140960795 + 5779462 * 2 ^ 59
def prefixEnd_5779462 : Nat := 4983230072969 + 3 ^ 40 * 5779462 * 2
def baseEnd_5779462 : Nat := 2967641930395372062045745

theorem tailTrace_5779462 : CollatzResearch.WordTrace tailWord_5779462 prefixEnd_5779462 2967641930395372062045745 := by
  unfold tailWord_5779462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6587321768375115699105145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140529531058669134914243093 6587321768375115699105145)
  ·
    refine ⟨4940491326281336774328859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6587321768375115699105145 4940491326281336774328859)
    ·
      refine ⟨7410736989422005161493289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4940491326281336774328859 7410736989422005161493289)
      ·
        refine ⟨5558052742066503871119967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7410736989422005161493289 5558052742066503871119967)
        ·
          refine ⟨8337079113099755806679951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5558052742066503871119967 8337079113099755806679951)
          ·
            refine ⟨12505618669649633710019927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8337079113099755806679951 12505618669649633710019927)
            ·
              refine ⟨18758428004474450565029891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12505618669649633710019927 18758428004474450565029891)
              ·
                refine ⟨28137642006711675847544837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18758428004474450565029891 28137642006711675847544837)
                ·
                  refine ⟨5275807876258439221414657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28137642006711675847544837 5275807876258439221414657)
                  ·
                    refine ⟨3956855907193829416060993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5275807876258439221414657 3956855907193829416060993)
                    ·
                      refine ⟨2967641930395372062045745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956855907193829416060993 2967641930395372062045745)
                      ·
                        rfl

theorem cell23_5779462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_5779462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779462 prefixEnd_5779462 := by exact prefixLift 5779462
  have htrace : WordTrace (prefixWord ++ tailWord_5779462) baseStart_5779462 baseEnd_5779462 := by
    simpa [prefixWord, tailWord_5779462, baseEnd_5779462] using wordTrace_append hprefix tailTrace_5779462
  have hstable : (prefixWord ++ tailWord_5779462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779462).length < 2 ^ (prefixWord ++ tailWord_5779462).sum := by decide
  have hdescent : baseEnd_5779462 < baseStart_5779462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779467 : List Nat := [1, 1, 1, 1, 6, 1, 1, 1, 4, 4, 2]
def baseStart_5779467 : Nat := 118140960795 + 5779467 * 2 ^ 59
def prefixEnd_5779467 : Nat := 4983230072969 + 3 ^ 40 * 5779467 * 2
def baseEnd_5779467 : Nat := 2967644497798644542483221

theorem tailTrace_5779467 : CollatzResearch.WordTrace tailWord_5779467 prefixEnd_5779467 2967644497798644542483221 := by
  unfold tailWord_5779467
  simp only [CollatzResearch.WordTrace]
  refine ⟨210794478952985588225296655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140529652635323725483531103 210794478952985588225296655)
  ·
    refine ⟨316191718429478382337944983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210794478952985588225296655 316191718429478382337944983)
    ·
      refine ⟨474287577644217573506917475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316191718429478382337944983 474287577644217573506917475)
      ·
        refine ⟨711431366466326360260376213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474287577644217573506917475 711431366466326360260376213)
        ·
          refine ⟨33348345303109048137205135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 711431366466326360260376213 33348345303109048137205135)
          ·
            refine ⟨50022517954663572205807703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33348345303109048137205135 50022517954663572205807703)
            ·
              refine ⟨75033776931995358308711555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50022517954663572205807703 75033776931995358308711555)
              ·
                refine ⟨112550665397993037463067333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75033776931995358308711555 112550665397993037463067333)
                ·
                  refine ⟨21103249762123694524325125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112550665397993037463067333 21103249762123694524325125)
                  ·
                    refine ⟨3956859330398192723310961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21103249762123694524325125 3956859330398192723310961)
                    ·
                      refine ⟨2967644497798644542483221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956859330398192723310961 2967644497798644542483221)
                      ·
                        rfl

theorem cell23_5779467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 1, 4, 4, 2].length) (baseStart_5779467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779467 prefixEnd_5779467 := by exact prefixLift 5779467
  have htrace : WordTrace (prefixWord ++ tailWord_5779467) baseStart_5779467 baseEnd_5779467 := by
    simpa [prefixWord, tailWord_5779467, baseEnd_5779467] using wordTrace_append hprefix tailTrace_5779467
  have hstable : (prefixWord ++ tailWord_5779467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779467).length < 2 ^ (prefixWord ++ tailWord_5779467).sum := by decide
  have hdescent : baseEnd_5779467 < baseStart_5779467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779480 : List Nat := [2, 1, 2, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_5779480 : Nat := 118140960795 + 5779480 * 2 ^ 59
def prefixEnd_5779480 : Nat := 4983230072969 + 3 ^ 40 * 5779480 * 2
def baseEnd_5779480 : Nat := 2967651173047152991620661

theorem tailTrace_5779480 : CollatzResearch.WordTrace tailWord_5779480 prefixEnd_5779480 2967651173047152991620661 := by
  unfold tailWord_5779480
  simp only [CollatzResearch.WordTrace]
  refine ⟨105397476550969245722759947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140529968734625660963679929 105397476550969245722759947)
  ·
    refine ⟨158096214826453868584139921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105397476550969245722759947 158096214826453868584139921)
    ·
      refine ⟨118572161119840401438104941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158096214826453868584139921 118572161119840401438104941)
      ·
        refine ⟨44464560419940150539289353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118572161119840401438104941 44464560419940150539289353)
        ·
          refine ⟨33348420314955112904467015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44464560419940150539289353 33348420314955112904467015)
          ·
            refine ⟨50022630472432669356700523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33348420314955112904467015 50022630472432669356700523)
            ·
              refine ⟨75033945708649004035050785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50022630472432669356700523 75033945708649004035050785)
              ·
                refine ⟨56275459281486753026288089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75033945708649004035050785 56275459281486753026288089)
                ·
                  refine ⟨42206594461115064769716067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56275459281486753026288089 42206594461115064769716067)
                  ·
                    refine ⟨63309891691672597154574101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42206594461115064769716067 63309891691672597154574101)
                    ·
                      refine ⟨2967651173047152991620661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63309891691672597154574101 2967651173047152991620661)
                      ·
                        rfl

theorem cell23_5779480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_5779480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779480 prefixEnd_5779480 := by exact prefixLift 5779480
  have htrace : WordTrace (prefixWord ++ tailWord_5779480) baseStart_5779480 baseEnd_5779480 := by
    simpa [prefixWord, tailWord_5779480, baseEnd_5779480] using wordTrace_append hprefix tailTrace_5779480
  have hstable : (prefixWord ++ tailWord_5779480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779480).length < 2 ^ (prefixWord ++ tailWord_5779480).sum := by decide
  have hdescent : baseEnd_5779480 < baseStart_5779480 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779484 : List Nat := [2, 2, 3, 1, 3, 1, 2, 1, 2, 4, 2]
def baseStart_5779484 : Nat := 118140960795 + 5779484 * 2 ^ 59
def prefixEnd_5779484 : Nat := 4983230072969 + 3 ^ 40 * 5779484 * 2
def baseEnd_5779484 : Nat := 2967653226969770975970643

theorem tailTrace_5779484 : CollatzResearch.WordTrace tailWord_5779484 prefixEnd_5779484 2967653226969770975970643 := by
  unfold tailWord_5779484
  simp only [CollatzResearch.WordTrace]
  refine ⟨105397549496962000064332753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140530065995949333419110337 105397549496962000064332753)
  ·
    refine ⟨79048162122721500048249565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105397549496962000064332753 79048162122721500048249565)
    ·
      refine ⟨29643060796020562518093587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79048162122721500048249565 29643060796020562518093587)
      ·
        refine ⟨44464591194030843777140381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29643060796020562518093587 44464591194030843777140381)
        ·
          refine ⟨16674221697761566416427643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44464591194030843777140381 16674221697761566416427643)
          ·
            refine ⟨25011332546642349624641465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16674221697761566416427643 25011332546642349624641465)
            ·
              refine ⟨18758499409981762218481099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25011332546642349624641465 18758499409981762218481099)
              ·
                refine ⟨28137749114972643327721649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18758499409981762218481099 28137749114972643327721649)
                ·
                  refine ⟨21103311836229482495791237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28137749114972643327721649 21103311836229482495791237)
                  ·
                    refine ⟨3956870969293027967960857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21103311836229482495791237 3956870969293027967960857)
                    ·
                      refine ⟨2967653226969770975970643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956870969293027967960857 2967653226969770975970643)
                      ·
                        rfl

theorem cell23_5779484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_5779484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779484 prefixEnd_5779484 := by exact prefixLift 5779484
  have htrace : WordTrace (prefixWord ++ tailWord_5779484) baseStart_5779484 baseEnd_5779484 := by
    simpa [prefixWord, tailWord_5779484, baseEnd_5779484] using wordTrace_append hprefix tailTrace_5779484
  have hstable : (prefixWord ++ tailWord_5779484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779484).length < 2 ^ (prefixWord ++ tailWord_5779484).sum := by decide
  have hdescent : baseEnd_5779484 < baseStart_5779484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779530 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7]
def baseStart_5779530 : Nat := 118140960795 + 5779530 * 2 ^ 59
def prefixEnd_5779530 : Nat := 4983230072969 + 3 ^ 40 * 5779530 * 2
def baseEnd_5779530 : Nat := 2967676847079877795995431

theorem tailTrace_5779530 : CollatzResearch.WordTrace tailWord_5779530 prefixEnd_5779530 2967676847079877795995431 := by
  unfold tailWord_5779530
  simp only [CollatzResearch.WordTrace]
  refine ⟨52699194187939337496210011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140531184501171566656560029 52699194187939337496210011)
  ·
    refine ⟨79048791281909006244315017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52699194187939337496210011 79048791281909006244315017)
    ·
      refine ⟨59286593461431754683236263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79048791281909006244315017 59286593461431754683236263)
      ·
        refine ⟨88929890192147632024854395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59286593461431754683236263 88929890192147632024854395)
        ·
          refine ⟨133394835288221448037281593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88929890192147632024854395 133394835288221448037281593)
          ·
            refine ⟨100046126466166086027961195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133394835288221448037281593 100046126466166086027961195)
            ·
              refine ⟨150069189699249129041941793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100046126466166086027961195 150069189699249129041941793)
              ·
                refine ⟨112551892274436846781456345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150069189699249129041941793 112551892274436846781456345)
                ·
                  refine ⟨84413919205827635086092259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112551892274436846781456345 84413919205827635086092259)
                  ·
                    refine ⟨126620878808741452629138389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84413919205827635086092259 126620878808741452629138389)
                    ·
                      refine ⟨2967676847079877795995431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126620878808741452629138389 2967676847079877795995431)
                      ·
                        rfl

theorem cell23_5779530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_5779530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779530 prefixEnd_5779530 := by exact prefixLift 5779530
  have htrace : WordTrace (prefixWord ++ tailWord_5779530) baseStart_5779530 baseEnd_5779530 := by
    simpa [prefixWord, tailWord_5779530, baseEnd_5779530] using wordTrace_append hprefix tailTrace_5779530
  have hstable : (prefixWord ++ tailWord_5779530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779530).length < 2 ^ (prefixWord ++ tailWord_5779530).sum := by decide
  have hdescent : baseEnd_5779530 < baseStart_5779530 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779567 : List Nat := [1, 1, 2, 1, 3, 5, 1, 2, 1, 6]
def baseStart_5779567 : Nat := 118140960795 + 5779567 * 2 ^ 59
def prefixEnd_5779567 : Nat := 4983230072969 + 3 ^ 40 * 5779567 * 2
def baseEnd_5779567 : Nat := 989231948621364717077587

theorem tailTrace_5779567 : CollatzResearch.WordTrace tailWord_5779567 prefixEnd_5779567 989231948621364717077587 := by
  unfold tailWord_5779567
  simp only [CollatzResearch.WordTrace]
  refine ⟨210798126252623305303936955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140532084168415536869291303 210798126252623305303936955)
  ·
    refine ⟨316197189378934957955905433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210798126252623305303936955 316197189378934957955905433)
    ·
      refine ⟨237147892034201218466929075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316197189378934957955905433 237147892034201218466929075)
      ·
        refine ⟨355721838051301827700393613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237147892034201218466929075 355721838051301827700393613)
        ·
          refine ⟨133395689269238185387647605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355721838051301827700393613 133395689269238185387647605)
          ·
            refine ⟨12505845868991079880091963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133395689269238185387647605 12505845868991079880091963)
            ·
              refine ⟨18758768803486619820137945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12505845868991079880091963 18758768803486619820137945)
              ·
                refine ⟨14069076602614964865103459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18758768803486619820137945 14069076602614964865103459)
                ·
                  refine ⟨21103614903922447297655189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14069076602614964865103459 21103614903922447297655189)
                  ·
                    refine ⟨989231948621364717077587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21103614903922447297655189 989231948621364717077587)
                    ·
                      rfl

theorem cell23_5779567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 1, 6].length) (baseStart_5779567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779567 prefixEnd_5779567 := by exact prefixLift 5779567
  have htrace : WordTrace (prefixWord ++ tailWord_5779567) baseStart_5779567 baseEnd_5779567 := by
    simpa [prefixWord, tailWord_5779567, baseEnd_5779567] using wordTrace_append hprefix tailTrace_5779567
  have hstable : (prefixWord ++ tailWord_5779567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779567).length < 2 ^ (prefixWord ++ tailWord_5779567).sum := by decide
  have hdescent : baseEnd_5779567 < baseStart_5779567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779580 : List Nat := [2, 2, 2, 1, 1, 15]
def baseStart_5779580 : Nat := 118140960795 + 5779580 * 2 ^ 59
def prefixEnd_5779580 : Nat := 4983230072969 + 3 ^ 40 * 5779580 * 2
def baseEnd_5779580 : Nat := 12212767576595072429507

theorem tailTrace_5779580 : CollatzResearch.WordTrace tailWord_5779580 prefixEnd_5779580 12212767576595072429507 := by
  unfold tailWord_5779580
  simp only [CollatzResearch.WordTrace]
  refine ⟨105399300200788104262080097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140532400267717472349440129 105399300200788104262080097)
  ·
    refine ⟨79049475150591078196560073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105399300200788104262080097 79049475150591078196560073)
    ·
      refine ⟨59287106362943308647420055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79049475150591078196560073 59287106362943308647420055)
      ·
        refine ⟨88930659544414962971130083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59287106362943308647420055 88930659544414962971130083)
        ·
          refine ⟨133395989316622444456695125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88930659544414962971130083 133395989316622444456695125)
          ·
            refine ⟨12212767576595072429507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 15 133395989316622444456695125 12212767576595072429507)
            ·
              rfl

theorem cell23_5779580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 15].length) (baseStart_5779580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779580 prefixEnd_5779580 := by exact prefixLift 5779580
  have htrace : WordTrace (prefixWord ++ tailWord_5779580) baseStart_5779580 baseEnd_5779580 := by
    simpa [prefixWord, tailWord_5779580, baseEnd_5779580] using wordTrace_append hprefix tailTrace_5779580
  have hstable : (prefixWord ++ tailWord_5779580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779580).length < 2 ^ (prefixWord ++ tailWord_5779580).sum := by decide
  have hdescent : baseEnd_5779580 < baseStart_5779580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779594 : List Nat := [3, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3]
def baseStart_5779594 : Nat := 118140960795 + 5779594 * 2 ^ 59
def prefixEnd_5779594 : Nat := 4983230072969 + 3 ^ 40 * 5779594 * 2
def baseEnd_5779594 : Nat := 2967709709841765545595137

theorem tailTrace_5779594 : CollatzResearch.WordTrace tailWord_5779594 prefixEnd_5779594 2967709709841765545595137 := by
  unfold tailWord_5779594
  simp only [CollatzResearch.WordTrace]
  refine ⟨52699777755881372228792459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140532740682350325943446557 52699777755881372228792459)
  ·
    refine ⟨79049666633822058343188689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52699777755881372228792459 79049666633822058343188689)
    ·
      refine ⟨59287249975366543757391517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79049666633822058343188689 59287249975366543757391517)
      ·
        refine ⟨22232718740762453909021819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59287249975366543757391517 22232718740762453909021819)
        ·
          refine ⟨33349078111143680863532729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22232718740762453909021819 33349078111143680863532729)
          ·
            refine ⟨25011808583357760647649547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33349078111143680863532729 25011808583357760647649547)
            ·
              refine ⟨37517712875036640971474321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25011808583357760647649547 37517712875036640971474321)
              ·
                refine ⟨28138284656277480728605741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37517712875036640971474321 28138284656277480728605741)
                ·
                  refine ⟨10551856746104055273227153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28138284656277480728605741 10551856746104055273227153)
                  ·
                    refine ⟨7913892559578041454920365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10551856746104055273227153 7913892559578041454920365)
                    ·
                      refine ⟨2967709709841765545595137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7913892559578041454920365 2967709709841765545595137)
                      ·
                        rfl

theorem cell23_5779594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_5779594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779594 prefixEnd_5779594 := by exact prefixLift 5779594
  have htrace : WordTrace (prefixWord ++ tailWord_5779594) baseStart_5779594 baseEnd_5779594 := by
    simpa [prefixWord, tailWord_5779594, baseEnd_5779594] using wordTrace_append hprefix tailTrace_5779594
  have hstable : (prefixWord ++ tailWord_5779594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779594).length < 2 ^ (prefixWord ++ tailWord_5779594).sum := by decide
  have hdescent : baseEnd_5779594 < baseStart_5779594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779608 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 3, 2, 2]
def baseStart_5779608 : Nat := 118140960795 + 5779608 * 2 ^ 59
def prefixEnd_5779608 : Nat := 4983230072969 + 3 ^ 40 * 5779608 * 2
def baseEnd_5779608 : Nat := 2967716898570928490820073

theorem tailTrace_5779608 : CollatzResearch.WordTrace tailWord_5779608 prefixEnd_5779608 2967716898570928490820073 := by
  unfold tailWord_5779608
  simp only [CollatzResearch.WordTrace]
  refine ⟨105399810822737384653089739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140533081096983179537452985 105399810822737384653089739)
  ·
    refine ⟨158099716234106076979634609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105399810822737384653089739 158099716234106076979634609)
    ·
      refine ⟨118574787175579557734725957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158099716234106076979634609 118574787175579557734725957)
      ·
        refine ⟨22232772595421167075261117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118574787175579557734725957 22232772595421167075261117)
        ·
          refine ⟨8337289723282937653222919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22232772595421167075261117 8337289723282937653222919)
          ·
            refine ⟨12505934584924406479834379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8337289723282937653222919 12505934584924406479834379)
            ·
              refine ⟨18758901877386609719751569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12505934584924406479834379 18758901877386609719751569)
              ·
                refine ⟨14069176408039957289813677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18758901877386609719751569 14069176408039957289813677)
                ·
                  refine ⟨5275941153014983983680129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14069176408039957289813677 5275941153014983983680129)
                  ·
                    refine ⟨3956955864761237987760097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5275941153014983983680129 3956955864761237987760097)
                    ·
                      refine ⟨2967716898570928490820073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3956955864761237987760097 2967716898570928490820073)
                      ·
                        rfl

theorem cell23_5779608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_5779608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779608 prefixEnd_5779608 := by exact prefixLift 5779608
  have htrace : WordTrace (prefixWord ++ tailWord_5779608) baseStart_5779608 baseEnd_5779608 := by
    simpa [prefixWord, tailWord_5779608, baseEnd_5779608] using wordTrace_append hprefix tailTrace_5779608
  have hstable : (prefixWord ++ tailWord_5779608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779608).length < 2 ^ (prefixWord ++ tailWord_5779608).sum := by decide
  have hdescent : baseEnd_5779608 < baseStart_5779608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779658 : List Nat := [3, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3]
def baseStart_5779658 : Nat := 118140960795 + 5779658 * 2 ^ 59
def prefixEnd_5779658 : Nat := 4983230072969 + 3 ^ 40 * 5779658 * 2
def baseEnd_5779658 : Nat := 2967742572603653295194843

theorem tailTrace_5779658 : CollatzResearch.WordTrace tailWord_5779658 prefixEnd_5779658 2967742572603653295194843 := by
  unfold tailWord_5779658
  simp only [CollatzResearch.WordTrace]
  refine ⟨52700361323823406961374907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140534296863529085230333085 52700361323823406961374907)
  ·
    refine ⟨79050541985735110442062361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52700361323823406961374907 79050541985735110442062361)
    ·
      refine ⟨59287906489301332831546771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79050541985735110442062361 59287906489301332831546771)
      ·
        refine ⟨88931859733951999247320157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59287906489301332831546771 88931859733951999247320157)
        ·
          refine ⟨33349447400231999717745059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88931859733951999247320157 33349447400231999717745059)
          ·
            refine ⟨50024171100347999576617589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33349447400231999717745059 50024171100347999576617589)
            ·
              refine ⟨4689766040657624960307899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50024171100347999576617589 4689766040657624960307899)
              ·
                refine ⟨7034649060986437440461849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4689766040657624960307899 7034649060986437440461849)
                ·
                  refine ⟨5275986795739828080346387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7034649060986437440461849 5275986795739828080346387)
                  ·
                    refine ⟨7913980193609742120519581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5275986795739828080346387 7913980193609742120519581)
                    ·
                      refine ⟨2967742572603653295194843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7913980193609742120519581 2967742572603653295194843)
                      ·
                        rfl

theorem cell23_5779658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3].length) (baseStart_5779658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779658 prefixEnd_5779658 := by exact prefixLift 5779658
  have htrace : WordTrace (prefixWord ++ tailWord_5779658) baseStart_5779658 baseEnd_5779658 := by
    simpa [prefixWord, tailWord_5779658, baseEnd_5779658] using wordTrace_append hprefix tailTrace_5779658
  have hstable : (prefixWord ++ tailWord_5779658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779658).length < 2 ^ (prefixWord ++ tailWord_5779658).sum := by decide
  have hdescent : baseEnd_5779658 < baseStart_5779658 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779676 : List Nat := [2, 2, 5, 2, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5779676 : Nat := 118140960795 + 5779676 * 2 ^ 59
def prefixEnd_5779676 : Nat := 4983230072969 + 3 ^ 40 * 5779676 * 2
def baseEnd_5779676 : Nat := 2967751815255434224769761

theorem tailTrace_5779676 : CollatzResearch.WordTrace tailWord_5779676 prefixEnd_5779676 2967751815255434224769761 := by
  unfold tailWord_5779676
  simp only [CollatzResearch.WordTrace]
  refine ⟨105401050904614208459827441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140534734539485611279769921 105401050904614208459827441)
  ·
    refine ⟨79050788178460656344870581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105401050904614208459827441 79050788178460656344870581)
    ·
      refine ⟨7411011391730686532331617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79050788178460656344870581 7411011391730686532331617)
      ·
        refine ⟨5558258543798014899248713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7411011391730686532331617 5558258543798014899248713)
        ·
          refine ⟨4168693907848511174436535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5558258543798014899248713 4168693907848511174436535)
          ·
            refine ⟨6253040861772766761654803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168693907848511174436535 6253040861772766761654803)
            ·
              refine ⟨9379561292659150142482205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6253040861772766761654803 9379561292659150142482205)
              ·
                refine ⟨3517335484747181303430827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9379561292659150142482205 3517335484747181303430827)
                ·
                  refine ⟨5276003227120771955146241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3517335484747181303430827 5276003227120771955146241)
                  ·
                    refine ⟨3957002420340578966359681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5276003227120771955146241 3957002420340578966359681)
                    ·
                      refine ⟨2967751815255434224769761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957002420340578966359681 2967751815255434224769761)
                      ·
                        rfl

theorem cell23_5779676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5779676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779676 prefixEnd_5779676 := by exact prefixLift 5779676
  have htrace : WordTrace (prefixWord ++ tailWord_5779676) baseStart_5779676 baseEnd_5779676 := by
    simpa [prefixWord, tailWord_5779676, baseEnd_5779676] using wordTrace_append hprefix tailTrace_5779676
  have hstable : (prefixWord ++ tailWord_5779676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779676).length < 2 ^ (prefixWord ++ tailWord_5779676).sum := by decide
  have hdescent : baseEnd_5779676 < baseStart_5779676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779681 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_5779681 : Nat := 118140960795 + 5779681 * 2 ^ 59
def prefixEnd_5779681 : Nat := 4983230072969 + 3 ^ 40 * 5779681 * 2
def baseEnd_5779681 : Nat := 2967754382658706705207237

theorem tailTrace_5779681 : CollatzResearch.WordTrace tailWord_5779681 prefixEnd_5779681 2967754382658706705207237 := by
  unfold tailWord_5779681
  simp only [CollatzResearch.WordTrace]
  refine ⟨210802284174210302773586897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140534856116140201849057931 210802284174210302773586897)
  ·
    refine ⟨158101713130657727080190173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210802284174210302773586897 158101713130657727080190173)
    ·
      refine ⟨59288142423996647655071315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158101713130657727080190173 59288142423996647655071315)
      ·
        refine ⟨88932213635994971482606973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59288142423996647655071315 88932213635994971482606973)
        ·
          refine ⟨33349580113498114305977615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88932213635994971482606973 33349580113498114305977615)
          ·
            refine ⟨50024370170247171458966423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33349580113498114305977615 50024370170247171458966423)
            ·
              refine ⟨75036555255370757188449635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50024370170247171458966423 75036555255370757188449635)
              ·
                refine ⟨112554832883056135782674453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75036555255370757188449635 112554832883056135782674453)
                ·
                  refine ⟨5276007791393256364812865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 112554832883056135782674453 5276007791393256364812865)
                  ·
                    refine ⟨3957005843544942273609649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5276007791393256364812865 3957005843544942273609649)
                    ·
                      refine ⟨2967754382658706705207237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957005843544942273609649 2967754382658706705207237)
                      ·
                        rfl

theorem cell23_5779681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_5779681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779681 prefixEnd_5779681 := by exact prefixLift 5779681
  have htrace : WordTrace (prefixWord ++ tailWord_5779681) baseStart_5779681 baseEnd_5779681 := by
    simpa [prefixWord, tailWord_5779681, baseEnd_5779681] using wordTrace_append hprefix tailTrace_5779681
  have hstable : (prefixWord ++ tailWord_5779681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779681).length < 2 ^ (prefixWord ++ tailWord_5779681).sum := by decide
  have hdescent : baseEnd_5779681 < baseStart_5779681 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779698 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_5779698 : Nat := 118140960795 + 5779698 * 2 ^ 59
def prefixEnd_5779698 : Nat := 4983230072969 + 3 ^ 40 * 5779698 * 2
def baseEnd_5779698 : Nat := 2967763111829833138694659

theorem tailTrace_5779698 : CollatzResearch.WordTrace tailWord_5779698 prefixEnd_5779698 2967763111829833138694659 := by
  unfold tailWord_5779698
  simp only [CollatzResearch.WordTrace]
  refine ⟨52700726053787178669238937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140535269476765809784637165 52700726053787178669238937)
  ·
    refine ⟨39525544540340384001929203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52700726053787178669238937 39525544540340384001929203)
    ·
      refine ⟨59288316810510576002893805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39525544540340384001929203 59288316810510576002893805)
      ·
        refine ⟨22233118803941466001085177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59288316810510576002893805 22233118803941466001085177)
        ·
          refine ⟨16674839102956099500813883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22233118803941466001085177 16674839102956099500813883)
          ·
            refine ⟨25012258654434149251220825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16674839102956099500813883 25012258654434149251220825)
            ·
              refine ⟨18759193990825611938415619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25012258654434149251220825 18759193990825611938415619)
              ·
                refine ⟨28138790986238417907623429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18759193990825611938415619 28138790986238417907623429)
                ·
                  refine ⟨5276023309919703357679393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28138790986238417907623429 5276023309919703357679393)
                  ·
                    refine ⟨3957017482439777518259545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5276023309919703357679393 3957017482439777518259545)
                    ·
                      refine ⟨2967763111829833138694659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957017482439777518259545 2967763111829833138694659)
                      ·
                        rfl

theorem cell23_5779698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_5779698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779698 prefixEnd_5779698 := by exact prefixLift 5779698
  have htrace : WordTrace (prefixWord ++ tailWord_5779698) baseStart_5779698 baseEnd_5779698 := by
    simpa [prefixWord, tailWord_5779698, baseEnd_5779698] using wordTrace_append hprefix tailTrace_5779698
  have hstable : (prefixWord ++ tailWord_5779698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779698).length < 2 ^ (prefixWord ++ tailWord_5779698).sum := by decide
  have hdescent : baseEnd_5779698 < baseStart_5779698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779704 : List Nat := [2, 1, 2, 1, 1, 2, 1, 8, 5]
def baseStart_5779704 : Nat := 118140960795 + 5779704 * 2 ^ 59
def prefixEnd_5779704 : Nat := 4983230072969 + 3 ^ 40 * 5779704 * 2
def baseEnd_5779704 : Nat := 329751799190417790579959

theorem tailTrace_5779704 : CollatzResearch.WordTrace tailWord_5779704 prefixEnd_5779704 329751799190417790579959 := by
  unfold tailWord_5779704
  simp only [CollatzResearch.WordTrace]
  refine ⟨105401561526563488850837083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140535415368751318467782777 105401561526563488850837083)
  ·
    refine ⟨158102342289845233276255625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105401561526563488850837083 158102342289845233276255625)
    ·
      refine ⟨118576756717383924957191719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158102342289845233276255625 118576756717383924957191719)
      ·
        refine ⟨177865135076075887435787579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118576756717383924957191719 177865135076075887435787579)
        ·
          refine ⟨266797702614113831153681369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177865135076075887435787579 266797702614113831153681369)
          ·
            refine ⟨200098276960585373365261027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266797702614113831153681369 200098276960585373365261027)
            ·
              refine ⟨300147415440878060047891541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200098276960585373365261027 300147415440878060047891541)
              ·
                refine ⟨3517352524697789766186229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 300147415440878060047891541 3517352524697789766186229)
                ·
                  refine ⟨329751799190417790579959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3517352524697789766186229 329751799190417790579959)
                  ·
                    rfl

theorem cell23_5779704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 5].length) (baseStart_5779704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779704 prefixEnd_5779704 := by exact prefixLift 5779704
  have htrace : WordTrace (prefixWord ++ tailWord_5779704) baseStart_5779704 baseEnd_5779704 := by
    simpa [prefixWord, tailWord_5779704, baseEnd_5779704] using wordTrace_append hprefix tailTrace_5779704
  have hstable : (prefixWord ++ tailWord_5779704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779704).length < 2 ^ (prefixWord ++ tailWord_5779704).sum := by decide
  have hdescent : baseEnd_5779704 < baseStart_5779704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779717 : List Nat := [1, 3, 1, 1, 2, 1, 2, 4, 1, 7]
def baseStart_5779717 : Nat := 118140960795 + 5779717 * 2 ^ 59
def prefixEnd_5779717 : Nat := 4983230072969 + 3 ^ 40 * 5779717 * 2
def baseEnd_5779717 : Nat := 989257622654089521452357

theorem tailTrace_5779717 : CollatzResearch.WordTrace tailWord_5779717 prefixEnd_5779717 989257622654089521452357 := by
  unfold tailWord_5779717
  simp only [CollatzResearch.WordTrace]
  refine ⟨210803597202079880921897405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140535731468053253947931603 210803597202079880921897405)
  ·
    refine ⟨79051348950779955345711527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210803597202079880921897405 79051348950779955345711527)
    ·
      refine ⟨118577023426169933018567291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79051348950779955345711527 118577023426169933018567291)
      ·
        refine ⟨177865535139254899527850937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118577023426169933018567291 177865535139254899527850937)
        ·
          refine ⟨133399151354441174645888203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177865535139254899527850937 133399151354441174645888203)
          ·
            refine ⟨200098727031661761968832305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133399151354441174645888203 200098727031661761968832305)
            ·
              refine ⟨150074045273746321476624229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200098727031661761968832305 150074045273746321476624229)
              ·
                refine ⟨28138883488827435276867043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150074045273746321476624229 28138883488827435276867043)
                ·
                  refine ⟨42208325233241152915300565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28138883488827435276867043 42208325233241152915300565)
                  ·
                    refine ⟨989257622654089521452357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42208325233241152915300565 989257622654089521452357)
                    ·
                      rfl

theorem cell23_5779717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_5779717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779717 prefixEnd_5779717 := by exact prefixLift 5779717
  have htrace : WordTrace (prefixWord ++ tailWord_5779717) baseStart_5779717 baseEnd_5779717 := by
    simpa [prefixWord, tailWord_5779717, baseEnd_5779717] using wordTrace_append hprefix tailTrace_5779717
  have hstable : (prefixWord ++ tailWord_5779717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779717).length < 2 ^ (prefixWord ++ tailWord_5779717).sum := by decide
  have hdescent : baseEnd_5779717 < baseStart_5779717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779744 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_5779744 : Nat := 118140960795 + 5779744 * 2 ^ 59
def prefixEnd_5779744 : Nat := 4983230072969 + 3 ^ 40 * 5779744 * 2
def baseEnd_5779744 : Nat := 2967786731939939958719447

theorem tailTrace_5779744 : CollatzResearch.WordTrace tailWord_5779744 prefixEnd_5779744 2967786731939939958719447 := by
  unfold tailWord_5779744
  simp only [CollatzResearch.WordTrace]
  refine ⟨105402290986491032266565143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140536387981988043022086857 105402290986491032266565143)
  ·
    refine ⟨158103436479736548399847715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105402290986491032266565143 158103436479736548399847715)
    ·
      refine ⟨237155154719604822599771573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158103436479736548399847715 237155154719604822599771573)
      ·
        refine ⟨22233295754962952118728585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237155154719604822599771573 22233295754962952118728585)
        ·
          refine ⟨16674971816222214089046439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22233295754962952118728585 16674971816222214089046439)
          ·
            refine ⟨25012457724333321133569659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16674971816222214089046439 25012457724333321133569659)
            ·
              refine ⟨37518686586499981700354489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25012457724333321133569659 37518686586499981700354489)
              ·
                refine ⟨28139014939874986275265867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37518686586499981700354489 28139014939874986275265867)
                ·
                  refine ⟨42208522409812479412898801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28139014939874986275265867 42208522409812479412898801)
                  ·
                    refine ⟨31656391807359359559674101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42208522409812479412898801 31656391807359359559674101)
                    ·
                      refine ⟨2967786731939939958719447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31656391807359359559674101 2967786731939939958719447)
                      ·
                        rfl

theorem cell23_5779744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_5779744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779744 prefixEnd_5779744 := by exact prefixLift 5779744
  have htrace : WordTrace (prefixWord ++ tailWord_5779744) baseStart_5779744 baseEnd_5779744 := by
    simpa [prefixWord, tailWord_5779744, baseEnd_5779744] using wordTrace_append hprefix tailTrace_5779744
  have hstable : (prefixWord ++ tailWord_5779744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779744).length < 2 ^ (prefixWord ++ tailWord_5779744).sum := by decide
  have hdescent : baseEnd_5779744 < baseStart_5779744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779831 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 6, 3, 2]
def baseStart_5779831 : Nat := 118140960795 + 5779831 * 2 ^ 59
def prefixEnd_5779831 : Nat := 4983230072969 + 3 ^ 40 * 5779831 * 2
def baseEnd_5779831 : Nat := 2967831404756881118331547

theorem tailTrace_5779831 : CollatzResearch.WordTrace tailWord_5779831 prefixEnd_5779831 2967831404756881118331547 := by
  unfold tailWord_5779831
  simp only [CollatzResearch.WordTrace]
  refine ⟨210807755123666878391547347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140538503415777918927698231 210807755123666878391547347)
  ·
    refine ⟨316211632685500317587321021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210807755123666878391547347 316211632685500317587321021)
    ·
      refine ⟨118579362257062619095245383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316211632685500317587321021 118579362257062619095245383)
      ·
        refine ⟨177869043385593928642868075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118579362257062619095245383 177869043385593928642868075)
        ·
          refine ⟨266803565078390892964302113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177869043385593928642868075 266803565078390892964302113)
          ·
            refine ⟨200102673808793169723226585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266803565078390892964302113 200102673808793169723226585)
            ·
              refine ⟨150077005356594877292419939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200102673808793169723226585 150077005356594877292419939)
              ·
                refine ⟨225115508034892315938629909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150077005356594877292419939 225115508034892315938629909)
                ·
                  refine ⟨10552289439135577309623277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 225115508034892315938629909 10552289439135577309623277)
                  ·
                    refine ⟨3957108539675841491108729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10552289439135577309623277 3957108539675841491108729)
                    ·
                      refine ⟨2967831404756881118331547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957108539675841491108729 2967831404756881118331547)
                      ·
                        rfl

theorem cell23_5779831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_5779831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779831 prefixEnd_5779831 := by exact prefixLift 5779831
  have htrace : WordTrace (prefixWord ++ tailWord_5779831) baseStart_5779831 baseEnd_5779831 := by
    simpa [prefixWord, tailWord_5779831, baseEnd_5779831] using wordTrace_append hprefix tailTrace_5779831
  have hstable : (prefixWord ++ tailWord_5779831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779831).length < 2 ^ (prefixWord ++ tailWord_5779831).sum := by decide
  have hdescent : baseEnd_5779831 < baseStart_5779831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779848 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 2, 3, 2]
def baseStart_5779848 : Nat := 118140960795 + 5779848 * 2 ^ 59
def prefixEnd_5779848 : Nat := 4983230072969 + 3 ^ 40 * 5779848 * 2
def baseEnd_5779848 : Nat := 2967840133928007551818969

theorem tailTrace_5779848 : CollatzResearch.WordTrace tailWord_5779848 prefixEnd_5779848 2967840133928007551818969 := by
  unfold tailWord_5779848
  simp only [CollatzResearch.WordTrace]
  refine ⟨105404187582302645147458099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140538916776403526863277465 105404187582302645147458099)
  ·
    refine ⟨158106281373453967721187149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105404187582302645147458099 158106281373453967721187149)
    ·
      refine ⟨59289855515045237895445181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158106281373453967721187149 59289855515045237895445181)
      ·
        refine ⟨22233695818141964210791943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59289855515045237895445181 22233695818141964210791943)
        ·
          refine ⟨33350543727212946316187915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22233695818141964210791943 33350543727212946316187915)
          ·
            refine ⟨50025815590819419474281873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33350543727212946316187915 50025815590819419474281873)
            ·
              refine ⟨37519361693114564605711405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50025815590819419474281873 37519361693114564605711405)
              ·
                refine ⟨14069760634917961727141777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37519361693114564605711405 14069760634917961727141777)
                ·
                  refine ⟨10552320476188471295356333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14069760634917961727141777 10552320476188471295356333)
                  ·
                    refine ⟨3957120178570676735758625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10552320476188471295356333 3957120178570676735758625)
                    ·
                      refine ⟨2967840133928007551818969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957120178570676735758625 2967840133928007551818969)
                      ·
                        rfl

theorem cell23_5779848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_5779848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779848 prefixEnd_5779848 := by exact prefixLift 5779848
  have htrace : WordTrace (prefixWord ++ tailWord_5779848) baseStart_5779848 baseEnd_5779848 := by
    simpa [prefixWord, tailWord_5779848, baseEnd_5779848] using wordTrace_append hprefix tailTrace_5779848
  have hstable : (prefixWord ++ tailWord_5779848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779848).length < 2 ^ (prefixWord ++ tailWord_5779848).sum := by decide
  have hdescent : baseEnd_5779848 < baseStart_5779848 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779871 : List Nat := [1, 1, 2, 5, 1, 1, 1, 3, 4, 4]
def baseStart_5779871 : Nat := 118140960795 + 5779871 * 2 ^ 59
def prefixEnd_5779871 : Nat := 4983230072969 + 3 ^ 40 * 5779871 * 2
def baseEnd_5779871 : Nat := 989283981327686987277121

theorem tailTrace_5779871 : CollatzResearch.WordTrace tailWord_5779871 prefixEnd_5779871 989283981327686987277121 := by
  unfold tailWord_5779871
  simp only [CollatzResearch.WordTrace]
  refine ⟨210809214043521965223003467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140539476029014643482002311 210809214043521965223003467)
  ·
    refine ⟨316213821065282947834505201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210809214043521965223003467 316213821065282947834505201)
    ·
      refine ⟨237160365798962210875878901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316213821065282947834505201 237160365798962210875878901)
      ·
        refine ⟨22233784293652707269613647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237160365798962210875878901 22233784293652707269613647)
        ·
          refine ⟨33350676440479060904420471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22233784293652707269613647 33350676440479060904420471)
          ·
            refine ⟨50026014660718591356630707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33350676440479060904420471 50026014660718591356630707)
            ·
              refine ⟨75039021991077887034946061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50026014660718591356630707 75039021991077887034946061)
              ·
                refine ⟨28139633246654207638104773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75039021991077887034946061 28139633246654207638104773)
                ·
                  refine ⟨5276181233747663932144645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28139633246654207638104773 5276181233747663932144645)
                  ·
                    refine ⟨989283981327686987277121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5276181233747663932144645 989283981327686987277121)
                    ·
                      rfl

theorem cell23_5779871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 3, 4, 4].length) (baseStart_5779871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779871 prefixEnd_5779871 := by exact prefixLift 5779871
  have htrace : WordTrace (prefixWord ++ tailWord_5779871) baseStart_5779871 baseEnd_5779871 := by
    simpa [prefixWord, tailWord_5779871, baseEnd_5779871] using wordTrace_append hprefix tailTrace_5779871
  have hstable : (prefixWord ++ tailWord_5779871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779871).length < 2 ^ (prefixWord ++ tailWord_5779871).sum := by decide
  have hdescent : baseEnd_5779871 < baseStart_5779871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779872 : List Nat := [2, 1, 1, 4, 1, 4, 3, 2, 1, 1, 3]
def baseStart_5779872 : Nat := 118140960795 + 5779872 * 2 ^ 59
def prefixEnd_5779872 : Nat := 4983230072969 + 3 ^ 40 * 5779872 * 2
def baseEnd_5779872 : Nat := 2967852457463715457918859

theorem tailTrace_5779872 : CollatzResearch.WordTrace tailWord_5779872 prefixEnd_5779872 2967852457463715457918859 := by
  unfold tailWord_5779872
  simp only [CollatzResearch.WordTrace]
  refine ⟨105404625258259171196894935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140539500344345561595859913 105404625258259171196894935)
  ·
    refine ⟨158106937887388756795342403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105404625258259171196894935 158106937887388756795342403)
    ·
      refine ⟨237160406831083135193013605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158106937887388756795342403 237160406831083135193013605)
      ·
        refine ⟨44467576280828087848690051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237160406831083135193013605 44467576280828087848690051)
        ·
          refine ⟨66701364421242131773035077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44467576280828087848690051 66701364421242131773035077)
          ·
            refine ⟨12506505828982899707444077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66701364421242131773035077 12506505828982899707444077)
            ·
              refine ⟨4689939685868587390291529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12506505828982899707444077 4689939685868587390291529)
              ·
                refine ⟨3517454764401440542718647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4689939685868587390291529 3517454764401440542718647)
                ·
                  refine ⟨5276182146602160814077971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3517454764401440542718647 5276182146602160814077971)
                  ·
                    refine ⟨7914273219903241221116957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5276182146602160814077971 7914273219903241221116957)
                    ·
                      refine ⟨2967852457463715457918859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7914273219903241221116957 2967852457463715457918859)
                      ·
                        rfl

theorem cell23_5779872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_5779872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779872 prefixEnd_5779872 := by exact prefixLift 5779872
  have htrace : WordTrace (prefixWord ++ tailWord_5779872) baseStart_5779872 baseEnd_5779872 := by
    simpa [prefixWord, tailWord_5779872, baseEnd_5779872] using wordTrace_append hprefix tailTrace_5779872
  have hstable : (prefixWord ++ tailWord_5779872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779872).length < 2 ^ (prefixWord ++ tailWord_5779872).sum := by decide
  have hdescent : baseEnd_5779872 < baseStart_5779872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779911 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_5779911 : Nat := 118140960795 + 5779911 * 2 ^ 59
def prefixEnd_5779911 : Nat := 4983230072969 + 3 ^ 40 * 5779911 * 2
def baseEnd_5779911 : Nat := 2967872483209240805331179

theorem tailTrace_5779911 : CollatzResearch.WordTrace tailWord_5779911 prefixEnd_5779911 2967872483209240805331179 := by
  unfold tailWord_5779911
  simp only [CollatzResearch.WordTrace]
  refine ⟨210810672963377052054459587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140540448642251368036306391 210810672963377052054459587)
  ·
    refine ⟨316216009445065578081689381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210810672963377052054459587 316216009445065578081689381)
    ·
      refine ⟨59290501770949795890316759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316216009445065578081689381 59290501770949795890316759)
      ·
        refine ⟨88935752656424693835475139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59290501770949795890316759 88935752656424693835475139)
        ·
          refine ⟨133403628984637040753212709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88935752656424693835475139 133403628984637040753212709)
          ·
            refine ⟨25013180434619445141227383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 133403628984637040753212709 25013180434619445141227383)
            ·
              refine ⟨37519770651929167711841075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25013180434619445141227383 37519770651929167711841075)
              ·
                refine ⟨56279655977893751567761613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37519770651929167711841075 56279655977893751567761613)
                ·
                  refine ⟨21104870991710156837910605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56279655977893751567761613 21104870991710156837910605)
                  ·
                    refine ⟨7914326621891308814216477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21104870991710156837910605 7914326621891308814216477)
                    ·
                      refine ⟨2967872483209240805331179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7914326621891308814216477 2967872483209240805331179)
                      ·
                        rfl

theorem cell23_5779911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_5779911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779911 prefixEnd_5779911 := by exact prefixLift 5779911
  have htrace : WordTrace (prefixWord ++ tailWord_5779911) baseStart_5779911 baseEnd_5779911 := by
    simpa [prefixWord, tailWord_5779911, baseEnd_5779911] using wordTrace_append hprefix tailTrace_5779911
  have hstable : (prefixWord ++ tailWord_5779911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779911).length < 2 ^ (prefixWord ++ tailWord_5779911).sum := by decide
  have hdescent : baseEnd_5779911 < baseStart_5779911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779922 : List Nat := [3, 2, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_5779922 : Nat := 118140960795 + 5779922 * 2 ^ 59
def prefixEnd_5779922 : Nat := 4983230072969 + 3 ^ 40 * 5779922 * 2
def baseEnd_5779922 : Nat := 989292710498813420764543

theorem tailTrace_5779922 : CollatzResearch.WordTrace tailWord_5779922 prefixEnd_5779922 989292710498813420764543 := by
  unfold tailWord_5779922
  simp only [CollatzResearch.WordTrace]
  refine ⟨52702768541584300233277505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140540716110891467288740013 52702768541584300233277505)
  ·
    refine ⟨39527076406188225174958129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52702768541584300233277505 39527076406188225174958129)
    ·
      refine ⟨29645307304641168881218597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39527076406188225174958129 29645307304641168881218597)
      ·
        refine ⟨5558495119620219165228487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29645307304641168881218597 5558495119620219165228487)
        ·
          refine ⟨8337742679430328747842731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5558495119620219165228487 8337742679430328747842731)
          ·
            refine ⟨12506614019145493121764097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8337742679430328747842731 12506614019145493121764097)
            ·
              refine ⟨9379960514359119841323073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12506614019145493121764097 9379960514359119841323073)
              ·
                refine ⟨7034970385769339880992305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9379960514359119841323073 7034970385769339880992305)
                ·
                  refine ⟨5276227789327004910744229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7034970385769339880992305 5276227789327004910744229)
                  ·
                    refine ⟨989292710498813420764543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5276227789327004910744229 989292710498813420764543)
                    ·
                      rfl

theorem cell23_5779922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_5779922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779922 prefixEnd_5779922 := by exact prefixLift 5779922
  have htrace : WordTrace (prefixWord ++ tailWord_5779922) baseStart_5779922 baseEnd_5779922 := by
    simpa [prefixWord, tailWord_5779922, baseEnd_5779922] using wordTrace_append hprefix tailTrace_5779922
  have hstable : (prefixWord ++ tailWord_5779922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779922).length < 2 ^ (prefixWord ++ tailWord_5779922).sum := by decide
  have hdescent : baseEnd_5779922 < baseStart_5779922 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779972 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5779972 : Nat := 118140960795 + 5779972 * 2 ^ 59
def prefixEnd_5779972 : Nat := 4983230072969 + 3 ^ 40 * 5779972 * 2
def baseEnd_5779972 : Nat := 2967903805529165066668399

theorem tailTrace_5779972 : CollatzResearch.WordTrace tailWord_5779972 prefixEnd_5779972 2967903805529165066668399 := by
  unfold tailWord_5779972
  simp only [CollatzResearch.WordTrace]
  refine ⟨105406448908078029736215085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140541931877437372981620113 105406448908078029736215085)
  ·
    refine ⟨39527418340529261151080657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105406448908078029736215085 39527418340529261151080657)
    ·
      refine ⟨29645563755396945863310493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39527418340529261151080657 29645563755396945863310493)
      ·
        refine ⟨11117086408273854698741435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29645563755396945863310493 11117086408273854698741435)
        ·
          refine ⟨16675629612410782048112153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11117086408273854698741435 16675629612410782048112153)
          ·
            refine ⟨12506722209308086536084115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16675629612410782048112153 12506722209308086536084115)
            ·
              refine ⟨18760083313962129804126173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12506722209308086536084115 18760083313962129804126173)
              ·
                refine ⟨7035031242735798676547315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18760083313962129804126173 7035031242735798676547315)
                ·
                  refine ⟨10552546864103698014820973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7035031242735798676547315 10552546864103698014820973)
                  ·
                    refine ⟨3957205074038886755557865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10552546864103698014820973 3957205074038886755557865)
                    ·
                      refine ⟨2967903805529165066668399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957205074038886755557865 2967903805529165066668399)
                      ·
                        rfl

theorem cell23_5779972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5779972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779972 prefixEnd_5779972 := by exact prefixLift 5779972
  have htrace : WordTrace (prefixWord ++ tailWord_5779972) baseStart_5779972 baseEnd_5779972 := by
    simpa [prefixWord, tailWord_5779972, baseEnd_5779972] using wordTrace_append hprefix tailTrace_5779972
  have hstable : (prefixWord ++ tailWord_5779972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779972).length < 2 ^ (prefixWord ++ tailWord_5779972).sum := by decide
  have hdescent : baseEnd_5779972 < baseStart_5779972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5779985 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 2, 2, 2]
def baseStart_5779985 : Nat := 118140960795 + 5779985 * 2 ^ 59
def prefixEnd_5779985 : Nat := 4983230072969 + 3 ^ 40 * 5779985 * 2
def baseEnd_5779985 : Nat := 2967910480777673515805839

theorem tailTrace_5779985 : CollatzResearch.WordTrace tailWord_5779985 prefixEnd_5779985 2967910480777673515805839 := by
  unfold tailWord_5779985
  simp only [CollatzResearch.WordTrace]
  refine ⟨210813371965108962692653409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140542247976739308461768939 210813371965108962692653409)
  ·
    refine ⟨158110028973831722019490057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210813371965108962692653409 158110028973831722019490057)
    ·
      refine ⟨118582521730373791514617543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158110028973831722019490057 118582521730373791514617543)
      ·
        refine ⟨177873782595560687271926315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118582521730373791514617543 177873782595560687271926315)
        ·
          refine ⟨266810673893341030907889473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177873782595560687271926315 266810673893341030907889473)
          ·
            refine ⟨200108005420005773180917105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266810673893341030907889473 200108005420005773180917105)
            ·
              refine ⟨150081004065004329885687829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200108005420005773180917105 150081004065004329885687829)
              ·
                refine ⟨7035047065547077963391617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150081004065004329885687829 7035047065547077963391617)
                ·
                  refine ⟨5276285299160308472543713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7035047065547077963391617 5276285299160308472543713)
                  ·
                    refine ⟨3957213974370231354407785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5276285299160308472543713 3957213974370231354407785)
                    ·
                      refine ⟨2967910480777673515805839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957213974370231354407785 2967910480777673515805839)
                      ·
                        rfl

theorem cell23_5779985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 2, 2, 2].length) (baseStart_5779985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5779985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5779985 prefixEnd_5779985 := by exact prefixLift 5779985
  have htrace : WordTrace (prefixWord ++ tailWord_5779985) baseStart_5779985 baseEnd_5779985 := by
    simpa [prefixWord, tailWord_5779985, baseEnd_5779985] using wordTrace_append hprefix tailTrace_5779985
  have hstable : (prefixWord ++ tailWord_5779985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5779985).length < 2 ^ (prefixWord ++ tailWord_5779985).sum := by decide
  have hdescent : baseEnd_5779985 < baseStart_5779985 := by decide
  rcases family_descends (prefixWord ++ tailWord_5779985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780008 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 7]
def baseStart_5780008 : Nat := 118140960795 + 5780008 * 2 ^ 59
def prefixEnd_5780008 : Nat := 4983230072969 + 3 ^ 40 * 5780008 * 2
def baseEnd_5780008 : Nat := 329769143425858547313137

theorem tailTrace_5780008 : CollatzResearch.WordTrace tailWord_5780008 prefixEnd_5780008 329769143425858547313137 := by
  unfold tailWord_5780008
  simp only [CollatzResearch.WordTrace]
  refine ⟨105407105422012818810370339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140542807229350425080493785 105407105422012818810370339)
  ·
    refine ⟨158110658133019228215555509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105407105422012818810370339 158110658133019228215555509)
    ·
      refine ⟨14822874199970552645208329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158110658133019228215555509 14822874199970552645208329)
      ·
        refine ⟨11117155649977914483906247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14822874199970552645208329 11117155649977914483906247)
        ·
          refine ⟨16675733474966871725859371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11117155649977914483906247 16675733474966871725859371)
          ·
            refine ⟨25013600212450307588789057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16675733474966871725859371 25013600212450307588789057)
            ·
              refine ⟨18760200159337730691591793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25013600212450307588789057 18760200159337730691591793)
              ·
                refine ⟨14070150119503298018693845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18760200159337730691591793 14070150119503298018693845)
                ·
                  refine ⟨329769143425858547313137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14070150119503298018693845 329769143425858547313137)
                  ·
                    rfl

theorem cell23_5780008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 7].length) (baseStart_5780008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780008 prefixEnd_5780008 := by exact prefixLift 5780008
  have htrace : WordTrace (prefixWord ++ tailWord_5780008) baseStart_5780008 baseEnd_5780008 := by
    simpa [prefixWord, tailWord_5780008, baseEnd_5780008] using wordTrace_append hprefix tailTrace_5780008
  have hstable : (prefixWord ++ tailWord_5780008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780008).length < 2 ^ (prefixWord ++ tailWord_5780008).sum := by decide
  have hdescent : baseEnd_5780008 < baseStart_5780008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780021 : List Nat := [1, 3, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_5780021 : Nat := 118140960795 + 5780021 * 2 ^ 59
def prefixEnd_5780021 : Nat := 4983230072969 + 3 ^ 40 * 5780021 * 2
def baseEnd_5780021 : Nat := 989309655360411791651891

theorem tailTrace_5780021 : CollatzResearch.WordTrace tailWord_5780021 prefixEnd_5780021 989309655360411791651891 := by
  unfold tailWord_5780021
  simp only [CollatzResearch.WordTrace]
  refine ⟨210814684992978540840963917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140543123328652360560642611 210814684992978540840963917)
  ·
    refine ⟨79055506872366952815361469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210814684992978540840963917 79055506872366952815361469)
    ·
      refine ⟨29645815077137607305760551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79055506872366952815361469 29645815077137607305760551)
      ·
        refine ⟨44468722615706410958640827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29645815077137607305760551 44468722615706410958640827)
        ·
          refine ⟨66703083923559616437961241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44468722615706410958640827 66703083923559616437961241)
          ·
            refine ⟨50027312942669712328470931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66703083923559616437961241 50027312942669712328470931)
            ·
              refine ⟨75040969414004568492706397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50027312942669712328470931 75040969414004568492706397)
              ·
                refine ⟨28140363530251713184764899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75040969414004568492706397 28140363530251713184764899)
                ·
                  refine ⟨42210545295377569777147349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28140363530251713184764899 42210545295377569777147349)
                  ·
                    refine ⟨989309655360411791651891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42210545295377569777147349 989309655360411791651891)
                    ·
                      rfl

theorem cell23_5780021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_5780021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780021 prefixEnd_5780021 := by exact prefixLift 5780021
  have htrace : WordTrace (prefixWord ++ tailWord_5780021) baseStart_5780021 baseEnd_5780021 := by
    simpa [prefixWord, tailWord_5780021, baseEnd_5780021] using wordTrace_append hprefix tailTrace_5780021
  have hstable : (prefixWord ++ tailWord_5780021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780021).length < 2 ^ (prefixWord ++ tailWord_5780021).sum := by decide
  have hdescent : baseEnd_5780021 < baseStart_5780021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780031 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 5]
def baseStart_5780031 : Nat := 118140960795 + 5780031 * 2 ^ 59
def prefixEnd_5780031 : Nat := 4983230072969 + 3 ^ 40 * 5780031 * 2
def baseEnd_5780031 : Nat := 2967934100887780335830627

theorem tailTrace_5780031 : CollatzResearch.WordTrace tailWord_5780031 prefixEnd_5780031 2967934100887780335830627 := by
  unfold tailWord_5780031
  simp only [CollatzResearch.WordTrace]
  refine ⟨210815049722942312548827947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140543366481961541699218631 210815049722942312548827947)
  ·
    refine ⟨316222574584413468823241921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210815049722942312548827947 316222574584413468823241921)
    ·
      refine ⟨237166930938310101617431441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316222574584413468823241921 237166930938310101617431441)
      ·
        refine ⟨177875198203732576213073581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237166930938310101617431441 177875198203732576213073581)
        ·
          refine ⟨66703199326399716079902593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177875198203732576213073581 66703199326399716079902593)
          ·
            refine ⟨50027399494799787059926945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66703199326399716079902593 50027399494799787059926945)
            ·
              refine ⟨37520549621099840294945209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50027399494799787059926945 37520549621099840294945209)
              ·
                refine ⟨28140412215824880221208907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37520549621099840294945209 28140412215824880221208907)
                ·
                  refine ⟨42210618323737320331813361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28140412215824880221208907 42210618323737320331813361)
                  ·
                    refine ⟨31657963742802990248860021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42210618323737320331813361 31657963742802990248860021)
                    ·
                      refine ⟨2967934100887780335830627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31657963742802990248860021 2967934100887780335830627)
                      ·
                        rfl

theorem cell23_5780031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_5780031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780031 prefixEnd_5780031 := by exact prefixLift 5780031
  have htrace : WordTrace (prefixWord ++ tailWord_5780031) baseStart_5780031 baseEnd_5780031 := by
    simpa [prefixWord, tailWord_5780031, baseEnd_5780031] using wordTrace_append hprefix tailTrace_5780031
  have hstable : (prefixWord ++ tailWord_5780031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780031).length < 2 ^ (prefixWord ++ tailWord_5780031).sum := by decide
  have hdescent : baseEnd_5780031 < baseStart_5780031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780068 : List Nat := [2, 3, 1, 1, 2, 2, 2, 1, 5, 4]
def baseStart_5780068 : Nat := 118140960795 + 5780068 * 2 ^ 59
def prefixEnd_5780068 : Nat := 4983230072969 + 3 ^ 40 * 5780068 * 2
def baseEnd_5780068 : Nat := 989317699890665563689319

theorem tailTrace_5780068 : CollatzResearch.WordTrace tailWord_5780068 prefixEnd_5780068 989317699890665563689319 := by
  unfold tailWord_5780068
  simp only [CollatzResearch.WordTrace]
  refine ⟨105408199611904133933962429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140544266149205511911949905 105408199611904133933962429)
  ·
    refine ⟨39528074854464050225235911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105408199611904133933962429 39528074854464050225235911)
    ·
      refine ⟨59292112281696075337853867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39528074854464050225235911 59292112281696075337853867)
      ·
        refine ⟨88938168422544113006780801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59292112281696075337853867 88938168422544113006780801)
        ·
          refine ⟨66703626316908084755085601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88938168422544113006780801 66703626316908084755085601)
          ·
            refine ⟨50027719737681063566314201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66703626316908084755085601 50027719737681063566314201)
            ·
              refine ⟨37520789803260797674735651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50027719737681063566314201 37520789803260797674735651)
              ·
                refine ⟨56281184704891196512103477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37520789803260797674735651 56281184704891196512103477)
                ·
                  refine ⟨5276361066083549673009701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56281184704891196512103477 5276361066083549673009701)
                  ·
                    refine ⟨989317699890665563689319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5276361066083549673009701 989317699890665563689319)
                    ·
                      rfl

theorem cell23_5780068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_5780068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780068 prefixEnd_5780068 := by exact prefixLift 5780068
  have htrace : WordTrace (prefixWord ++ tailWord_5780068) baseStart_5780068 baseEnd_5780068 := by
    simpa [prefixWord, tailWord_5780068, baseEnd_5780068] using wordTrace_append hprefix tailTrace_5780068
  have hstable : (prefixWord ++ tailWord_5780068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780068).length < 2 ^ (prefixWord ++ tailWord_5780068).sum := by decide
  have hdescent : baseEnd_5780068 < baseStart_5780068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780071 : List Nat := [1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_5780071 : Nat := 118140960795 + 5780071 * 2 ^ 59
def prefixEnd_5780071 : Nat := 4983230072969 + 3 ^ 40 * 5780071 * 2
def baseEnd_5780071 : Nat := 2967954640113960179330443

theorem tailTrace_5780071 : CollatzResearch.WordTrace tailWord_5780071 prefixEnd_5780071 2967954640113960179330443 := by
  unfold tailWord_5780071
  simp only [CollatzResearch.WordTrace]
  refine ⟨210816508642797399380284067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140544339095198266253522711 210816508642797399380284067)
  ·
    refine ⟨316224762964196099070426101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210816508642797399380284067 316224762964196099070426101)
    ·
      refine ⟨29646071527893384287852447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316224762964196099070426101 29646071527893384287852447)
      ·
        refine ⟨44469107291840076431778671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29646071527893384287852447 44469107291840076431778671)
        ·
          refine ⟨66703660937760114647668007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44469107291840076431778671 66703660937760114647668007)
          ·
            refine ⟨100055491406640171971502011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66703660937760114647668007 100055491406640171971502011)
            ·
              refine ⟨150083237109960257957253017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100055491406640171971502011 150083237109960257957253017)
              ·
                refine ⟨112562427832470193467939763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150083237109960257957253017 112562427832470193467939763)
                ·
                  refine ⟨168843641748705290201909645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112562427832470193467939763 168843641748705290201909645)
                  ·
                    refine ⟨63316365655764483825716117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 168843641748705290201909645 63316365655764483825716117)
                    ·
                      refine ⟨2967954640113960179330443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63316365655764483825716117 2967954640113960179330443)
                      ·
                        rfl

theorem cell23_5780071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_5780071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780071 prefixEnd_5780071 := by exact prefixLift 5780071
  have htrace : WordTrace (prefixWord ++ tailWord_5780071) baseStart_5780071 baseEnd_5780071 := by
    simpa [prefixWord, tailWord_5780071, baseEnd_5780071] using wordTrace_append hprefix tailTrace_5780071
  have hstable : (prefixWord ++ tailWord_5780071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780071).length < 2 ^ (prefixWord ++ tailWord_5780071).sum := by decide
  have hdescent : baseEnd_5780071 < baseStart_5780071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780121 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 7]
def baseStart_5780121 : Nat := 118140960795 + 5780121 * 2 ^ 59
def prefixEnd_5780121 : Nat := 4983230072969 + 3 ^ 40 * 5780121 * 2
def baseEnd_5780121 : Nat := 2967980314146684983705213

theorem tailTrace_5780121 : CollatzResearch.WordTrace tailWord_5780121 prefixEnd_5780121 2967980314146684983705213 := by
  unfold tailWord_5780121
  simp only [CollatzResearch.WordTrace]
  refine ⟨210818332292616257919604217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140545554861744171946402811 210818332292616257919604217)
  ·
    refine ⟨158113749219462193439703163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210818332292616257919604217 158113749219462193439703163)
    ·
      refine ⟨237170623829193290159554745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158113749219462193439703163 237170623829193290159554745)
      ·
        refine ⟨177877967871894967619666059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237170623829193290159554745 177877967871894967619666059)
        ·
          refine ⟨266816951807842451429499089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177877967871894967619666059 266816951807842451429499089)
          ·
            refine ⟨200112713855881838572124317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266816951807842451429499089 200112713855881838572124317)
            ·
              refine ⟨75042267695955689464546619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200112713855881838572124317 75042267695955689464546619)
              ·
                refine ⟨112563401543933534196819929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75042267695955689464546619 112563401543933534196819929)
                ·
                  refine ⟨84422551157950150647614947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112563401543933534196819929 84422551157950150647614947)
                  ·
                    refine ⟨126633826736925225971422421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84422551157950150647614947 126633826736925225971422421)
                    ·
                      refine ⟨2967980314146684983705213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126633826736925225971422421 2967980314146684983705213)
                      ·
                        rfl

theorem cell23_5780121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 2, 1, 7].length) (baseStart_5780121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780121 prefixEnd_5780121 := by exact prefixLift 5780121
  have htrace : WordTrace (prefixWord ++ tailWord_5780121) baseStart_5780121 baseEnd_5780121 := by
    simpa [prefixWord, tailWord_5780121, baseEnd_5780121] using wordTrace_append hprefix tailTrace_5780121
  have hstable : (prefixWord ++ tailWord_5780121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780121).length < 2 ^ (prefixWord ++ tailWord_5780121).sum := by decide
  have hdescent : baseEnd_5780121 < baseStart_5780121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780125 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_5780125 : Nat := 118140960795 + 5780125 * 2 ^ 59
def prefixEnd_5780125 : Nat := 4983230072969 + 3 ^ 40 * 5780125 * 2
def baseEnd_5780125 : Nat := 2967982368069302968055195

theorem tailTrace_5780125 : CollatzResearch.WordTrace tailWord_5780125 prefixEnd_5780125 2967982368069302968055195 := by
  unfold tailWord_5780125
  simp only [CollatzResearch.WordTrace]
  refine ⟨210818478184601766602749829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140545652123067844401833219 210818478184601766602749829)
  ·
    refine ⟨39528464659612831238015593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210818478184601766602749829 39528464659612831238015593)
    ·
      refine ⟨29646348494709623428511695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39528464659612831238015593 29646348494709623428511695)
      ·
        refine ⟨44469522742064435142767543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29646348494709623428511695 44469522742064435142767543)
        ·
          refine ⟨66704284113096652714151315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44469522742064435142767543 66704284113096652714151315)
          ·
            refine ⟨100056426169644979071226973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66704284113096652714151315 100056426169644979071226973)
            ·
              refine ⟨37521159813616867151710115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100056426169644979071226973 37521159813616867151710115)
              ·
                refine ⟨56281739720425300727565173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37521159813616867151710115 56281739720425300727565173)
                ·
                  refine ⟨5276413098789871943209235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56281739720425300727565173 5276413098789871943209235)
                  ·
                    refine ⟨7914619648184807914813853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5276413098789871943209235 7914619648184807914813853)
                    ·
                      refine ⟨2967982368069302968055195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7914619648184807914813853 2967982368069302968055195)
                      ·
                        rfl

theorem cell23_5780125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_5780125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780125 prefixEnd_5780125 := by exact prefixLift 5780125
  have htrace : WordTrace (prefixWord ++ tailWord_5780125) baseStart_5780125 baseEnd_5780125 := by
    simpa [prefixWord, tailWord_5780125, baseEnd_5780125] using wordTrace_append hprefix tailTrace_5780125
  have hstable : (prefixWord ++ tailWord_5780125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780125).length < 2 ^ (prefixWord ++ tailWord_5780125).sum := by decide
  have hdescent : baseEnd_5780125 < baseStart_5780125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780129 : List Nat := [1, 2, 3, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_5780129 : Nat := 118140960795 + 5780129 * 2 ^ 59
def prefixEnd_5780129 : Nat := 4983230072969 + 3 ^ 40 * 5780129 * 2
def baseEnd_5780129 : Nat := 2967984421991920952405177

theorem tailTrace_5780129 : CollatzResearch.WordTrace tailWord_5780129 prefixEnd_5780129 2967984421991920952405177 := by
  unfold tailWord_5780129
  simp only [CollatzResearch.WordTrace]
  refine ⟨210818624076587275285895441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140545749384391516857263627 210818624076587275285895441)
  ·
    refine ⟨158113968057440456464421581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210818624076587275285895441 158113968057440456464421581)
    ·
      refine ⟨59292738021540171174158093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158113968057440456464421581 59292738021540171174158093)
      ·
        refine ⟨22234776758077564190309285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59292738021540171174158093 22234776758077564190309285)
        ·
          refine ⟨4169020642139543285682991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22234776758077564190309285 4169020642139543285682991)
          ·
            refine ⟨6253530963209314928524487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169020642139543285682991 6253530963209314928524487)
            ·
              refine ⟨9380296444813972392786731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6253530963209314928524487 9380296444813972392786731)
              ·
                refine ⟨14070444667220958589180097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9380296444813972392786731 14070444667220958589180097)
                ·
                  refine ⟨10552833500415718941885073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14070444667220958589180097 10552833500415718941885073)
                  ·
                    refine ⟨7914625125311789206413805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10552833500415718941885073 7914625125311789206413805)
                    ·
                      refine ⟨2967984421991920952405177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7914625125311789206413805 2967984421991920952405177)
                      ·
                        rfl

theorem cell23_5780129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_5780129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780129 prefixEnd_5780129 := by exact prefixLift 5780129
  have htrace : WordTrace (prefixWord ++ tailWord_5780129) baseStart_5780129 baseEnd_5780129 := by
    simpa [prefixWord, tailWord_5780129, baseEnd_5780129] using wordTrace_append hprefix tailTrace_5780129
  have hstable : (prefixWord ++ tailWord_5780129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780129).length < 2 ^ (prefixWord ++ tailWord_5780129).sum := by decide
  have hdescent : baseEnd_5780129 < baseStart_5780129 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780166 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_5780166 : Nat := 118140960795 + 5780166 * 2 ^ 59
def prefixEnd_5780166 : Nat := 4983230072969 + 3 ^ 40 * 5780166 * 2
def baseEnd_5780166 : Nat := 329778157864015256404723

theorem tailTrace_5780166 : CollatzResearch.WordTrace tailWord_5780166 prefixEnd_5780166 329778157864015256404723 := by
  unfold tailWord_5780166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6588124174295413456406011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 140546649051635487069994901 6588124174295413456406011)
  ·
    refine ⟨9882186261443120184609017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6588124174295413456406011 9882186261443120184609017)
    ·
      refine ⟨7411639696082340138456763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9882186261443120184609017 7411639696082340138456763)
      ·
        refine ⟨11117459544123510207685145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7411639696082340138456763 11117459544123510207685145)
        ·
          refine ⟨8338094658092632655763859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11117459544123510207685145 8338094658092632655763859)
          ·
            refine ⟨12507141987138948983645789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8338094658092632655763859 12507141987138948983645789)
            ·
              refine ⟨4690178245177105868867171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12507141987138948983645789 4690178245177105868867171)
              ·
                refine ⟨7035267367765658803300757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4690178245177105868867171 7035267367765658803300757)
                ·
                  refine ⟨329778157864015256404723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7035267367765658803300757 329778157864015256404723)
                  ·
                    rfl

theorem cell23_5780166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_5780166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780166 prefixEnd_5780166 := by exact prefixLift 5780166
  have htrace : WordTrace (prefixWord ++ tailWord_5780166) baseStart_5780166 baseEnd_5780166 := by
    simpa [prefixWord, tailWord_5780166, baseEnd_5780166] using wordTrace_append hprefix tailTrace_5780166
  have hstable : (prefixWord ++ tailWord_5780166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780166).length < 2 ^ (prefixWord ++ tailWord_5780166).sum := by decide
  have hdescent : baseEnd_5780166 < baseStart_5780166 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780168 : List Nat := [2, 1, 3, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_5780168 : Nat := 118140960795 + 5780168 * 2 ^ 59
def prefixEnd_5780168 : Nat := 4983230072969 + 3 ^ 40 * 5780168 * 2
def baseEnd_5780168 : Nat := 2968004447737446299817497

theorem tailTrace_5780168 : CollatzResearch.WordTrace tailWord_5780168 prefixEnd_5780168 2968004447737446299817497 := by
  unfold tailWord_5780168
  simp only [CollatzResearch.WordTrace]
  refine ⟨105410023261722992473282579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140546697682297323297710105 105410023261722992473282579)
  ·
    refine ⟨158115034892584488709923869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105410023261722992473282579 158115034892584488709923869)
    ·
      refine ⟨59293138084719183266221451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158115034892584488709923869 59293138084719183266221451)
      ·
        refine ⟨88939707127078774899332177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59293138084719183266221451 88939707127078774899332177)
        ·
          refine ⟨66704780345309081174499133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88939707127078774899332177 66704780345309081174499133)
          ·
            refine ⟨25014292629490905440437175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66704780345309081174499133 25014292629490905440437175)
            ·
              refine ⟨37521438944236358160655763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25014292629490905440437175 37521438944236358160655763)
              ·
                refine ⟨56282158416354537240983645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37521438944236358160655763 56282158416354537240983645)
                ·
                  refine ⟨21105809406132951465368867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56282158416354537240983645 21105809406132951465368867)
                  ·
                    refine ⟨31658714109199427198053301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21105809406132951465368867 31658714109199427198053301)
                    ·
                      refine ⟨2968004447737446299817497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31658714109199427198053301 2968004447737446299817497)
                      ·
                        rfl

theorem cell23_5780168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_5780168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780168 prefixEnd_5780168 := by exact prefixLift 5780168
  have htrace : WordTrace (prefixWord ++ tailWord_5780168) baseStart_5780168 baseEnd_5780168 := by
    simpa [prefixWord, tailWord_5780168, baseEnd_5780168] using wordTrace_append hprefix tailTrace_5780168
  have hstable : (prefixWord ++ tailWord_5780168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780168).length < 2 ^ (prefixWord ++ tailWord_5780168).sum := by decide
  have hdescent : baseEnd_5780168 < baseStart_5780168 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780216 : List Nat := [2, 1, 2, 1, 1, 2, 7, 2, 1, 2, 2]
def baseStart_5780216 : Nat := 118140960795 + 5780216 * 2 ^ 59
def prefixEnd_5780216 : Nat := 4983230072969 + 3 ^ 40 * 5780216 * 2
def baseEnd_5780216 : Nat := 2968029094808862112017277

theorem tailTrace_5780216 : CollatzResearch.WordTrace tailWord_5780216 prefixEnd_5780216 2968029094808862112017277 := by
  unfold tailWord_5780216
  simp only [CollatzResearch.WordTrace]
  refine ⟨105410898613636044572156251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140547864818181392762875001 105410898613636044572156251)
  ·
    refine ⟨158116347920454066858234377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105410898613636044572156251 158116347920454066858234377)
    ·
      refine ⟨118587260940340550143675783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158116347920454066858234377 118587260940340550143675783)
      ·
        refine ⟨177880891410510825215513675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118587260940340550143675783 177880891410510825215513675)
        ·
          refine ⟨266821337115766237823270513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177880891410510825215513675 266821337115766237823270513)
          ·
            refine ⟨200116002836824678367452885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266821337115766237823270513 200116002836824678367452885)
            ·
              refine ⟨4690218816488078399237177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 200116002836824678367452885 4690218816488078399237177)
              ·
                refine ⟨3517664112366058799427883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4690218816488078399237177 3517664112366058799427883)
                ·
                  refine ⟨5276496168549088199141825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3517664112366058799427883 5276496168549088199141825)
                  ·
                    refine ⟨3957372126411816149356369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5276496168549088199141825 3957372126411816149356369)
                    ·
                      refine ⟨2968029094808862112017277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957372126411816149356369 2968029094808862112017277)
                      ·
                        rfl

theorem cell23_5780216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 2, 1, 2, 2].length) (baseStart_5780216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780216 prefixEnd_5780216 := by exact prefixLift 5780216
  have htrace : WordTrace (prefixWord ++ tailWord_5780216) baseStart_5780216 baseEnd_5780216 := by
    simpa [prefixWord, tailWord_5780216, baseEnd_5780216] using wordTrace_append hprefix tailTrace_5780216
  have hstable : (prefixWord ++ tailWord_5780216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780216).length < 2 ^ (prefixWord ++ tailWord_5780216).sum := by decide
  have hdescent : baseEnd_5780216 < baseStart_5780216 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780225 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_5780225 : Nat := 118140960795 + 5780225 * 2 ^ 59
def prefixEnd_5780225 : Nat := 4983230072969 + 3 ^ 40 * 5780225 * 2
def baseEnd_5780225 : Nat := 2968033716134752576804735

theorem tailTrace_5780225 : CollatzResearch.WordTrace tailWord_5780225 prefixEnd_5780225 2968033716134752576804735 := by
  unfold tailWord_5780225
  simp only [CollatzResearch.WordTrace]
  refine ⟨210822125484239483681390129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140548083656159655787593419 210822125484239483681390129)
  ·
    refine ⟨158116594113179612761042597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210822125484239483681390129 158116594113179612761042597)
    ·
      refine ⟨29646861396221177392695487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158116594113179612761042597 29646861396221177392695487)
      ·
        refine ⟨44470292094331766089043231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29646861396221177392695487 44470292094331766089043231)
        ·
          refine ⟨66705438141497649133564847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44470292094331766089043231 66705438141497649133564847)
          ·
            refine ⟨100058157212246473700347271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66705438141497649133564847 100058157212246473700347271)
            ·
              refine ⟨150087235818369710550520907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100058157212246473700347271 150087235818369710550520907)
              ·
                refine ⟨225130853727554565825781361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150087235818369710550520907 225130853727554565825781361)
                ·
                  refine ⟨168848140295665924369336021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225130853727554565825781361 168848140295665924369336021)
                  ·
                    refine ⟨3957378288179670102406313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 168848140295665924369336021 3957378288179670102406313)
                    ·
                      refine ⟨2968033716134752576804735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957378288179670102406313 2968033716134752576804735)
                      ·
                        rfl

theorem cell23_5780225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_5780225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780225 prefixEnd_5780225 := by exact prefixLift 5780225
  have htrace : WordTrace (prefixWord ++ tailWord_5780225) baseStart_5780225 baseEnd_5780225 := by
    simpa [prefixWord, tailWord_5780225, baseEnd_5780225] using wordTrace_append hprefix tailTrace_5780225
  have hstable : (prefixWord ++ tailWord_5780225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780225).length < 2 ^ (prefixWord ++ tailWord_5780225).sum := by decide
  have hdescent : baseEnd_5780225 < baseStart_5780225 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780226 : List Nat := [3, 4, 1, 1, 1, 4, 2, 1, 2, 4]
def baseStart_5780226 : Nat := 118140960795 + 5780226 * 2 ^ 59
def prefixEnd_5780226 : Nat := 4983230072969 + 3 ^ 40 * 5780226 * 2
def baseEnd_5780226 : Nat := 989344743205135690964077

theorem tailTrace_5780226 : CollatzResearch.WordTrace tailWord_5780226 prefixEnd_5780226 989344743205135690964077 := by
  unfold tailWord_5780226
  simp only [CollatzResearch.WordTrace]
  refine ⟨52705540489308965213044133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140548107971490573901451021 52705540489308965213044133)
  ·
    refine ⟨9882288841745430977445775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52705540489308965213044133 9882288841745430977445775)
    ·
      refine ⟨14823433262618146466168663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9882288841745430977445775 14823433262618146466168663)
      ·
        refine ⟨22235149893927219699252995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14823433262618146466168663 22235149893927219699252995)
        ·
          refine ⟨33352724840890829548879493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22235149893927219699252995 33352724840890829548879493)
          ·
            refine ⟨6253635907667030540414905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33352724840890829548879493 6253635907667030540414905)
            ·
              refine ⟨4690226930750272905311179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6253635907667030540414905 4690226930750272905311179)
              ·
                refine ⟨7035340396125409357966769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4690226930750272905311179 7035340396125409357966769)
                ·
                  refine ⟨5276505297094057018475077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7035340396125409357966769 5276505297094057018475077)
                  ·
                    refine ⟨989344743205135690964077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5276505297094057018475077 989344743205135690964077)
                    ·
                      rfl

theorem cell23_5780226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_5780226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780226 prefixEnd_5780226 := by exact prefixLift 5780226
  have htrace : WordTrace (prefixWord ++ tailWord_5780226) baseStart_5780226 baseEnd_5780226 := by
    simpa [prefixWord, tailWord_5780226, baseEnd_5780226] using wordTrace_append hprefix tailTrace_5780226
  have hstable : (prefixWord ++ tailWord_5780226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780226).length < 2 ^ (prefixWord ++ tailWord_5780226).sum := by decide
  have hdescent : baseEnd_5780226 < baseStart_5780226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780238 : List Nat := [4, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_5780238 : Nat := 118140960795 + 5780238 * 2 ^ 59
def prefixEnd_5780238 : Nat := 4983230072969 + 3 ^ 40 * 5780238 * 2
def baseEnd_5780238 : Nat := 2968040391383261025942175

theorem tailTrace_5780238 : CollatzResearch.WordTrace tailWord_5780238 prefixEnd_5780238 2968040391383261025942175 := by
  unfold tailWord_5780238
  simp only [CollatzResearch.WordTrace]
  refine ⟨26352824954149048362701671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140548399755461591267742245 26352824954149048362701671)
  ·
    refine ⟨39529237431223572544052507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26352824954149048362701671 39529237431223572544052507)
    ·
      refine ⟨59293856146835358816078761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39529237431223572544052507 59293856146835358816078761)
      ·
        refine ⟨44470392110126519112059071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59293856146835358816078761 44470392110126519112059071)
        ·
          refine ⟨66705588165189778668088607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44470392110126519112059071 66705588165189778668088607)
          ·
            refine ⟨100058382247784668002132911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66705588165189778668088607 100058382247784668002132911)
            ·
              refine ⟨150087573371677002003199367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100058382247784668002132911 150087573371677002003199367)
              ·
                refine ⟨225131360057515503004799051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150087573371677002003199367 225131360057515503004799051)
                ·
                  refine ⟨337697040086273254507198577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225131360057515503004799051 337697040086273254507198577)
                  ·
                    refine ⟨253272780064704940880398933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 337697040086273254507198577 253272780064704940880398933)
                    ·
                      refine ⟨2968040391383261025942175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 253272780064704940880398933 2968040391383261025942175)
                      ·
                        rfl

theorem cell23_5780238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_5780238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780238 prefixEnd_5780238 := by exact prefixLift 5780238
  have htrace : WordTrace (prefixWord ++ tailWord_5780238) baseStart_5780238 baseEnd_5780238 := by
    simpa [prefixWord, tailWord_5780238, baseEnd_5780238] using wordTrace_append hprefix tailTrace_5780238
  have hstable : (prefixWord ++ tailWord_5780238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780238).length < 2 ^ (prefixWord ++ tailWord_5780238).sum := by decide
  have hdescent : baseEnd_5780238 < baseStart_5780238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780248 : List Nat := [2, 1, 2, 3, 1, 1, 1, 2, 4, 6]
def baseStart_5780248 : Nat := 118140960795 + 5780248 * 2 ^ 59
def prefixEnd_5780248 : Nat := 4983230072969 + 3 ^ 40 * 5780248 * 2
def baseEnd_5780248 : Nat := 989348508729935328939043

theorem tailTrace_5780248 : CollatzResearch.WordTrace tailWord_5780248 prefixEnd_5780248 989348508729935328939043 := by
  unfold tailWord_5780248
  simp only [CollatzResearch.WordTrace]
  refine ⟨105411482181578079304738699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140548642908770772406318265 105411482181578079304738699)
  ·
    refine ⟨158117223272367118957108049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105411482181578079304738699 158117223272367118957108049)
    ·
      refine ⟨118587917454275339217831037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158117223272367118957108049 118587917454275339217831037)
      ·
        refine ⟨44470469045353252206686639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118587917454275339217831037 44470469045353252206686639)
        ·
          refine ⟨66705703568029878310029959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44470469045353252206686639 66705703568029878310029959)
          ·
            refine ⟨100058555352044817465044939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66705703568029878310029959 100058555352044817465044939)
            ·
              refine ⟨150087833028067226197567409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100058555352044817465044939 150087833028067226197567409)
              ·
                refine ⟨112565874771050419648175557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150087833028067226197567409 112565874771050419648175557)
                ·
                  refine ⟨21106101519571953684032917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112565874771050419648175557 21106101519571953684032917)
                  ·
                    refine ⟨989348508729935328939043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21106101519571953684032917 989348508729935328939043)
                    ·
                      rfl

theorem cell23_5780248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_5780248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780248 prefixEnd_5780248 := by exact prefixLift 5780248
  have htrace : WordTrace (prefixWord ++ tailWord_5780248) baseStart_5780248 baseEnd_5780248 := by
    simpa [prefixWord, tailWord_5780248, baseEnd_5780248] using wordTrace_append hprefix tailTrace_5780248
  have hstable : (prefixWord ++ tailWord_5780248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780248).length < 2 ^ (prefixWord ++ tailWord_5780248).sum := by decide
  have hdescent : baseEnd_5780248 < baseStart_5780248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780272 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 4, 2, 2]
def baseStart_5780272 : Nat := 118140960795 + 5780272 * 2 ^ 59
def prefixEnd_5780272 : Nat := 4983230072969 + 3 ^ 40 * 5780272 * 2
def baseEnd_5780272 : Nat := 2968057849725513892917019

theorem tailTrace_5780272 : CollatzResearch.WordTrace tailWord_5780272 prefixEnd_5780272 2968057849725513892917019 := by
  unfold tailWord_5780272
  simp only [CollatzResearch.WordTrace]
  refine ⟨105411919857534605354175535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140549226476712807138900713 105411919857534605354175535)
  ·
    refine ⟨158117879786301908031263303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105411919857534605354175535 158117879786301908031263303)
    ·
      refine ⟨237176819679452862046894955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158117879786301908031263303 237176819679452862046894955)
      ·
        refine ⟨355765229519179293070342433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237176819679452862046894955 355765229519179293070342433)
        ·
          refine ⟨266823922139384469802756825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355765229519179293070342433 266823922139384469802756825)
          ·
            refine ⟨200117941604538352352067619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266823922139384469802756825 200117941604538352352067619)
            ·
              refine ⟨300176912406807528528101429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200117941604538352352067619 300176912406807528528101429)
              ·
                refine ⟨28141585538138205799509509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 300176912406807528528101429 28141585538138205799509509)
                ·
                  refine ⟨5276547288400913587408033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28141585538138205799509509 5276547288400913587408033)
                  ·
                    refine ⟨3957410466300685190556025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5276547288400913587408033 3957410466300685190556025)
                    ·
                      refine ⟨2968057849725513892917019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957410466300685190556025 2968057849725513892917019)
                      ·
                        rfl

theorem cell23_5780272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4, 2, 2].length) (baseStart_5780272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780272 prefixEnd_5780272 := by exact prefixLift 5780272
  have htrace : WordTrace (prefixWord ++ tailWord_5780272) baseStart_5780272 baseEnd_5780272 := by
    simpa [prefixWord, tailWord_5780272, baseEnd_5780272] using wordTrace_append hprefix tailTrace_5780272
  have hstable : (prefixWord ++ tailWord_5780272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780272).length < 2 ^ (prefixWord ++ tailWord_5780272).sum := by decide
  have hdescent : baseEnd_5780272 < baseStart_5780272 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780275 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 3]
def baseStart_5780275 : Nat := 118140960795 + 5780275 * 2 ^ 59
def prefixEnd_5780275 : Nat := 4983230072969 + 3 ^ 40 * 5780275 * 2
def baseEnd_5780275 : Nat := 2968059390167477381179505

theorem tailTrace_5780275 : CollatzResearch.WordTrace tailWord_5780275 prefixEnd_5780275 2968059390167477381179505 := by
  unfold tailWord_5780275
  simp only [CollatzResearch.WordTrace]
  refine ⟨210823949134058342220710279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140549299422705561480473519 210823949134058342220710279)
  ·
    refine ⟨316235923701087513331065419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210823949134058342220710279 316235923701087513331065419)
    ·
      refine ⟨474353885551631269996598129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316235923701087513331065419 474353885551631269996598129)
      ·
        refine ⟨355765414163723452497448597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474353885551631269996598129 355765414163723452497448597)
        ·
          refine ⟨16676503788924536835817903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 355765414163723452497448597 16676503788924536835817903)
          ·
            refine ⟨25014755683386805253726855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16676503788924536835817903 25014755683386805253726855)
            ·
              refine ⟨37522133525080207880590283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25014755683386805253726855 37522133525080207880590283)
              ·
                refine ⟨56283200287620311820885425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37522133525080207880590283 56283200287620311820885425)
                ·
                  refine ⟨42212400215715233865664069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56283200287620311820885425 42212400215715233865664069)
                  ·
                    refine ⟨7914825040446606349812013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42212400215715233865664069 7914825040446606349812013)
                    ·
                      refine ⟨2968059390167477381179505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7914825040446606349812013 2968059390167477381179505)
                      ·
                        rfl

theorem cell23_5780275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_5780275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780275 prefixEnd_5780275 := by exact prefixLift 5780275
  have htrace : WordTrace (prefixWord ++ tailWord_5780275) baseStart_5780275 baseEnd_5780275 := by
    simpa [prefixWord, tailWord_5780275, baseEnd_5780275] using wordTrace_append hprefix tailTrace_5780275
  have hstable : (prefixWord ++ tailWord_5780275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780275).length < 2 ^ (prefixWord ++ tailWord_5780275).sum := by decide
  have hdescent : baseEnd_5780275 < baseStart_5780275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780325 : List Nat := [1, 3, 1, 3, 1, 1, 2, 4, 2, 5]
def baseStart_5780325 : Nat := 118140960795 + 5780325 * 2 ^ 59
def prefixEnd_5780325 : Nat := 4983230072969 + 3 ^ 40 * 5780325 * 2
def baseEnd_5780325 : Nat := 989361688066734061851425

theorem tailTrace_5780325 : CollatzResearch.WordTrace tailWord_5780325 prefixEnd_5780325 989361688066734061851425 := by
  unfold tailWord_5780325
  simp only [CollatzResearch.WordTrace]
  refine ⟨210825772783877200760030429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140550515189251467173353619 210825772783877200760030429)
  ·
    refine ⟨79059664793953950285011411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210825772783877200760030429 79059664793953950285011411)
    ·
      refine ⟨118589497190930925427517117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79059664793953950285011411 118589497190930925427517117)
      ·
        refine ⟨44471061446599097035318919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118589497190930925427517117 44471061446599097035318919)
        ·
          refine ⟨66706592169898645552978379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44471061446599097035318919 66706592169898645552978379)
          ·
            refine ⟨100059888254847968329467569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66706592169898645552978379 100059888254847968329467569)
            ·
              refine ⟨75044916191135976247100677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100059888254847968329467569 75044916191135976247100677)
              ·
                refine ⟨14070921785837995546331377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75044916191135976247100677 14070921785837995546331377)
                ·
                  refine ⟨10553191339378496659748533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14070921785837995546331377 10553191339378496659748533)
                  ·
                    refine ⟨989361688066734061851425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10553191339378496659748533 989361688066734061851425)
                    ·
                      rfl

theorem cell23_5780325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_5780325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780325 prefixEnd_5780325 := by exact prefixLift 5780325
  have htrace : WordTrace (prefixWord ++ tailWord_5780325) baseStart_5780325 baseEnd_5780325 := by
    simpa [prefixWord, tailWord_5780325, baseEnd_5780325] using wordTrace_append hprefix tailTrace_5780325
  have hstable : (prefixWord ++ tailWord_5780325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780325).length < 2 ^ (prefixWord ++ tailWord_5780325).sum := by decide
  have hdescent : baseEnd_5780325 < baseStart_5780325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780342 : List Nat := [5, 1, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_5780342 : Nat := 118140960795 + 5780342 * 2 ^ 59
def prefixEnd_5780342 : Nat := 4983230072969 + 3 ^ 40 * 5780342 * 2
def baseEnd_5780342 : Nat := 989364597790442873013899

theorem tailTrace_5780342 : CollatzResearch.WordTrace tailWord_5780342 prefixEnd_5780342 989364597790442873013899 := by
  unfold tailWord_5780342
  simp only [CollatzResearch.WordTrace]
  refine ⟨13176649551550975791462455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140550928549877075108932853 13176649551550975791462455)
  ·
    refine ⟨19764974327326463687193683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13176649551550975791462455 19764974327326463687193683)
    ·
      refine ⟨29647461490989695530790525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19764974327326463687193683 29647461490989695530790525)
      ·
        refine ⟨11117798059121135824046447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29647461490989695530790525 11117798059121135824046447)
        ·
          refine ⟨16676697088681703736069671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11117798059121135824046447 16676697088681703736069671)
          ·
            refine ⟨25015045633022555604104507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16676697088681703736069671 25015045633022555604104507)
            ·
              refine ⟨37522568449533833406156761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25015045633022555604104507 37522568449533833406156761)
              ·
                refine ⟨28141926337150375054617571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37522568449533833406156761 28141926337150375054617571)
                ·
                  refine ⟨42212889505725562581926357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28141926337150375054617571 42212889505725562581926357)
                  ·
                    refine ⟨989364597790442873013899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42212889505725562581926357 989364597790442873013899)
                    ·
                      rfl

theorem cell23_5780342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_5780342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780342 prefixEnd_5780342 := by exact prefixLift 5780342
  have htrace : WordTrace (prefixWord ++ tailWord_5780342) baseStart_5780342 baseEnd_5780342 := by
    simpa [prefixWord, tailWord_5780342, baseEnd_5780342] using wordTrace_append hprefix tailTrace_5780342
  have hstable : (prefixWord ++ tailWord_5780342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780342).length < 2 ^ (prefixWord ++ tailWord_5780342).sum := by decide
  have hdescent : baseEnd_5780342 < baseStart_5780342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780345 : List Nat := [1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 4]
def baseStart_5780345 : Nat := 118140960795 + 5780345 * 2 ^ 59
def prefixEnd_5780345 : Nat := 4983230072969 + 3 ^ 40 * 5780345 * 2
def baseEnd_5780345 : Nat := 2968095333813292107304183

theorem tailTrace_5780345 : CollatzResearch.WordTrace tailWord_5780345 prefixEnd_5780345 2968095333813292107304183 := by
  unfold tailWord_5780345
  simp only [CollatzResearch.WordTrace]
  refine ⟨210826502243804744175758489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140551001495869829450505659 210826502243804744175758489)
  ·
    refine ⟨158119876682853558131818867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210826502243804744175758489 158119876682853558131818867)
    ·
      refine ⟨237179815024280337197728301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158119876682853558131818867 237179815024280337197728301)
      ·
        refine ⟨88942430634105126449148113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237179815024280337197728301 88942430634105126449148113)
        ·
          refine ⟨66706822975578844836861085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88942430634105126449148113 66706822975578844836861085)
          ·
            refine ⟨25015058615842066813822907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66706822975578844836861085 25015058615842066813822907)
            ·
              refine ⟨37522587923763100220734361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25015058615842066813822907 37522587923763100220734361)
              ·
                refine ⟨28141940942822325165550771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37522587923763100220734361 28141940942822325165550771)
                ·
                  refine ⟨42212911414233487748326157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28141940942822325165550771 42212911414233487748326157)
                  ·
                    refine ⟨15829841780337557905622309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42212911414233487748326157 15829841780337557905622309)
                    ·
                      refine ⟨2968095333813292107304183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15829841780337557905622309 2968095333813292107304183)
                      ·
                        rfl

theorem cell23_5780345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 1, 2, 1, 3, 4].length) (baseStart_5780345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780345 prefixEnd_5780345 := by exact prefixLift 5780345
  have htrace : WordTrace (prefixWord ++ tailWord_5780345) baseStart_5780345 baseEnd_5780345 := by
    simpa [prefixWord, tailWord_5780345, baseEnd_5780345] using wordTrace_append hprefix tailTrace_5780345
  have hstable : (prefixWord ++ tailWord_5780345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780345).length < 2 ^ (prefixWord ++ tailWord_5780345).sum := by decide
  have hdescent : baseEnd_5780345 < baseStart_5780345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780362 : List Nat := [3, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4]
def baseStart_5780362 : Nat := 118140960795 + 5780362 * 2 ^ 59
def prefixEnd_5780362 : Nat := 4983230072969 + 3 ^ 40 * 5780362 * 2
def baseEnd_5780362 : Nat := 2968104062984418540791605

theorem tailTrace_5780362 : CollatzResearch.WordTrace tailWord_5780362 prefixEnd_5780362 2968104062984418540791605 := by
  unfold tailWord_5780362
  simp only [CollatzResearch.WordTrace]
  refine ⟨52706780571185789019781835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140551414856495437386084893 52706780571185789019781835)
  ·
    refine ⟨79060170856778683529672753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52706780571185789019781835 79060170856778683529672753)
    ·
      refine ⟨59295128142584012647254565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79060170856778683529672753 59295128142584012647254565)
      ·
        refine ⟨11117836526734502371360231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59295128142584012647254565 11117836526734502371360231)
        ·
          refine ⟨16676754790101753557040347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11117836526734502371360231 16676754790101753557040347)
          ·
            refine ⟨25015132185152630335560521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16676754790101753557040347 25015132185152630335560521)
            ·
              refine ⟨18761349138864472751670391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25015132185152630335560521 18761349138864472751670391)
              ·
                refine ⟨28142023708296709127505587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18761349138864472751670391 28142023708296709127505587)
                ·
                  refine ⟨42213035562445063691258381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28142023708296709127505587 42213035562445063691258381)
                  ·
                    refine ⟨15829888335916898884221893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42213035562445063691258381 15829888335916898884221893)
                    ·
                      refine ⟨2968104062984418540791605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15829888335916898884221893 2968104062984418540791605)
                      ·
                        rfl

theorem cell23_5780362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_5780362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780362 prefixEnd_5780362 := by exact prefixLift 5780362
  have htrace : WordTrace (prefixWord ++ tailWord_5780362) baseStart_5780362 baseEnd_5780362 := by
    simpa [prefixWord, tailWord_5780362, baseEnd_5780362] using wordTrace_append hprefix tailTrace_5780362
  have hstable : (prefixWord ++ tailWord_5780362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780362).length < 2 ^ (prefixWord ++ tailWord_5780362).sum := by decide
  have hdescent : baseEnd_5780362 < baseStart_5780362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780503 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 3, 2, 2]
def baseStart_5780503 : Nat := 118140960795 + 5780503 * 2 ^ 59
def prefixEnd_5780503 : Nat := 4983230072969 + 3 ^ 40 * 5780503 * 2
def baseEnd_5780503 : Nat := 2968176463756702489128457

theorem tailTrace_5780503 : CollatzResearch.WordTrace tailWord_5780503 prefixEnd_5780503 2968176463756702489128457 := by
  unfold tailWord_5780503
  simp only [CollatzResearch.WordTrace]
  refine ⟨210832264977232337160010163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140554843318154891440006775 210832264977232337160010163)
  ·
    refine ⟨316248397465848505740015245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210832264977232337160010163 316248397465848505740015245)
    ·
      refine ⟨118593149049693189652505717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316248397465848505740015245 118593149049693189652505717)
      ·
        refine ⟨11118107723408736529922411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118593149049693189652505717 11118107723408736529922411)
        ·
          refine ⟨16677161585113104794883617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118107723408736529922411 16677161585113104794883617)
          ·
            refine ⟨12507871188834828596162713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16677161585113104794883617 12507871188834828596162713)
            ·
              refine ⟨9380903391626121447122035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12507871188834828596162713 9380903391626121447122035)
              ·
                refine ⟨14071355087439182170683053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9380903391626121447122035 14071355087439182170683053)
                ·
                  refine ⟨5276758157789693314006145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14071355087439182170683053 5276758157789693314006145)
                  ·
                    refine ⟨3957568618342269985504609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5276758157789693314006145 3957568618342269985504609)
                    ·
                      refine ⟨2968176463756702489128457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957568618342269985504609 2968176463756702489128457)
                      ·
                        rfl

theorem cell23_5780503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_5780503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780503 prefixEnd_5780503 := by exact prefixLift 5780503
  have htrace : WordTrace (prefixWord ++ tailWord_5780503) baseStart_5780503 baseEnd_5780503 := by
    simpa [prefixWord, tailWord_5780503, baseEnd_5780503] using wordTrace_append hprefix tailTrace_5780503
  have hstable : (prefixWord ++ tailWord_5780503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780503).length < 2 ^ (prefixWord ++ tailWord_5780503).sum := by decide
  have hdescent : baseEnd_5780503 < baseStart_5780503 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780505 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 1, 9]
def baseStart_5780505 : Nat := 118140960795 + 5780505 * 2 ^ 59
def prefixEnd_5780505 : Nat := 4983230072969 + 3 ^ 40 * 5780505 * 2
def baseEnd_5780505 : Nat := 989392496906003827101149

theorem tailTrace_5780505 : CollatzResearch.WordTrace tailWord_5780505 prefixEnd_5780505 989392496906003827101149 := by
  unfold tailWord_5780505
  simp only [CollatzResearch.WordTrace]
  refine ⟨210832337923225091501582969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140554891948816727667721979 210832337923225091501582969)
  ·
    refine ⟨158124253442418818626187227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210832337923225091501582969 158124253442418818626187227)
    ·
      refine ⟨237186380163628227939280841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158124253442418818626187227 237186380163628227939280841)
      ·
        refine ⟨177889785122721170954460631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237186380163628227939280841 177889785122721170954460631)
        ·
          refine ⟨266834677684081756431690947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177889785122721170954460631 266834677684081756431690947)
          ·
            refine ⟨400252016526122634647536421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266834677684081756431690947 400252016526122634647536421)
            ·
              refine ⟨75047253098647993996413079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 400252016526122634647536421 75047253098647993996413079)
              ·
                refine ⟨112570879647971990994619619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75047253098647993996413079 112570879647971990994619619)
                ·
                  refine ⟨168856319471957986491929429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112570879647971990994619619 168856319471957986491929429)
                  ·
                    refine ⟨989392496906003827101149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 168856319471957986491929429 989392496906003827101149)
                    ·
                      rfl

theorem cell23_5780505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 1, 9].length) (baseStart_5780505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780505 prefixEnd_5780505 := by exact prefixLift 5780505
  have htrace : WordTrace (prefixWord ++ tailWord_5780505) baseStart_5780505 baseEnd_5780505 := by
    simpa [prefixWord, tailWord_5780505, baseEnd_5780505] using wordTrace_append hprefix tailTrace_5780505
  have hstable : (prefixWord ++ tailWord_5780505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780505).length < 2 ^ (prefixWord ++ tailWord_5780505).sum := by decide
  have hdescent : baseEnd_5780505 < baseStart_5780505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780516 : List Nat := [2, 3, 1, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_5780516 : Nat := 118140960795 + 5780516 * 2 ^ 59
def prefixEnd_5780516 : Nat := 4983230072969 + 3 ^ 40 * 5780516 * 2
def baseEnd_5780516 : Nat := 2968183139005210938265897

theorem tailTrace_5780516 : CollatzResearch.WordTrace tailWord_5780516 prefixEnd_5780516 2968183139005210938265897 := by
  unfold tailWord_5780516
  simp only [CollatzResearch.WordTrace]
  refine ⟨105416369563092620190116701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140555159417456826920155601 105416369563092620190116701)
  ·
    refine ⟨39531138586159732571293763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105416369563092620190116701 39531138586159732571293763)
    ·
      refine ⟨59296707879239598856940645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39531138586159732571293763 59296707879239598856940645)
      ·
        refine ⟨11118132727357424785676371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59296707879239598856940645 11118132727357424785676371)
        ·
          refine ⟨16677199091036137178514557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118132727357424785676371 16677199091036137178514557)
          ·
            refine ⟨6253949659138551441942959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16677199091036137178514557 6253949659138551441942959)
            ·
              refine ⟨9380924488707827162914439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6253949659138551441942959 9380924488707827162914439)
              ·
                refine ⟨14071386733061740744371659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9380924488707827162914439 14071386733061740744371659)
                ·
                  refine ⟨21107080099592611116557489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14071386733061740744371659 21107080099592611116557489)
                  ·
                    refine ⟨15830310074694458337418117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21107080099592611116557489 15830310074694458337418117)
                    ·
                      refine ⟨2968183139005210938265897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15830310074694458337418117 2968183139005210938265897)
                      ·
                        rfl

theorem cell23_5780516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_5780516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780516 prefixEnd_5780516 := by exact prefixLift 5780516
  have htrace : WordTrace (prefixWord ++ tailWord_5780516) baseStart_5780516 baseEnd_5780516 := by
    simpa [prefixWord, tailWord_5780516, baseEnd_5780516] using wordTrace_append hprefix tailTrace_5780516
  have hstable : (prefixWord ++ tailWord_5780516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780516).length < 2 ^ (prefixWord ++ tailWord_5780516).sum := by decide
  have hdescent : baseEnd_5780516 < baseStart_5780516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780597 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5780597 : Nat := 118140960795 + 5780597 * 2 ^ 59
def prefixEnd_5780597 : Nat := 4983230072969 + 3 ^ 40 * 5780597 * 2
def baseEnd_5780597 : Nat := 2968224730938225121353025

theorem tailTrace_5780597 : CollatzResearch.WordTrace tailWord_5780597 prefixEnd_5780597 2968224730938225121353025 := by
  unfold tailWord_5780597
  simp only [CollatzResearch.WordTrace]
  refine ⟨210835693438891791213932045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140557128959261194142621363 210835693438891791213932045)
  ·
    refine ⟨79063385039584421705224517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210835693438891791213932045 79063385039584421705224517)
    ·
      refine ⟨14824384694922079069729597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79063385039584421705224517 14824384694922079069729597)
      ·
        refine ⟨5559144260595779651148599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14824384694922079069729597 5559144260595779651148599)
        ·
          refine ⟨8338716390893669476722899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5559144260595779651148599 8338716390893669476722899)
          ·
            refine ⟨12508074586340504215084349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8338716390893669476722899 12508074586340504215084349)
            ·
              refine ⟨4690527969877689080656631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12508074586340504215084349 4690527969877689080656631)
              ·
                refine ⟨7035791954816533620984947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4690527969877689080656631 7035791954816533620984947)
                ·
                  refine ⟨10553687932224800431477421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7035791954816533620984947 10553687932224800431477421)
                  ·
                    refine ⟨3957632974584300161804033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10553687932224800431477421 3957632974584300161804033)
                    ·
                      refine ⟨2968224730938225121353025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957632974584300161804033 2968224730938225121353025)
                      ·
                        rfl

theorem cell23_5780597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5780597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780597 prefixEnd_5780597 := by exact prefixLift 5780597
  have htrace : WordTrace (prefixWord ++ tailWord_5780597) baseStart_5780597 baseEnd_5780597 := by
    simpa [prefixWord, tailWord_5780597, baseEnd_5780597] using wordTrace_append hprefix tailTrace_5780597
  have hstable : (prefixWord ++ tailWord_5780597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780597).length < 2 ^ (prefixWord ++ tailWord_5780597).sum := by decide
  have hdescent : baseEnd_5780597 < baseStart_5780597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780599 : List Nat := [1, 1, 3, 1, 1, 4, 2, 5, 5]
def baseStart_5780599 : Nat := 118140960795 + 5780599 * 2 ^ 59
def prefixEnd_5780599 : Nat := 4983230072969 + 3 ^ 40 * 5780599 * 2
def baseEnd_5780599 : Nat := 329802861988837123725335

theorem tailTrace_5780599 : CollatzResearch.WordTrace tailWord_5780599 prefixEnd_5780599 329802861988837123725335 := by
  unfold tailWord_5780599
  simp only [CollatzResearch.WordTrace]
  refine ⟨210835766384884545555504851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140557177589923030370336567 210835766384884545555504851)
  ·
    refine ⟨316253649577326818333257277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210835766384884545555504851 316253649577326818333257277)
    ·
      refine ⟨118595118591497556874971479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316253649577326818333257277 118595118591497556874971479)
      ·
        refine ⟨177892677887246335312457219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118595118591497556874971479 177892677887246335312457219)
        ·
          refine ⟨266839016830869502968685829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177892677887246335312457219 266839016830869502968685829)
          ·
            refine ⟨50032315655788031806628593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266839016830869502968685829 50032315655788031806628593)
            ·
              refine ⟨37524236741841023854971445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50032315655788031806628593 37524236741841023854971445)
              ·
                refine ⟨3517897194547595986403573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37524236741841023854971445 3517897194547595986403573)
                ·
                  refine ⟨329802861988837123725335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3517897194547595986403573 329802861988837123725335)
                  ·
                    rfl

theorem cell23_5780599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 5].length) (baseStart_5780599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780599 prefixEnd_5780599 := by exact prefixLift 5780599
  have htrace : WordTrace (prefixWord ++ tailWord_5780599) baseStart_5780599 baseEnd_5780599 := by
    simpa [prefixWord, tailWord_5780599, baseEnd_5780599] using wordTrace_append hprefix tailTrace_5780599
  have hstable : (prefixWord ++ tailWord_5780599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780599).length < 2 ^ (prefixWord ++ tailWord_5780599).sum := by decide
  have hdescent : baseEnd_5780599 < baseStart_5780599 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780626 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_5780626 : Nat := 118140960795 + 5780626 * 2 ^ 59
def prefixEnd_5780626 : Nat := 4983230072969 + 3 ^ 40 * 5780626 * 2
def baseEnd_5780626 : Nat := 2968239621877205507890391

theorem tailTrace_5780626 : CollatzResearch.WordTrace tailWord_5780626 prefixEnd_5780626 2968239621877205507890391 := by
  unfold tailWord_5780626
  simp only [CollatzResearch.WordTrace]
  refine ⟨52709187788946682291684433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140557834103857819444491821 52709187788946682291684433)
  ·
    refine ⟨39531890841710011718763325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52709187788946682291684433 39531890841710011718763325)
    ·
      refine ⟨14824459065641254394536247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39531890841710011718763325 14824459065641254394536247)
      ·
        refine ⟨22236688598461881591804371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14824459065641254394536247 22236688598461881591804371)
        ·
          refine ⟨33355032897692822387706557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22236688598461881591804371 33355032897692822387706557)
          ·
            refine ⟨12508137336634808395389959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33355032897692822387706557 12508137336634808395389959)
            ·
              refine ⟨18762206004952212593084939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12508137336634808395389959 18762206004952212593084939)
              ·
                refine ⟨28143309007428318889627409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18762206004952212593084939 28143309007428318889627409)
                ·
                  refine ⟨21107481755571239167220557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28143309007428318889627409 21107481755571239167220557)
                  ·
                    refine ⟨7915305658339214687707709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21107481755571239167220557 7915305658339214687707709)
                    ·
                      refine ⟨2968239621877205507890391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7915305658339214687707709 2968239621877205507890391)
                      ·
                        rfl

theorem cell23_5780626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_5780626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780626 prefixEnd_5780626 := by exact prefixLift 5780626
  have htrace : WordTrace (prefixWord ++ tailWord_5780626) baseStart_5780626 baseEnd_5780626 := by
    simpa [prefixWord, tailWord_5780626, baseEnd_5780626] using wordTrace_append hprefix tailTrace_5780626
  have hstable : (prefixWord ++ tailWord_5780626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780626).length < 2 ^ (prefixWord ++ tailWord_5780626).sum := by decide
  have hdescent : baseEnd_5780626 < baseStart_5780626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780652 : List Nat := [2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_5780652 : Nat := 118140960795 + 5780652 * 2 ^ 59
def prefixEnd_5780652 : Nat := 4983230072969 + 3 ^ 40 * 5780652 * 2
def baseEnd_5780652 : Nat := 2968252972374222406165271

theorem tailTrace_5780652 : CollatzResearch.WordTrace tailWord_5780652 prefixEnd_5780652 2968252972374222406165271 := by
  unfold tailWord_5780652
  simp only [CollatzResearch.WordTrace]
  refine ⟨105418849726846267803592105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140558466302461690404789473 105418849726846267803592105)
  ·
    refine ⟨79064137295134700852694079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105418849726846267803592105 79064137295134700852694079)
    ·
      refine ⟨118596205942702051279041119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79064137295134700852694079 118596205942702051279041119)
      ·
        refine ⟨177894308914053076918561679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118596205942702051279041119 177894308914053076918561679)
        ·
          refine ⟨266841463371079615377842519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177894308914053076918561679 266841463371079615377842519)
          ·
            refine ⟨400262195056619423066763779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266841463371079615377842519 400262195056619423066763779)
            ·
              refine ⟨600393292584929134600145669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400262195056619423066763779 600393292584929134600145669)
              ·
                refine ⟨112573742359674212737527313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600393292584929134600145669 112573742359674212737527313)
                ·
                  refine ⟨84430306769755659553145485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112573742359674212737527313 84430306769755659553145485)
                  ·
                    refine ⟨31661365038658372332429557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84430306769755659553145485 31661365038658372332429557)
                    ·
                      refine ⟨2968252972374222406165271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31661365038658372332429557 2968252972374222406165271)
                      ·
                        rfl

theorem cell23_5780652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_5780652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780652 prefixEnd_5780652 := by exact prefixLift 5780652
  have htrace : WordTrace (prefixWord ++ tailWord_5780652) baseStart_5780652 baseEnd_5780652 := by
    simpa [prefixWord, tailWord_5780652, baseEnd_5780652] using wordTrace_append hprefix tailTrace_5780652
  have hstable : (prefixWord ++ tailWord_5780652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780652).length < 2 ^ (prefixWord ++ tailWord_5780652).sum := by decide
  have hdescent : baseEnd_5780652 < baseStart_5780652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780770 : List Nat := [3, 3, 1, 1, 4, 1, 3, 1, 1, 5]
def baseStart_5780770 : Nat := 118140960795 + 5780770 * 2 ^ 59
def prefixEnd_5780770 : Nat := 4983230072969 + 3 ^ 40 * 5780770 * 2
def baseEnd_5780770 : Nat := 989437854363817648163243

theorem tailTrace_5780770 : CollatzResearch.WordTrace tailWord_5780770 prefixEnd_5780770 989437854363817648163243 := by
  unfold tailWord_5780770
  simp only [CollatzResearch.WordTrace]
  refine ⟨52710500816816260439994941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140561335511510027839986509 52710500816816260439994941)
  ·
    refine ⟨19766437806306097664998103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52710500816816260439994941 19766437806306097664998103)
    ·
      refine ⟨29649656709459146497497155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19766437806306097664998103 29649656709459146497497155)
      ·
        refine ⟨44474485064188719746245733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29649656709459146497497155 44474485064188719746245733)
        ·
          refine ⟨8338965949535384952421075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44474485064188719746245733 8338965949535384952421075)
          ·
            refine ⟨12508448924303077428631613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8338965949535384952421075 12508448924303077428631613)
            ·
              refine ⟨4690668346613654035736855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12508448924303077428631613 4690668346613654035736855)
              ·
                refine ⟨7036002519920481053605283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4690668346613654035736855 7036002519920481053605283)
                ·
                  refine ⟨10554003779880721580407925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7036002519920481053605283 10554003779880721580407925)
                  ·
                    refine ⟨989437854363817648163243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10554003779880721580407925 989437854363817648163243)
                    ·
                      rfl

theorem cell23_5780770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_5780770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780770 prefixEnd_5780770 := by exact prefixLift 5780770
  have htrace : WordTrace (prefixWord ++ tailWord_5780770) baseStart_5780770 baseEnd_5780770 := by
    simpa [prefixWord, tailWord_5780770, baseEnd_5780770] using wordTrace_append hprefix tailTrace_5780770
  have hstable : (prefixWord ++ tailWord_5780770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780770).length < 2 ^ (prefixWord ++ tailWord_5780770).sum := by decide
  have hdescent : baseEnd_5780770 < baseStart_5780770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780796 : List Nat := [2, 2, 2, 2, 1, 5, 1, 8]
def baseStart_5780796 : Nat := 118140960795 + 5780796 * 2 ^ 59
def prefixEnd_5780796 : Nat := 4983230072969 + 3 ^ 40 * 5780796 * 2
def baseEnd_5780796 : Nat := 109938033836609994176467

theorem tailTrace_5780796 : CollatzResearch.WordTrace tailWord_5780796 prefixEnd_5780796 109938033836609994176467 := by
  unfold tailWord_5780796
  simp only [CollatzResearch.WordTrace]
  refine ⟨105421475782585424100213121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140561967710113898800284161 105421475782585424100213121)
  ·
    refine ⟨79066106836939068075159841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105421475782585424100213121 79066106836939068075159841)
    ·
      refine ⟨59299580127704301056369881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79066106836939068075159841 59299580127704301056369881)
      ·
        refine ⟨44474685095778225792277411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59299580127704301056369881 44474685095778225792277411)
        ·
          refine ⟨66712027643667338688416117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44474685095778225792277411 66712027643667338688416117)
          ·
            refine ⟨6254252591593813002039011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66712027643667338688416117 6254252591593813002039011)
            ·
              refine ⟨9381378887390719503058517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6254252591593813002039011 9381378887390719503058517)
              ·
                refine ⟨109938033836609994176467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9381378887390719503058517 109938033836609994176467)
                ·
                  rfl

theorem cell23_5780796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 5, 1, 8].length) (baseStart_5780796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780796 prefixEnd_5780796 := by exact prefixLift 5780796
  have htrace : WordTrace (prefixWord ++ tailWord_5780796) baseStart_5780796 baseEnd_5780796 := by
    simpa [prefixWord, tailWord_5780796, baseEnd_5780796] using wordTrace_append hprefix tailTrace_5780796
  have hstable : (prefixWord ++ tailWord_5780796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780796).length < 2 ^ (prefixWord ++ tailWord_5780796).sum := by decide
  have hdescent : baseEnd_5780796 < baseStart_5780796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780819 : List Nat := [1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 5]
def baseStart_5780819 : Nat := 118140960795 + 5780819 * 2 ^ 59
def prefixEnd_5780819 : Nat := 4983230072969 + 3 ^ 40 * 5780819 * 2
def baseEnd_5780819 : Nat := 2968338723643523252777003

theorem tailTrace_5780819 : CollatzResearch.WordTrace tailWord_5780819 prefixEnd_5780819 2968338723643523252777003 := by
  unfold tailWord_5780819
  simp only [CollatzResearch.WordTrace]
  refine ⟨210843790444087523128513511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140562526962725015419009007 210843790444087523128513511)
  ·
    refine ⟨316265685666131284692770267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210843790444087523128513511 316265685666131284692770267)
    ·
      refine ⟨474398528499196927039155401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316265685666131284692770267 474398528499196927039155401)
      ·
        refine ⟨355798896374397695279366551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474398528499196927039155401 355798896374397695279366551)
        ·
          refine ⟨533698344561596542919049827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355798896374397695279366551 533698344561596542919049827)
          ·
            refine ⟨800547516842394814378574741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533698344561596542919049827 800547516842394814378574741)
            ·
              refine ⟨37525664851987256923995691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 800547516842394814378574741 37525664851987256923995691)
              ·
                refine ⟨56288497277980885385993537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37525664851987256923995691 56288497277980885385993537)
                ·
                  refine ⟨42216372958485664039495153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56288497277980885385993537 42216372958485664039495153)
                  ·
                    refine ⟨31662279718864248029621365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42216372958485664039495153 31662279718864248029621365)
                    ·
                      refine ⟨2968338723643523252777003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31662279718864248029621365 2968338723643523252777003)
                      ·
                        rfl

theorem cell23_5780819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_5780819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780819 prefixEnd_5780819 := by exact prefixLift 5780819
  have htrace : WordTrace (prefixWord ++ tailWord_5780819) baseStart_5780819 baseEnd_5780819 := by
    simpa [prefixWord, tailWord_5780819, baseEnd_5780819] using wordTrace_append hprefix tailTrace_5780819
  have hstable : (prefixWord ++ tailWord_5780819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780819).length < 2 ^ (prefixWord ++ tailWord_5780819).sum := by decide
  have hdescent : baseEnd_5780819 < baseStart_5780819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780840 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 4, 1, 3]
def baseStart_5780840 : Nat := 118140960795 + 5780840 * 2 ^ 59
def prefixEnd_5780840 : Nat := 4983230072969 + 3 ^ 40 * 5780840 * 2
def baseEnd_5780840 : Nat := 2968349506737267670614407

theorem tailTrace_5780840 : CollatzResearch.WordTrace tailWord_5780840 prefixEnd_5780840 2968349506737267670614407 := by
  unfold tailWord_5780840
  simp only [CollatzResearch.WordTrace]
  refine ⟨105422278188505721857513987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140563037584674295810018649 105422278188505721857513987)
  ·
    refine ⟨158133417282758582786270981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105422278188505721857513987 158133417282758582786270981)
    ·
      refine ⟨29650015740517234272425809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158133417282758582786270981 29650015740517234272425809)
      ·
        refine ⟨22237511805387925704319357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29650015740517234272425809 22237511805387925704319357)
        ·
          refine ⟨8339066927020472139119759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22237511805387925704319357 8339066927020472139119759)
          ·
            refine ⟨12508600390530708208679639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8339066927020472139119759 12508600390530708208679639)
            ·
              refine ⟨18762900585796062313019459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12508600390530708208679639 18762900585796062313019459)
              ·
                refine ⟨28144350878694093469529189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18762900585796062313019459 28144350878694093469529189)
                ·
                  refine ⟨5277065789755142525536723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28144350878694093469529189 5277065789755142525536723)
                  ·
                    refine ⟨7915598684632713788305085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5277065789755142525536723 7915598684632713788305085)
                    ·
                      refine ⟨2968349506737267670614407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7915598684632713788305085 2968349506737267670614407)
                      ·
                        rfl

theorem cell23_5780840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_5780840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780840 prefixEnd_5780840 := by exact prefixLift 5780840
  have htrace : WordTrace (prefixWord ++ tailWord_5780840) baseStart_5780840 baseEnd_5780840 := by
    simpa [prefixWord, tailWord_5780840, baseEnd_5780840] using wordTrace_append hprefix tailTrace_5780840
  have hstable : (prefixWord ++ tailWord_5780840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780840).length < 2 ^ (prefixWord ++ tailWord_5780840).sum := by decide
  have hdescent : baseEnd_5780840 < baseStart_5780840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780863 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 8, 2, 2]
def baseStart_5780863 : Nat := 118140960795 + 5780863 * 2 ^ 59
def prefixEnd_5780863 : Nat := 4983230072969 + 3 ^ 40 * 5780863 * 2
def baseEnd_5780863 : Nat := 2968361316792321080626801

theorem tailTrace_5780863 : CollatzResearch.WordTrace tailWord_5780863 prefixEnd_5780863 2968361316792321080626801 := by
  unfold tailWord_5780863
  simp only [CollatzResearch.WordTrace]
  refine ⟨210845395255928118643115243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140563596837285412428743495 210845395255928118643115243)
  ·
    refine ⟨316268092883892177964672865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210845395255928118643115243 316268092883892177964672865)
    ·
      refine ⟨237201069662919133473504649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316268092883892177964672865 237201069662919133473504649)
      ·
        refine ⟨177900802247189350105128487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237201069662919133473504649 177900802247189350105128487)
        ·
          refine ⟨266851203370784025157692731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177900802247189350105128487 266851203370784025157692731)
          ·
            refine ⟨400276805056176037736539097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266851203370784025157692731 400276805056176037736539097)
            ·
              refine ⟨300207603792132028302404323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400276805056176037736539097 300207603792132028302404323)
              ·
                refine ⟨450311405688198042453606485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300207603792132028302404323 450311405688198042453606485)
                ·
                  refine ⟨5277086785408570810003201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 450311405688198042453606485 5277086785408570810003201)
                  ·
                    refine ⟨3957815089056428107502401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5277086785408570810003201 3957815089056428107502401)
                    ·
                      refine ⟨2968361316792321080626801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957815089056428107502401 2968361316792321080626801)
                      ·
                        rfl

theorem cell23_5780863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_5780863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780863 prefixEnd_5780863 := by exact prefixLift 5780863
  have htrace : WordTrace (prefixWord ++ tailWord_5780863) baseStart_5780863 baseEnd_5780863 := by
    simpa [prefixWord, tailWord_5780863, baseEnd_5780863] using wordTrace_append hprefix tailTrace_5780863
  have hstable : (prefixWord ++ tailWord_5780863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780863).length < 2 ^ (prefixWord ++ tailWord_5780863).sum := by decide
  have hdescent : baseEnd_5780863 < baseStart_5780863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780926 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_5780926 : Nat := 118140960795 + 5780926 * 2 ^ 59
def prefixEnd_5780926 : Nat := 4983230072969 + 3 ^ 40 * 5780926 * 2
def baseEnd_5780926 : Nat := 2968393666073554334139011

theorem tailTrace_5780926 : CollatzResearch.WordTrace tailWord_5780926 prefixEnd_5780926 2968393666073554334139011 := by
  unfold tailWord_5780926
  simp only [CollatzResearch.WordTrace]
  refine ⟨26355961631837485050332329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140565128703133253601772421 26355961631837485050332329)
  ·
    refine ⟨19766971223878113787749247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26355961631837485050332329 19766971223878113787749247)
    ·
      refine ⟨29650456835817170681623871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19766971223878113787749247 29650456835817170681623871)
      ·
        refine ⟨44475685253725756022435807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29650456835817170681623871 44475685253725756022435807)
        ·
          refine ⟨66713527880588634033653711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44475685253725756022435807 66713527880588634033653711)
          ·
            refine ⟨100070291820882951050480567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66713527880588634033653711 100070291820882951050480567)
            ·
              refine ⟨150105437731324426575720851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100070291820882951050480567 150105437731324426575720851)
              ·
                refine ⟨225158156596986639863581277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150105437731324426575720851 225158156596986639863581277)
                ·
                  refine ⟨84434308723869989948842979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 225158156596986639863581277 84434308723869989948842979)
                  ·
                    refine ⟨126651463085804984923264469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 84434308723869989948842979 126651463085804984923264469)
                    ·
                      refine ⟨2968393666073554334139011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 126651463085804984923264469 2968393666073554334139011)
                      ·
                        rfl

theorem cell23_5780926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_5780926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780926 prefixEnd_5780926 := by exact prefixLift 5780926
  have htrace : WordTrace (prefixWord ++ tailWord_5780926) baseStart_5780926 baseEnd_5780926 := by
    simpa [prefixWord, tailWord_5780926, baseEnd_5780926] using wordTrace_append hprefix tailTrace_5780926
  have hstable : (prefixWord ++ tailWord_5780926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780926).length < 2 ^ (prefixWord ++ tailWord_5780926).sum := by decide
  have hdescent : baseEnd_5780926 < baseStart_5780926 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780950 : List Nat := [5, 2, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5780950 : Nat := 118140960795 + 5780950 * 2 ^ 59
def prefixEnd_5780950 : Nat := 4983230072969 + 3 ^ 40 * 5780950 * 2
def baseEnd_5780950 : Nat := 989468663203087413412967

theorem tailTrace_5780950 : CollatzResearch.WordTrace tailWord_5780950 prefixEnd_5780950 989468663203087413412967 := by
  unfold tailWord_5780950
  simp only [CollatzResearch.WordTrace]
  refine ⟨13178035525413308281345769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140565712271075288334354869 13178035525413308281345769)
  ·
    refine ⟨9883526644059981211009327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13178035525413308281345769 9883526644059981211009327)
    ·
      refine ⟨14825289966089971816513991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9883526644059981211009327 14825289966089971816513991)
      ·
        refine ⟨22237934949134957724770987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14825289966089971816513991 22237934949134957724770987)
        ·
          refine ⟨33356902423702436587156481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22237934949134957724770987 33356902423702436587156481)
          ·
            refine ⟨25017676817776827440367361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33356902423702436587156481 25017676817776827440367361)
            ·
              refine ⟨18763257613332620580275521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25017676817776827440367361 18763257613332620580275521)
              ·
                refine ⟨14072443209999465435206641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18763257613332620580275521 14072443209999465435206641)
                ·
                  refine ⟨10554332407499599076404981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14072443209999465435206641 10554332407499599076404981)
                  ·
                    refine ⟨989468663203087413412967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10554332407499599076404981 989468663203087413412967)
                    ·
                      rfl

theorem cell23_5780950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5780950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780950 prefixEnd_5780950 := by exact prefixLift 5780950
  have htrace : WordTrace (prefixWord ++ tailWord_5780950) baseStart_5780950 baseEnd_5780950 := by
    simpa [prefixWord, tailWord_5780950, baseEnd_5780950] using wordTrace_append hprefix tailTrace_5780950
  have hstable : (prefixWord ++ tailWord_5780950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780950).length < 2 ^ (prefixWord ++ tailWord_5780950).sum := by decide
  have hdescent : baseEnd_5780950 < baseStart_5780950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5780953 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 4]
def baseStart_5780953 : Nat := 118140960795 + 5780953 * 2 ^ 59
def prefixEnd_5780953 : Nat := 4983230072969 + 3 ^ 40 * 5780953 * 2
def baseEnd_5780953 : Nat := 2968407530051225728501387

theorem tailTrace_5780953 : CollatzResearch.WordTrace tailWord_5780953 prefixEnd_5780953 2968407530051225728501387 := by
  unfold tailWord_5780953
  simp only [CollatzResearch.WordTrace]
  refine ⟨210848677825602064013891513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140565785217068042675927675 210848677825602064013891513)
  ·
    refine ⟨158136508369201548010418635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210848677825602064013891513 158136508369201548010418635)
    ·
      refine ⟨237204762553802322015627953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158136508369201548010418635 237204762553802322015627953)
      ·
        refine ⟨177903571915351741511720965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237204762553802322015627953 177903571915351741511720965)
        ·
          refine ⟨33356919734128451533447681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177903571915351741511720965 33356919734128451533447681)
          ·
            refine ⟨25017689800596338650085761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33356919734128451533447681 25017689800596338650085761)
            ·
              refine ⟨18763267350447253987564321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25017689800596338650085761 18763267350447253987564321)
              ·
                refine ⟨14072450512835440490673241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18763267350447253987564321 14072450512835440490673241)
                ·
                  refine ⟨10554337884626580368004931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14072450512835440490673241 10554337884626580368004931)
                  ·
                    refine ⟨15831506826939870552007397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10554337884626580368004931 15831506826939870552007397)
                    ·
                      refine ⟨2968407530051225728501387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15831506826939870552007397 2968407530051225728501387)
                      ·
                        rfl

theorem cell23_5780953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_5780953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5780953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5780953 prefixEnd_5780953 := by exact prefixLift 5780953
  have htrace : WordTrace (prefixWord ++ tailWord_5780953) baseStart_5780953 baseEnd_5780953 := by
    simpa [prefixWord, tailWord_5780953, baseEnd_5780953] using wordTrace_append hprefix tailTrace_5780953
  have hstable : (prefixWord ++ tailWord_5780953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5780953).length < 2 ^ (prefixWord ++ tailWord_5780953).sum := by decide
  have hdescent : baseEnd_5780953 < baseStart_5780953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5780953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781070 : List Nat := [4, 1, 1, 1, 1, 2, 1, 6, 2, 4]
def baseStart_5781070 : Nat := 118140960795 + 5781070 * 2 ^ 59
def prefixEnd_5781070 : Nat := 4983230072969 + 3 ^ 40 * 5781070 * 2
def baseEnd_5781070 : Nat := 989489202429267256912783

theorem tailTrace_5781070 : CollatzResearch.WordTrace tailWord_5781070 prefixEnd_5781070 989489202429267256912783 := by
  unfold tailWord_5781070
  simp only [CollatzResearch.WordTrace]
  refine ⟨26356618145772274124487583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140568630110785461997267109 26356618145772274124487583)
  ·
    refine ⟨39534927218658411186731375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26356618145772274124487583 39534927218658411186731375)
    ·
      refine ⟨59302390827987616780097063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39534927218658411186731375 59302390827987616780097063)
      ·
        refine ⟨88953586241981425170145595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59302390827987616780097063 88953586241981425170145595)
        ·
          refine ⟨133430379362972137755218393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88953586241981425170145595 133430379362972137755218393)
          ·
            refine ⟨100072784522229103316413795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133430379362972137755218393 100072784522229103316413795)
            ·
              refine ⟨150109176783343654974620693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100072784522229103316413795 150109176783343654974620693)
              ·
                refine ⟨7036367661719233826935345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150109176783343654974620693 7036367661719233826935345)
                ·
                  refine ⟨5277275746289425370201509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7036367661719233826935345 5277275746289425370201509)
                  ·
                    refine ⟨989489202429267256912783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5277275746289425370201509 989489202429267256912783)
                    ·
                      rfl

theorem cell23_5781070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_5781070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781070 prefixEnd_5781070 := by exact prefixLift 5781070
  have htrace : WordTrace (prefixWord ++ tailWord_5781070) baseStart_5781070 baseEnd_5781070 := by
    simpa [prefixWord, tailWord_5781070, baseEnd_5781070] using wordTrace_append hprefix tailTrace_5781070
  have hstable : (prefixWord ++ tailWord_5781070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781070).length < 2 ^ (prefixWord ++ tailWord_5781070).sum := by decide
  have hdescent : baseEnd_5781070 < baseStart_5781070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781078 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 6]
def baseStart_5781078 : Nat := 118140960795 + 5781078 * 2 ^ 59
def prefixEnd_5781078 : Nat := 4983230072969 + 3 ^ 40 * 5781078 * 2
def baseEnd_5781078 : Nat := 329830190570337526604257

theorem tailTrace_5781078 : CollatzResearch.WordTrace tailWord_5781078 prefixEnd_5781078 329830190570337526604257 := by
  unfold tailWord_5781078
  simp only [CollatzResearch.WordTrace]
  refine ⟨13178327309384325647636993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140568824633432806908127925 13178327309384325647636993)
  ·
    refine ⟨9883745482038244235727745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13178327309384325647636993 9883745482038244235727745)
    ·
      refine ⟨7412809111528683176795809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9883745482038244235727745 7412809111528683176795809)
      ·
        refine ⟨5559606833646512382596857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7412809111528683176795809 5559606833646512382596857)
        ·
          refine ⟨4169705125234884286947643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5559606833646512382596857 4169705125234884286947643)
          ·
            refine ⟨6254557687852326430421465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169705125234884286947643 6254557687852326430421465)
            ·
              refine ⟨4690918265889244822816099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6254557687852326430421465 4690918265889244822816099)
              ·
                refine ⟨7036377398833867234224149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4690918265889244822816099 7036377398833867234224149)
                ·
                  refine ⟨329830190570337526604257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7036377398833867234224149 329830190570337526604257)
                  ·
                    rfl

theorem cell23_5781078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_5781078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781078 prefixEnd_5781078 := by exact prefixLift 5781078
  have htrace : WordTrace (prefixWord ++ tailWord_5781078) baseStart_5781078 baseEnd_5781078 := by
    simpa [prefixWord, tailWord_5781078, baseEnd_5781078] using wordTrace_append hprefix tailTrace_5781078
  have hstable : (prefixWord ++ tailWord_5781078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781078).length < 2 ^ (prefixWord ++ tailWord_5781078).sum := by decide
  have hdescent : baseEnd_5781078 < baseStart_5781078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781127 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 3]
def baseStart_5781127 : Nat := 118140960795 + 5781127 * 2 ^ 59
def prefixEnd_5781127 : Nat := 4983230072969 + 3 ^ 40 * 5781127 * 2
def baseEnd_5781127 : Nat := 2968496875685108047725587

theorem tailTrace_5781127 : CollatzResearch.WordTrace tailWord_5781127 prefixEnd_5781127 2968496875685108047725587 := by
  unfold tailWord_5781127
  simp only [CollatzResearch.WordTrace]
  refine ⟨210855024126971691730725635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140570016084647794487150423 210855024126971691730725635)
  ·
    refine ⟨316282536190457537596088453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210855024126971691730725635 316282536190457537596088453)
    ·
      refine ⟨59302975535710788299266585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316282536190457537596088453 59302975535710788299266585)
      ·
        refine ⟨44477231651783091224449939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59302975535710788299266585 44477231651783091224449939)
        ·
          refine ⟨66715847477674636836674909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44477231651783091224449939 66715847477674636836674909)
          ·
            refine ⟨25018442804127988813753091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66715847477674636836674909 25018442804127988813753091)
            ·
              refine ⟨37527664206191983220629637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25018442804127988813753091 37527664206191983220629637)
              ·
                refine ⟨7036437038660996853868057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37527664206191983220629637 7036437038660996853868057)
                ·
                  refine ⟨5277327778995747640401043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7036437038660996853868057 5277327778995747640401043)
                  ·
                    refine ⟨7915991668493621460601565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5277327778995747640401043 7915991668493621460601565)
                    ·
                      refine ⟨2968496875685108047725587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7915991668493621460601565 2968496875685108047725587)
                      ·
                        rfl

theorem cell23_5781127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_5781127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781127 prefixEnd_5781127 := by exact prefixLift 5781127
  have htrace : WordTrace (prefixWord ++ tailWord_5781127) baseStart_5781127 baseEnd_5781127 := by
    simpa [prefixWord, tailWord_5781127, baseEnd_5781127] using wordTrace_append hprefix tailTrace_5781127
  have hstable : (prefixWord ++ tailWord_5781127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781127).length < 2 ^ (prefixWord ++ tailWord_5781127).sum := by decide
  have hdescent : baseEnd_5781127 < baseStart_5781127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781128 : List Nat := [2, 1, 3, 5, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5781128 : Nat := 118140960795 + 5781128 * 2 ^ 59
def prefixEnd_5781128 : Nat := 4983230072969 + 3 ^ 40 * 5781128 * 2
def baseEnd_5781128 : Nat := 2968497389165762543813083

theorem tailTrace_5781128 : CollatzResearch.WordTrace tailWord_5781128 prefixEnd_5781128 2968497389165762543813083 := by
  unfold tailWord_5781128
  simp only [CollatzResearch.WordTrace]
  refine ⟨105427530299984034450756019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140570040399978712601008025 105427530299984034450756019)
  ·
    refine ⟨158141295449976051676134029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105427530299984034450756019 158141295449976051676134029)
    ·
      refine ⟨59302985793741019378550261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158141295449976051676134029 59302985793741019378550261)
      ·
        refine ⟨5559654918163220566739087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59302985793741019378550261 5559654918163220566739087)
        ·
          refine ⟨8339482377244830850108631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5559654918163220566739087 8339482377244830850108631)
          ·
            refine ⟨12509223565867246275162947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8339482377244830850108631 12509223565867246275162947)
            ·
              refine ⟨18763835348800869412744421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12509223565867246275162947 18763835348800869412744421)
              ·
                refine ⟨3518219127900163014889579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18763835348800869412744421 3518219127900163014889579)
                ·
                  refine ⟨5277328691850244522334369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518219127900163014889579 5277328691850244522334369)
                  ·
                    refine ⟨3957996518887683391750777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5277328691850244522334369 3957996518887683391750777)
                    ·
                      refine ⟨2968497389165762543813083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3957996518887683391750777 2968497389165762543813083)
                      ·
                        rfl

theorem cell23_5781128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5781128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781128 prefixEnd_5781128 := by exact prefixLift 5781128
  have htrace : WordTrace (prefixWord ++ tailWord_5781128) baseStart_5781128 baseEnd_5781128 := by
    simpa [prefixWord, tailWord_5781128, baseEnd_5781128] using wordTrace_append hprefix tailTrace_5781128
  have hstable : (prefixWord ++ tailWord_5781128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781128).length < 2 ^ (prefixWord ++ tailWord_5781128).sum := by decide
  have hdescent : baseEnd_5781128 < baseStart_5781128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781143 : List Nat := [1, 1, 3, 3, 2, 2, 1, 1, 1, 8]
def baseStart_5781143 : Nat := 118140960795 + 5781143 * 2 ^ 59
def prefixEnd_5781143 : Nat := 4983230072969 + 3 ^ 40 * 5781143 * 2
def baseEnd_5781143 : Nat := 989501697125193328375171

theorem tailTrace_5781143 : CollatzResearch.WordTrace tailWord_5781143 prefixEnd_5781143 989501697125193328375171 := by
  unfold tailWord_5781143
  simp only [CollatzResearch.WordTrace]
  refine ⟨210855607694913726463308083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140570405129942484308872055 210855607694913726463308083)
  ·
    refine ⟨316283411542370589694962125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210855607694913726463308083 316283411542370589694962125)
    ·
      refine ⟨118606279328388971135610797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316283411542370589694962125 118606279328388971135610797)
      ·
        refine ⟨44477354748145864175854049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118606279328388971135610797 44477354748145864175854049)
        ·
          refine ⟨33358016061109398131890537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44477354748145864175854049 33358016061109398131890537)
          ·
            refine ⟨25018512045832048598917903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33358016061109398131890537 25018512045832048598917903)
            ·
              refine ⟨37527768068748072898376855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25018512045832048598917903 37527768068748072898376855)
              ·
                refine ⟨56291652103122109347565283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37527768068748072898376855 56291652103122109347565283)
                ·
                  refine ⟨84437478154683164021347925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56291652103122109347565283 84437478154683164021347925)
                  ·
                    refine ⟨989501697125193328375171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84437478154683164021347925 989501697125193328375171)
                    ·
                      rfl

theorem cell23_5781143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_5781143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781143 prefixEnd_5781143 := by exact prefixLift 5781143
  have htrace : WordTrace (prefixWord ++ tailWord_5781143) baseStart_5781143 baseEnd_5781143 := by
    simpa [prefixWord, tailWord_5781143, baseEnd_5781143] using wordTrace_append hprefix tailTrace_5781143
  have hstable : (prefixWord ++ tailWord_5781143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781143).length < 2 ^ (prefixWord ++ tailWord_5781143).sum := by decide
  have hdescent : baseEnd_5781143 < baseStart_5781143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781167 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 4, 2, 2]
def baseStart_5781167 : Nat := 118140960795 + 5781167 * 2 ^ 59
def prefixEnd_5781167 : Nat := 4983230072969 + 3 ^ 40 * 5781167 * 2
def baseEnd_5781167 : Nat := 2968517414911287891225403

theorem tailTrace_5781167 : CollatzResearch.WordTrace tailWord_5781167 prefixEnd_5781167 2968517414911287891225403 := by
  unfold tailWord_5781167
  simp only [CollatzResearch.WordTrace]
  refine ⟨210856483046826778562181755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140570988697884519041454503 210856483046826778562181755)
  ·
    refine ⟨316284724570240167843272633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210856483046826778562181755 316284724570240167843272633)
    ·
      refine ⟨237213543427680125882454475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316284724570240167843272633 237213543427680125882454475)
      ·
        refine ⟨355820315141520188823681713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237213543427680125882454475 355820315141520188823681713)
        ·
          refine ⟨266865236356140141617761285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355820315141520188823681713 266865236356140141617761285)
          ·
            refine ⟨50037231816776276553330241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 266865236356140141617761285 50037231816776276553330241)
            ·
              refine ⟨37527923862582207414997681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50037231816776276553330241 37527923862582207414997681)
              ·
                refine ⟨28145942896936655561248261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37527923862582207414997681 28145942896936655561248261)
                ·
                  refine ⟨5277364293175622917734049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28145942896936655561248261 5277364293175622917734049)
                  ·
                    refine ⟨3958023219881717188300537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5277364293175622917734049 3958023219881717188300537)
                    ·
                      refine ⟨2968517414911287891225403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3958023219881717188300537 2968517414911287891225403)
                      ·
                        rfl

theorem cell23_5781167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 4, 2, 2].length) (baseStart_5781167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781167 prefixEnd_5781167 := by exact prefixLift 5781167
  have htrace : WordTrace (prefixWord ++ tailWord_5781167) baseStart_5781167 baseEnd_5781167 := by
    simpa [prefixWord, tailWord_5781167, baseEnd_5781167] using wordTrace_append hprefix tailTrace_5781167
  have hstable : (prefixWord ++ tailWord_5781167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781167).length < 2 ^ (prefixWord ++ tailWord_5781167).sum := by decide
  have hdescent : baseEnd_5781167 < baseStart_5781167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781180 : List Nat := [2, 2, 2, 3, 1, 2, 1, 2, 2, 2, 4]
def baseStart_5781180 : Nat := 118140960795 + 5781180 * 2 ^ 59
def prefixEnd_5781180 : Nat := 4983230072969 + 3 ^ 40 * 5781180 * 2
def baseEnd_5781180 : Nat := 2968524090159796340362843

theorem tailTrace_5781180 : CollatzResearch.WordTrace tailWord_5781180 prefixEnd_5781180 2968524090159796340362843 := by
  unfold tailWord_5781180
  simp only [CollatzResearch.WordTrace]
  refine ⟨105428478597889840891202497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140571304797186454521603329 105428478597889840891202497)
  ·
    refine ⟨79071358948417380668401873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105428478597889840891202497 79071358948417380668401873)
    ·
      refine ⟨59303519211313035501301405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79071358948417380668401873 59303519211313035501301405)
      ·
        refine ⟨22238819704242388312988027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59303519211313035501301405 22238819704242388312988027)
        ·
          refine ⟨33358229556363582469482041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22238819704242388312988027 33358229556363582469482041)
          ·
            refine ⟨25018672167272686852111531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33358229556363582469482041 25018672167272686852111531)
            ·
              refine ⟨37528008250909030278167297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25018672167272686852111531 37528008250909030278167297)
              ·
                refine ⟨28146006188181772708625473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37528008250909030278167297 28146006188181772708625473)
                ·
                  refine ⟨21109504641136329531469105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28146006188181772708625473 21109504641136329531469105)
                  ·
                    refine ⟨15832128480852247148601829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21109504641136329531469105 15832128480852247148601829)
                    ·
                      refine ⟨2968524090159796340362843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15832128480852247148601829 2968524090159796340362843)
                      ·
                        rfl

theorem cell23_5781180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_5781180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781180 prefixEnd_5781180 := by exact prefixLift 5781180
  have htrace : WordTrace (prefixWord ++ tailWord_5781180) baseStart_5781180 baseEnd_5781180 := by
    simpa [prefixWord, tailWord_5781180, baseEnd_5781180] using wordTrace_append hprefix tailTrace_5781180
  have hstable : (prefixWord ++ tailWord_5781180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781180).length < 2 ^ (prefixWord ++ tailWord_5781180).sum := by decide
  have hdescent : baseEnd_5781180 < baseStart_5781180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781201 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 2, 2, 2]
def baseStart_5781201 : Nat := 118140960795 + 5781201 * 2 ^ 59
def prefixEnd_5781201 : Nat := 4983230072969 + 3 ^ 40 * 5781201 * 2
def baseEnd_5781201 : Nat := 2968534873253540758200247

theorem tailTrace_5781201 : CollatzResearch.WordTrace tailWord_5781201 prefixEnd_5781201 2968534873253540758200247 := by
  unfold tailWord_5781201
  simp only [CollatzResearch.WordTrace]
  refine ⟨210857723128703602368919457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140571815419135734912612971 210857723128703602368919457)
  ·
    refine ⟨158143292346527701776689593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210857723128703602368919457 158143292346527701776689593)
    ·
      refine ⟨118607469259895776332517195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158143292346527701776689593 118607469259895776332517195)
      ·
        refine ⟨177911203889843664498775793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118607469259895776332517195 177911203889843664498775793)
        ·
          refine ⟨133433402917382748374081845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177911203889843664498775793 133433402917382748374081845)
          ·
            refine ⟨12509381523504632660070173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133433402917382748374081845 12509381523504632660070173)
            ·
              refine ⟨4691018071314237247526315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12509381523504632660070173 4691018071314237247526315)
              ·
                refine ⟨7036527106971355871289473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691018071314237247526315 7036527106971355871289473)
                ·
                  refine ⟨5277395330228516903467105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7036527106971355871289473 5277395330228516903467105)
                  ·
                    refine ⟨3958046497671387677600329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5277395330228516903467105 3958046497671387677600329)
                    ·
                      refine ⟨2968534873253540758200247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3958046497671387677600329 2968534873253540758200247)
                      ·
                        rfl

theorem cell23_5781201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 2, 2, 2].length) (baseStart_5781201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781201 prefixEnd_5781201 := by exact prefixLift 5781201
  have htrace : WordTrace (prefixWord ++ tailWord_5781201) baseStart_5781201 baseEnd_5781201 := by
    simpa [prefixWord, tailWord_5781201, baseEnd_5781201] using wordTrace_append hprefix tailTrace_5781201
  have hstable : (prefixWord ++ tailWord_5781201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781201).length < 2 ^ (prefixWord ++ tailWord_5781201).sum := by decide
  have hdescent : baseEnd_5781201 < baseStart_5781201 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781220 : List Nat := [2, 3, 1, 1, 1, 3, 2, 3, 2, 5]
def baseStart_5781220 : Nat := 118140960795 + 5781220 * 2 ^ 59
def prefixEnd_5781220 : Nat := 4983230072969 + 3 ^ 40 * 5781220 * 2
def baseEnd_5781220 : Nat := 989514876461992061287553

theorem tailTrace_5781220 : CollatzResearch.WordTrace tailWord_5781220 prefixEnd_5781220 989514876461992061287553 := by
  unfold tailWord_5781220
  simp only [CollatzResearch.WordTrace]
  refine ⟨105429208057817384306930557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140572277410423179075907409 105429208057817384306930557)
  ·
    refine ⟨39535953021681519115098959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105429208057817384306930557 39535953021681519115098959)
    ·
      refine ⟨59303929532522278672648439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39535953021681519115098959 59303929532522278672648439)
      ·
        refine ⟨88955894298783418008972659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59303929532522278672648439 88955894298783418008972659)
        ·
          refine ⟨133433841448175127013458989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88955894298783418008972659 133433841448175127013458989)
          ·
            refine ⟨50037690543065672630047121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133433841448175127013458989 50037690543065672630047121)
            ·
              refine ⟨37528267907299254472535341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50037690543065672630047121 37528267907299254472535341)
              ·
                refine ⟨14073100465237220427200753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37528267907299254472535341 14073100465237220427200753)
                ·
                  refine ⟨10554825348927915320400565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14073100465237220427200753 10554825348927915320400565)
                  ·
                    refine ⟨989514876461992061287553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10554825348927915320400565 989514876461992061287553)
                    ·
                      rfl

theorem cell23_5781220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_5781220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781220 prefixEnd_5781220 := by exact prefixLift 5781220
  have htrace : WordTrace (prefixWord ++ tailWord_5781220) baseStart_5781220 baseEnd_5781220 := by
    simpa [prefixWord, tailWord_5781220, baseEnd_5781220] using wordTrace_append hprefix tailTrace_5781220
  have hstable : (prefixWord ++ tailWord_5781220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781220).length < 2 ^ (prefixWord ++ tailWord_5781220).sum := by decide
  have hdescent : baseEnd_5781220 < baseStart_5781220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781224 : List Nat := [2, 1, 4, 1, 3, 3, 1, 3, 5]
def baseStart_5781224 : Nat := 118140960795 + 5781224 * 2 ^ 59
def prefixEnd_5781224 : Nat := 4983230072969 + 3 ^ 40 * 5781224 * 2
def baseEnd_5781224 : Nat := 329838520367621574245849

theorem tailTrace_5781224 : CollatzResearch.WordTrace tailWord_5781224 prefixEnd_5781224 329838520367621574245849 := by
  unfold tailWord_5781224
  simp only [CollatzResearch.WordTrace]
  refine ⟨105429281003810138648503363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140572374671746851531337817 105429281003810138648503363)
  ·
    refine ⟨158143921505715207972755045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105429281003810138648503363 158143921505715207972755045)
    ·
      refine ⟨29651985282321601494891571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158143921505715207972755045 29651985282321601494891571)
      ·
        refine ⟨44477977923482402242337357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29651985282321601494891571 44477977923482402242337357)
        ·
          refine ⟨16679241721305900840876509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44477977923482402242337357 16679241721305900840876509)
          ·
            refine ⟨6254715645489712815328691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16679241721305900840876509 6254715645489712815328691)
            ·
              refine ⟨9382073468234569222993037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6254715645489712815328691 9382073468234569222993037)
              ·
                refine ⟨3518277550587963458622389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9382073468234569222993037 3518277550587963458622389)
                ·
                  refine ⟨329838520367621574245849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3518277550587963458622389 329838520367621574245849)
                  ·
                    rfl

theorem cell23_5781224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 5].length) (baseStart_5781224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781224 prefixEnd_5781224 := by exact prefixLift 5781224
  have htrace : WordTrace (prefixWord ++ tailWord_5781224) baseStart_5781224 baseEnd_5781224 := by
    simpa [prefixWord, tailWord_5781224, baseEnd_5781224] using wordTrace_append hprefix tailTrace_5781224
  have hstable : (prefixWord ++ tailWord_5781224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781224).length < 2 ^ (prefixWord ++ tailWord_5781224).sum := by decide
  have hdescent : baseEnd_5781224 < baseStart_5781224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781230 : List Nat := [4, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_5781230 : Nat := 118140960795 + 5781230 * 2 ^ 59
def prefixEnd_5781230 : Nat := 4983230072969 + 3 ^ 40 * 5781230 * 2
def baseEnd_5781230 : Nat := 2968549764192521144737613

theorem tailTrace_5781230 : CollatzResearch.WordTrace tailWord_5781230 prefixEnd_5781230 2968549764192521144737613 := by
  unfold tailWord_5781230
  simp only [CollatzResearch.WordTrace]
  refine ⟨26357347605699817540215643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140572520563732360214483429 26357347605699817540215643)
  ·
    refine ⟨39536021408549726310323465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26357347605699817540215643 39536021408549726310323465)
    ·
      refine ⟨29652016056412294732742599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39536021408549726310323465 29652016056412294732742599)
      ·
        refine ⟨44478024084618442099113899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29652016056412294732742599 44478024084618442099113899)
        ·
          refine ⟨66717036126927663148670849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44478024084618442099113899 66717036126927663148670849)
          ·
            refine ⟨50037777095195747361503137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66717036126927663148670849 50037777095195747361503137)
            ·
              refine ⟨37528332821396810521127353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50037777095195747361503137 37528332821396810521127353)
              ·
                refine ⟨28146249616047607890845515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37528332821396810521127353 28146249616047607890845515)
                ·
                  refine ⟨42219374424071411836268273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28146249616047607890845515 42219374424071411836268273)
                  ·
                    refine ⟨31664530818053558877201205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42219374424071411836268273 31664530818053558877201205)
                    ·
                      refine ⟨2968549764192521144737613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31664530818053558877201205 2968549764192521144737613)
                      ·
                        rfl

theorem cell23_5781230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_5781230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781230 prefixEnd_5781230 := by exact prefixLift 5781230
  have htrace : WordTrace (prefixWord ++ tailWord_5781230) baseStart_5781230 baseEnd_5781230 := by
    simpa [prefixWord, tailWord_5781230, baseEnd_5781230] using wordTrace_append hprefix tailTrace_5781230
  have hstable : (prefixWord ++ tailWord_5781230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781230).length < 2 ^ (prefixWord ++ tailWord_5781230).sum := by decide
  have hdescent : baseEnd_5781230 < baseStart_5781230 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781243 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 5]
def baseStart_5781243 : Nat := 118140960795 + 5781243 * 2 ^ 59
def prefixEnd_5781243 : Nat := 4983230072969 + 3 ^ 40 * 5781243 * 2
def baseEnd_5781243 : Nat := 2968556439441029593875053

theorem tailTrace_5781243 : CollatzResearch.WordTrace tailWord_5781243 prefixEnd_5781243 2968556439441029593875053 := by
  unfold tailWord_5781243
  simp only [CollatzResearch.WordTrace]
  refine ⟨210859254994551443541948383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140572836663034295694632255 210859254994551443541948383)
  ·
    refine ⟨316288882491827165312922575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210859254994551443541948383 316288882491827165312922575)
    ·
      refine ⟨474433323737740747969383863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316288882491827165312922575 474433323737740747969383863)
      ·
        refine ⟨711649985606611121954075795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474433323737740747969383863 711649985606611121954075795)
        ·
          refine ⟨1067474978409916682931113693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711649985606611121954075795 1067474978409916682931113693)
          ·
            refine ⟨400303116903718756099167635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1067474978409916682931113693 400303116903718756099167635)
            ·
              refine ⟨600454675355578134148751453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400303116903718756099167635 600454675355578134148751453)
              ·
                refine ⟨225170503258341800305781795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 600454675355578134148751453 225170503258341800305781795)
                ·
                  refine ⟨337755754887512700458672693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225170503258341800305781795 337755754887512700458672693)
                  ·
                    refine ⟨31664602020704315668000565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 337755754887512700458672693 31664602020704315668000565)
                    ·
                      refine ⟨2968556439441029593875053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31664602020704315668000565 2968556439441029593875053)
                      ·
                        rfl

theorem cell23_5781243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 5].length) (baseStart_5781243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781243 prefixEnd_5781243 := by exact prefixLift 5781243
  have htrace : WordTrace (prefixWord ++ tailWord_5781243) baseStart_5781243 baseEnd_5781243 := by
    simpa [prefixWord, tailWord_5781243, baseEnd_5781243] using wordTrace_append hprefix tailTrace_5781243
  have hstable : (prefixWord ++ tailWord_5781243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781243).length < 2 ^ (prefixWord ++ tailWord_5781243).sum := by decide
  have hdescent : baseEnd_5781243 < baseStart_5781243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781260 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 3, 4, 3]
def baseStart_5781260 : Nat := 118140960795 + 5781260 * 2 ^ 59
def prefixEnd_5781260 : Nat := 4983230072969 + 3 ^ 40 * 5781260 * 2
def baseEnd_5781260 : Nat := 2968565168612156027362475

theorem tailTrace_5781260 : CollatzResearch.WordTrace tailWord_5781260 prefixEnd_5781260 2968565168612156027362475 := by
  unfold tailWord_5781260
  simp only [CollatzResearch.WordTrace]
  refine ⟨105429937517744927722658617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140573250023659903630211489 105429937517744927722658617)
  ·
    refine ⟨79072453138308695791993963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105429937517744927722658617 79072453138308695791993963)
    ·
      refine ⟨118608679707463043687990945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79072453138308695791993963 118608679707463043687990945)
      ·
        refine ⟨88956509780597282765993209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118608679707463043687990945 88956509780597282765993209)
        ·
          refine ⟨66717382335447962074494907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88956509780597282765993209 66717382335447962074494907)
          ·
            refine ⟨100076073503171943111742361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66717382335447962074494907 100076073503171943111742361)
            ·
              refine ⟨75057055127378957333806771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100076073503171943111742361 75057055127378957333806771)
              ·
                refine ⟨112585582691068436000710157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75057055127378957333806771 112585582691068436000710157)
                ·
                  refine ⟨42219593509150663500266309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112585582691068436000710157 42219593509150663500266309)
                  ·
                    refine ⟨7916173782965749406299933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42219593509150663500266309 7916173782965749406299933)
                    ·
                      refine ⟨2968565168612156027362475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7916173782965749406299933 2968565168612156027362475)
                      ·
                        rfl

theorem cell23_5781260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_5781260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781260 prefixEnd_5781260 := by exact prefixLift 5781260
  have htrace : WordTrace (prefixWord ++ tailWord_5781260) baseStart_5781260 baseEnd_5781260 := by
    simpa [prefixWord, tailWord_5781260, baseEnd_5781260] using wordTrace_append hprefix tailTrace_5781260
  have hstable : (prefixWord ++ tailWord_5781260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781260).length < 2 ^ (prefixWord ++ tailWord_5781260).sum := by decide
  have hdescent : baseEnd_5781260 < baseStart_5781260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781263 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 10]
def baseStart_5781263 : Nat := 118140960795 + 5781263 * 2 ^ 59
def prefixEnd_5781263 : Nat := 4983230072969 + 3 ^ 40 * 5781263 * 2
def baseEnd_5781263 : Nat := 329840745450457723958329

theorem tailTrace_5781263 : CollatzResearch.WordTrace tailWord_5781263 prefixEnd_5781263 329840745450457723958329 := by
  unfold tailWord_5781263
  simp only [CollatzResearch.WordTrace]
  refine ⟨210859984454478986957676443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140573322969652657971784295 210859984454478986957676443)
  ·
    refine ⟨316289976681718480436514665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210859984454478986957676443 316289976681718480436514665)
    ·
      refine ⟨237217482511288860327385999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316289976681718480436514665 237217482511288860327385999)
      ·
        refine ⟨355826223766933290491078999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237217482511288860327385999 355826223766933290491078999)
        ·
          refine ⟨533739335650399935736618499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355826223766933290491078999 533739335650399935736618499)
          ·
            refine ⟨800609003475599903604927749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533739335650399935736618499 800609003475599903604927749)
            ·
              refine ⟨150114188151674981925923953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 800609003475599903604927749 150114188151674981925923953)
              ·
                refine ⟨112585641113756236444442965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150114188151674981925923953 112585641113756236444442965)
                ·
                  refine ⟨329840745450457723958329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112585641113756236444442965 329840745450457723958329)
                  ·
                    rfl

theorem cell23_5781263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 10].length) (baseStart_5781263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781263 prefixEnd_5781263 := by exact prefixLift 5781263
  have htrace : WordTrace (prefixWord ++ tailWord_5781263) baseStart_5781263 baseEnd_5781263 := by
    simpa [prefixWord, tailWord_5781263, baseEnd_5781263] using wordTrace_append hprefix tailTrace_5781263
  have hstable : (prefixWord ++ tailWord_5781263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781263).length < 2 ^ (prefixWord ++ tailWord_5781263).sum := by decide
  have hdescent : baseEnd_5781263 < baseStart_5781263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781297 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 6]
def baseStart_5781297 : Nat := 118140960795 + 5781297 * 2 ^ 59
def prefixEnd_5781297 : Nat := 4983230072969 + 3 ^ 40 * 5781297 * 2
def baseEnd_5781297 : Nat := 329842685266263598066645

theorem tailTrace_5781297 : CollatzResearch.WordTrace tailWord_5781297 prefixEnd_5781297 329842685266263598066645 := by
  unfold tailWord_5781297
  simp only [CollatzResearch.WordTrace]
  refine ⟨210861224536355810764414145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140574149690903873842942763 210861224536355810764414145)
  ·
    refine ⟨158145918402266858073310609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210861224536355810764414145 158145918402266858073310609)
    ·
      refine ⟨118609438801700143554982957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158145918402266858073310609 118609438801700143554982957)
      ·
        refine ⟨44478539550637553833118609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118609438801700143554982957 44478539550637553833118609)
        ·
          refine ⟨33358904662978165374838957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44478539550637553833118609 33358904662978165374838957)
          ·
            refine ⟨12509589248616812015564609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33358904662978165374838957 12509589248616812015564609)
            ·
              refine ⟨9382191936462609011673457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12509589248616812015564609 9382191936462609011673457)
              ·
                refine ⟨7036643952346956758755093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9382191936462609011673457 7036643952346956758755093)
                ·
                  refine ⟨329842685266263598066645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7036643952346956758755093 329842685266263598066645)
                  ·
                    rfl

theorem cell23_5781297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 6].length) (baseStart_5781297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781297 prefixEnd_5781297 := by exact prefixLift 5781297
  have htrace : WordTrace (prefixWord ++ tailWord_5781297) baseStart_5781297 baseEnd_5781297 := by
    simpa [prefixWord, tailWord_5781297, baseEnd_5781297] using wordTrace_append hprefix tailTrace_5781297
  have hstable : (prefixWord ++ tailWord_5781297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781297).length < 2 ^ (prefixWord ++ tailWord_5781297).sum := by decide
  have hdescent : baseEnd_5781297 < baseStart_5781297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781301 : List Nat := [1, 3, 3, 1, 4, 1, 1, 4, 1, 4]
def baseStart_5781301 : Nat := 118140960795 + 5781301 * 2 ^ 59
def prefixEnd_5781301 : Nat := 4983230072969 + 3 ^ 40 * 5781301 * 2
def baseEnd_5781301 : Nat := 989528740439663455649929

theorem tailTrace_5781301 : CollatzResearch.WordTrace tailWord_5781301 prefixEnd_5781301 989528740439663455649929 := by
  unfold tailWord_5781301
  simp only [CollatzResearch.WordTrace]
  refine ⟨210861370428341319447559757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140574246952227546298373171 210861370428341319447559757)
  ·
    refine ⟨79073013910627994792834909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210861370428341319447559757 79073013910627994792834909)
    ·
      refine ⟨29652380216485498047313091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79073013910627994792834909 29652380216485498047313091)
      ·
        refine ⟨44478570324728247070969637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29652380216485498047313091 44478570324728247070969637)
        ·
          refine ⟨8339731935886546325806807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44478570324728247070969637 8339731935886546325806807)
          ·
            refine ⟨12509597903829819488710211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8339731935886546325806807 12509597903829819488710211)
            ·
              refine ⟨18764396855744729233065317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12509597903829819488710211 18764396855744729233065317)
              ·
                refine ⟨3518324410452136731199747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18764396855744729233065317 3518324410452136731199747)
                ·
                  refine ⟨5277486615678205096799621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518324410452136731199747 5277486615678205096799621)
                  ·
                    refine ⟨989528740439663455649929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5277486615678205096799621 989528740439663455649929)
                    ·
                      rfl

theorem cell23_5781301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_5781301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781301 prefixEnd_5781301 := by exact prefixLift 5781301
  have htrace : WordTrace (prefixWord ++ tailWord_5781301) baseStart_5781301 baseEnd_5781301 := by
    simpa [prefixWord, tailWord_5781301, baseEnd_5781301] using wordTrace_append hprefix tailTrace_5781301
  have hstable : (prefixWord ++ tailWord_5781301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781301).length < 2 ^ (prefixWord ++ tailWord_5781301).sum := by decide
  have hdescent : baseEnd_5781301 < baseStart_5781301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781317 : List Nat := [1, 3, 1, 1, 1, 2, 4, 2, 1, 5, 2]
def baseStart_5781317 : Nat := 118140960795 + 5781317 * 2 ^ 59
def prefixEnd_5781317 : Nat := 4983230072969 + 3 ^ 40 * 5781317 * 2
def baseEnd_5781317 : Nat := 2968594437009462304349713

theorem tailTrace_5781317 : CollatzResearch.WordTrace tailWord_5781317 prefixEnd_5781317 2968594437009462304349713 := by
  unfold tailWord_5781317
  simp only [CollatzResearch.WordTrace]
  refine ⟨210861953996283354180142205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140574635997522236120094803 210861953996283354180142205)
  ·
    refine ⟨79073232748606257817553327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210861953996283354180142205 79073232748606257817553327)
    ·
      refine ⟨118609849122909386726329991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79073232748606257817553327 118609849122909386726329991)
      ·
        refine ⟨177914773684364080089494987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118609849122909386726329991 177914773684364080089494987)
        ·
          refine ⟨266872160526546120134242481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177914773684364080089494987 266872160526546120134242481)
          ·
            refine ⟨200154120394909590100681861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266872160526546120134242481 200154120394909590100681861)
            ·
              refine ⟨37528897574045548143877849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200154120394909590100681861 37528897574045548143877849)
              ·
                refine ⟨28146673180534161107908387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37528897574045548143877849 28146673180534161107908387)
                ·
                  refine ⟨42220009770801241661862581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28146673180534161107908387 42220009770801241661862581)
                  ·
                    refine ⟨3958125916012616405799617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42220009770801241661862581 3958125916012616405799617)
                    ·
                      refine ⟨2968594437009462304349713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3958125916012616405799617 2968594437009462304349713)
                      ·
                        rfl

theorem cell23_5781317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 2, 1, 5, 2].length) (baseStart_5781317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781317 prefixEnd_5781317 := by exact prefixLift 5781317
  have htrace : WordTrace (prefixWord ++ tailWord_5781317) baseStart_5781317 baseEnd_5781317 := by
    simpa [prefixWord, tailWord_5781317, baseEnd_5781317] using wordTrace_append hprefix tailTrace_5781317
  have hstable : (prefixWord ++ tailWord_5781317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781317).length < 2 ^ (prefixWord ++ tailWord_5781317).sum := by decide
  have hdescent : baseEnd_5781317 < baseStart_5781317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781344 : List Nat := [2, 1, 1, 3, 3, 2, 4, 1, 1, 5]
def baseStart_5781344 : Nat := 118140960795 + 5781344 * 2 ^ 59
def prefixEnd_5781344 : Nat := 4983230072969 + 3 ^ 40 * 5781344 * 2
def baseEnd_5781344 : Nat := 989536100329044566237363

theorem tailTrace_5781344 : CollatzResearch.WordTrace tailWord_5781344 prefixEnd_5781344 989536100329044566237363 := by
  unfold tailWord_5781344
  simp only [CollatzResearch.WordTrace]
  refine ⟨105431469383592768895687543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140575292511457025194250057 105431469383592768895687543)
  ·
    refine ⟨158147204075389153343531315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105431469383592768895687543 158147204075389153343531315)
    ·
      refine ⟨237220806113083730015296973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158147204075389153343531315 237220806113083730015296973)
      ·
        refine ⟨88957802292406398755736365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237220806113083730015296973 88957802292406398755736365)
        ·
          refine ⟨33359175859652399533401137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88957802292406398755736365 33359175859652399533401137)
          ·
            refine ⟨25019381894739299650050853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33359175859652399533401137 25019381894739299650050853)
            ·
              refine ⟨4691134105263618684384535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25019381894739299650050853 4691134105263618684384535)
              ·
                refine ⟨7036701157895428026576803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691134105263618684384535 7036701157895428026576803)
                ·
                  refine ⟨10555051736843142039865205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7036701157895428026576803 10555051736843142039865205)
                  ·
                    refine ⟨989536100329044566237363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10555051736843142039865205 989536100329044566237363)
                    ·
                      rfl

theorem cell23_5781344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 1, 1, 5].length) (baseStart_5781344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781344 prefixEnd_5781344 := by exact prefixLift 5781344
  have htrace : WordTrace (prefixWord ++ tailWord_5781344) baseStart_5781344 baseEnd_5781344 := by
    simpa [prefixWord, tailWord_5781344, baseEnd_5781344] using wordTrace_append hprefix tailTrace_5781344
  have hstable : (prefixWord ++ tailWord_5781344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781344).length < 2 ^ (prefixWord ++ tailWord_5781344).sum := by decide
  have hdescent : baseEnd_5781344 < baseStart_5781344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781358 : List Nat := [4, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_5781358 : Nat := 118140960795 + 5781358 * 2 ^ 59
def prefixEnd_5781358 : Nat := 4983230072969 + 3 ^ 40 * 5781358 * 2
def baseEnd_5781358 : Nat := 2968615489716296643937025

theorem tailTrace_5781358 : CollatzResearch.WordTrace tailWord_5781358 prefixEnd_5781358 2968615489716296643937025 := by
  unfold tailWord_5781358
  simp only [CollatzResearch.WordTrace]
  refine ⟨26357931173641852272798091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140575632926089878788256485 26357931173641852272798091)
  ·
    refine ⟨39536896760462778409197137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26357931173641852272798091 39536896760462778409197137)
    ·
      refine ⟨29652672570347083806897853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39536896760462778409197137 29652672570347083806897853)
      ·
        refine ⟨11119752213880156427586695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29652672570347083806897853 11119752213880156427586695)
        ·
          refine ⟨16679628320820234641380043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11119752213880156427586695 16679628320820234641380043)
          ·
            refine ⟨25019442481230351962070065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16679628320820234641380043 25019442481230351962070065)
            ·
              refine ⟨18764581860922763971552549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25019442481230351962070065 18764581860922763971552549)
              ·
                refine ⟨3518359098923018244666103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18764581860922763971552549 3518359098923018244666103)
                ·
                  refine ⟨5277538648384527366999155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518359098923018244666103 5277538648384527366999155)
                  ·
                    refine ⟨7916307972576791050498733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5277538648384527366999155 7916307972576791050498733)
                    ·
                      refine ⟨2968615489716296643937025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7916307972576791050498733 2968615489716296643937025)
                      ·
                        rfl

theorem cell23_5781358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_5781358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781358 prefixEnd_5781358 := by exact prefixLift 5781358
  have htrace : WordTrace (prefixWord ++ tailWord_5781358) baseStart_5781358 baseEnd_5781358 := by
    simpa [prefixWord, tailWord_5781358, baseEnd_5781358] using wordTrace_append hprefix tailTrace_5781358
  have hstable : (prefixWord ++ tailWord_5781358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781358).length < 2 ^ (prefixWord ++ tailWord_5781358).sum := by decide
  have hdescent : baseEnd_5781358 < baseStart_5781358 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781360 : List Nat := [2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_5781360 : Nat := 118140960795 + 5781360 * 2 ^ 59
def prefixEnd_5781360 : Nat := 4983230072969 + 3 ^ 40 * 5781360 * 2
def baseEnd_5781360 : Nat := 2968616516677605636112015

theorem tailTrace_5781360 : CollatzResearch.WordTrace tailWord_5781360 prefixEnd_5781360 2968616516677605636112015 := by
  unfold tailWord_5781360
  simp only [CollatzResearch.WordTrace]
  refine ⟨105431761167563786261978767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140575681556751715015971689 105431761167563786261978767)
  ·
    refine ⟨158147641751345679392968151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105431761167563786261978767 158147641751345679392968151)
    ·
      refine ⟨237221462627018519089452227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158147641751345679392968151 237221462627018519089452227)
      ·
        refine ⟨355832193940527778634178341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237221462627018519089452227 355832193940527778634178341)
        ·
          refine ⟨66718536363848958493908439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 355832193940527778634178341 66718536363848958493908439)
          ·
            refine ⟨100077804545773437740862659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66718536363848958493908439 100077804545773437740862659)
            ·
              refine ⟨150116706818660156611293989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100077804545773437740862659 150116706818660156611293989)
              ·
                refine ⟨28146882528498779364617623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 150116706818660156611293989 28146882528498779364617623)
                ·
                  refine ⟨42220323792748169046926435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28146882528498779364617623 42220323792748169046926435)
                  ·
                    refine ⟨63330485689122253570389653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42220323792748169046926435 63330485689122253570389653)
                    ·
                      refine ⟨2968616516677605636112015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63330485689122253570389653 2968616516677605636112015)
                      ·
                        rfl

theorem cell23_5781360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_5781360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781360 prefixEnd_5781360 := by exact prefixLift 5781360
  have htrace : WordTrace (prefixWord ++ tailWord_5781360) baseStart_5781360 baseEnd_5781360 := by
    simpa [prefixWord, tailWord_5781360, baseEnd_5781360] using wordTrace_append hprefix tailTrace_5781360
  have hstable : (prefixWord ++ tailWord_5781360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781360).length < 2 ^ (prefixWord ++ tailWord_5781360).sum := by decide
  have hdescent : baseEnd_5781360 < baseStart_5781360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781397 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 3]
def baseStart_5781397 : Nat := 118140960795 + 5781397 * 2 ^ 59
def prefixEnd_5781397 : Nat := 4983230072969 + 3 ^ 40 * 5781397 * 2
def baseEnd_5781397 : Nat := 2968635515461821991349345

theorem tailTrace_5781397 : CollatzResearch.WordTrace tailWord_5781397 prefixEnd_5781397 2968635515461821991349345 := by
  unfold tailWord_5781397
  simp only [CollatzResearch.WordTrace]
  refine ⟨210864871835993527843054445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140576581223995685228702963 210864871835993527843054445)
  ·
    refine ⟨79074326938497572941145417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210864871835993527843054445 79074326938497572941145417)
    ·
      refine ⟨59305745203873179705859063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79074326938497572941145417 59305745203873179705859063)
      ·
        refine ⟨88958617805809769558788595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59305745203873179705859063 88958617805809769558788595)
        ·
          refine ⟨133437926708714654338182893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88958617805809769558788595 133437926708714654338182893)
          ·
            refine ⟨50039222515767995376818585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133437926708714654338182893 50039222515767995376818585)
            ·
              refine ⟨37529416886825996532613939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50039222515767995376818585 37529416886825996532613939)
              ·
                refine ⟨56294125330238994798920909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37529416886825996532613939 56294125330238994798920909)
                ·
                  refine ⟨21110296998839623049595341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56294125330238994798920909 21110296998839623049595341)
                  ·
                    refine ⟨7916361374564858643598253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21110296998839623049595341 7916361374564858643598253)
                    ·
                      refine ⟨2968635515461821991349345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7916361374564858643598253 2968635515461821991349345)
                      ·
                        rfl

theorem cell23_5781397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 3, 3, 3].length) (baseStart_5781397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781397 prefixEnd_5781397 := by exact prefixLift 5781397
  have htrace : WordTrace (prefixWord ++ tailWord_5781397) baseStart_5781397 baseEnd_5781397 := by
    simpa [prefixWord, tailWord_5781397, baseEnd_5781397] using wordTrace_append hprefix tailTrace_5781397
  have hstable : (prefixWord ++ tailWord_5781397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781397).length < 2 ^ (prefixWord ++ tailWord_5781397).sum := by decide
  have hdescent : baseEnd_5781397 < baseStart_5781397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781511 : List Nat := [1, 1, 4, 3, 1, 3, 2, 3, 5]
def baseStart_5781511 : Nat := 118140960795 + 5781511 * 2 ^ 59
def prefixEnd_5781511 : Nat := 4983230072969 + 3 ^ 40 * 5781511 * 2
def baseEnd_5781511 : Nat := 329854894695159393924869

theorem tailTrace_5781511 : CollatzResearch.WordTrace tailWord_5781511 prefixEnd_5781511 329854894695159393924869 := by
  unfold tailWord_5781511
  simp only [CollatzResearch.WordTrace]
  refine ⟨210869029757580525312704387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140579353171720350208469591 210869029757580525312704387)
  ·
    refine ⟨316303544636370787969056581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210869029757580525312704387 316303544636370787969056581)
    ·
      refine ⟨59306914619319522744198109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316303544636370787969056581 59306914619319522744198109)
      ·
        refine ⟨22240092982244821029074291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59306914619319522744198109 22240092982244821029074291)
        ·
          refine ⟨33360139473367231543611437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22240092982244821029074291 33360139473367231543611437)
          ·
            refine ⟨12510052302512711828854289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33360139473367231543611437 12510052302512711828854289)
            ·
              refine ⟨9382539226884533871640717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12510052302512711828854289 9382539226884533871640717)
              ·
                refine ⟨3518452210081700201865269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9382539226884533871640717 3518452210081700201865269)
                ·
                  refine ⟨329854894695159393924869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3518452210081700201865269 329854894695159393924869)
                  ·
                    rfl

theorem cell23_5781511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 5].length) (baseStart_5781511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781511 prefixEnd_5781511 := by exact prefixLift 5781511
  have htrace : WordTrace (prefixWord ++ tailWord_5781511) baseStart_5781511 baseEnd_5781511 := by
    simpa [prefixWord, tailWord_5781511, baseEnd_5781511] using wordTrace_append hprefix tailTrace_5781511
  have hstable : (prefixWord ++ tailWord_5781511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781511).length < 2 ^ (prefixWord ++ tailWord_5781511).sum := by decide
  have hdescent : baseEnd_5781511 < baseStart_5781511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781564 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 1, 4, 3]
def baseStart_5781564 : Nat := 118140960795 + 5781564 * 2 ^ 59
def prefixEnd_5781564 : Nat := 4983230072969 + 3 ^ 40 * 5781564 * 2
def baseEnd_5781564 : Nat := 2968721266731122837961077

theorem tailTrace_5781564 : CollatzResearch.WordTrace tailWord_5781564 prefixEnd_5781564 2968721266731122837961077 := by
  unfold tailWord_5781564
  simp only [CollatzResearch.WordTrace]
  refine ⟨105435481413194257682191873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140580641884259010242922497 105435481413194257682191873)
  ·
    refine ⟨79076611059895693261643905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105435481413194257682191873 79076611059895693261643905)
    ·
      refine ⟨59307458294921769946232929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79076611059895693261643905 59307458294921769946232929)
      ·
        refine ⟨44480593721191327459674697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59307458294921769946232929 44480593721191327459674697)
        ·
          refine ⟨33360445290893495594756023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44480593721191327459674697 33360445290893495594756023)
          ·
            refine ⟨50040667936340243392134035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33360445290893495594756023 50040667936340243392134035)
            ·
              refine ⟨75061001904510365088201053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50040667936340243392134035 75061001904510365088201053)
              ·
                refine ⟨28147875714191386908075395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75061001904510365088201053 28147875714191386908075395)
                ·
                  refine ⟨42221813571287080362113093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28147875714191386908075395 42221813571287080362113093)
                  ·
                    refine ⟨7916590044616327567896205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42221813571287080362113093 7916590044616327567896205)
                    ·
                      refine ⟨2968721266731122837961077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7916590044616327567896205 2968721266731122837961077)
                      ·
                        rfl

theorem cell23_5781564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_5781564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781564 prefixEnd_5781564 := by exact prefixLift 5781564
  have htrace : WordTrace (prefixWord ++ tailWord_5781564) baseStart_5781564 baseEnd_5781564 := by
    simpa [prefixWord, tailWord_5781564, baseEnd_5781564] using wordTrace_append hprefix tailTrace_5781564
  have hstable : (prefixWord ++ tailWord_5781564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781564).length < 2 ^ (prefixWord ++ tailWord_5781564).sum := by decide
  have hdescent : baseEnd_5781564 < baseStart_5781564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781567 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 8]
def baseStart_5781567 : Nat := 118140960795 + 5781567 * 2 ^ 59
def prefixEnd_5781567 : Nat := 4983230072969 + 3 ^ 40 * 5781567 * 2
def baseEnd_5781567 : Nat := 329858089685898480691507

theorem tailTrace_5781567 : CollatzResearch.WordTrace tailWord_5781567 prefixEnd_5781567 329858089685898480691507 := by
  unfold tailWord_5781567
  simp only [CollatzResearch.WordTrace]
  refine ⟨210871072245377646876742955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140580714830251764584495303 210871072245377646876742955)
  ·
    refine ⟨316306608368066470315114433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210871072245377646876742955 316306608368066470315114433)
    ·
      refine ⟨237229956276049852736335825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316306608368066470315114433 237229956276049852736335825)
      ·
        refine ⟨177922467207037389552251869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237229956276049852736335825 177922467207037389552251869)
        ·
          refine ⟨66720925202639021082094451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177922467207037389552251869 66720925202639021082094451)
          ·
            refine ⟨100081387803958531623141677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66720925202639021082094451 100081387803958531623141677)
            ·
              refine ⟨37530520426484449358678129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100081387803958531623141677 37530520426484449358678129)
              ·
                refine ⟨28147890319863337019008597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37530520426484449358678129 28147890319863337019008597)
                ·
                  refine ⟨329858089685898480691507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28147890319863337019008597 329858089685898480691507)
                  ·
                    rfl

theorem cell23_5781567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 8].length) (baseStart_5781567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781567 prefixEnd_5781567 := by exact prefixLift 5781567
  have htrace : WordTrace (prefixWord ++ tailWord_5781567) baseStart_5781567 baseEnd_5781567 := by
    simpa [prefixWord, tailWord_5781567, baseEnd_5781567] using wordTrace_append hprefix tailTrace_5781567
  have hstable : (prefixWord ++ tailWord_5781567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781567).length < 2 ^ (prefixWord ++ tailWord_5781567).sum := by decide
  have hdescent : baseEnd_5781567 < baseStart_5781567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781571 : List Nat := [1, 1, 1, 3, 1, 2, 2, 7, 1, 4]
def baseStart_5781571 : Nat := 118140960795 + 5781571 * 2 ^ 59
def prefixEnd_5781571 : Nat := 4983230072969 + 3 ^ 40 * 5781571 * 2
def baseEnd_5781571 : Nat := 989574953698568103524515

theorem tailTrace_5781571 : CollatzResearch.WordTrace tailWord_5781571 prefixEnd_5781571 989574953698568103524515 := by
  unfold tailWord_5781571
  simp only [CollatzResearch.WordTrace]
  refine ⟨210871218137363155559888567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140580812091575437039925711 210871218137363155559888567)
  ·
    refine ⟨316306827206044733339832851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210871218137363155559888567 316306827206044733339832851)
    ·
      refine ⟨474460240809067100009749277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316306827206044733339832851 474460240809067100009749277)
      ·
        refine ⟨177922590303400162503655979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474460240809067100009749277 177922590303400162503655979)
        ·
          refine ⟨266883885455100243755483969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177922590303400162503655979 266883885455100243755483969)
          ·
            refine ⟨200162914091325182816612977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266883885455100243755483969 200162914091325182816612977)
            ·
              refine ⟨150122185568493887112459733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200162914091325182816612977 150122185568493887112459733)
              ·
                refine ⟨3518488724261575479198275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 150122185568493887112459733 3518488724261575479198275)
                ·
                  refine ⟨5277733086392363218797413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518488724261575479198275 5277733086392363218797413)
                  ·
                    refine ⟨989574953698568103524515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5277733086392363218797413 989574953698568103524515)
                    ·
                      rfl

theorem cell23_5781571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 7, 1, 4].length) (baseStart_5781571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781571 prefixEnd_5781571 := by exact prefixLift 5781571
  have htrace : WordTrace (prefixWord ++ tailWord_5781571) baseStart_5781571 baseEnd_5781571 := by
    simpa [prefixWord, tailWord_5781571, baseEnd_5781571] using wordTrace_append hprefix tailTrace_5781571
  have hstable : (prefixWord ++ tailWord_5781571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781571).length < 2 ^ (prefixWord ++ tailWord_5781571).sum := by decide
  have hdescent : baseEnd_5781571 < baseStart_5781571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781661 : List Nat := [1, 4, 2, 1, 1, 4, 2, 1, 1, 6]
def baseStart_5781661 : Nat := 118140960795 + 5781661 * 2 ^ 59
def prefixEnd_5781661 : Nat := 4983230072969 + 3 ^ 40 * 5781661 * 2
def baseEnd_5781661 : Nat := 989590358118202986149377

theorem tailTrace_5781661 : CollatzResearch.WordTrace tailWord_5781661 prefixEnd_5781661 989590358118202986149377 := by
  unfold tailWord_5781661
  simp only [CollatzResearch.WordTrace]
  refine ⟨210874500707037100930664837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140583000471358067287109891 210874500707037100930664837)
  ·
    refine ⟨39538968882569456424499657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210874500707037100930664837 39538968882569456424499657)
    ·
      refine ⟨29654226661927092318374743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39538968882569456424499657 29654226661927092318374743)
      ·
        refine ⟨44481339992890638477562115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29654226661927092318374743 44481339992890638477562115)
        ·
          refine ⟨66722009989335957716343173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44481339992890638477562115 66722009989335957716343173)
          ·
            refine ⟨12510376873000492071814345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66722009989335957716343173 12510376873000492071814345)
            ·
              refine ⟨9382782654750369053860759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12510376873000492071814345 9382782654750369053860759)
              ·
                refine ⟨14074173982125553580791139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9382782654750369053860759 14074173982125553580791139)
                ·
                  refine ⟨21111260973188330371186709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14074173982125553580791139 21111260973188330371186709)
                  ·
                    refine ⟨989590358118202986149377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21111260973188330371186709 989590358118202986149377)
                    ·
                      rfl

theorem cell23_5781661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_5781661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781661 prefixEnd_5781661 := by exact prefixLift 5781661
  have htrace : WordTrace (prefixWord ++ tailWord_5781661) baseStart_5781661 baseEnd_5781661 := by
    simpa [prefixWord, tailWord_5781661, baseEnd_5781661] using wordTrace_append hprefix tailTrace_5781661
  have hstable : (prefixWord ++ tailWord_5781661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781661).length < 2 ^ (prefixWord ++ tailWord_5781661).sum := by decide
  have hdescent : baseEnd_5781661 < baseStart_5781661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781685 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_5781685 : Nat := 118140960795 + 5781685 * 2 ^ 59
def prefixEnd_5781685 : Nat := 4983230072969 + 3 ^ 40 * 5781685 * 2
def baseEnd_5781685 : Nat := 2968783397890316864548021

theorem tailTrace_5781685 : CollatzResearch.WordTrace tailWord_5781685 prefixEnd_5781685 2968783397890316864548021 := by
  unfold tailWord_5781685
  simp only [CollatzResearch.WordTrace]
  refine ⟨210875376058950153029538509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140583584039300102019692339 210875376058950153029538509)
  ·
    refine ⟨79078266022106307386076941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210875376058950153029538509 79078266022106307386076941)
    ·
      refine ⟨29654349758289865269778853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79078266022106307386076941 29654349758289865269778853)
      ·
        refine ⟨5560190579679349738083535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29654349758289865269778853 5560190579679349738083535)
        ·
          refine ⟨8340285869519024607125303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560190579679349738083535 8340285869519024607125303)
          ·
            refine ⟨12510428804278536910687955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8340285869519024607125303 12510428804278536910687955)
            ·
              refine ⟨18765643206417805366031933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12510428804278536910687955 18765643206417805366031933)
              ·
                refine ⟨7037116202406677012261975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18765643206417805366031933 7037116202406677012261975)
                ·
                  refine ⟨10555674303610015518392963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7037116202406677012261975 10555674303610015518392963)
                  ·
                    refine ⟨15833511455415023277589445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10555674303610015518392963 15833511455415023277589445)
                    ·
                      refine ⟨2968783397890316864548021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15833511455415023277589445 2968783397890316864548021)
                      ·
                        rfl

theorem cell23_5781685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_5781685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781685 prefixEnd_5781685 := by exact prefixLift 5781685
  have htrace : WordTrace (prefixWord ++ tailWord_5781685) baseStart_5781685 baseEnd_5781685 := by
    simpa [prefixWord, tailWord_5781685, baseEnd_5781685] using wordTrace_append hprefix tailTrace_5781685
  have hstable : (prefixWord ++ tailWord_5781685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781685).length < 2 ^ (prefixWord ++ tailWord_5781685).sum := by decide
  have hdescent : baseEnd_5781685 < baseStart_5781685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781761 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_5781761 : Nat := 118140960795 + 5781761 * 2 ^ 59
def prefixEnd_5781761 : Nat := 4983230072969 + 3 ^ 40 * 5781761 * 2
def baseEnd_5781761 : Nat := 2968822422420058567197671

theorem tailTrace_5781761 : CollatzResearch.WordTrace tailWord_5781761 prefixEnd_5781761 2968822422420058567197671 := by
  unfold tailWord_5781761
  simp only [CollatzResearch.WordTrace]
  refine ⟨210878148006674818009305137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140585432004449878672870091 210878148006674818009305137)
  ·
    refine ⟨158158611005006113506978853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210878148006674818009305137 158158611005006113506978853)
    ·
      refine ⟨29654739563438646282558535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158158611005006113506978853 29654739563438646282558535)
      ·
        refine ⟨44482109345157969423837803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29654739563438646282558535 44482109345157969423837803)
        ·
          refine ⟨66723164017736954135756705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44482109345157969423837803 66723164017736954135756705)
          ·
            refine ⟨50042373013302715601817529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66723164017736954135756705 50042373013302715601817529)
            ·
              refine ⟨37531779759977036701363147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50042373013302715601817529 37531779759977036701363147)
              ·
                refine ⟨56297669639965555052044721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37531779759977036701363147 56297669639965555052044721)
                ·
                  refine ⟨42223252229974166289033541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56297669639965555052044721 42223252229974166289033541)
                  ·
                    refine ⟨7916859793120156179193789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42223252229974166289033541 7916859793120156179193789)
                    ·
                      refine ⟨2968822422420058567197671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7916859793120156179193789 2968822422420058567197671)
                      ·
                        rfl

theorem cell23_5781761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_5781761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781761 prefixEnd_5781761 := by exact prefixLift 5781761
  have htrace : WordTrace (prefixWord ++ tailWord_5781761) baseStart_5781761 baseEnd_5781761 := by
    simpa [prefixWord, tailWord_5781761, baseEnd_5781761] using wordTrace_append hprefix tailTrace_5781761
  have hstable : (prefixWord ++ tailWord_5781761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781761).length < 2 ^ (prefixWord ++ tailWord_5781761).sum := by decide
  have hdescent : baseEnd_5781761 < baseStart_5781761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781811 : List Nat := [1, 1, 1, 2, 5, 1, 1, 4, 2, 5]
def baseStart_5781811 : Nat := 118140960795 + 5781811 * 2 ^ 59
def prefixEnd_5781811 : Nat := 4983230072969 + 3 ^ 40 * 5781811 * 2
def baseEnd_5781811 : Nat := 989616032150927790524147

theorem tailTrace_5781811 : CollatzResearch.WordTrace tailWord_5781811 prefixEnd_5781811 989616032150927790524147 := by
  unfold tailWord_5781811
  simp only [CollatzResearch.WordTrace]
  refine ⟨210879971656493676548625287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140586647770995784365750191 210879971656493676548625287)
  ·
    refine ⟨316319957484740514822937931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210879971656493676548625287 316319957484740514822937931)
    ·
      refine ⟨474479936227110772234406897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316319957484740514822937931 474479936227110772234406897)
      ·
        refine ⟨355859952170333079175805173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474479936227110772234406897 355859952170333079175805173)
        ·
          refine ⟨33361870515968726172731735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 355859952170333079175805173 33361870515968726172731735)
          ·
            refine ⟨50042805773953089259097603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33361870515968726172731735 50042805773953089259097603)
            ·
              refine ⟨75064208660929633888646405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50042805773953089259097603 75064208660929633888646405)
              ·
                refine ⟨14074539123924306354121201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75064208660929633888646405 14074539123924306354121201)
                ·
                  refine ⟨10555904342943229765590901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14074539123924306354121201 10555904342943229765590901)
                  ·
                    refine ⟨989616032150927790524147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10555904342943229765590901 989616032150927790524147)
                    ·
                      rfl

theorem cell23_5781811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 4, 2, 5].length) (baseStart_5781811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781811 prefixEnd_5781811 := by exact prefixLift 5781811
  have htrace : WordTrace (prefixWord ++ tailWord_5781811) baseStart_5781811 baseEnd_5781811 := by
    simpa [prefixWord, tailWord_5781811, baseEnd_5781811] using wordTrace_append hprefix tailTrace_5781811
  have hstable : (prefixWord ++ tailWord_5781811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781811).length < 2 ^ (prefixWord ++ tailWord_5781811).sum := by decide
  have hdescent : baseEnd_5781811 < baseStart_5781811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781818 : List Nat := [3, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2]
def baseStart_5781818 : Nat := 118140960795 + 5781818 * 2 ^ 59
def prefixEnd_5781818 : Nat := 4983230072969 + 3 ^ 40 * 5781818 * 2
def baseEnd_5781818 : Nat := 2968851690817364844184909

theorem tailTrace_5781818 : CollatzResearch.WordTrace tailWord_5781818 prefixEnd_5781818 2968851690817364844184909 := by
  unfold tailWord_5781818
  simp only [CollatzResearch.WordTrace]
  refine ⟨52720056741867079186032527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140586817978312211162753405 52720056741867079186032527)
  ·
    refine ⟨79080085112800618779048791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52720056741867079186032527 79080085112800618779048791)
    ·
      refine ⟨118620127669200928168573187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79080085112800618779048791 118620127669200928168573187)
      ·
        refine ⟨177930191503801392252859781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118620127669200928168573187 177930191503801392252859781)
        ·
          refine ⟨33361910906962761047411209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177930191503801392252859781 33361910906962761047411209)
          ·
            refine ⟨25021433180222070785558407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33361910906962761047411209 25021433180222070785558407)
            ·
              refine ⟨37532149770333106178337611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25021433180222070785558407 37532149770333106178337611)
              ·
                refine ⟨56298224655499659267506417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37532149770333106178337611 56298224655499659267506417)
                ·
                  refine ⟨42223668491624744450629813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56298224655499659267506417 42223668491624744450629813)
                  ·
                    refine ⟨3958468921089819792246545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42223668491624744450629813 3958468921089819792246545)
                    ·
                      refine ⟨2968851690817364844184909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3958468921089819792246545 2968851690817364844184909)
                      ·
                        rfl

theorem cell23_5781818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2].length) (baseStart_5781818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781818 prefixEnd_5781818 := by exact prefixLift 5781818
  have htrace : WordTrace (prefixWord ++ tailWord_5781818) baseStart_5781818 baseEnd_5781818 := by
    simpa [prefixWord, tailWord_5781818, baseEnd_5781818] using wordTrace_append hprefix tailTrace_5781818
  have hstable : (prefixWord ++ tailWord_5781818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781818).length < 2 ^ (prefixWord ++ tailWord_5781818).sum := by decide
  have hdescent : baseEnd_5781818 < baseStart_5781818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781825 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5781825 : Nat := 118140960795 + 5781825 * 2 ^ 59
def prefixEnd_5781825 : Nat := 4983230072969 + 3 ^ 40 * 5781825 * 2
def baseEnd_5781825 : Nat := 2968855285181946316797377

theorem tailTrace_5781825 : CollatzResearch.WordTrace tailWord_5781825 prefixEnd_5781825 2968855285181946316797377 := by
  unfold tailWord_5781825
  simp only [CollatzResearch.WordTrace]
  refine ⟨210880482278442956939634929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140586988185628637959756619 210880482278442956939634929)
  ·
    refine ⟨158160361708832217704726197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210880482278442956939634929 158160361708832217704726197)
    ·
      refine ⟨14827533910203020409818081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158160361708832217704726197 14827533910203020409818081)
      ·
        refine ⟨11120650432652265307363561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14827533910203020409818081 11120650432652265307363561)
        ·
          refine ⟨8340487824489198980522671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11120650432652265307363561 8340487824489198980522671)
          ·
            refine ⟨12510731736733798470784007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8340487824489198980522671 12510731736733798470784007)
            ·
              refine ⟨18766097605100697706176011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12510731736733798470784007 18766097605100697706176011)
              ·
                refine ⟨28149146407651046559264017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18766097605100697706176011 28149146407651046559264017)
                ·
                  refine ⟨21111859805738284919448013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28149146407651046559264017 21111859805738284919448013)
                  ·
                    refine ⟨7916947427151856844793005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21111859805738284919448013 7916947427151856844793005)
                    ·
                      refine ⟨2968855285181946316797377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7916947427151856844793005 2968855285181946316797377)
                      ·
                        rfl

theorem cell23_5781825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5781825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781825 prefixEnd_5781825 := by exact prefixLift 5781825
  have htrace : WordTrace (prefixWord ++ tailWord_5781825) baseStart_5781825 baseEnd_5781825 := by
    simpa [prefixWord, tailWord_5781825, baseEnd_5781825] using wordTrace_append hprefix tailTrace_5781825
  have hstable : (prefixWord ++ tailWord_5781825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781825).length < 2 ^ (prefixWord ++ tailWord_5781825).sum := by decide
  have hdescent : baseEnd_5781825 < baseStart_5781825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781831 : List Nat := [1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 4]
def baseStart_5781831 : Nat := 118140960795 + 5781831 * 2 ^ 59
def prefixEnd_5781831 : Nat := 4983230072969 + 3 ^ 40 * 5781831 * 2
def baseEnd_5781831 : Nat := 2968858366065873293322349

theorem tailTrace_5781831 : CollatzResearch.WordTrace tailWord_5781831 prefixEnd_5781831 2968858366065873293322349 := by
  unfold tailWord_5781831
  simp only [CollatzResearch.WordTrace]
  refine ⟨210880701116421219964353347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140587134077614146642902231 210880701116421219964353347)
  ·
    refine ⟨316321051674631829946530021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210880701116421219964353347 316321051674631829946530021)
    ·
      refine ⟨59310197188993468114974379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316321051674631829946530021 59310197188993468114974379)
      ·
        refine ⟨88965295783490202172461569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59310197188993468114974379 88965295783490202172461569)
        ·
          refine ⟨66723971837617651629346177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88965295783490202172461569 66723971837617651629346177)
          ·
            refine ⟨50042978878213238722009633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66723971837617651629346177 50042978878213238722009633)
            ·
              refine ⟨37532234158659929041507225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50042978878213238722009633 37532234158659929041507225)
              ·
                refine ⟨28149175618994946781130419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37532234158659929041507225 28149175618994946781130419)
                ·
                  refine ⟨42223763428492420171695629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28149175618994946781130419 42223763428492420171695629)
                  ·
                    refine ⟨15833911285684657564385861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42223763428492420171695629 15833911285684657564385861)
                    ·
                      refine ⟨2968858366065873293322349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15833911285684657564385861 2968858366065873293322349)
                      ·
                        rfl

theorem cell23_5781831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_5781831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781831 prefixEnd_5781831 := by exact prefixLift 5781831
  have htrace : WordTrace (prefixWord ++ tailWord_5781831) baseStart_5781831 baseEnd_5781831 := by
    simpa [prefixWord, tailWord_5781831, baseEnd_5781831] using wordTrace_append hprefix tailTrace_5781831
  have hstable : (prefixWord ++ tailWord_5781831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781831).length < 2 ^ (prefixWord ++ tailWord_5781831).sum := by decide
  have hdescent : baseEnd_5781831 < baseStart_5781831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781845 : List Nat := [1, 3, 2, 2, 4, 2, 1, 1, 2, 5]
def baseStart_5781845 : Nat := 118140960795 + 5781845 * 2 ^ 59
def prefixEnd_5781845 : Nat := 4983230072969 + 3 ^ 40 * 5781845 * 2
def baseEnd_5781845 : Nat := 989621851598345412849095

theorem tailTrace_5781845 : CollatzResearch.WordTrace tailWord_5781845 prefixEnd_5781845 989621851598345412849095 := by
  unfold tailWord_5781845
  simp only [CollatzResearch.WordTrace]
  refine ⟨210881211738370500355362989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140587474492247000236908659 210881211738370500355362989)
  ·
    refine ⟨79080454401888937633261121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210881211738370500355362989 79080454401888937633261121)
    ·
      refine ⟨59310340801416703224945841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79080454401888937633261121 59310340801416703224945841)
      ·
        refine ⟨44482755601062527418709381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59310340801416703224945841 44482755601062527418709381)
        ·
          refine ⟨8340516675199223891008009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44482755601062527418709381 8340516675199223891008009)
          ·
            refine ⟨6255387506399417918256007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8340516675199223891008009 6255387506399417918256007)
            ·
              refine ⟨9383081259599126877384011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6255387506399417918256007 9383081259599126877384011)
              ·
                refine ⟨14074621889398690316076017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9383081259599126877384011 14074621889398690316076017)
                ·
                  refine ⟨10555966417049017737057013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14074621889398690316076017 10555966417049017737057013)
                  ·
                    refine ⟨989621851598345412849095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10555966417049017737057013 989621851598345412849095)
                    ·
                      rfl

theorem cell23_5781845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 2, 5].length) (baseStart_5781845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781845 prefixEnd_5781845 := by exact prefixLift 5781845
  have htrace : WordTrace (prefixWord ++ tailWord_5781845) baseStart_5781845 baseEnd_5781845 := by
    simpa [prefixWord, tailWord_5781845, baseEnd_5781845] using wordTrace_append hprefix tailTrace_5781845
  have hstable : (prefixWord ++ tailWord_5781845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781845).length < 2 ^ (prefixWord ++ tailWord_5781845).sum := by decide
  have hdescent : baseEnd_5781845 < baseStart_5781845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781861 : List Nat := [1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 6]
def baseStart_5781861 : Nat := 118140960795 + 5781861 * 2 ^ 59
def prefixEnd_5781861 : Nat := 4983230072969 + 3 ^ 40 * 5781861 * 2
def baseEnd_5781861 : Nat := 2968873770485508175947211

theorem tailTrace_5781861 : CollatzResearch.WordTrace tailWord_5781861 prefixEnd_5781861 2968873770485508175947211 := by
  unfold tailWord_5781861
  simp only [CollatzResearch.WordTrace]
  refine ⟨210881795306312535087945437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140587863537541690058630291 210881795306312535087945437)
  ·
    refine ⟨79080673239867200657979539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210881795306312535087945437 79080673239867200657979539)
    ·
      refine ⟨118621009859800800986969309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79080673239867200657979539 118621009859800800986969309)
      ·
        refine ⟨44482878697425300370113491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118621009859800800986969309 44482878697425300370113491)
        ·
          refine ⟨66724318046137950555170237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44482878697425300370113491 66724318046137950555170237)
          ·
            refine ⟨25021619267301731458188839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66724318046137950555170237 25021619267301731458188839)
            ·
              refine ⟨37532428900952597187283259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25021619267301731458188839 37532428900952597187283259)
              ·
                refine ⟨56298643351428895780924889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37532428900952597187283259 56298643351428895780924889)
                ·
                  refine ⟨42223982513571671835693667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56298643351428895780924889 42223982513571671835693667)
                  ·
                    refine ⟨63335973770357507753540501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42223982513571671835693667 63335973770357507753540501)
                    ·
                      refine ⟨2968873770485508175947211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63335973770357507753540501 2968873770485508175947211)
                      ·
                        rfl

theorem cell23_5781861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_5781861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781861 prefixEnd_5781861 := by exact prefixLift 5781861
  have htrace : WordTrace (prefixWord ++ tailWord_5781861) baseStart_5781861 baseEnd_5781861 := by
    simpa [prefixWord, tailWord_5781861, baseEnd_5781861] using wordTrace_append hprefix tailTrace_5781861
  have hstable : (prefixWord ++ tailWord_5781861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781861).length < 2 ^ (prefixWord ++ tailWord_5781861).sum := by decide
  have hdescent : baseEnd_5781861 < baseStart_5781861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781871 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 6]
def baseStart_5781871 : Nat := 118140960795 + 5781871 * 2 ^ 59
def prefixEnd_5781871 : Nat := 4983230072969 + 3 ^ 40 * 5781871 * 2
def baseEnd_5781871 : Nat := 329875433921339237424685

theorem tailTrace_5781871 : CollatzResearch.WordTrace tailWord_5781871 prefixEnd_5781871 329875433921339237424685 := by
  unfold tailWord_5781871
  simp only [CollatzResearch.WordTrace]
  refine ⟨210882160036276306795809467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140588106690850871197206311 210882160036276306795809467)
  ·
    refine ⟨316323240054414460193714201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210882160036276306795809467 316323240054414460193714201)
    ·
      refine ⟨237242430040810845145285651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316323240054414460193714201 237242430040810845145285651)
      ·
        refine ⟨355863645061216267717928477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237242430040810845145285651 355863645061216267717928477)
        ·
          refine ⟨133448866897956100394223179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355863645061216267717928477 133448866897956100394223179)
          ·
            refine ⟨200173300346934150591334769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133448866897956100394223179 200173300346934150591334769)
            ·
              refine ⟨150129975260200612943501077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200173300346934150591334769 150129975260200612943501077)
              ·
                refine ⟨7037342590321903731726613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 150129975260200612943501077 7037342590321903731726613)
                ·
                  refine ⟨329875433921339237424685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7037342590321903731726613 329875433921339237424685)
                  ·
                    rfl

theorem cell23_5781871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 6].length) (baseStart_5781871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781871 prefixEnd_5781871 := by exact prefixLift 5781871
  have htrace : WordTrace (prefixWord ++ tailWord_5781871) baseStart_5781871 baseEnd_5781871 := by
    simpa [prefixWord, tailWord_5781871, baseEnd_5781871] using wordTrace_append hprefix tailTrace_5781871
  have hstable : (prefixWord ++ tailWord_5781871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781871).length < 2 ^ (prefixWord ++ tailWord_5781871).sum := by decide
  have hdescent : baseEnd_5781871 < baseStart_5781871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781925 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 2, 3, 2]
def baseStart_5781925 : Nat := 118140960795 + 5781925 * 2 ^ 59
def prefixEnd_5781925 : Nat := 4983230072969 + 3 ^ 40 * 5781925 * 2
def baseEnd_5781925 : Nat := 2968906633247395925546917

theorem tailTrace_5781925 : CollatzResearch.WordTrace tailWord_5781925 prefixEnd_5781925 2968906633247395925546917 := by
  unfold tailWord_5781925
  simp only [CollatzResearch.WordTrace]
  refine ⟨210884129578080674018275229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140589419718720449345516819 210884129578080674018275229)
  ·
    refine ⟨79081548591780252756853211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210884129578080674018275229 79081548591780252756853211)
    ·
      refine ⟨118622322887670379135279817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79081548591780252756853211 118622322887670379135279817)
      ·
        refine ⟨88966742165752784351459863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118622322887670379135279817 88966742165752784351459863)
        ·
          refine ⟨133450113248629176527189795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88966742165752784351459863 133450113248629176527189795)
          ·
            refine ⟨200175169872943764790784693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133450113248629176527189795 200175169872943764790784693)
            ·
              refine ⟨18766422175588477949136065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200175169872943764790784693 18766422175588477949136065)
              ·
                refine ⟨14074816631691358461852049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18766422175588477949136065 14074816631691358461852049)
                ·
                  refine ⟨10556112473768518846389037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14074816631691358461852049 10556112473768518846389037)
                  ·
                    refine ⟨3958542177663194567395889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10556112473768518846389037 3958542177663194567395889)
                    ·
                      refine ⟨2968906633247395925546917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3958542177663194567395889 2968906633247395925546917)
                      ·
                        rfl

theorem cell23_5781925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 2, 3, 2].length) (baseStart_5781925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781925 prefixEnd_5781925 := by exact prefixLift 5781925
  have htrace : WordTrace (prefixWord ++ tailWord_5781925) baseStart_5781925 baseEnd_5781925 := by
    simpa [prefixWord, tailWord_5781925, baseEnd_5781925] using wordTrace_append hprefix tailTrace_5781925
  have hstable : (prefixWord ++ tailWord_5781925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781925).length < 2 ^ (prefixWord ++ tailWord_5781925).sum := by decide
  have hdescent : baseEnd_5781925 < baseStart_5781925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781938 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_5781938 : Nat := 118140960795 + 5781938 * 2 ^ 59
def prefixEnd_5781938 : Nat := 4983230072969 + 3 ^ 40 * 5781938 * 2
def baseEnd_5781938 : Nat := 2968913308495904374684357

theorem tailTrace_5781938 : CollatzResearch.WordTrace tailWord_5781938 prefixEnd_5781938 2968913308495904374684357 := by
  unfold tailWord_5781938
  simp only [CollatzResearch.WordTrace]
  refine ⟨52721150931758394309624617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140589735818022384825665645 52721150931758394309624617)
  ·
    refine ⟨39540863198818795732218463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52721150931758394309624617 39540863198818795732218463)
    ·
      refine ⟨59311294798228193598327695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39540863198818795732218463 59311294798228193598327695)
      ·
        refine ⟨88966942197342290397491543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59311294798228193598327695 88966942197342290397491543)
        ·
          refine ⟨133450413296013435596237315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88966942197342290397491543 133450413296013435596237315)
          ·
            refine ⟨200175619944020153394355973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133450413296013435596237315 200175619944020153394355973)
            ·
              refine ⟨37532928739503778761441745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200175619944020153394355973 37532928739503778761441745)
              ·
                refine ⟨28149696554627834071081309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37532928739503778761441745 28149696554627834071081309)
                ·
                  refine ⟨10556136207985437776655491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28149696554627834071081309 10556136207985437776655491)
                  ·
                    refine ⟨15834204311978156664983237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10556136207985437776655491 15834204311978156664983237)
                    ·
                      refine ⟨2968913308495904374684357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15834204311978156664983237 2968913308495904374684357)
                      ·
                        rfl

theorem cell23_5781938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_5781938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781938 prefixEnd_5781938 := by exact prefixLift 5781938
  have htrace : WordTrace (prefixWord ++ tailWord_5781938) baseStart_5781938 baseEnd_5781938 := by
    simpa [prefixWord, tailWord_5781938, baseEnd_5781938] using wordTrace_append hprefix tailTrace_5781938
  have hstable : (prefixWord ++ tailWord_5781938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781938).length < 2 ^ (prefixWord ++ tailWord_5781938).sum := by decide
  have hdescent : baseEnd_5781938 < baseStart_5781938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781955 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 5, 2, 2]
def baseStart_5781955 : Nat := 118140960795 + 5781955 * 2 ^ 59
def prefixEnd_5781955 : Nat := 4983230072969 + 3 ^ 40 * 5781955 * 2
def baseEnd_5781955 : Nat := 2968922037667030808171779

theorem tailTrace_5781955 : CollatzResearch.WordTrace tailWord_5781955 prefixEnd_5781955 2968922037667030808171779 := by
  unfold tailWord_5781955
  simp only [CollatzResearch.WordTrace]
  refine ⟨210885223767971989141867319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140590149178647992761244879 210885223767971989141867319)
  ·
    refine ⟨316327835651957983712800979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210885223767971989141867319 316327835651957983712800979)
    ·
      refine ⟨474491753477936975569201469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316327835651957983712800979 474491753477936975569201469)
      ·
        refine ⟨177934407554226365838450551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474491753477936975569201469 177934407554226365838450551)
        ·
          refine ⟨266901611331339548757675827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177934407554226365838450551 266901611331339548757675827)
          ·
            refine ⟨400352416997009323136513741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266901611331339548757675827 400352416997009323136513741)
            ·
              refine ⟨150132156373878496176192653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 400352416997009323136513741 150132156373878496176192653)
              ·
                refine ⟨56299558640204436066072245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150132156373878496176192653 56299558640204436066072245)
                ·
                  refine ⟨5278083622519165881194273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56299558640204436066072245 5278083622519165881194273)
                  ·
                    refine ⟨3958562716889374410895705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5278083622519165881194273 3958562716889374410895705)
                    ·
                      refine ⟨2968922037667030808171779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3958562716889374410895705 2968922037667030808171779)
                      ·
                        rfl

theorem cell23_5781955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5, 2, 2].length) (baseStart_5781955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781955 prefixEnd_5781955 := by exact prefixLift 5781955
  have htrace : WordTrace (prefixWord ++ tailWord_5781955) baseStart_5781955 baseEnd_5781955 := by
    simpa [prefixWord, tailWord_5781955, baseEnd_5781955] using wordTrace_append hprefix tailTrace_5781955
  have hstable : (prefixWord ++ tailWord_5781955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781955).length < 2 ^ (prefixWord ++ tailWord_5781955).sum := by decide
  have hdescent : baseEnd_5781955 < baseStart_5781955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5781961 : List Nat := [1, 2, 1, 1, 2, 1, 6, 9]
def baseStart_5781961 : Nat := 118140960795 + 5781961 * 2 ^ 59
def prefixEnd_5781961 : Nat := 4983230072969 + 3 ^ 40 * 5781961 * 2
def baseEnd_5781961 : Nat := 109960189575961399433213

theorem tailTrace_5781961 : CollatzResearch.WordTrace tailWord_5781961 prefixEnd_5781961 109960189575961399433213 := by
  unfold tailWord_5781961
  simp only [CollatzResearch.WordTrace]
  refine ⟨210885442605950252166585737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140590295070633501444390491 210885442605950252166585737)
  ·
    refine ⟨158164081954462689124939303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210885442605950252166585737 158164081954462689124939303)
    ·
      refine ⟨237246122931694033687408955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158164081954462689124939303 237246122931694033687408955)
      ·
        refine ⟨355869184397541050531113433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237246122931694033687408955 355869184397541050531113433)
        ·
          refine ⟨266901888298155787898335075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 355869184397541050531113433 266901888298155787898335075)
          ·
            refine ⟨400352832447233681847502613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266901888298155787898335075 400352832447233681847502613)
            ·
              refine ⟨18766539020964078836601685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 400352832447233681847502613 18766539020964078836601685)
              ·
                refine ⟨109960189575961399433213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18766539020964078836601685 109960189575961399433213)
                ·
                  rfl

theorem cell23_5781961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 9].length) (baseStart_5781961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5781961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5781961 prefixEnd_5781961 := by exact prefixLift 5781961
  have htrace : WordTrace (prefixWord ++ tailWord_5781961) baseStart_5781961 baseEnd_5781961 := by
    simpa [prefixWord, tailWord_5781961, baseEnd_5781961] using wordTrace_append hprefix tailTrace_5781961
  have hstable : (prefixWord ++ tailWord_5781961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5781961).length < 2 ^ (prefixWord ++ tailWord_5781961).sum := by decide
  have hdescent : baseEnd_5781961 < baseStart_5781961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5781961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782002 : List Nat := [3, 2, 1, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_5782002 : Nat := 118140960795 + 5782002 * 2 ^ 59
def prefixEnd_5782002 : Nat := 4983230072969 + 3 ^ 40 * 5782002 * 2
def baseEnd_5782002 : Nat := 2968946171257792124284063

theorem tailTrace_5782002 : CollatzResearch.WordTrace tailWord_5782002 prefixEnd_5782002 2968946171257792124284063 := by
  unfold tailWord_5782002
  simp only [CollatzResearch.WordTrace]
  refine ⟨52721734499700429042207065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140591291999201144112552173 52721734499700429042207065)
  ·
    refine ⟨39541300874775321781655299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52721734499700429042207065 39541300874775321781655299)
    ·
      refine ⟨59311951312162982672482949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39541300874775321781655299 59311951312162982672482949)
      ·
        refine ⟨11120990871030559251090553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59311951312162982672482949 11120990871030559251090553)
        ·
          refine ⟨8340743153272919438317915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11120990871030559251090553 8340743153272919438317915)
          ·
            refine ⟨12511114729909379157476873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8340743153272919438317915 12511114729909379157476873)
            ·
              refine ⟨9383336047432034368107655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12511114729909379157476873 9383336047432034368107655)
              ·
                refine ⟨14075004071148051552161483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9383336047432034368107655 14075004071148051552161483)
                ·
                  refine ⟨21112506106722077328242225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14075004071148051552161483 21112506106722077328242225)
                  ·
                    refine ⟨15834379580041557996181669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21112506106722077328242225 15834379580041557996181669)
                    ·
                      refine ⟨2968946171257792124284063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15834379580041557996181669 2968946171257792124284063)
                      ·
                        rfl

theorem cell23_5782002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_5782002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782002 prefixEnd_5782002 := by exact prefixLift 5782002
  have htrace : WordTrace (prefixWord ++ tailWord_5782002) baseStart_5782002 baseEnd_5782002 := by
    simpa [prefixWord, tailWord_5782002, baseEnd_5782002] using wordTrace_append hprefix tailTrace_5782002
  have hstable : (prefixWord ++ tailWord_5782002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782002).length < 2 ^ (prefixWord ++ tailWord_5782002).sum := by decide
  have hdescent : baseEnd_5782002 < baseStart_5782002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782011 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 10]
def baseStart_5782011 : Nat := 118140960795 + 5782011 * 2 ^ 59
def prefixEnd_5782011 : Nat := 4983230072969 + 3 ^ 40 * 5782011 * 2
def baseEnd_5782011 : Nat := 2968950792583682589071521

theorem tailTrace_5782011 : CollatzResearch.WordTrace tailWord_5782011 prefixEnd_5782011 2968950792583682589071521 := by
  unfold tailWord_5782011
  simp only [CollatzResearch.WordTrace]
  refine ⟨210887266255769110705905887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140591510837179407137270591 210887266255769110705905887)
  ·
    refine ⟨316330899383653666058858831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210887266255769110705905887 316330899383653666058858831)
    ·
      refine ⟨474496349075480499088288247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316330899383653666058858831 474496349075480499088288247)
      ·
        refine ⟨711744523613220748632432371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474496349075480499088288247 711744523613220748632432371)
        ·
          refine ⟨1067616785419831122948648557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 711744523613220748632432371 1067616785419831122948648557)
          ·
            refine ⟨400356294532436671105743209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1067616785419831122948648557 400356294532436671105743209)
            ·
              refine ⟨300267220899327503329307407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 400356294532436671105743209 300267220899327503329307407)
              ·
                refine ⟨450400831348991254993961111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 300267220899327503329307407 450400831348991254993961111)
                ·
                  refine ⟨675601247023486882490941667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 450400831348991254993961111 675601247023486882490941667)
                  ·
                    refine ⟨1013401870535230323736412501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 675601247023486882490941667 1013401870535230323736412501)
                    ·
                      refine ⟨2968950792583682589071521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1013401870535230323736412501 2968950792583682589071521)
                      ·
                        rfl

theorem cell23_5782011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 10].length) (baseStart_5782011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782011 prefixEnd_5782011 := by exact prefixLift 5782011
  have htrace : WordTrace (prefixWord ++ tailWord_5782011) baseStart_5782011 baseEnd_5782011 := by
    simpa [prefixWord, tailWord_5782011, baseEnd_5782011] using wordTrace_append hprefix tailTrace_5782011
  have hstable : (prefixWord ++ tailWord_5782011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782011).length < 2 ^ (prefixWord ++ tailWord_5782011).sum := by decide
  have hdescent : baseEnd_5782011 < baseStart_5782011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782015 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 3, 3, 2]
def baseStart_5782015 : Nat := 118140960795 + 5782015 * 2 ^ 59
def prefixEnd_5782015 : Nat := 4983230072969 + 3 ^ 40 * 5782015 * 2
def baseEnd_5782015 : Nat := 2968952846506300573421503

theorem tailTrace_5782015 : CollatzResearch.WordTrace tailWord_5782015 prefixEnd_5782015 2968952846506300573421503 := by
  unfold tailWord_5782015
  simp only [CollatzResearch.WordTrace]
  refine ⟨210887412147754619389051499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140591608098503079592700999 210887412147754619389051499)
  ·
    refine ⟨316331118221631929083577249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210887412147754619389051499 316331118221631929083577249)
    ·
      refine ⟨237248338666223946812682937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316331118221631929083577249 237248338666223946812682937)
      ·
        refine ⟨177936253999667960109512203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237248338666223946812682937 177936253999667960109512203)
        ·
          refine ⟨266904380999501940164268305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177936253999667960109512203 266904380999501940164268305)
          ·
            refine ⟨200178285749626455123201229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266904380999501940164268305 200178285749626455123201229)
            ·
              refine ⟨75066857156109920671200461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 200178285749626455123201229 75066857156109920671200461)
              ·
                refine ⟨28150071433541220251700173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75066857156109920671200461 28150071433541220251700173)
                ·
                  refine ⟨10556276787577957594387565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28150071433541220251700173 10556276787577957594387565)
                  ·
                    refine ⟨3958603795341734097895337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10556276787577957594387565 3958603795341734097895337)
                    ·
                      refine ⟨2968952846506300573421503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3958603795341734097895337 2968952846506300573421503)
                      ·
                        rfl

theorem cell23_5782015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_5782015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782015 prefixEnd_5782015 := by exact prefixLift 5782015
  have htrace : WordTrace (prefixWord ++ tailWord_5782015) baseStart_5782015 baseEnd_5782015 := by
    simpa [prefixWord, tailWord_5782015, baseEnd_5782015] using wordTrace_append hprefix tailTrace_5782015
  have hstable : (prefixWord ++ tailWord_5782015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782015).length < 2 ^ (prefixWord ++ tailWord_5782015).sum := by decide
  have hdescent : baseEnd_5782015 < baseStart_5782015 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782039 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5782039 : Nat := 118140960795 + 5782039 * 2 ^ 59
def prefixEnd_5782039 : Nat := 4983230072969 + 3 ^ 40 * 5782039 * 2
def baseEnd_5782039 : Nat := 2968965170042008479521393

theorem tailTrace_5782039 : CollatzResearch.WordTrace tailWord_5782039 prefixEnd_5782039 2968965170042008479521393 := by
  unfold tailWord_5782039
  simp only [CollatzResearch.WordTrace]
  refine ⟨210888287499667671487925171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140592191666445114325283447 210888287499667671487925171)
  ·
    refine ⟨316332431249501507231887757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210888287499667671487925171 316332431249501507231887757)
    ·
      refine ⟨118624661718563065211957909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316332431249501507231887757 118624661718563065211957909)
      ·
        refine ⟨5560531018057643681810527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 118624661718563065211957909 5560531018057643681810527)
        ·
          refine ⟨8340796527086465522715791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560531018057643681810527 8340796527086465522715791)
          ·
            refine ⟨12511194790629698284073687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8340796527086465522715791 12511194790629698284073687)
            ·
              refine ⟨18766792185944547426110531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12511194790629698284073687 18766792185944547426110531)
              ·
                refine ⟨28150188278916821139165797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18766792185944547426110531 28150188278916821139165797)
                ·
                  refine ⟨5278160302296903963593587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28150188278916821139165797 5278160302296903963593587)
                  ·
                    refine ⟨7917240453445355945390381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5278160302296903963593587 7917240453445355945390381)
                    ·
                      refine ⟨2968965170042008479521393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7917240453445355945390381 2968965170042008479521393)
                      ·
                        rfl

theorem cell23_5782039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5782039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782039 prefixEnd_5782039 := by exact prefixLift 5782039
  have htrace : WordTrace (prefixWord ++ tailWord_5782039) baseStart_5782039 baseEnd_5782039 := by
    simpa [prefixWord, tailWord_5782039, baseEnd_5782039] using wordTrace_append hprefix tailTrace_5782039
  have hstable : (prefixWord ++ tailWord_5782039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782039).length < 2 ^ (prefixWord ++ tailWord_5782039).sum := by decide
  have hdescent : baseEnd_5782039 < baseStart_5782039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782056 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5782056 : Nat := 118140960795 + 5782056 * 2 ^ 59
def prefixEnd_5782056 : Nat := 4983230072969 + 3 ^ 40 * 5782056 * 2
def baseEnd_5782056 : Nat := 2968973899213134913008815

theorem tailTrace_5782056 : CollatzResearch.WordTrace tailWord_5782056 prefixEnd_5782056 2968973899213134913008815 := by
  unfold tailWord_5782056
  simp only [CollatzResearch.WordTrace]
  refine ⟨105444453770303041695647011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140592605027070722260862681 105444453770303041695647011)
  ·
    refine ⟨158166680655454562543470517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105444453770303041695647011 158166680655454562543470517)
    ·
      refine ⟨14828126311448865238450361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158166680655454562543470517 14828126311448865238450361)
      ·
        refine ⟨11121094733586648928837771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14828126311448865238450361 11121094733586648928837771)
        ·
          refine ⟨16681642100379973393256657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11121094733586648928837771 16681642100379973393256657)
          ·
            refine ⟨12511231575284980044942493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16681642100379973393256657 12511231575284980044942493)
            ·
              refine ⟨4691711840731867516853435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12511231575284980044942493 4691711840731867516853435)
              ·
                refine ⟨7037567761097801275280153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691711840731867516853435 7037567761097801275280153)
                ·
                  refine ⟨5278175820823350956460115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7037567761097801275280153 5278175820823350956460115)
                  ·
                    refine ⟨7917263731235026434690173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5278175820823350956460115 7917263731235026434690173)
                    ·
                      refine ⟨2968973899213134913008815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7917263731235026434690173 2968973899213134913008815)
                      ·
                        rfl

theorem cell23_5782056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5782056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782056 prefixEnd_5782056 := by exact prefixLift 5782056
  have htrace : WordTrace (prefixWord ++ tailWord_5782056) baseStart_5782056 baseEnd_5782056 := by
    simpa [prefixWord, tailWord_5782056, baseEnd_5782056] using wordTrace_append hprefix tailTrace_5782056
  have hstable : (prefixWord ++ tailWord_5782056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782056).length < 2 ^ (prefixWord ++ tailWord_5782056).sum := by decide
  have hdescent : baseEnd_5782056 < baseStart_5782056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782135 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 4]
def baseStart_5782135 : Nat := 118140960795 + 5782135 * 2 ^ 59
def prefixEnd_5782135 : Nat := 4983230072969 + 3 ^ 40 * 5782135 * 2
def baseEnd_5782135 : Nat := 2969014464184840103920951

theorem tailTrace_5782135 : CollatzResearch.WordTrace tailWord_5782135 prefixEnd_5782135 2969014464184840103920951 := by
  unfold tailWord_5782135
  simp only [CollatzResearch.WordTrace]
  refine ⟨210891788907319879883419859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140594525938213253255613239 210891788907319879883419859)
  ·
    refine ⟨316337683360979819825129789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210891788907319879883419859 316337683360979819825129789)
    ·
      refine ⟨118626631260367432434423671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316337683360979819825129789 118626631260367432434423671)
      ·
        refine ⟨177939946890551148651635507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118626631260367432434423671 177939946890551148651635507)
        ·
          refine ⟨266909920335826722977453261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177939946890551148651635507 266909920335826722977453261)
          ·
            refine ⟨100091220125935021116544973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266909920335826722977453261 100091220125935021116544973)
            ·
              refine ⟨37534207547225632918704365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100091220125935021116544973 37534207547225632918704365)
              ·
                refine ⟨14075327830209612344514137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37534207547225632918704365 14075327830209612344514137)
                ·
                  refine ⟨10556495872657209258385603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14075327830209612344514137 10556495872657209258385603)
                  ·
                    refine ⟨15834743808985813887578405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10556495872657209258385603 15834743808985813887578405)
                    ·
                      refine ⟨2969014464184840103920951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15834743808985813887578405 2969014464184840103920951)
                      ·
                        rfl

theorem cell23_5782135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_5782135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782135 prefixEnd_5782135 := by exact prefixLift 5782135
  have htrace : WordTrace (prefixWord ++ tailWord_5782135) baseStart_5782135 baseEnd_5782135 := by
    simpa [prefixWord, tailWord_5782135, baseEnd_5782135] using wordTrace_append hprefix tailTrace_5782135
  have hstable : (prefixWord ++ tailWord_5782135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782135).length < 2 ^ (prefixWord ++ tailWord_5782135).sum := by decide
  have hdescent : baseEnd_5782135 < baseStart_5782135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782155 : List Nat := [1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 3]
def baseStart_5782155 : Nat := 118140960795 + 5782155 * 2 ^ 59
def prefixEnd_5782155 : Nat := 4983230072969 + 3 ^ 40 * 5782155 * 2
def baseEnd_5782155 : Nat := 2969024733797930025670859

theorem tailTrace_5782155 : CollatzResearch.WordTrace tailWord_5782155 prefixEnd_5782155 2969024733797930025670859 := by
  unfold tailWord_5782155
  simp only [CollatzResearch.WordTrace]
  refine ⟨210892518367247423299147919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140595012244831615532765279 210892518367247423299147919)
  ·
    refine ⟨316338777550871134948721879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210892518367247423299147919 316338777550871134948721879)
    ·
      refine ⟨474508166326306702423082819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316338777550871134948721879 474508166326306702423082819)
      ·
        refine ⟨711762249489460053634624229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474508166326306702423082819 711762249489460053634624229)
        ·
          refine ⟨133455421779273760056492043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 711762249489460053634624229 133455421779273760056492043)
          ·
            refine ⟨200183132668910640084738065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133455421779273760056492043 200183132668910640084738065)
            ·
              refine ⟨150137349501682980063553549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200183132668910640084738065 150137349501682980063553549)
              ·
                refine ⟨56301506063131117523832581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 150137349501682980063553549 56301506063131117523832581)
                ·
                  refine ⟨10556532386837084535718609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56301506063131117523832581 10556532386837084535718609)
                  ·
                    refine ⟨7917399290127813401788957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10556532386837084535718609 7917399290127813401788957)
                    ·
                      refine ⟨2969024733797930025670859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7917399290127813401788957 2969024733797930025670859)
                      ·
                        rfl

theorem cell23_5782155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 3].length) (baseStart_5782155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782155 prefixEnd_5782155 := by exact prefixLift 5782155
  have htrace : WordTrace (prefixWord ++ tailWord_5782155) baseStart_5782155 baseEnd_5782155 := by
    simpa [prefixWord, tailWord_5782155, baseEnd_5782155] using wordTrace_append hprefix tailTrace_5782155
  have hstable : (prefixWord ++ tailWord_5782155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782155).length < 2 ^ (prefixWord ++ tailWord_5782155).sum := by decide
  have hdescent : baseEnd_5782155 < baseStart_5782155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782189 : List Nat := [1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_5782189 : Nat := 118140960795 + 5782189 * 2 ^ 59
def prefixEnd_5782189 : Nat := 4983230072969 + 3 ^ 40 * 5782189 * 2
def baseEnd_5782189 : Nat := 2969042192140182892645703

theorem tailTrace_5782189 : CollatzResearch.WordTrace tailWord_5782189 prefixEnd_5782189 2969042192140182892645703 := by
  unfold tailWord_5782189
  simp only [CollatzResearch.WordTrace]
  refine ⟨210893758449124247105885621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140595838966082831403923747 210893758449124247105885621)
  ·
    refine ⟨19771289854605398166176777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 210893758449124247105885621 19771289854605398166176777)
    ·
      refine ⟨14828467390954048624632583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19771289854605398166176777 14828467390954048624632583)
      ·
        refine ⟨22242701086431072936948875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14828467390954048624632583 22242701086431072936948875)
        ·
          refine ⟨33364051629646609405423313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22242701086431072936948875 33364051629646609405423313)
          ·
            refine ⟨25023038722234957054067485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33364051629646609405423313 25023038722234957054067485)
            ·
              refine ⟨9383639520838108895275307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25023038722234957054067485 9383639520838108895275307)
              ·
                refine ⟨14075459281257163342912961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9383639520838108895275307 14075459281257163342912961)
                ·
                  refine ⟨10556594460942872507184721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14075459281257163342912961 10556594460942872507184721)
                  ·
                    refine ⟨7917445845707154380388541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10556594460942872507184721 7917445845707154380388541)
                    ·
                      refine ⟨2969042192140182892645703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7917445845707154380388541 2969042192140182892645703)
                      ·
                        rfl

theorem cell23_5782189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_5782189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782189 prefixEnd_5782189 := by exact prefixLift 5782189
  have htrace : WordTrace (prefixWord ++ tailWord_5782189) baseStart_5782189 baseEnd_5782189 := by
    simpa [prefixWord, tailWord_5782189, baseEnd_5782189] using wordTrace_append hprefix tailTrace_5782189
  have hstable : (prefixWord ++ tailWord_5782189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782189).length < 2 ^ (prefixWord ++ tailWord_5782189).sum := by decide
  have hdescent : baseEnd_5782189 < baseStart_5782189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782202 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3]
def baseStart_5782202 : Nat := 118140960795 + 5782202 * 2 ^ 59
def prefixEnd_5782202 : Nat := 4983230072969 + 3 ^ 40 * 5782202 * 2
def baseEnd_5782202 : Nat := 2969048867388691341783143

theorem tailTrace_5782202 : CollatzResearch.WordTrace tailWord_5782202 prefixEnd_5782202 2969048867388691341783143 := by
  unfold tailWord_5782202
  simp only [CollatzResearch.WordTrace]
  refine ⟨52723558149519287581527215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140596155065384766884072573 52723558149519287581527215)
  ·
    refine ⟨79085337224278931372290823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52723558149519287581527215 79085337224278931372290823)
    ·
      refine ⟨118628005836418397058436235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79085337224278931372290823 118628005836418397058436235)
      ·
        refine ⟨177942008754627595587654353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118628005836418397058436235 177942008754627595587654353)
        ·
          refine ⟨133456506565970696690740765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177942008754627595587654353 133456506565970696690740765)
          ·
            refine ⟨50046189962239011259027787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133456506565970696690740765 50046189962239011259027787)
            ·
              refine ⟨75069284943358516888541681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50046189962239011259027787 75069284943358516888541681)
              ·
                refine ⟨56301963707518887666406261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75069284943358516888541681 56301963707518887666406261)
                ·
                  refine ⟨5278309097579895718725587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56301963707518887666406261 5278309097579895718725587)
                  ·
                    refine ⟨7917463646369843578088381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5278309097579895718725587 7917463646369843578088381)
                    ·
                      refine ⟨2969048867388691341783143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7917463646369843578088381 2969048867388691341783143)
                      ·
                        rfl

theorem cell23_5782202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 5, 1, 3].length) (baseStart_5782202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782202 prefixEnd_5782202 := by exact prefixLift 5782202
  have htrace : WordTrace (prefixWord ++ tailWord_5782202) baseStart_5782202 baseEnd_5782202 := by
    simpa [prefixWord, tailWord_5782202, baseEnd_5782202] using wordTrace_append hprefix tailTrace_5782202
  have hstable : (prefixWord ++ tailWord_5782202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782202).length < 2 ^ (prefixWord ++ tailWord_5782202).sum := by decide
  have hdescent : baseEnd_5782202 < baseStart_5782202 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782209 : List Nat := [1, 2, 6, 2, 1, 1, 1, 1, 8]
def baseStart_5782209 : Nat := 118140960795 + 5782209 * 2 ^ 59
def prefixEnd_5782209 : Nat := 4983230072969 + 3 ^ 40 * 5782209 * 2
def baseEnd_5782209 : Nat := 329894717972585868266179

theorem tailTrace_5782209 : CollatzResearch.WordTrace tailWord_5782209 prefixEnd_5782209 329894717972585868266179 := by
  unfold tailWord_5782209
  simp only [CollatzResearch.WordTrace]
  refine ⟨210894487909051790521613681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140596325272701193681075787 210894487909051790521613681)
  ·
    refine ⟨158170865931788842891210261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210894487909051790521613681 158170865931788842891210261)
    ·
      refine ⟨7414259340552602010525481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158170865931788842891210261 7414259340552602010525481)
      ·
        refine ⟨5560694505414451507894111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7414259340552602010525481 5560694505414451507894111)
        ·
          refine ⟨8341041758121677261841167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5560694505414451507894111 8341041758121677261841167)
          ·
            refine ⟨12511562637182515892761751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8341041758121677261841167 12511562637182515892761751)
            ·
              refine ⟨18767343955773773839142627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12511562637182515892761751 18767343955773773839142627)
              ·
                refine ⟨28151015933660660758713941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18767343955773773839142627 28151015933660660758713941)
                ·
                  refine ⟨329894717972585868266179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28151015933660660758713941 329894717972585868266179)
                  ·
                    rfl

theorem cell23_5782209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 1, 8].length) (baseStart_5782209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782209 prefixEnd_5782209 := by exact prefixLift 5782209
  have htrace : WordTrace (prefixWord ++ tailWord_5782209) baseStart_5782209 baseEnd_5782209 := by
    simpa [prefixWord, tailWord_5782209, baseEnd_5782209] using wordTrace_append hprefix tailTrace_5782209
  have hstable : (prefixWord ++ tailWord_5782209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782209).length < 2 ^ (prefixWord ++ tailWord_5782209).sum := by decide
  have hdescent : baseEnd_5782209 < baseStart_5782209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782236 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 3, 1, 3]
def baseStart_5782236 : Nat := 118140960795 + 5782236 * 2 ^ 59
def prefixEnd_5782236 : Nat := 4983230072969 + 3 ^ 40 * 5782236 * 2
def baseEnd_5782236 : Nat := 2969066325730944208757987

theorem tailTrace_5782236 : CollatzResearch.WordTrace tailWord_5782236 prefixEnd_5782236 2969066325730944208757987 := by
  unfold tailWord_5782236
  simp only [CollatzResearch.WordTrace]
  refine ⟨105447736339976987066423281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140596981786635982755231041 105447736339976987066423281)
  ·
    refine ⟨79085802254982740299817461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105447736339976987066423281 79085802254982740299817461)
    ·
      refine ⟨7414293961404631903107887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79085802254982740299817461 7414293961404631903107887)
      ·
        refine ⟨11121440942106947854661831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7414293961404631903107887 11121440942106947854661831)
        ·
          refine ⟨16682161413160421781992747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11121440942106947854661831 16682161413160421781992747)
          ·
            refine ⟨25023242119740632672989121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16682161413160421781992747 25023242119740632672989121)
            ·
              refine ⟨18767431589805474504741841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25023242119740632672989121 18767431589805474504741841)
              ·
                refine ⟨14075573692354105878556381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18767431589805474504741841 14075573692354105878556381)
                ·
                  refine ⟨5278340134632789704458643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14075573692354105878556381 5278340134632789704458643)
                  ·
                    refine ⟨7917510201949184556687965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5278340134632789704458643 7917510201949184556687965)
                    ·
                      refine ⟨2969066325730944208757987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7917510201949184556687965 2969066325730944208757987)
                      ·
                        rfl

theorem cell23_5782236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_5782236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782236 prefixEnd_5782236 := by exact prefixLift 5782236
  have htrace : WordTrace (prefixWord ++ tailWord_5782236) baseStart_5782236 baseEnd_5782236 := by
    simpa [prefixWord, tailWord_5782236, baseEnd_5782236] using wordTrace_append hprefix tailTrace_5782236
  have hstable : (prefixWord ++ tailWord_5782236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782236).length < 2 ^ (prefixWord ++ tailWord_5782236).sum := by decide
  have hdescent : baseEnd_5782236 < baseStart_5782236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782270 : List Nat := [4, 2, 2, 1, 2, 2, 3, 2, 1, 1, 3]
def baseStart_5782270 : Nat := 118140960795 + 5782270 * 2 ^ 59
def prefixEnd_5782270 : Nat := 4983230072969 + 3 ^ 40 * 5782270 * 2
def baseEnd_5782270 : Nat := 2969083784073197075732831

theorem tailTrace_5782270 : CollatzResearch.WordTrace tailWord_5782270 prefixEnd_5782270 2969083784073197075732831 := by
  unfold tailWord_5782270
  simp only [CollatzResearch.WordTrace]
  refine ⟨26362089095228849742448033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140597808507887198626389509 26362089095228849742448033)
  ·
    refine ⟨19771566821421637306836025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26362089095228849742448033 19771566821421637306836025)
    ·
      refine ⟨14828675116066227980127019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19771566821421637306836025 14828675116066227980127019)
      ·
        refine ⟨22243012674099341970190529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14828675116066227980127019 22243012674099341970190529)
        ·
          refine ⟨16682259505574506477642897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22243012674099341970190529 16682259505574506477642897)
          ·
            refine ⟨12511694629180879858232173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16682259505574506477642897 12511694629180879858232173)
            ·
              refine ⟨4691885485942829946837065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12511694629180879858232173 4691885485942829946837065)
              ·
                refine ⟨3518914114457122460127799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4691885485942829946837065 3518914114457122460127799)
                ·
                  refine ⟨5278371171685683690191699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3518914114457122460127799 5278371171685683690191699)
                  ·
                    refine ⟨7917556757528525535287549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5278371171685683690191699 7917556757528525535287549)
                    ·
                      refine ⟨2969083784073197075732831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7917556757528525535287549 2969083784073197075732831)
                      ·
                        rfl

theorem cell23_5782270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_5782270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782270 prefixEnd_5782270 := by exact prefixLift 5782270
  have htrace : WordTrace (prefixWord ++ tailWord_5782270) baseStart_5782270 baseEnd_5782270 := by
    simpa [prefixWord, tailWord_5782270, baseEnd_5782270] using wordTrace_append hprefix tailTrace_5782270
  have hstable : (prefixWord ++ tailWord_5782270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782270).length < 2 ^ (prefixWord ++ tailWord_5782270).sum := by decide
  have hdescent : baseEnd_5782270 < baseStart_5782270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782315 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 4]
def baseStart_5782315 : Nat := 118140960795 + 5782315 * 2 ^ 59
def prefixEnd_5782315 : Nat := 4983230072969 + 3 ^ 40 * 5782315 * 2
def baseEnd_5782315 : Nat := 2969106890702649399670123

theorem tailTrace_5782315 : CollatzResearch.WordTrace tailWord_5782315 prefixEnd_5782315 2969106890702649399670123 := by
  unfold tailWord_5782315
  simp only [CollatzResearch.WordTrace]
  refine ⟨210898354046667770624972399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140598902697778513749981599 210898354046667770624972399)
  ·
    refine ⟨316347531070001655937458599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210898354046667770624972399 316347531070001655937458599)
    ·
      refine ⟨474521296605002483906187899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316347531070001655937458599 474521296605002483906187899)
      ·
        refine ⟨711781944907503725859281849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474521296605002483906187899 711781944907503725859281849)
        ·
          refine ⟨533836458680627794394461387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 711781944907503725859281849 533836458680627794394461387)
          ·
            refine ⟨800754688020941691591692081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533836458680627794394461387 800754688020941691591692081)
            ·
              refine ⟨600566016015706268693769061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 800754688020941691591692081 600566016015706268693769061)
              ·
                refine ⟨112606128002944925380081699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 600566016015706268693769061 112606128002944925380081699)
                ·
                  refine ⟨168909192004417388070122549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112606128002944925380081699 168909192004417388070122549)
                  ·
                    refine ⟨15835236750414130131573989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 168909192004417388070122549 15835236750414130131573989)
                    ·
                      refine ⟨2969106890702649399670123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15835236750414130131573989 2969106890702649399670123)
                      ·
                        rfl

theorem cell23_5782315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 4].length) (baseStart_5782315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782315 prefixEnd_5782315 := by exact prefixLift 5782315
  have htrace : WordTrace (prefixWord ++ tailWord_5782315) baseStart_5782315 baseEnd_5782315 := by
    simpa [prefixWord, tailWord_5782315, baseEnd_5782315] using wordTrace_append hprefix tailTrace_5782315
  have hstable : (prefixWord ++ tailWord_5782315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782315).length < 2 ^ (prefixWord ++ tailWord_5782315).sum := by decide
  have hdescent : baseEnd_5782315 < baseStart_5782315 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782389 : List Nat := [1, 3, 4, 1, 1, 3, 2, 1, 7]
def baseStart_5782389 : Nat := 118140960795 + 5782389 * 2 ^ 59
def prefixEnd_5782389 : Nat := 4983230072969 + 3 ^ 40 * 5782389 * 2
def baseEnd_5782389 : Nat := 329904987585675790016087

theorem tailTrace_5782389 : CollatzResearch.WordTrace tailWord_5782389 prefixEnd_5782389 329904987585675790016087 := by
  unfold tailWord_5782389
  simp only [CollatzResearch.WordTrace]
  refine ⟨210901053048399681263166221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140600702032266454175444147 210901053048399681263166221)
  ·
    refine ⟨79087894893149880473687333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210901053048399681263166221 79087894893149880473687333)
    ·
      refine ⟨14828980292465602588816375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79087894893149880473687333 14828980292465602588816375)
      ·
        refine ⟨22243470438698403883224563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14828980292465602588816375 22243470438698403883224563)
        ·
          refine ⟨33365205658047605824836845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22243470438698403883224563 33365205658047605824836845)
          ·
            refine ⟨12511952121767852184313817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33365205658047605824836845 12511952121767852184313817)
            ·
              refine ⟨9383964091325889138235363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12511952121767852184313817 9383964091325889138235363)
              ·
                refine ⟨14075946136988833707353045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9383964091325889138235363 14075946136988833707353045)
                ·
                  refine ⟨329904987585675790016087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14075946136988833707353045 329904987585675790016087)
                  ·
                    rfl

theorem cell23_5782389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_5782389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782389 prefixEnd_5782389 := by exact prefixLift 5782389
  have htrace : WordTrace (prefixWord ++ tailWord_5782389) baseStart_5782389 baseEnd_5782389 := by
    simpa [prefixWord, tailWord_5782389, baseEnd_5782389] using wordTrace_append hprefix tailTrace_5782389
  have hstable : (prefixWord ++ tailWord_5782389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782389).length < 2 ^ (prefixWord ++ tailWord_5782389).sum := by decide
  have hdescent : baseEnd_5782389 < baseStart_5782389 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782476 : List Nat := [2, 2, 1, 4, 1, 1, 4, 1, 2, 2, 3]
def baseStart_5782476 : Nat := 118140960795 + 5782476 * 2 ^ 59
def prefixEnd_5782476 : Nat := 4983230072969 + 3 ^ 40 * 5782476 * 2
def baseEnd_5782476 : Nat := 2969189561088023269756883

theorem tailTrace_5782476 : CollatzResearch.WordTrace tailWord_5782476 prefixEnd_5782476 2969189561088023269756883 := by
  unfold tailWord_5782476
  simp only [CollatzResearch.WordTrace]
  refine ⟨105452113099542247560791641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140602817466056330081055521 105452113099542247560791641)
  ·
    refine ⟨79089084824656685670593731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105452113099542247560791641 79089084824656685670593731)
    ·
      refine ⟨118633627236985028505890597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79089084824656685670593731 118633627236985028505890597)
      ·
        refine ⟨22243805106934692844854487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118633627236985028505890597 22243805106934692844854487)
        ·
          refine ⟨33365707660402039267281731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22243805106934692844854487 33365707660402039267281731)
          ·
            refine ⟨50048561490603058900922597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33365707660402039267281731 50048561490603058900922597)
            ·
              refine ⟨9384105279488073543922987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50048561490603058900922597 9384105279488073543922987)
              ·
                refine ⟨14076157919232110315884481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9384105279488073543922987 14076157919232110315884481)
                ·
                  refine ⟨10557118439424082736913361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14076157919232110315884481 10557118439424082736913361)
                  ·
                    refine ⟨7917838829568062052685021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10557118439424082736913361 7917838829568062052685021)
                    ·
                      refine ⟨2969189561088023269756883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7917838829568062052685021 2969189561088023269756883)
                      ·
                        rfl

theorem cell23_5782476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_5782476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782476 prefixEnd_5782476 := by exact prefixLift 5782476
  have htrace : WordTrace (prefixWord ++ tailWord_5782476) baseStart_5782476 baseEnd_5782476 := by
    simpa [prefixWord, tailWord_5782476, baseEnd_5782476] using wordTrace_append hprefix tailTrace_5782476
  have hstable : (prefixWord ++ tailWord_5782476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782476).length < 2 ^ (prefixWord ++ tailWord_5782476).sum := by decide
  have hdescent : baseEnd_5782476 < baseStart_5782476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782539 : List Nat := [1, 1, 1, 1, 6, 2, 2, 2, 1, 6]
def baseStart_5782539 : Nat := 118140960795 + 5782539 * 2 ^ 59
def prefixEnd_5782539 : Nat := 4983230072969 + 3 ^ 40 * 5782539 * 2
def baseEnd_5782539 : Nat := 989740636789752174423031

theorem tailTrace_5782539 : CollatzResearch.WordTrace tailWord_5782539 prefixEnd_5782539 989740636789752174423031 := by
  unfold tailWord_5782539
  simp only [CollatzResearch.WordTrace]
  refine ⟨210906523997856256881126671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140604349331904171254084447 210906523997856256881126671)
  ·
    refine ⟨316359785996784385321690007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210906523997856256881126671 316359785996784385321690007)
    ·
      refine ⟨474539678995176577982535011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316359785996784385321690007 474539678995176577982535011)
      ·
        refine ⟨711809518492764866973802517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474539678995176577982535011 711809518492764866973802517)
        ·
          refine ⟨33366071179348353139396993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 711809518492764866973802517 33366071179348353139396993)
          ·
            refine ⟨25024553384511264854547745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33366071179348353139396993 25024553384511264854547745)
            ·
              refine ⟨18768415038383448640910809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25024553384511264854547745 18768415038383448640910809)
              ·
                refine ⟨14076311278787586480683107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18768415038383448640910809 14076311278787586480683107)
                ·
                  refine ⟨21114466918181379721024661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14076311278787586480683107 21114466918181379721024661)
                  ·
                    refine ⟨989740636789752174423031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21114466918181379721024661 989740636789752174423031)
                    ·
                      rfl

theorem cell23_5782539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 2, 1, 6].length) (baseStart_5782539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782539 prefixEnd_5782539 := by exact prefixLift 5782539
  have htrace : WordTrace (prefixWord ++ tailWord_5782539) baseStart_5782539 baseEnd_5782539 := by
    simpa [prefixWord, tailWord_5782539, baseEnd_5782539] using wordTrace_append hprefix tailTrace_5782539
  have hstable : (prefixWord ++ tailWord_5782539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782539).length < 2 ^ (prefixWord ++ tailWord_5782539).sum := by decide
  have hdescent : baseEnd_5782539 < baseStart_5782539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782540 : List Nat := [2, 2, 1, 2, 3, 3, 2, 3, 1, 1, 3]
def baseStart_5782540 : Nat := 118140960795 + 5782540 * 2 ^ 59
def prefixEnd_5782540 : Nat := 4983230072969 + 3 ^ 40 * 5782540 * 2
def baseEnd_5782540 : Nat := 2969222423849911019356589

theorem tailTrace_5782540 : CollatzResearch.WordTrace tailWord_5782540 prefixEnd_5782540 2969222423849911019356589 := by
  unfold tailWord_5782540
  simp only [CollatzResearch.WordTrace]
  refine ⟨105453280235426317025956537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140604373647235089367942049 105453280235426317025956537)
  ·
    refine ⟨79089960176569737769467403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105453280235426317025956537 79089960176569737769467403)
    ·
      refine ⟨118634940264854606654201105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79089960176569737769467403 118634940264854606654201105)
      ·
        refine ⟨88976205198640954990650829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118634940264854606654201105 88976205198640954990650829)
        ·
          refine ⟨33366076949490358121494061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88976205198640954990650829 33366076949490358121494061)
          ·
            refine ⟨12512278856058884295560273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33366076949490358121494061 12512278856058884295560273)
            ·
              refine ⟨9384209142044163221670205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12512278856058884295560273 9384209142044163221670205)
              ·
                refine ⟨3519078428266561208126327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9384209142044163221670205 3519078428266561208126327)
                ·
                  refine ⟨5278617642399841812189491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519078428266561208126327 5278617642399841812189491)
                  ·
                    refine ⟨7917926463599762718284237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5278617642399841812189491 7917926463599762718284237)
                    ·
                      refine ⟨2969222423849911019356589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7917926463599762718284237 2969222423849911019356589)
                      ·
                        rfl

theorem cell23_5782540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_5782540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782540 prefixEnd_5782540 := by exact prefixLift 5782540
  have htrace : WordTrace (prefixWord ++ tailWord_5782540) baseStart_5782540 baseEnd_5782540 := by
    simpa [prefixWord, tailWord_5782540, baseEnd_5782540] using wordTrace_append hprefix tailTrace_5782540
  have hstable : (prefixWord ++ tailWord_5782540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782540).length < 2 ^ (prefixWord ++ tailWord_5782540).sum := by decide
  have hdescent : baseEnd_5782540 < baseStart_5782540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782563 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 3, 2, 2]
def baseStart_5782563 : Nat := 118140960795 + 5782563 * 2 ^ 59
def prefixEnd_5782563 : Nat := 4983230072969 + 3 ^ 40 * 5782563 * 2
def baseEnd_5782563 : Nat := 2969234233904964429368983

theorem tailTrace_5782563 : CollatzResearch.WordTrace tailWord_5782563 prefixEnd_5782563 2969234233904964429368983 := by
  unfold tailWord_5782563
  simp only [CollatzResearch.WordTrace]
  refine ⟨210907399349769308980000343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140604932899846205986666895 210907399349769308980000343)
  ·
    refine ⟨316361099024653963470000515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210907399349769308980000343 316361099024653963470000515)
    ·
      refine ⟨474541648536980945205000773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316361099024653963470000515 474541648536980945205000773)
      ·
        refine ⟨88976559100683927225937645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 474541648536980945205000773 88976559100683927225937645)
        ·
          refine ⟨33366209662756472709726617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88976559100683927225937645 33366209662756472709726617)
          ·
            refine ⟨25024657247067354532294963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33366209662756472709726617 25024657247067354532294963)
            ·
              refine ⟨37536985870601031798442445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25024657247067354532294963 37536985870601031798442445)
              ·
                refine ⟨14076369701475386924415917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37536985870601031798442445 14076369701475386924415917)
                ·
                  refine ⟨5278638638053270096655969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14076369701475386924415917 5278638638053270096655969)
                  ·
                    refine ⟨3958978978539952572491977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5278638638053270096655969 3958978978539952572491977)
                    ·
                      refine ⟨2969234233904964429368983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3958978978539952572491977 2969234233904964429368983)
                      ·
                        rfl

theorem cell23_5782563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 3, 2, 2].length) (baseStart_5782563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782563 prefixEnd_5782563 := by exact prefixLift 5782563
  have htrace : WordTrace (prefixWord ++ tailWord_5782563) baseStart_5782563 baseEnd_5782563 := by
    simpa [prefixWord, tailWord_5782563, baseEnd_5782563] using wordTrace_append hprefix tailTrace_5782563
  have hstable : (prefixWord ++ tailWord_5782563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782563).length < 2 ^ (prefixWord ++ tailWord_5782563).sum := by decide
  have hdescent : baseEnd_5782563 < baseStart_5782563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782580 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 1, 1, 4]
def baseStart_5782580 : Nat := 118140960795 + 5782580 * 2 ^ 59
def prefixEnd_5782580 : Nat := 4983230072969 + 3 ^ 40 * 5782580 * 2
def baseEnd_5782580 : Nat := 2969242963076090862856405

theorem tailTrace_5782580 : CollatzResearch.WordTrace tailWord_5782580 prefixEnd_5782580 2969242963076090862856405 := by
  unfold tailWord_5782580
  simp only [CollatzResearch.WordTrace]
  refine ⟨105454009695353860441684597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140605346260471813922246129 105454009695353860441684597)
  ·
    refine ⟨9886313408939424416407931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105454009695353860441684597 9886313408939424416407931)
    ·
      refine ⟨14829470113409136624611897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9886313408939424416407931 14829470113409136624611897)
      ·
        refine ⟨11122102585056852468458923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14829470113409136624611897 11122102585056852468458923)
        ·
          refine ⟨16683153877585278702688385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11122102585056852468458923 16683153877585278702688385)
          ·
            refine ⟨12512365408188959027016289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16683153877585278702688385 12512365408188959027016289)
            ·
              refine ⟨9384274056141719270262217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12512365408188959027016289 9384274056141719270262217)
              ·
                refine ⟨7038205542106289452696663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9384274056141719270262217 7038205542106289452696663)
                ·
                  refine ⟨10557308313159434179044995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7038205542106289452696663 10557308313159434179044995)
                  ·
                    refine ⟨15835962469739151268567493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10557308313159434179044995 15835962469739151268567493)
                    ·
                      refine ⟨2969242963076090862856405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15835962469739151268567493 2969242963076090862856405)
                      ·
                        rfl

theorem cell23_5782580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_5782580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782580 prefixEnd_5782580 := by exact prefixLift 5782580
  have htrace : WordTrace (prefixWord ++ tailWord_5782580) baseStart_5782580 baseEnd_5782580 := by
    simpa [prefixWord, tailWord_5782580, baseEnd_5782580] using wordTrace_append hprefix tailTrace_5782580
  have hstable : (prefixWord ++ tailWord_5782580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782580).length < 2 ^ (prefixWord ++ tailWord_5782580).sum := by decide
  have hdescent : baseEnd_5782580 < baseStart_5782580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782613 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_5782613 : Nat := 118140960795 + 5782613 * 2 ^ 59
def prefixEnd_5782613 : Nat := 4983230072969 + 3 ^ 40 * 5782613 * 2
def baseEnd_5782613 : Nat := 2969259907937689233743753

theorem tailTrace_5782613 : CollatzResearch.WordTrace tailWord_5782613 prefixEnd_5782613 2969259907937689233743753 := by
  unfold tailWord_5782613
  simp only [CollatzResearch.WordTrace]
  refine ⟨210909222999588167519320493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140606148666392111679546995 210909222999588167519320493)
  ·
    refine ⟨79090958624845562819745185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210909222999588167519320493 79090958624845562819745185)
    ·
      refine ⟨59318218968634172114808889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79090958624845562819745185 59318218968634172114808889)
      ·
        refine ⟨44488664226475629086106667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59318218968634172114808889 44488664226475629086106667)
        ·
          refine ⟨66732996339713443629160001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44488664226475629086106667 66732996339713443629160001)
          ·
            refine ⟨50049747254785082721870001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66732996339713443629160001 50049747254785082721870001)
            ·
              refine ⟨37537310441088812041402501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50049747254785082721870001 37537310441088812041402501)
              ·
                refine ⟨7038245707704152257762969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37537310441088812041402501 7038245707704152257762969)
                ·
                  refine ⟨5278684280778114193322227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7038245707704152257762969 5278684280778114193322227)
                  ·
                    refine ⟨7918026421167171289983341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5278684280778114193322227 7918026421167171289983341)
                    ·
                      refine ⟨2969259907937689233743753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7918026421167171289983341 2969259907937689233743753)
                      ·
                        rfl

theorem cell23_5782613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_5782613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782613 prefixEnd_5782613 := by exact prefixLift 5782613
  have htrace : WordTrace (prefixWord ++ tailWord_5782613) baseStart_5782613 baseEnd_5782613 := by
    simpa [prefixWord, tailWord_5782613, baseEnd_5782613] using wordTrace_append hprefix tailTrace_5782613
  have hstable : (prefixWord ++ tailWord_5782613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782613).length < 2 ^ (prefixWord ++ tailWord_5782613).sum := by decide
  have hdescent : baseEnd_5782613 < baseStart_5782613 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782629 : List Nat := [1, 3, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_5782629 : Nat := 118140960795 + 5782629 * 2 ^ 59
def prefixEnd_5782629 : Nat := 4983230072969 + 3 ^ 40 * 5782629 * 2
def baseEnd_5782629 : Nat := 989756041209387057047893

theorem tailTrace_5782629 : CollatzResearch.WordTrace tailWord_5782629 prefixEnd_5782629 989756041209387057047893 := by
  unfold tailWord_5782629
  simp only [CollatzResearch.WordTrace]
  refine ⟨210909806567530202251902941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140606537711686801501268627 210909806567530202251902941)
  ·
    refine ⟨79091177462823825844463603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210909806567530202251902941 79091177462823825844463603)
    ·
      refine ⟨118636766194235738766695405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79091177462823825844463603 118636766194235738766695405)
      ·
        refine ⟨44488787322838402037510777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118636766194235738766695405 44488787322838402037510777)
        ·
          refine ⟨33366590492128801528133083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44488787322838402037510777 33366590492128801528133083)
          ·
            refine ⟨50049885738193202292199625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33366590492128801528133083 50049885738193202292199625)
            ·
              refine ⟨37537414303644901719149719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50049885738193202292199625 37537414303644901719149719)
              ·
                refine ⟨56306121455467352578724579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37537414303644901719149719 56306121455467352578724579)
                ·
                  refine ⟨84459182183201028868086869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56306121455467352578724579 84459182183201028868086869)
                  ·
                    refine ⟨989756041209387057047893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84459182183201028868086869 989756041209387057047893)
                    ·
                      rfl

theorem cell23_5782629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_5782629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782629 prefixEnd_5782629 := by exact prefixLift 5782629
  have htrace : WordTrace (prefixWord ++ tailWord_5782629) baseStart_5782629 baseEnd_5782629 := by
    simpa [prefixWord, tailWord_5782629, baseEnd_5782629] using wordTrace_append hprefix tailTrace_5782629
  have hstable : (prefixWord ++ tailWord_5782629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782629).length < 2 ^ (prefixWord ++ tailWord_5782629).sum := by decide
  have hdescent : baseEnd_5782629 < baseStart_5782629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782639 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 5]
def baseStart_5782639 : Nat := 118140960795 + 5782639 * 2 ^ 59
def prefixEnd_5782639 : Nat := 4983230072969 + 3 ^ 40 * 5782639 * 2
def baseEnd_5782639 : Nat := 2969273258434706132018633

theorem tailTrace_5782639 : CollatzResearch.WordTrace tailWord_5782639 prefixEnd_5782639 2969273258434706132018633 := by
  unfold tailWord_5782639
  simp only [CollatzResearch.WordTrace]
  refine ⟨210910171297493973959766971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140606780864995982639844647 210910171297493973959766971)
  ·
    refine ⟨316365256946240960939650457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210910171297493973959766971 316365256946240960939650457)
    ·
      refine ⟨237273942709680720704737843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316365256946240960939650457 237273942709680720704737843)
      ·
        refine ⟨355910914064521081057106765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237273942709680720704737843 355910914064521081057106765)
        ·
          refine ⟨133466592774195405396415037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355910914064521081057106765 133466592774195405396415037)
          ·
            refine ⟨50049972290323277023655639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133466592774195405396415037 50049972290323277023655639)
            ·
              refine ⟨75074958435484915535483459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50049972290323277023655639 75074958435484915535483459)
              ·
                refine ⟨112612437653227373303225189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75074958435484915535483459 112612437653227373303225189)
                ·
                  refine ⟨21114832059980132494354723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112612437653227373303225189 21114832059980132494354723)
                  ·
                    refine ⟨31672248089970198741532085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21114832059980132494354723 31672248089970198741532085)
                    ·
                      refine ⟨2969273258434706132018633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31672248089970198741532085 2969273258434706132018633)
                      ·
                        rfl

theorem cell23_5782639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 5].length) (baseStart_5782639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782639 prefixEnd_5782639 := by exact prefixLift 5782639
  have htrace : WordTrace (prefixWord ++ tailWord_5782639) baseStart_5782639 baseEnd_5782639 := by
    simpa [prefixWord, tailWord_5782639, baseEnd_5782639] using wordTrace_append hprefix tailTrace_5782639
  have hstable : (prefixWord ++ tailWord_5782639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782639).length < 2 ^ (prefixWord ++ tailWord_5782639).sum := by decide
  have hdescent : baseEnd_5782639 < baseStart_5782639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782653 : List Nat := [1, 4, 1, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_5782653 : Nat := 118140960795 + 5782653 * 2 ^ 59
def prefixEnd_5782653 : Nat := 4983230072969 + 3 ^ 40 * 5782653 * 2
def baseEnd_5782653 : Nat := 2969280447163869077243569

theorem tailTrace_5782653 : CollatzResearch.WordTrace tailWord_5782653 prefixEnd_5782653 2969280447163869077243569 := by
  unfold tailWord_5782653
  simp only [CollatzResearch.WordTrace]
  refine ⟨210910681919443254350776613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140607121279628836233851075 210910681919443254350776613)
  ·
    refine ⟨39545752859895610190770615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210910681919443254350776613 39545752859895610190770615)
    ·
      refine ⟨59318629289843415286155923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39545752859895610190770615 59318629289843415286155923)
      ·
        refine ⟨88977943934765122929233885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59318629289843415286155923 88977943934765122929233885)
        ·
          refine ⟨33366728975536921098462707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88977943934765122929233885 33366728975536921098462707)
          ·
            refine ⟨50050093463305381647694061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33366728975536921098462707 50050093463305381647694061)
            ·
              refine ⟨18768785048739518117885273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50050093463305381647694061 18768785048739518117885273)
              ·
                refine ⟨14076588786554638588413955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18768785048739518117885273 14076588786554638588413955)
                ·
                  refine ⟨21114883179831957882620933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14076588786554638588413955 21114883179831957882620933)
                  ·
                    refine ⟨3959040596218492102991425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21114883179831957882620933 3959040596218492102991425)
                    ·
                      refine ⟨2969280447163869077243569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959040596218492102991425 2969280447163869077243569)
                      ·
                        rfl

theorem cell23_5782653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_5782653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782653 prefixEnd_5782653 := by exact prefixLift 5782653
  have htrace : WordTrace (prefixWord ++ tailWord_5782653) baseStart_5782653 baseEnd_5782653 := by
    simpa [prefixWord, tailWord_5782653, baseEnd_5782653] using wordTrace_append hprefix tailTrace_5782653
  have hstable : (prefixWord ++ tailWord_5782653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782653).length < 2 ^ (prefixWord ++ tailWord_5782653).sum := by decide
  have hdescent : baseEnd_5782653 < baseStart_5782653 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782657 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_5782657 : Nat := 118140960795 + 5782657 * 2 ^ 59
def prefixEnd_5782657 : Nat := 4983230072969 + 3 ^ 40 * 5782657 * 2
def baseEnd_5782657 : Nat := 2969282501086487061593551

theorem tailTrace_5782657 : CollatzResearch.WordTrace tailWord_5782657 prefixEnd_5782657 2969282501086487061593551 := by
  unfold tailWord_5782657
  simp only [CollatzResearch.WordTrace]
  refine ⟨210910827811428763033922225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140607218540952508689281483 210910827811428763033922225)
  ·
    refine ⟨158183120858571572275441669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210910827811428763033922225 158183120858571572275441669)
    ·
      refine ⟨29659335160982169801645313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158183120858571572275441669 29659335160982169801645313)
      ·
        refine ⟨22244501370736627351233985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29659335160982169801645313 22244501370736627351233985)
        ·
          refine ⟨16683376028052470513425489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22244501370736627351233985 16683376028052470513425489)
          ·
            refine ⟨12512532021039352885069117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16683376028052470513425489 12512532021039352885069117)
            ·
              refine ⟨4692199507889757331900919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12512532021039352885069117 4692199507889757331900919)
              ·
                refine ⟨7038299261834635997851379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4692199507889757331900919 7038299261834635997851379)
                ·
                  refine ⟨10557448892751953996777069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7038299261834635997851379 10557448892751953996777069)
                  ·
                    refine ⟨3959043334781982748791401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10557448892751953996777069 3959043334781982748791401)
                    ·
                      refine ⟨2969282501086487061593551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959043334781982748791401 2969282501086487061593551)
                      ·
                        rfl

theorem cell23_5782657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_5782657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782657 prefixEnd_5782657 := by exact prefixLift 5782657
  have htrace : WordTrace (prefixWord ++ tailWord_5782657) baseStart_5782657 baseEnd_5782657 := by
    simpa [prefixWord, tailWord_5782657, baseEnd_5782657] using wordTrace_append hprefix tailTrace_5782657
  have hstable : (prefixWord ++ tailWord_5782657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782657).length < 2 ^ (prefixWord ++ tailWord_5782657).sum := by decide
  have hdescent : baseEnd_5782657 < baseStart_5782657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782666 : List Nat := [3, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4]
def baseStart_5782666 : Nat := 118140960795 + 5782666 * 2 ^ 59
def prefixEnd_5782666 : Nat := 4983230072969 + 3 ^ 40 * 5782666 * 2
def baseEnd_5782666 : Nat := 2969287122412377526381009

theorem tailTrace_5782666 : CollatzResearch.WordTrace tailWord_5782666 prefixEnd_5782666 2969287122412377526381009 := by
  unfold tailWord_5782666
  simp only [CollatzResearch.WordTrace]
  refine ⟨52727789017099039392749963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140607437378930771713999901 52727789017099039392749963)
  ·
    refine ⟨79091683525648559089124945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52727789017099039392749963 79091683525648559089124945)
    ·
      refine ⟨59318762644236419316843709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79091683525648559089124945 59318762644236419316843709)
      ·
        refine ⟨22244535991588657243816391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59318762644236419316843709 22244535991588657243816391)
        ·
          refine ⟨33366803987382985865724587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22244535991588657243816391 33366803987382985865724587)
          ·
            refine ⟨50050205981074478798586881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33366803987382985865724587 50050205981074478798586881)
            ·
              refine ⟨37537654485805859098940161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50050205981074478798586881 37537654485805859098940161)
              ·
                refine ⟨28153240864354394324205121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37537654485805859098940161 28153240864354394324205121)
                ·
                  refine ⟨21114930648265795743153841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28153240864354394324205121 21114930648265795743153841)
                  ·
                    refine ⟨15836197986199346807365381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21114930648265795743153841 15836197986199346807365381)
                    ·
                      refine ⟨2969287122412377526381009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15836197986199346807365381 2969287122412377526381009)
                      ·
                        rfl

theorem cell23_5782666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_5782666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782666 prefixEnd_5782666 := by exact prefixLift 5782666
  have htrace : WordTrace (prefixWord ++ tailWord_5782666) baseStart_5782666 baseEnd_5782666 := by
    simpa [prefixWord, tailWord_5782666, baseEnd_5782666] using wordTrace_append hprefix tailTrace_5782666
  have hstable : (prefixWord ++ tailWord_5782666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782666).length < 2 ^ (prefixWord ++ tailWord_5782666).sum := by decide
  have hdescent : baseEnd_5782666 < baseStart_5782666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782706 : List Nat := [3, 2, 1, 1, 1, 5, 1, 1, 1, 7]
def baseStart_5782706 : Nat := 118140960795 + 5782706 * 2 ^ 59
def prefixEnd_5782706 : Nat := 4983230072969 + 3 ^ 40 * 5782706 * 2
def baseEnd_5782706 : Nat := 989769220546185789960275

theorem tailTrace_5782706 : CollatzResearch.WordTrace tailWord_5782706 prefixEnd_5782706 989769220546185789960275 := by
  unfold tailWord_5782706
  simp only [CollatzResearch.WordTrace]
  refine ⟨52728153747062811100613993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140608409992167496268303981 52728153747062811100613993)
  ·
    refine ⟨39546115310297108325460495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52728153747062811100613993 39546115310297108325460495)
    ·
      refine ⟨59319172965445662488190743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39546115310297108325460495 59319172965445662488190743)
      ·
        refine ⟨88978759448168493732286115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59319172965445662488190743 88978759448168493732286115)
        ·
          refine ⟨133468139172252740598429173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88978759448168493732286115 133468139172252740598429173)
          ·
            refine ⟨12512638047398694431102735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133468139172252740598429173 12512638047398694431102735)
            ·
              refine ⟨18768957071098041646654103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12512638047398694431102735 18768957071098041646654103)
              ·
                refine ⟨28153435606647062469981155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18768957071098041646654103 28153435606647062469981155)
                ·
                  refine ⟨42230153409970593704971733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28153435606647062469981155 42230153409970593704971733)
                  ·
                    refine ⟨989769220546185789960275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42230153409970593704971733 989769220546185789960275)
                    ·
                      rfl

theorem cell23_5782706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_5782706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782706 prefixEnd_5782706 := by exact prefixLift 5782706
  have htrace : WordTrace (prefixWord ++ tailWord_5782706) baseStart_5782706 baseEnd_5782706 := by
    simpa [prefixWord, tailWord_5782706, baseEnd_5782706] using wordTrace_append hprefix tailTrace_5782706
  have hstable : (prefixWord ++ tailWord_5782706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782706).length < 2 ^ (prefixWord ++ tailWord_5782706).sum := by decide
  have hdescent : baseEnd_5782706 < baseStart_5782706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782743 : List Nat := [1, 1, 3, 2, 1, 2, 4, 1, 2, 4, 2]
def baseStart_5782743 : Nat := 118140960795 + 5782743 * 2 ^ 59
def prefixEnd_5782743 : Nat := 4983230072969 + 3 ^ 40 * 5782743 * 2
def baseEnd_5782743 : Nat := 2969326660422773725118155

theorem tailTrace_5782743 : CollatzResearch.WordTrace tailWord_5782743 prefixEnd_5782743 2969326660422773725118155 := by
  unfold tailWord_5782743
  simp only [CollatzResearch.WordTrace]
  refine ⟨210913964489117199721552883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140609309659411466481035255 210913964489117199721552883)
  ·
    refine ⟨316370946733675799582329325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210913964489117199721552883 316370946733675799582329325)
    ·
      refine ⟨118639105025128424843373497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316370946733675799582329325 118639105025128424843373497)
      ·
        refine ⟨88979328768846318632530123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118639105025128424843373497 88979328768846318632530123)
        ·
          refine ⟨133468993153269477948795185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88979328768846318632530123 133468993153269477948795185)
          ·
            refine ⟨100101744864952108461596389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133468993153269477948795185 100101744864952108461596389)
            ·
              refine ⟨18769077162178520336549323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100101744864952108461596389 18769077162178520336549323)
              ·
                refine ⟨28153615743267780504823985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18769077162178520336549323 28153615743267780504823985)
                ·
                  refine ⟨21115211807450835378617989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28153615743267780504823985 21115211807450835378617989)
                  ·
                    refine ⟨3959102213897031633490873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21115211807450835378617989 3959102213897031633490873)
                    ·
                      refine ⟨2969326660422773725118155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959102213897031633490873 2969326660422773725118155)
                      ·
                        rfl

theorem cell23_5782743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_5782743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782743 prefixEnd_5782743 := by exact prefixLift 5782743
  have htrace : WordTrace (prefixWord ++ tailWord_5782743) baseStart_5782743 baseEnd_5782743 := by
    simpa [prefixWord, tailWord_5782743, baseEnd_5782743] using wordTrace_append hprefix tailTrace_5782743
  have hstable : (prefixWord ++ tailWord_5782743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782743).length < 2 ^ (prefixWord ++ tailWord_5782743).sum := by decide
  have hdescent : baseEnd_5782743 < baseStart_5782743 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782753 : List Nat := [1, 2, 3, 1, 3, 2, 2, 2, 3, 4]
def baseStart_5782753 : Nat := 118140960795 + 5782753 * 2 ^ 59
def prefixEnd_5782753 : Nat := 4983230072969 + 3 ^ 40 * 5782753 * 2
def baseEnd_5782753 : Nat := 989777265076439561997703

theorem tailTrace_5782753 : CollatzResearch.WordTrace tailWord_5782753 prefixEnd_5782753 989777265076439561997703 := by
  unfold tailWord_5782753
  simp only [CollatzResearch.WordTrace]
  refine ⟨210914329219080971429416913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140609552812720647619611275 210914329219080971429416913)
  ·
    refine ⟨158185746914310728572062685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210914329219080971429416913 158185746914310728572062685)
    ·
      refine ⟨59319655092866523214523507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158185746914310728572062685 59319655092866523214523507)
      ·
        refine ⟨88979482639299784821785261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59319655092866523214523507 88979482639299784821785261)
        ·
          refine ⟨33367305989737419308169473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88979482639299784821785261 33367305989737419308169473)
          ·
            refine ⟨25025479492303064481127105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33367305989737419308169473 25025479492303064481127105)
            ·
              refine ⟨18769109619227298360845329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25025479492303064481127105 18769109619227298360845329)
              ·
                refine ⟨14076832214420473770633997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18769109619227298360845329 14076832214420473770633997)
                ·
                  refine ⟨5278812080407677663987749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14076832214420473770633997 5278812080407677663987749)
                  ·
                    refine ⟨989777265076439561997703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5278812080407677663987749 989777265076439561997703)
                    ·
                      rfl

theorem cell23_5782753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_5782753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782753 prefixEnd_5782753 := by exact prefixLift 5782753
  have htrace : WordTrace (prefixWord ++ tailWord_5782753) baseStart_5782753 baseEnd_5782753 := by
    simpa [prefixWord, tailWord_5782753, baseEnd_5782753] using wordTrace_append hprefix tailTrace_5782753
  have hstable : (prefixWord ++ tailWord_5782753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782753).length < 2 ^ (prefixWord ++ tailWord_5782753).sum := by decide
  have hdescent : baseEnd_5782753 < baseStart_5782753 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782766 : List Nat := [4, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_5782766 : Nat := 118140960795 + 5782766 * 2 ^ 59
def prefixEnd_5782766 : Nat := 4983230072969 + 3 ^ 40 * 5782766 * 2
def baseEnd_5782766 : Nat := 329926496719758570570061

theorem tailTrace_5782766 : CollatzResearch.WordTrace tailWord_5782766 prefixEnd_5782766 329926496719758570570061 := by
  unfold tailWord_5782766
  simp only [CollatzResearch.WordTrace]
  refine ⟨26364350421004234331205019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140609868912022583099760101 26364350421004234331205019)
  ·
    refine ⟨39546525631506351496807529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26364350421004234331205019 39546525631506351496807529)
    ·
      refine ⟨29659894223629763622605647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39546525631506351496807529 29659894223629763622605647)
      ·
        refine ⟨44489841335444645433908471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29659894223629763622605647 44489841335444645433908471)
        ·
          refine ⟨66734762003166968150862707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44489841335444645433908471 66734762003166968150862707)
          ·
            refine ⟨100102143004750452226294061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66734762003166968150862707 100102143004750452226294061)
            ·
              refine ⟨37538303626781419584860273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100102143004750452226294061 37538303626781419584860273)
              ·
                refine ⟨28153727720086064688645205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37538303626781419584860273 28153727720086064688645205)
                ·
                  refine ⟨329926496719758570570061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28153727720086064688645205 329926496719758570570061)
                  ·
                    rfl

theorem cell23_5782766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_5782766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782766 prefixEnd_5782766 := by exact prefixLift 5782766
  have htrace : WordTrace (prefixWord ++ tailWord_5782766) baseStart_5782766 baseEnd_5782766 := by
    simpa [prefixWord, tailWord_5782766, baseEnd_5782766] using wordTrace_append hprefix tailTrace_5782766
  have hstable : (prefixWord ++ tailWord_5782766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782766).length < 2 ^ (prefixWord ++ tailWord_5782766).sum := by decide
  have hdescent : baseEnd_5782766 < baseStart_5782766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782780 : List Nat := [2, 2, 2, 1, 5, 1, 1, 2, 2, 2, 3]
def baseStart_5782780 : Nat := 118140960795 + 5782780 * 2 ^ 59
def prefixEnd_5782780 : Nat := 4983230072969 + 3 ^ 40 * 5782780 * 2
def baseEnd_5782780 : Nat := 2969345659206990080355485

theorem tailTrace_5782780 : CollatzResearch.WordTrace tailWord_5782780 prefixEnd_5782780 2969345659206990080355485 := by
  unfold tailWord_5782780
  simp only [CollatzResearch.WordTrace]
  refine ⟨105457656994991577520324897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140610209326655436693766529 105457656994991577520324897)
  ·
    refine ⟨79093242746243683140243673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105457656994991577520324897 79093242746243683140243673)
    ·
      refine ⟨59319932059682762355182755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79093242746243683140243673 59319932059682762355182755)
      ·
        refine ⟨88979898089524143532774133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59319932059682762355182755 88979898089524143532774133)
        ·
          refine ⟨8341865445892888456197575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88979898089524143532774133 8341865445892888456197575)
          ·
            refine ⟨12512798168839332684296363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8341865445892888456197575 12512798168839332684296363)
            ·
              refine ⟨18769197253258999026444545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12512798168839332684296363 18769197253258999026444545)
              ·
                refine ⟨14076897939944249269833409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18769197253258999026444545 14076897939944249269833409)
                ·
                  refine ⟨10557673454958186952375057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14076897939944249269833409 10557673454958186952375057)
                  ·
                    refine ⟨7918255091218640214281293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10557673454958186952375057 7918255091218640214281293)
                    ·
                      refine ⟨2969345659206990080355485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7918255091218640214281293 2969345659206990080355485)
                      ·
                        rfl

theorem cell23_5782780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_5782780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782780 prefixEnd_5782780 := by exact prefixLift 5782780
  have htrace : WordTrace (prefixWord ++ tailWord_5782780) baseStart_5782780 baseEnd_5782780 := by
    simpa [prefixWord, tailWord_5782780, baseEnd_5782780] using wordTrace_append hprefix tailTrace_5782780
  have hstable : (prefixWord ++ tailWord_5782780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782780).length < 2 ^ (prefixWord ++ tailWord_5782780).sum := by decide
  have hdescent : baseEnd_5782780 < baseStart_5782780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782787 : List Nat := [1, 1, 1, 3, 2, 5, 3, 2, 1, 4]
def baseStart_5782787 : Nat := 118140960795 + 5782787 * 2 ^ 59
def prefixEnd_5782787 : Nat := 4983230072969 + 3 ^ 40 * 5782787 * 2
def baseEnd_5782787 : Nat := 989783084523857184322651

theorem tailTrace_5782787 : CollatzResearch.WordTrace tailWord_5782787 prefixEnd_5782787 989783084523857184322651 := by
  unfold tailWord_5782787
  simp only [CollatzResearch.WordTrace]
  refine ⟨210915569300957795236154615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140610379533971863490769743 210915569300957795236154615)
  ·
    refine ⟨316373353951436692854231923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210915569300957795236154615 316373353951436692854231923)
    ·
      refine ⟨474560030927155039281347885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316373353951436692854231923 474560030927155039281347885)
      ·
        refine ⟨177960011597683139730505457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474560030927155039281347885 177960011597683139730505457)
        ·
          refine ⟨133470008698262354797879093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177960011597683139730505457 133470008698262354797879093)
          ·
            refine ⟨12512813315462095762301165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133470008698262354797879093 12512813315462095762301165)
            ·
              refine ⟨4692304993298285910862937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12512813315462095762301165 4692304993298285910862937)
              ·
                refine ⟨3519228744973714433147203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4692304993298285910862937 3519228744973714433147203)
                ·
                  refine ⟨5278843117460571649720805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519228744973714433147203 5278843117460571649720805)
                  ·
                    refine ⟨989783084523857184322651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5278843117460571649720805 989783084523857184322651)
                    ·
                      rfl

theorem cell23_5782787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 2, 1, 4].length) (baseStart_5782787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782787 prefixEnd_5782787 := by exact prefixLift 5782787
  have htrace : WordTrace (prefixWord ++ tailWord_5782787) baseStart_5782787 baseEnd_5782787 := by
    simpa [prefixWord, tailWord_5782787, baseEnd_5782787] using wordTrace_append hprefix tailTrace_5782787
  have hstable : (prefixWord ++ tailWord_5782787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782787).length < 2 ^ (prefixWord ++ tailWord_5782787).sum := by decide
  have hdescent : baseEnd_5782787 < baseStart_5782787 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782814 : List Nat := [4, 3, 2, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_5782814 : Nat := 118140960795 + 5782814 * 2 ^ 59
def prefixEnd_5782814 : Nat := 4983230072969 + 3 ^ 40 * 5782814 * 2
def baseEnd_5782814 : Nat := 2969363117549242947330329

theorem tailTrace_5782814 : CollatzResearch.WordTrace tailWord_5782814 prefixEnd_5782814 2969363117549242947330329 := by
  unfold tailWord_5782814
  simp only [CollatzResearch.WordTrace]
  refine ⟨26364569258982497355923437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140611036047906652564924997 26364569258982497355923437)
  ·
    refine ⟨9886713472118436508471289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26364569258982497355923437 9886713472118436508471289)
    ·
      refine ⟨7415035104088827381353467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9886713472118436508471289 7415035104088827381353467)
      ·
        refine ⟨11122552656133241072030201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415035104088827381353467 11122552656133241072030201)
        ·
          refine ⟨8341914492099930804022651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11122552656133241072030201 8341914492099930804022651)
          ·
            refine ⟨12512871738149896206033977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8341914492099930804022651 12512871738149896206033977)
            ·
              refine ⟨9384653803612422154525483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12512871738149896206033977 9384653803612422154525483)
              ·
                refine ⟨14076980705418633231788225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9384653803612422154525483 14076980705418633231788225)
                ·
                  refine ⟨10557735529063974923841169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14076980705418633231788225 10557735529063974923841169)
                  ·
                    refine ⟨7918301646797981192880877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10557735529063974923841169 7918301646797981192880877)
                    ·
                      refine ⟨2969363117549242947330329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7918301646797981192880877 2969363117549242947330329)
                      ·
                        rfl

theorem cell23_5782814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_5782814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782814 prefixEnd_5782814 := by exact prefixLift 5782814
  have htrace : WordTrace (prefixWord ++ tailWord_5782814) baseStart_5782814 baseEnd_5782814 := by
    simpa [prefixWord, tailWord_5782814, baseEnd_5782814] using wordTrace_append hprefix tailTrace_5782814
  have hstable : (prefixWord ++ tailWord_5782814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782814).length < 2 ^ (prefixWord ++ tailWord_5782814).sum := by decide
  have hdescent : baseEnd_5782814 < baseStart_5782814 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782838 : List Nat := [5, 1, 2, 3, 1, 2, 2, 2, 1, 4]
def baseStart_5782838 : Nat := 118140960795 + 5782838 * 2 ^ 59
def prefixEnd_5782838 : Nat := 4983230072969 + 3 ^ 40 * 5782838 * 2
def baseEnd_5782838 : Nat := 989791813694983617810073

theorem tailTrace_5782838 : CollatzResearch.WordTrace tailWord_5782838 prefixEnd_5782838 989791813694983617810073 := by
  unfold tailWord_5782838
  simp only [CollatzResearch.WordTrace]
  refine ⟨13182339338985814434141323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140611619615848687297507445 13182339338985814434141323)
  ·
    refine ⟨19773509008478721651211985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13182339338985814434141323 19773509008478721651211985)
    ·
      refine ⟨14830131756359041238408989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19773509008478721651211985 14830131756359041238408989)
      ·
        refine ⟨5561299408634640464403371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14830131756359041238408989 5561299408634640464403371)
        ·
          refine ⟨8341949112951960696605057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5561299408634640464403371 8341949112951960696605057)
          ·
            refine ⟨6256461834713970522453793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8341949112951960696605057 6256461834713970522453793)
            ·
              refine ⟨4692346376035477891840345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6256461834713970522453793 4692346376035477891840345)
              ·
                refine ⟨3519259782026608418880259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4692346376035477891840345 3519259782026608418880259)
                ·
                  refine ⟨5278889673039912628320389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519259782026608418880259 5278889673039912628320389)
                  ·
                    refine ⟨989791813694983617810073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5278889673039912628320389 989791813694983617810073)
                    ·
                      rfl

theorem cell23_5782838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_5782838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782838 prefixEnd_5782838 := by exact prefixLift 5782838
  have htrace : WordTrace (prefixWord ++ tailWord_5782838) baseStart_5782838 baseEnd_5782838 := by
    simpa [prefixWord, tailWord_5782838, baseEnd_5782838] using wordTrace_append hprefix tailTrace_5782838
  have hstable : (prefixWord ++ tailWord_5782838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782838).length < 2 ^ (prefixWord ++ tailWord_5782838).sum := by decide
  have hdescent : baseEnd_5782838 < baseStart_5782838 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782844 : List Nat := [2, 2, 2, 2, 1, 3, 4, 2, 1, 1, 3]
def baseStart_5782844 : Nat := 118140960795 + 5782844 * 2 ^ 59
def prefixEnd_5782844 : Nat := 4983230072969 + 3 ^ 40 * 5782844 * 2
def baseEnd_5782844 : Nat := 2969378521968877829955191

theorem tailTrace_5782844 : CollatzResearch.WordTrace tailWord_5782844 prefixEnd_5782844 2969378521968877829955191 := by
  unfold tailWord_5782844
  simp only [CollatzResearch.WordTrace]
  refine ⟨105458824130875646985489793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140611765507834195980653057 105458824130875646985489793)
  ·
    refine ⟨79094118098156735239117345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105458824130875646985489793 79094118098156735239117345)
    ·
      refine ⟨59320588573617551429338009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79094118098156735239117345 59320588573617551429338009)
      ·
        refine ⟨44490441430213163572003507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59320588573617551429338009 44490441430213163572003507)
        ·
          refine ⟨66735662145319745358005261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44490441430213163572003507 66735662145319745358005261)
          ·
            refine ⟨25025873304494904509251973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66735662145319745358005261 25025873304494904509251973)
            ·
              refine ⟨4692351244592794595484745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25025873304494904509251973 4692351244592794595484745)
              ·
                refine ⟨3519263433444595946613559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4692351244592794595484745 3519263433444595946613559)
                ·
                  refine ⟨5278895150166893919920339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519263433444595946613559 5278895150166893919920339)
                  ·
                    refine ⟨7918342725250340879880509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5278895150166893919920339 7918342725250340879880509)
                    ·
                      refine ⟨2969378521968877829955191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7918342725250340879880509 2969378521968877829955191)
                      ·
                        rfl

theorem cell23_5782844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_5782844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782844 prefixEnd_5782844 := by exact prefixLift 5782844
  have htrace : WordTrace (prefixWord ++ tailWord_5782844) baseStart_5782844 baseEnd_5782844 := by
    simpa [prefixWord, tailWord_5782844, baseEnd_5782844] using wordTrace_append hprefix tailTrace_5782844
  have hstable : (prefixWord ++ tailWord_5782844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782844).length < 2 ^ (prefixWord ++ tailWord_5782844).sum := by decide
  have hdescent : baseEnd_5782844 < baseStart_5782844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782860 : List Nat := [2, 2, 1, 3, 2, 2, 2, 3, 2, 4]
def baseStart_5782860 : Nat := 118140960795 + 5782860 * 2 ^ 59
def prefixEnd_5782860 : Nat := 4983230072969 + 3 ^ 40 * 5782860 * 2
def baseEnd_5782860 : Nat := 989795579219783255785039

theorem tailTrace_5782860 : CollatzResearch.WordTrace tailWord_5782860 prefixEnd_5782860 989795579219783255785039 := by
  unfold tailWord_5782860
  simp only [CollatzResearch.WordTrace]
  refine ⟨105459115914846664351781017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140612154553128885802374689 105459115914846664351781017)
  ·
    refine ⟨79094336936134998263835763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105459115914846664351781017 79094336936134998263835763)
    ·
      refine ⟨118641505404202497395753645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79094336936134998263835763 118641505404202497395753645)
      ·
        refine ⟨44490564526575936523407617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118641505404202497395753645 44490564526575936523407617)
        ·
          refine ⟨33367923394931952392555713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44490564526575936523407617 33367923394931952392555713)
          ·
            refine ⟨25025942546198964294416785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33367923394931952392555713 25025942546198964294416785)
            ·
              refine ⟨18769456909649223220812589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25025942546198964294416785 18769456909649223220812589)
              ·
                refine ⟨7038546341118458707804721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18769456909649223220812589 7038546341118458707804721)
                ·
                  refine ⟨5278909755838844030853541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7038546341118458707804721 5278909755838844030853541)
                  ·
                    refine ⟨989795579219783255785039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5278909755838844030853541 989795579219783255785039)
                    ·
                      rfl

theorem cell23_5782860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 3, 2, 4].length) (baseStart_5782860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782860 prefixEnd_5782860 := by exact prefixLift 5782860
  have htrace : WordTrace (prefixWord ++ tailWord_5782860) baseStart_5782860 baseEnd_5782860 := by
    simpa [prefixWord, tailWord_5782860, baseEnd_5782860] using wordTrace_append hprefix tailTrace_5782860
  have hstable : (prefixWord ++ tailWord_5782860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782860).length < 2 ^ (prefixWord ++ tailWord_5782860).sum := by decide
  have hdescent : baseEnd_5782860 < baseStart_5782860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782884 : List Nat := [2, 3, 1, 1, 3, 2, 1, 5, 1, 2, 2]
def baseStart_5782884 : Nat := 118140960795 + 5782884 * 2 ^ 59
def prefixEnd_5782884 : Nat := 4983230072969 + 3 ^ 40 * 5782884 * 2
def baseEnd_5782884 : Nat := 2969399061195057673455007

theorem tailTrace_5782884 : CollatzResearch.WordTrace tailWord_5782884 prefixEnd_5782884 2969399061195057673455007 := by
  unfold tailWord_5782884
  simp only [CollatzResearch.WordTrace]
  refine ⟨105459553590803190401217853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140612738121070920534957137 105459553590803190401217853)
  ·
    refine ⟨39547332596551196400456695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105459553590803190401217853 39547332596551196400456695)
    ·
      refine ⟨59320998894826794600685043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39547332596551196400456695 59320998894826794600685043)
      ·
        refine ⟨88981498342240191901027565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59320998894826794600685043 88981498342240191901027565)
        ·
          refine ⟨33368061878340071962885337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88981498342240191901027565 33368061878340071962885337)
          ·
            refine ⟨25026046408755053972164003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33368061878340071962885337 25026046408755053972164003)
            ·
              refine ⟨37539069613132580958246005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25026046408755053972164003 37539069613132580958246005)
              ·
                refine ⟨3519287776231179464835563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37539069613132580958246005 3519287776231179464835563)
                ·
                  refine ⟨5278931664346769197253345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519287776231179464835563 5278931664346769197253345)
                  ·
                    refine ⟨3959198748260076897940009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5278931664346769197253345 3959198748260076897940009)
                    ·
                      refine ⟨2969399061195057673455007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959198748260076897940009 2969399061195057673455007)
                      ·
                        rfl

theorem cell23_5782884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_5782884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782884 prefixEnd_5782884 := by exact prefixLift 5782884
  have htrace : WordTrace (prefixWord ++ tailWord_5782884) baseStart_5782884 baseEnd_5782884 := by
    simpa [prefixWord, tailWord_5782884, baseEnd_5782884] using wordTrace_append hprefix tailTrace_5782884
  have hstable : (prefixWord ++ tailWord_5782884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782884).length < 2 ^ (prefixWord ++ tailWord_5782884).sum := by decide
  have hdescent : baseEnd_5782884 < baseStart_5782884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782887 : List Nat := [1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_5782887 : Nat := 118140960795 + 5782887 * 2 ^ 59
def prefixEnd_5782887 : Nat := 4983230072969 + 3 ^ 40 * 5782887 * 2
def baseEnd_5782887 : Nat := 2969400601637021161717493

theorem tailTrace_5782887 : CollatzResearch.WordTrace tailWord_5782887 prefixEnd_5782887 2969400601637021161717493 := by
  unfold tailWord_5782887
  simp only [CollatzResearch.WordTrace]
  refine ⟨210919216600595512314794915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140612811067063674876529943 210919216600595512314794915)
  ·
    refine ⟨316378824900893268472192373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210919216600595512314794915 316378824900893268472192373)
    ·
      refine ⟨29660514834458743919268035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 316378824900893268472192373 29660514834458743919268035)
      ·
        refine ⟨44490772251688115878902053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29660514834458743919268035 44490772251688115878902053)
        ·
          refine ⟨8342019797191521727294135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44490772251688115878902053 8342019797191521727294135)
          ·
            refine ⟨12513029695787282590941203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8342019797191521727294135 12513029695787282590941203)
            ·
              refine ⟨18769544543680923886411805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12513029695787282590941203 18769544543680923886411805)
              ·
                refine ⟨7038579203880346457404427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18769544543680923886411805 7038579203880346457404427)
                ·
                  refine ⟨10557868805820519686106641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7038579203880346457404427 10557868805820519686106641)
                  ·
                    refine ⟨7918401604365389764579981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10557868805820519686106641 7918401604365389764579981)
                    ·
                      refine ⟨2969400601637021161717493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7918401604365389764579981 2969400601637021161717493)
                      ·
                        rfl

theorem cell23_5782887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_5782887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782887 prefixEnd_5782887 := by exact prefixLift 5782887
  have htrace : WordTrace (prefixWord ++ tailWord_5782887) baseStart_5782887 baseEnd_5782887 := by
    simpa [prefixWord, tailWord_5782887, baseEnd_5782887] using wordTrace_append hprefix tailTrace_5782887
  have hstable : (prefixWord ++ tailWord_5782887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782887).length < 2 ^ (prefixWord ++ tailWord_5782887).sum := by decide
  have hdescent : baseEnd_5782887 < baseStart_5782887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782914 : List Nat := [3, 4, 2, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_5782914 : Nat := 118140960795 + 5782914 * 2 ^ 59
def prefixEnd_5782914 : Nat := 4983230072969 + 3 ^ 40 * 5782914 * 2
def baseEnd_5782914 : Nat := 2969414465614692556079869

theorem tailTrace_5782914 : CollatzResearch.WordTrace tailWord_5782914 prefixEnd_5782914 2969414465614692556079869 := by
  unfold tailWord_5782914
  simp only [CollatzResearch.WordTrace]
  refine ⟨52730050342874423981506949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140613467580998463950685197 52730050342874423981506949)
  ·
    refine ⟨9886884439288954496532553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52730050342874423981506949 9886884439288954496532553)
    ·
      refine ⟨7415163329466715872399415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9886884439288954496532553 7415163329466715872399415)
      ·
        refine ⟨11122744994200073808599123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415163329466715872399415 11122744994200073808599123)
        ·
          refine ⟨16684117491300110712898685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11122744994200073808599123 16684117491300110712898685)
          ·
            refine ⟨6256544059237541517337007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16684117491300110712898685 6256544059237541517337007)
            ·
              refine ⟨9384816088856312276005511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6256544059237541517337007 9384816088856312276005511)
              ·
                refine ⟨14077224133284468414008267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9384816088856312276005511 14077224133284468414008267)
                ·
                  refine ⟨21115836199926702621012401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14077224133284468414008267 21115836199926702621012401)
                  ·
                    refine ⟨15836877149945026965759301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21115836199926702621012401 15836877149945026965759301)
                    ·
                      refine ⟨2969414465614692556079869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15836877149945026965759301 2969414465614692556079869)
                      ·
                        rfl

theorem cell23_5782914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_5782914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782914 prefixEnd_5782914 := by exact prefixLift 5782914
  have htrace : WordTrace (prefixWord ++ tailWord_5782914) baseStart_5782914 baseEnd_5782914 := by
    simpa [prefixWord, tailWord_5782914, baseEnd_5782914] using wordTrace_append hprefix tailTrace_5782914
  have hstable : (prefixWord ++ tailWord_5782914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782914).length < 2 ^ (prefixWord ++ tailWord_5782914).sum := by decide
  have hdescent : baseEnd_5782914 < baseStart_5782914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5782943 : List Nat := [1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 5]
def baseStart_5782943 : Nat := 118140960795 + 5782943 * 2 ^ 59
def prefixEnd_5782943 : Nat := 4983230072969 + 3 ^ 40 * 5782943 * 2
def baseEnd_5782943 : Nat := 2969429356553672942617235

theorem tailTrace_5782943 : CollatzResearch.WordTrace tailWord_5782943 prefixEnd_5782943 2969429356553672942617235 := by
  unfold tailWord_5782943
  simp only [CollatzResearch.WordTrace]
  refine ⟨210921259088392633878833483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140614172725595089252555655 210921259088392633878833483)
  ·
    refine ⟨316381888632588950818250225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210921259088392633878833483 316381888632588950818250225)
    ·
      refine ⟨237286416474441713113687669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316381888632588950818250225 237286416474441713113687669)
      ·
        refine ⟨22245601544478910604408219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237286416474441713113687669 22245601544478910604408219)
        ·
          refine ⟨33368402316718365906612329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22245601544478910604408219 33368402316718365906612329)
          ·
            refine ⟨25026301737538774429959247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33368402316718365906612329 25026301737538774429959247)
            ·
              refine ⟨37539452606308161644938871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25026301737538774429959247 37539452606308161644938871)
              ·
                refine ⟨56309178909462242467408307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37539452606308161644938871 56309178909462242467408307)
                ·
                  refine ⟨84463768364193363701112461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56309178909462242467408307 84463768364193363701112461)
                  ·
                    refine ⟨31673913136572511387917173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 84463768364193363701112461 31673913136572511387917173)
                    ·
                      refine ⟨2969429356553672942617235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31673913136572511387917173 2969429356553672942617235)
                      ·
                        rfl

theorem cell23_5782943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_5782943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5782943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5782943 prefixEnd_5782943 := by exact prefixLift 5782943
  have htrace : WordTrace (prefixWord ++ tailWord_5782943) baseStart_5782943 baseEnd_5782943 := by
    simpa [prefixWord, tailWord_5782943, baseEnd_5782943] using wordTrace_append hprefix tailTrace_5782943
  have hstable : (prefixWord ++ tailWord_5782943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5782943).length < 2 ^ (prefixWord ++ tailWord_5782943).sum := by decide
  have hdescent : baseEnd_5782943 < baseStart_5782943 := by decide
  rcases family_descends (prefixWord ++ tailWord_5782943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783043 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 4]
def baseStart_5783043 : Nat := 118140960795 + 5783043 * 2 ^ 59
def prefixEnd_5783043 : Nat := 4983230072969 + 3 ^ 40 * 5783043 * 2
def baseEnd_5783043 : Nat := 2969480704619122551366775

theorem tailTrace_5783043 : CollatzResearch.WordTrace tailWord_5783043 prefixEnd_5783043 2969480704619122551366775 := by
  unfold tailWord_5783043
  simp only [CollatzResearch.WordTrace]
  refine ⟨210924906388030350957473783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140616604258686900638315855 210924906388030350957473783)
  ·
    refine ⟨316387359582045526436210675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210924906388030350957473783 316387359582045526436210675)
    ·
      refine ⟨474581039373068289654316013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316387359582045526436210675 474581039373068289654316013)
      ·
        refine ⟨177967889764900608620368505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474581039373068289654316013 177967889764900608620368505)
        ·
          refine ⟨133475917323675456465276379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177967889764900608620368505 133475917323675456465276379)
          ·
            refine ⟨200213875985513184697914569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133475917323675456465276379 200213875985513184697914569)
            ·
              refine ⟨150160406989134888523435927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200213875985513184697914569 150160406989134888523435927)
              ·
                refine ⟨225240610483702332785153891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150160406989134888523435927 225240610483702332785153891)
                ·
                  refine ⟨337860915725553499177730837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 225240610483702332785153891 337860915725553499177730837)
                  ·
                    refine ⟨15837230424635320273956133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 337860915725553499177730837 15837230424635320273956133)
                    ·
                      refine ⟨2969480704619122551366775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15837230424635320273956133 2969480704619122551366775)
                      ·
                        rfl

theorem cell23_5783043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_5783043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783043 prefixEnd_5783043 := by exact prefixLift 5783043
  have htrace : WordTrace (prefixWord ++ tailWord_5783043) baseStart_5783043 baseEnd_5783043 := by
    simpa [prefixWord, tailWord_5783043, baseEnd_5783043] using wordTrace_append hprefix tailTrace_5783043
  have hstable : (prefixWord ++ tailWord_5783043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783043).length < 2 ^ (prefixWord ++ tailWord_5783043).sum := by decide
  have hdescent : baseEnd_5783043 < baseStart_5783043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783044 : List Nat := [2, 3, 2, 3, 2, 2, 1, 1, 2, 5]
def baseStart_5783044 : Nat := 118140960795 + 5783044 * 2 ^ 59
def prefixEnd_5783044 : Nat := 4983230072969 + 3 ^ 40 * 5783044 * 2
def baseEnd_5783044 : Nat := 989827072699925682484757

theorem tailTrace_5783044 : CollatzResearch.WordTrace tailWord_5783044 prefixEnd_5783044 989827072699925682484757 := by
  unfold tailWord_5783044
  simp only [CollatzResearch.WordTrace]
  refine ⟨105462471430513364064130093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140616628574017818752173457 105462471430513364064130093)
  ·
    refine ⟨39548426786442511524048785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105462471430513364064130093 39548426786442511524048785)
    ·
      refine ⟨29661320089831883643036589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39548426786442511524048785 29661320089831883643036589)
      ·
        refine ⟨11122995033686956366138721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29661320089831883643036589 11122995033686956366138721)
        ·
          refine ⟨8342246275265217274604041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11122995033686956366138721 8342246275265217274604041)
          ·
            refine ⟨6256684706448912955953031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8342246275265217274604041 6256684706448912955953031)
            ·
              refine ⟨9385027059673369433929547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6256684706448912955953031 9385027059673369433929547)
              ·
                refine ⟨14077540589510054150894321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9385027059673369433929547 14077540589510054150894321)
                ·
                  refine ⟨10558155442132540613170741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14077540589510054150894321 10558155442132540613170741)
                  ·
                    refine ⟨989827072699925682484757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10558155442132540613170741 989827072699925682484757)
                    ·
                      rfl

theorem cell23_5783044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_5783044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783044 prefixEnd_5783044 := by exact prefixLift 5783044
  have htrace : WordTrace (prefixWord ++ tailWord_5783044) baseStart_5783044 baseEnd_5783044 := by
    simpa [prefixWord, tailWord_5783044, baseEnd_5783044] using wordTrace_append hprefix tailTrace_5783044
  have hstable : (prefixWord ++ tailWord_5783044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783044).length < 2 ^ (prefixWord ++ tailWord_5783044).sum := by decide
  have hdescent : baseEnd_5783044 < baseStart_5783044 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783047 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 4]
def baseStart_5783047 : Nat := 118140960795 + 5783047 * 2 ^ 59
def prefixEnd_5783047 : Nat := 4983230072969 + 3 ^ 40 * 5783047 * 2
def baseEnd_5783047 : Nat := 2969482758541740535716757

theorem tailTrace_5783047 : CollatzResearch.WordTrace tailWord_5783047 prefixEnd_5783047 2969482758541740535716757 := by
  unfold tailWord_5783047
  simp only [CollatzResearch.WordTrace]
  refine ⟨210925052280015859640619395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140616701520010573093746263 210925052280015859640619395)
  ·
    refine ⟨316387578420023789460929093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210925052280015859640619395 316387578420023789460929093)
    ·
      refine ⟨59322670953754460523924205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 316387578420023789460929093 59322670953754460523924205)
      ·
        refine ⟨22246001607657922696471577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59322670953754460523924205 22246001607657922696471577)
        ·
          refine ⟨16684501205743442022353683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22246001607657922696471577 16684501205743442022353683)
          ·
            refine ⟨25026751808615163033530525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16684501205743442022353683 25026751808615163033530525)
            ·
              refine ⟨9385031928230686137573947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25026751808615163033530525 9385031928230686137573947)
              ·
                refine ⟨14077547892346029206360921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9385031928230686137573947 14077547892346029206360921)
                ·
                  refine ⟨10558160919259521904770691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14077547892346029206360921 10558160919259521904770691)
                  ·
                    refine ⟨15837241378889282857156037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10558160919259521904770691 15837241378889282857156037)
                    ·
                      refine ⟨2969482758541740535716757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15837241378889282857156037 2969482758541740535716757)
                      ·
                        rfl

theorem cell23_5783047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_5783047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783047 prefixEnd_5783047 := by exact prefixLift 5783047
  have htrace : WordTrace (prefixWord ++ tailWord_5783047) baseStart_5783047 baseEnd_5783047 := by
    simpa [prefixWord, tailWord_5783047, baseEnd_5783047] using wordTrace_append hprefix tailTrace_5783047
  have hstable : (prefixWord ++ tailWord_5783047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783047).length < 2 ^ (prefixWord ++ tailWord_5783047).sum := by decide
  have hdescent : baseEnd_5783047 < baseStart_5783047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783074 : List Nat := [3, 3, 1, 1, 1, 1, 4, 4, 1, 4]
def baseStart_5783074 : Nat := 118140960795 + 5783074 * 2 ^ 59
def prefixEnd_5783074 : Nat := 4983230072969 + 3 ^ 40 * 5783074 * 2
def baseEnd_5783074 : Nat := 989832207506470643359711

theorem tailTrace_5783074 : CollatzResearch.WordTrace tailWord_5783074 prefixEnd_5783074 989832207506470643359711 := by
  unfold tailWord_5783074
  simp only [CollatzResearch.WordTrace]
  refine ⟨52731509262729510812963069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140617358033945362167901517 52731509262729510812963069)
  ·
    refine ⟨19774315973523566554861151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52731509262729510812963069 19774315973523566554861151)
    ·
      refine ⟨29661473960285349832291727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19774315973523566554861151 29661473960285349832291727)
      ·
        refine ⟨44492210940428024748437591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29661473960285349832291727 44492210940428024748437591)
        ·
          refine ⟨66738316410642037122656387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44492210940428024748437591 66738316410642037122656387)
          ·
            refine ⟨100107474615963055683984581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66738316410642037122656387 100107474615963055683984581)
            ·
              refine ⟨18770151490493072940747109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100107474615963055683984581 18770151490493072940747109)
              ·
                refine ⟨3519403404467451176390083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18770151490493072940747109 3519403404467451176390083)
                ·
                  refine ⟨5279105106701176764585125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519403404467451176390083 5279105106701176764585125)
                  ·
                    refine ⟨989832207506470643359711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279105106701176764585125 989832207506470643359711)
                    ·
                      rfl

theorem cell23_5783074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_5783074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783074 prefixEnd_5783074 := by exact prefixLift 5783074
  have htrace : WordTrace (prefixWord ++ tailWord_5783074) baseStart_5783074 baseEnd_5783074 := by
    simpa [prefixWord, tailWord_5783074, baseEnd_5783074] using wordTrace_append hprefix tailTrace_5783074
  have hstable : (prefixWord ++ tailWord_5783074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783074).length < 2 ^ (prefixWord ++ tailWord_5783074).sum := by decide
  have hdescent : baseEnd_5783074 < baseStart_5783074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783124 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 2, 3, 2]
def baseStart_5783124 : Nat := 118140960795 + 5783124 * 2 ^ 59
def prefixEnd_5783124 : Nat := 4983230072969 + 3 ^ 40 * 5783124 * 2
def baseEnd_5783124 : Nat := 2969522296552136734453903

theorem tailTrace_5783124 : CollatzResearch.WordTrace tailWord_5783124 prefixEnd_5783124 2969522296552136734453903 := by
  unfold tailWord_5783124
  simp only [CollatzResearch.WordTrace]
  refine ⟨105463930350368450895586213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140618573800491267860781617 105463930350368450895586213)
  ·
    refine ⟨19774486940694084542922415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105463930350368450895586213 19774486940694084542922415)
    ·
      refine ⟨29661730411041126814383623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19774486940694084542922415 29661730411041126814383623)
      ·
        refine ⟨44492595616561690221575435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29661730411041126814383623 44492595616561690221575435)
        ·
          refine ⟨66738893424842535332363153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44492595616561690221575435 66738893424842535332363153)
          ·
            refine ⟨50054170068631901499272365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66738893424842535332363153 50054170068631901499272365)
            ·
              refine ⟨18770313775736963062227137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50054170068631901499272365 18770313775736963062227137)
              ·
                refine ⟨14077735331802722296670353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18770313775736963062227137 14077735331802722296670353)
                ·
                  refine ⟨10558301498852041722502765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14077735331802722296670353 10558301498852041722502765)
                  ·
                    refine ⟨3959363062069515645938537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10558301498852041722502765 3959363062069515645938537)
                    ·
                      refine ⟨2969522296552136734453903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959363062069515645938537 2969522296552136734453903)
                      ·
                        rfl

theorem cell23_5783124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_5783124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783124 prefixEnd_5783124 := by exact prefixLift 5783124
  have htrace : WordTrace (prefixWord ++ tailWord_5783124) baseStart_5783124 baseEnd_5783124 := by
    simpa [prefixWord, tailWord_5783124, baseEnd_5783124] using wordTrace_append hprefix tailTrace_5783124
  have hstable : (prefixWord ++ tailWord_5783124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783124).length < 2 ^ (prefixWord ++ tailWord_5783124).sum := by decide
  have hdescent : baseEnd_5783124 < baseStart_5783124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783154 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_5783154 : Nat := 118140960795 + 5783154 * 2 ^ 59
def prefixEnd_5783154 : Nat := 4983230072969 + 3 ^ 40 * 5783154 * 2
def baseEnd_5783154 : Nat := 2969537700971771617078765

theorem tailTrace_5783154 : CollatzResearch.WordTrace tailWord_5783154 prefixEnd_5783154 2969537700971771617078765 := by
  unfold tailWord_5783154
  simp only [CollatzResearch.WordTrace]
  refine ⟨52732238722657054228691129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140619303260418811276509677 52732238722657054228691129)
  ·
    refine ⟨39549179041992790671518347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52732238722657054228691129 39549179041992790671518347)
    ·
      refine ⟨59323768562989186007277521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39549179041992790671518347 59323768562989186007277521)
      ·
        refine ⟨44492826422241889505458141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59323768562989186007277521 44492826422241889505458141)
        ·
          refine ⟨16684809908340708564546803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44492826422241889505458141 16684809908340708564546803)
          ·
            refine ⟨25027214862511062846820205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16684809908340708564546803 25027214862511062846820205)
            ·
              refine ⟨9385205573441648567557577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25027214862511062846820205 9385205573441648567557577)
              ·
                refine ⟨7038904180081236425668183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9385205573441648567557577 7038904180081236425668183)
                ·
                  refine ⟨10558356270121854638502275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7038904180081236425668183 10558356270121854638502275)
                  ·
                    refine ⟨15837534405182781957753413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10558356270121854638502275 15837534405182781957753413)
                    ·
                      refine ⟨2969537700971771617078765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15837534405182781957753413 2969537700971771617078765)
                      ·
                        rfl

theorem cell23_5783154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_5783154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783154 prefixEnd_5783154 := by exact prefixLift 5783154
  have htrace : WordTrace (prefixWord ++ tailWord_5783154) baseStart_5783154 baseEnd_5783154 := by
    simpa [prefixWord, tailWord_5783154, baseEnd_5783154] using wordTrace_append hprefix tailTrace_5783154
  have hstable : (prefixWord ++ tailWord_5783154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783154).length < 2 ^ (prefixWord ++ tailWord_5783154).sum := by decide
  have hdescent : baseEnd_5783154 < baseStart_5783154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783171 : List Nat := [1, 1, 1, 3, 3, 1, 1, 7, 1, 2, 2]
def baseStart_5783171 : Nat := 118140960795 + 5783171 * 2 ^ 59
def prefixEnd_5783171 : Nat := 4983230072969 + 3 ^ 40 * 5783171 * 2
def baseEnd_5783171 : Nat := 2969546430142898050566187

theorem tailTrace_5783171 : CollatzResearch.WordTrace tailWord_5783171 prefixEnd_5783171 2969546430142898050566187 := by
  unfold tailWord_5783171
  simp only [CollatzResearch.WordTrace]
  refine ⟨210929574931566628818133367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140619716621044419212088911 210929574931566628818133367)
  ·
    refine ⟨316394362397349943227200051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210929574931566628818133367 316394362397349943227200051)
    ·
      refine ⟨474591543596024914840800077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316394362397349943227200051 474591543596024914840800077)
      ·
        refine ⟨177971828848509343065300029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 474591543596024914840800077 177971828848509343065300029)
        ·
          refine ⟨66739435818191003649487511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177971828848509343065300029 66739435818191003649487511)
          ·
            refine ⟨100109153727286505474231267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66739435818191003649487511 100109153727286505474231267)
            ·
              refine ⟨150163730590929758211346901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100109153727286505474231267 150163730590929758211346901)
              ·
                refine ⟨3519462435724916208078443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 150163730590929758211346901 3519462435724916208078443)
                ·
                  refine ⟨5279193653587374312117665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519462435724916208078443 5279193653587374312117665)
                  ·
                    refine ⟨3959395240190530734088249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5279193653587374312117665 3959395240190530734088249)
                    ·
                      refine ⟨2969546430142898050566187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959395240190530734088249 2969546430142898050566187)
                      ·
                        rfl

theorem cell23_5783171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 7, 1, 2, 2].length) (baseStart_5783171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783171 prefixEnd_5783171 := by exact prefixLift 5783171
  have htrace : WordTrace (prefixWord ++ tailWord_5783171) baseStart_5783171 baseEnd_5783171 := by
    simpa [prefixWord, tailWord_5783171, baseEnd_5783171] using wordTrace_append hprefix tailTrace_5783171
  have hstable : (prefixWord ++ tailWord_5783171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783171).length < 2 ^ (prefixWord ++ tailWord_5783171).sum := by decide
  have hdescent : baseEnd_5783171 < baseStart_5783171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783204 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_5783204 : Nat := 118140960795 + 5783204 * 2 ^ 59
def prefixEnd_5783204 : Nat := 4983230072969 + 3 ^ 40 * 5783204 * 2
def baseEnd_5783204 : Nat := 2969563375004496421453535

theorem tailTrace_5783204 : CollatzResearch.WordTrace tailWord_5783204 prefixEnd_5783204 2969563375004496421453535 := by
  unfold tailWord_5783204
  simp only [CollatzResearch.WordTrace]
  refine ⟨105465389270223537727042333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140620519026964716969389777 105465389270223537727042333)
  ·
    refine ⟨39549520976333826647640875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105465389270223537727042333 39549520976333826647640875)
    ·
      refine ⟨59324281464500739971461313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39549520976333826647640875 59324281464500739971461313)
      ·
        refine ⟨44493211098375554978595985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59324281464500739971461313 44493211098375554978595985)
        ·
          refine ⟨33369908323781666233946989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44493211098375554978595985 33369908323781666233946989)
          ·
            refine ⟨12513715621418124837730121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33369908323781666233946989 12513715621418124837730121)
            ·
              refine ⟨9385286716063593628297591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12513715621418124837730121 9385286716063593628297591)
              ·
                refine ⟨14077930074095390442446387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9385286716063593628297591 14077930074095390442446387)
                ·
                  refine ⟨21116895111143085663669581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14077930074095390442446387 21116895111143085663669581)
                  ·
                    refine ⟨7918835666678657123876093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21116895111143085663669581 7918835666678657123876093)
                    ·
                      refine ⟨2969563375004496421453535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7918835666678657123876093 2969563375004496421453535)
                      ·
                        rfl

theorem cell23_5783204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_5783204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783204 prefixEnd_5783204 := by exact prefixLift 5783204
  have htrace : WordTrace (prefixWord ++ tailWord_5783204) baseStart_5783204 baseEnd_5783204 := by
    simpa [prefixWord, tailWord_5783204, baseEnd_5783204] using wordTrace_append hprefix tailTrace_5783204
  have hstable : (prefixWord ++ tailWord_5783204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783204).length < 2 ^ (prefixWord ++ tailWord_5783204).sum := by decide
  have hdescent : baseEnd_5783204 < baseStart_5783204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783222 : List Nat := [5, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2]
def baseStart_5783222 : Nat := 118140960795 + 5783222 * 2 ^ 59
def prefixEnd_5783222 : Nat := 4983230072969 + 3 ^ 40 * 5783222 * 2
def baseEnd_5783222 : Nat := 2969572617656277351028453

theorem tailTrace_5783222 : CollatzResearch.WordTrace tailWord_5783222 prefixEnd_5783222 2969572617656277351028453 := by
  unfold tailWord_5783222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13183214690898866533014995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140620956702921243018826613 13183214690898866533014995)
  ·
    refine ⟨19774822036348299799522493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13183214690898866533014995 19774822036348299799522493)
    ·
      refine ⟨7415558263630612424820935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19774822036348299799522493 7415558263630612424820935)
      ·
        refine ⟨11123337395445918637231403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415558263630612424820935 11123337395445918637231403)
        ·
          refine ⟨16685006093168877955847105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11123337395445918637231403 16685006093168877955847105)
          ·
            refine ⟨12513754569876658466885329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16685006093168877955847105 12513754569876658466885329)
            ·
              refine ⟨9385315927407493850163997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12513754569876658466885329 9385315927407493850163997)
              ·
                refine ⟨3519493472777810193811499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9385315927407493850163997 3519493472777810193811499)
                ·
                  refine ⟨5279240209166715290717249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519493472777810193811499 5279240209166715290717249)
                  ·
                    refine ⟨3959430156875036468037937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5279240209166715290717249 3959430156875036468037937)
                    ·
                      refine ⟨2969572617656277351028453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959430156875036468037937 2969572617656277351028453)
                      ·
                        rfl

theorem cell23_5783222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_5783222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783222 prefixEnd_5783222 := by exact prefixLift 5783222
  have htrace : WordTrace (prefixWord ++ tailWord_5783222) baseStart_5783222 baseEnd_5783222 := by
    simpa [prefixWord, tailWord_5783222, baseEnd_5783222] using wordTrace_append hprefix tailTrace_5783222
  have hstable : (prefixWord ++ tailWord_5783222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783222).length < 2 ^ (prefixWord ++ tailWord_5783222).sum := by decide
  have hdescent : baseEnd_5783222 < baseStart_5783222 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783257 : List Nat := [1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_5783257 : Nat := 118140960795 + 5783257 * 2 ^ 59
def prefixEnd_5783257 : Nat := 4983230072969 + 3 ^ 40 * 5783257 * 2
def baseEnd_5783257 : Nat := 2969590589479184714090791

theorem tailTrace_5783257 : CollatzResearch.WordTrace tailWord_5783257 prefixEnd_5783257 2969590589479184714090791 := by
  unfold tailWord_5783257
  simp only [CollatzResearch.WordTrace]
  refine ⟨210932711609255065505764025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140621807739503377003842683 210932711609255065505764025)
  ·
    refine ⟨158199533706941299129323019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210932711609255065505764025 158199533706941299129323019)
    ·
      refine ⟨237299300560411948693984529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158199533706941299129323019 237299300560411948693984529)
      ·
        refine ⟨177974475420308961520488397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237299300560411948693984529 177974475420308961520488397)
        ·
          refine ⟨66740428282615860570183149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177974475420308961520488397 66740428282615860570183149)
          ·
            refine ⟨25027660605980947713818681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66740428282615860570183149 25027660605980947713818681)
            ·
              refine ⟨18770745454485710785364011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25027660605980947713818681 18770745454485710785364011)
              ·
                refine ⟨28156118181728566178046017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18770745454485710785364011 28156118181728566178046017)
                ·
                  refine ⟨21117088636296424633534513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28156118181728566178046017 21117088636296424633534513)
                  ·
                    refine ⟨15837816477222318475150885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21117088636296424633534513 15837816477222318475150885)
                    ·
                      refine ⟨2969590589479184714090791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15837816477222318475150885 2969590589479184714090791)
                      ·
                        rfl

theorem cell23_5783257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_5783257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783257 prefixEnd_5783257 := by exact prefixLift 5783257
  have htrace : WordTrace (prefixWord ++ tailWord_5783257) baseStart_5783257 baseEnd_5783257 := by
    simpa [prefixWord, tailWord_5783257, baseEnd_5783257] using wordTrace_append hprefix tailTrace_5783257
  have hstable : (prefixWord ++ tailWord_5783257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783257).length < 2 ^ (prefixWord ++ tailWord_5783257).sum := by decide
  have hdescent : baseEnd_5783257 < baseStart_5783257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783297 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 4, 5]
def baseStart_5783297 : Nat := 118140960795 + 5783297 * 2 ^ 59
def prefixEnd_5783297 : Nat := 4983230072969 + 3 ^ 40 * 5783297 * 2
def baseEnd_5783297 : Nat := 989870376235121519196869

theorem tailTrace_5783297 : CollatzResearch.WordTrace tailWord_5783297 prefixEnd_5783297 989870376235121519196869 := by
  unfold tailWord_5783297
  simp only [CollatzResearch.WordTrace]
  refine ⟨210934170529110152337220145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140622780352740101558146763 210934170529110152337220145)
  ·
    refine ⟨158200627896832614252915109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210934170529110152337220145 158200627896832614252915109)
    ·
      refine ⟨29662617730656115172421583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 158200627896832614252915109 29662617730656115172421583)
      ·
        refine ⟨44493926595984172758632375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29662617730656115172421583 44493926595984172758632375)
        ·
          refine ⟨66740889893976259137948563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44493926595984172758632375 66740889893976259137948563)
          ·
            refine ⟨100111334840964388706922845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66740889893976259137948563 100111334840964388706922845)
            ·
              refine ⟨37541750565361645765096067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100111334840964388706922845 37541750565361645765096067)
              ·
                refine ⟨56312625848042468647644101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37541750565361645765096067 56312625848042468647644101)
                ·
                  refine ⟨10558617346507962871433269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56312625848042468647644101 10558617346507962871433269)
                  ·
                    refine ⟨989870376235121519196869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10558617346507962871433269 989870376235121519196869)
                    ·
                      rfl

theorem cell23_5783297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_5783297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783297 prefixEnd_5783297 := by exact prefixLift 5783297
  have htrace : WordTrace (prefixWord ++ tailWord_5783297) baseStart_5783297 baseEnd_5783297 := by
    simpa [prefixWord, tailWord_5783297, baseEnd_5783297] using wordTrace_append hprefix tailTrace_5783297
  have hstable : (prefixWord ++ tailWord_5783297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783297).length < 2 ^ (prefixWord ++ tailWord_5783297).sum := by decide
  have hdescent : baseEnd_5783297 < baseStart_5783297 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783304 : List Nat := [2, 1, 3, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_5783304 : Nat := 118140960795 + 5783304 * 2 ^ 59
def prefixEnd_5783304 : Nat := 4983230072969 + 3 ^ 40 * 5783304 * 2
def baseEnd_5783304 : Nat := 2969614723069946030203075

theorem tailTrace_5783304 : CollatzResearch.WordTrace tailWord_5783304 prefixEnd_5783304 2969614723069946030203075 := by
  unfold tailWord_5783304
  simp only [CollatzResearch.WordTrace]
  refine ⟨105467212920042396266362483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140622950560056528355149977 105467212920042396266362483)
  ·
    refine ⟨158200819380063594399543725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105467212920042396266362483 158200819380063594399543725)
    ·
      refine ⟨59325307267523847899828897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158200819380063594399543725 59325307267523847899828897)
      ·
        refine ⟨44493980450642885924871673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59325307267523847899828897 44493980450642885924871673)
        ·
          refine ⟨33370485337982164443653755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44493980450642885924871673 33370485337982164443653755)
          ·
            refine ⟨50055728006973246665480633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33370485337982164443653755 50055728006973246665480633)
            ·
              refine ⟨37541796005229934999110475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50055728006973246665480633 37541796005229934999110475)
              ·
                refine ⟨56312694007844902498665713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37541796005229934999110475 56312694007844902498665713)
                ·
                  refine ⟨42234520505883676873999285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56312694007844902498665713 42234520505883676873999285)
                  ·
                    refine ⟨3959486297426594706937433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42234520505883676873999285 3959486297426594706937433)
                    ·
                      refine ⟨2969614723069946030203075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959486297426594706937433 2969614723069946030203075)
                      ·
                        rfl

theorem cell23_5783304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_5783304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783304 prefixEnd_5783304 := by exact prefixLift 5783304
  have htrace : WordTrace (prefixWord ++ tailWord_5783304) baseStart_5783304 baseEnd_5783304 := by
    simpa [prefixWord, tailWord_5783304, baseEnd_5783304] using wordTrace_append hprefix tailTrace_5783304
  have hstable : (prefixWord ++ tailWord_5783304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783304).length < 2 ^ (prefixWord ++ tailWord_5783304).sum := by decide
  have hdescent : baseEnd_5783304 < baseStart_5783304 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783397 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_5783397 : Nat := 118140960795 + 5783397 * 2 ^ 59
def prefixEnd_5783397 : Nat := 4983230072969 + 3 ^ 40 * 5783397 * 2
def baseEnd_5783397 : Nat := 2969662476770814166340147

theorem tailTrace_5783397 : CollatzResearch.WordTrace tailWord_5783397 prefixEnd_5783397 2969662476770814166340147 := by
  unfold tailWord_5783397
  simp only [CollatzResearch.WordTrace]
  refine ⟨210937817828747869415860445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140625211885831912943906963 210937817828747869415860445)
  ·
    refine ⟨79101681685780451030947667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210937817828747869415860445 79101681685780451030947667)
    ·
      refine ⟨118652522528670676546421501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79101681685780451030947667 118652522528670676546421501)
      ·
        refine ⟨44494695948251503704908063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118652522528670676546421501 44494695948251503704908063)
        ·
          refine ⟨66742043922377255557362095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44494695948251503704908063 66742043922377255557362095)
          ·
            refine ⟨100113065883565883336043143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66742043922377255557362095 100113065883565883336043143)
            ·
              refine ⟨150169598825348825004064715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100113065883565883336043143 150169598825348825004064715)
              ·
                refine ⟨225254398238023237506097073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 150169598825348825004064715 225254398238023237506097073)
                ·
                  refine ⟨168940798678517428129572805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 225254398238023237506097073 168940798678517428129572805)
                  ·
                    refine ⟨31676399752222017774294901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 168940798678517428129572805 31676399752222017774294901)
                    ·
                      refine ⟨2969662476770814166340147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31676399752222017774294901 2969662476770814166340147)
                      ·
                        rfl

theorem cell23_5783397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_5783397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783397 prefixEnd_5783397 := by exact prefixLift 5783397
  have htrace : WordTrace (prefixWord ++ tailWord_5783397) baseStart_5783397 baseEnd_5783397 := by
    simpa [prefixWord, tailWord_5783397, baseEnd_5783397] using wordTrace_append hprefix tailTrace_5783397
  have hstable : (prefixWord ++ tailWord_5783397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783397).length < 2 ^ (prefixWord ++ tailWord_5783397).sum := by decide
  have hdescent : baseEnd_5783397 < baseStart_5783397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783418 : List Nat := [3, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3]
def baseStart_5783418 : Nat := 118140960795 + 5783418 * 2 ^ 59
def prefixEnd_5783418 : Nat := 4983230072969 + 3 ^ 40 * 5783418 * 2
def baseEnd_5783418 : Nat := 2969673259864558584177551

theorem tailTrace_5783418 : CollatzResearch.WordTrace tailWord_5783418 prefixEnd_5783418 2969673259864558584177551 := by
  unfold tailWord_5783418
  simp only [CollatzResearch.WordTrace]
  refine ⟨52734645940417947500593727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140625722507781193334916605 52734645940417947500593727)
  ·
    refine ⟨79101968910626921250890591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52734645940417947500593727 79101968910626921250890591)
    ·
      refine ⟨118652953365940381876335887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79101968910626921250890591 118652953365940381876335887)
      ·
        refine ⟨177979430048910572814503831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118652953365940381876335887 177979430048910572814503831)
        ·
          refine ⟨266969145073365859221755747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177979430048910572814503831 266969145073365859221755747)
          ·
            refine ⟨400453717610048788832633621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266969145073365859221755747 400453717610048788832633621)
            ·
              refine ⟨18771268012971036976529701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 400453717610048788832633621 18771268012971036976529701)
              ·
                refine ⟨3519612752432069433099319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18771268012971036976529701 3519612752432069433099319)
                ·
                  refine ⟨5279419128648104149648979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519612752432069433099319 5279419128648104149648979)
                  ·
                    refine ⟨7919128692972156224473469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5279419128648104149648979 7919128692972156224473469)
                    ·
                      refine ⟨2969673259864558584177551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7919128692972156224473469 2969673259864558584177551)
                      ·
                        rfl

theorem cell23_5783418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3].length) (baseStart_5783418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783418 prefixEnd_5783418 := by exact prefixLift 5783418
  have htrace : WordTrace (prefixWord ++ tailWord_5783418) baseStart_5783418 baseEnd_5783418 := by
    simpa [prefixWord, tailWord_5783418, baseEnd_5783418] using wordTrace_append hprefix tailTrace_5783418
  have hstable : (prefixWord ++ tailWord_5783418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783418).length < 2 ^ (prefixWord ++ tailWord_5783418).sum := by decide
  have hdescent : baseEnd_5783418 < baseStart_5783418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783446 : List Nat := [5, 3, 1, 1, 3, 1, 1, 3, 1, 4]
def baseStart_5783446 : Nat := 118140960795 + 5783446 * 2 ^ 59
def prefixEnd_5783446 : Nat := 4983230072969 + 3 ^ 40 * 5783446 * 2
def baseEnd_5783446 : Nat := 989895879107628158209141

theorem tailTrace_5783446 : CollatzResearch.WordTrace tailWord_5783446 prefixEnd_5783446 989895879107628158209141 := by
  unfold tailWord_5783446
  simp only [CollatzResearch.WordTrace]
  refine ⟨13183725312848146924024637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 140626403337046900522929461 13183725312848146924024637)
  ·
    refine ⟨4943896992318055096509239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13183725312848146924024637 4943896992318055096509239)
    ·
      refine ⟨7415845488477082644763859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4943896992318055096509239 7415845488477082644763859)
      ·
        refine ⟨11123768232715623967145789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415845488477082644763859 11123768232715623967145789)
        ·
          refine ⟨4171413087268358987679671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11123768232715623967145789 4171413087268358987679671)
          ·
            refine ⟨6257119630902538481519507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171413087268358987679671 6257119630902538481519507)
            ·
              refine ⟨9385679446353807722279261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257119630902538481519507 9385679446353807722279261)
              ·
                refine ⟨3519629792382677895854723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9385679446353807722279261 3519629792382677895854723)
                ·
                  refine ⟨5279444688574016843782085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519629792382677895854723 5279444688574016843782085)
                  ·
                    refine ⟨989895879107628158209141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279444688574016843782085 989895879107628158209141)
                    ·
                      rfl

theorem cell23_5783446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_5783446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783446 prefixEnd_5783446 := by exact prefixLift 5783446
  have htrace : WordTrace (prefixWord ++ tailWord_5783446) baseStart_5783446 baseEnd_5783446 := by
    simpa [prefixWord, tailWord_5783446, baseEnd_5783446] using wordTrace_append hprefix tailTrace_5783446
  have hstable : (prefixWord ++ tailWord_5783446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783446).length < 2 ^ (prefixWord ++ tailWord_5783446).sum := by decide
  have hdescent : baseEnd_5783446 < baseStart_5783446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783452 : List Nat := [2, 2, 3, 3, 1, 3, 1, 3, 1, 1, 3]
def baseStart_5783452 : Nat := 118140960795 + 5783452 * 2 ^ 59
def prefixEnd_5783452 : Nat := 4983230072969 + 3 ^ 40 * 5783452 * 2
def baseEnd_5783452 : Nat := 2969690718206811451152395

theorem tailTrace_5783452 : CollatzResearch.WordTrace tailWord_5783452 prefixEnd_5783452 2969690718206811451152395 := by
  unfold tailWord_5783452
  simp only [CollatzResearch.WordTrace]
  refine ⟨105469911921774306904556305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140626549229032409206075073 105469911921774306904556305)
  ·
    refine ⟨79102433941330730178417229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105469911921774306904556305 79102433941330730178417229)
    ·
      refine ⟨29663412727999023816906461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79102433941330730178417229 29663412727999023816906461)
      ·
        refine ⟨11123779772999633931339923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29663412727999023816906461 11123779772999633931339923)
        ·
          refine ⟨16685669659499450897009885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11123779772999633931339923 16685669659499450897009885)
          ·
            refine ⟨6257126122312294086378707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16685669659499450897009885 6257126122312294086378707)
            ·
              refine ⟨9385689183468441129568061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257126122312294086378707 9385689183468441129568061)
              ·
                refine ⟨3519633443800665423588023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9385689183468441129568061 3519633443800665423588023)
                ·
                  refine ⟨5279450165700998135382035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519633443800665423588023 5279450165700998135382035)
                  ·
                    refine ⟨7919175248551497203073053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5279450165700998135382035 7919175248551497203073053)
                    ·
                      refine ⟨2969690718206811451152395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7919175248551497203073053 2969690718206811451152395)
                      ·
                        rfl

theorem cell23_5783452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_5783452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783452 prefixEnd_5783452 := by exact prefixLift 5783452
  have htrace : WordTrace (prefixWord ++ tailWord_5783452) baseStart_5783452 baseEnd_5783452 := by
    simpa [prefixWord, tailWord_5783452, baseEnd_5783452] using wordTrace_append hprefix tailTrace_5783452
  have hstable : (prefixWord ++ tailWord_5783452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783452).length < 2 ^ (prefixWord ++ tailWord_5783452).sum := by decide
  have hdescent : baseEnd_5783452 < baseStart_5783452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783467 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 6]
def baseStart_5783467 : Nat := 118140960795 + 5783467 * 2 ^ 59
def prefixEnd_5783467 : Nat := 4983230072969 + 3 ^ 40 * 5783467 * 2
def baseEnd_5783467 : Nat := 2969698420416628892464825

theorem tailTrace_5783467 : CollatzResearch.WordTrace tailWord_5783467 prefixEnd_5783467 2969698420416628892464825 := by
  unfold tailWord_5783467
  simp only [CollatzResearch.WordTrace]
  refine ⟨210940370938494271370908655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140626913958996180913939103 210940370938494271370908655)
  ·
    refine ⟨316410556407741407056362983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210940370938494271370908655 316410556407741407056362983)
    ·
      refine ⟨474615834611612110584544475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316410556407741407056362983 474615834611612110584544475)
      ·
        refine ⟨711923751917418165876816713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 474615834611612110584544475 711923751917418165876816713)
        ·
          refine ⟨533942813938063624407612535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 711923751917418165876816713 533942813938063624407612535)
          ·
            refine ⟨800914220907095436611418803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 533942813938063624407612535 800914220907095436611418803)
            ·
              refine ⟨1201371331360643154917128205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 800914220907095436611418803 1201371331360643154917128205)
              ·
                refine ⟨450514249260241183093923077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1201371331360643154917128205 450514249260241183093923077)
                ·
                  refine ⟨84471421736295221830110577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 450514249260241183093923077 84471421736295221830110577)
                  ·
                    refine ⟨63353566302221416372582933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 84471421736295221830110577 63353566302221416372582933)
                    ·
                      refine ⟨2969698420416628892464825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63353566302221416372582933 2969698420416628892464825)
                      ·
                        rfl

theorem cell23_5783467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_5783467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783467 prefixEnd_5783467 := by exact prefixLift 5783467
  have htrace : WordTrace (prefixWord ++ tailWord_5783467) baseStart_5783467 baseEnd_5783467 := by
    simpa [prefixWord, tailWord_5783467, baseEnd_5783467] using wordTrace_append hprefix tailTrace_5783467
  have hstable : (prefixWord ++ tailWord_5783467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783467).length < 2 ^ (prefixWord ++ tailWord_5783467).sum := by decide
  have hdescent : baseEnd_5783467 < baseStart_5783467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783485 : List Nat := [1, 4, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_5783485 : Nat := 118140960795 + 5783485 * 2 ^ 59
def prefixEnd_5783485 : Nat := 4983230072969 + 3 ^ 40 * 5783485 * 2
def baseEnd_5783485 : Nat := 989902554356136607346581

theorem tailTrace_5783485 : CollatzResearch.WordTrace tailWord_5783485 prefixEnd_5783485 989902554356136607346581 := by
  unfold tailWord_5783485
  simp only [CollatzResearch.WordTrace]
  refine ⟨210941027452429060445063909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140627351634952706963375939 210941027452429060445063909)
  ·
    refine ⟨39551442647330448833449483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210941027452429060445063909 39551442647330448833449483)
    ·
      refine ⟨59327163970995673250174225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39551442647330448833449483 59327163970995673250174225)
      ·
        refine ⟨44495372978246754937630669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59327163970995673250174225 44495372978246754937630669)
        ·
          refine ⟨16685764866842533101611501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44495372978246754937630669 16685764866842533101611501)
          ·
            refine ⟨6257161825065949913104313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16685764866842533101611501 6257161825065949913104313)
            ·
              refine ⟨4692871368799462434828235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6257161825065949913104313 4692871368799462434828235)
              ·
                refine ⟨7039307053199193652242353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4692871368799462434828235 7039307053199193652242353)
                ·
                  refine ⟨5279480289899395239181765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7039307053199193652242353 5279480289899395239181765)
                  ·
                    refine ⟨989902554356136607346581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279480289899395239181765 989902554356136607346581)
                    ·
                      rfl

theorem cell23_5783485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_5783485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783485 prefixEnd_5783485 := by exact prefixLift 5783485
  have htrace : WordTrace (prefixWord ++ tailWord_5783485) baseStart_5783485 baseEnd_5783485 := by
    simpa [prefixWord, tailWord_5783485, baseEnd_5783485] using wordTrace_append hprefix tailTrace_5783485
  have hstable : (prefixWord ++ tailWord_5783485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783485).length < 2 ^ (prefixWord ++ tailWord_5783485).sum := by decide
  have hdescent : baseEnd_5783485 < baseStart_5783485 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783524 : List Nat := [2, 3, 1, 1, 1, 1, 4, 2, 2, 6]
def baseStart_5783524 : Nat := 118140960795 + 5783524 * 2 ^ 59
def prefixEnd_5783524 : Nat := 4983230072969 + 3 ^ 40 * 5783524 * 2
def baseEnd_5783524 : Nat := 989909229604645056484021

theorem tailTrace_5783524 : CollatzResearch.WordTrace tailWord_5783524 prefixEnd_5783524 989909229604645056484021 := by
  unfold tailWord_5783524
  simp only [CollatzResearch.WordTrace]
  refine ⟨105471224949643885052866813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140628299932858513403822417 105471224949643885052866813)
  ·
    refine ⟨39551709356116456894825055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105471224949643885052866813 39551709356116456894825055)
    ·
      refine ⟨59327564034174685342237583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39551709356116456894825055 59327564034174685342237583)
      ·
        refine ⟨88991346051262028013356375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59327564034174685342237583 88991346051262028013356375)
        ·
          refine ⟨133487019076893042020034563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88991346051262028013356375 133487019076893042020034563)
          ·
            refine ⟨200230528615339563030051845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133487019076893042020034563 200230528615339563030051845)
            ·
              refine ⟨37543224115376168068134721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 200230528615339563030051845 37543224115376168068134721)
              ·
                refine ⟨28157418086532126051101041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37543224115376168068134721 28157418086532126051101041)
                ·
                  refine ⟨21118063564899094538325781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28157418086532126051101041 21118063564899094538325781)
                  ·
                    refine ⟨989909229604645056484021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21118063564899094538325781 989909229604645056484021)
                    ·
                      rfl

theorem cell23_5783524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_5783524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783524 prefixEnd_5783524 := by exact prefixLift 5783524
  have htrace : WordTrace (prefixWord ++ tailWord_5783524) baseStart_5783524 baseEnd_5783524 := by
    simpa [prefixWord, tailWord_5783524, baseEnd_5783524] using wordTrace_append hprefix tailTrace_5783524
  have hstable : (prefixWord ++ tailWord_5783524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783524).length < 2 ^ (prefixWord ++ tailWord_5783524).sum := by decide
  have hdescent : baseEnd_5783524 < baseStart_5783524 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783544 : List Nat := [2, 1, 2, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_5783544 : Nat := 118140960795 + 5783544 * 2 ^ 59
def prefixEnd_5783544 : Nat := 4983230072969 + 3 ^ 40 * 5783544 * 2
def baseEnd_5783544 : Nat := 2969737958427025091201971

theorem tailTrace_5783544 : CollatzResearch.WordTrace tailWord_5783544 prefixEnd_5783544 2969737958427025091201971 := by
  unfold tailWord_5783544
  simp only [CollatzResearch.WordTrace]
  refine ⟨105471589679607656760730843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140628786239476875680974457 105471589679607656760730843)
  ·
    refine ⟨158207384519411485141096265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105471589679607656760730843 158207384519411485141096265)
    ·
      refine ⟨118655538389558613855822199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158207384519411485141096265 118655538389558613855822199)
      ·
        refine ⟨177983307584337920783733299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118655538389558613855822199 177983307584337920783733299)
        ·
          refine ⟨266974961376506881175599949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177983307584337920783733299 266974961376506881175599949)
          ·
            refine ⟨100115610516190080440849981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266974961376506881175599949 100115610516190080440849981)
            ·
              refine ⟨37543353943571280165318743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100115610516190080440849981 37543353943571280165318743)
              ·
                refine ⟨56315030915356920247978115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37543353943571280165318743 56315030915356920247978115)
                ·
                  refine ⟨84472546373035380371967173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56315030915356920247978115 84472546373035380371967173)
                  ·
                    refine ⟨15838602444944133819743845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 84472546373035380371967173 15838602444944133819743845)
                    ·
                      refine ⟨2969737958427025091201971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15838602444944133819743845 2969737958427025091201971)
                      ·
                        rfl

theorem cell23_5783544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_5783544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783544 prefixEnd_5783544 := by exact prefixLift 5783544
  have htrace : WordTrace (prefixWord ++ tailWord_5783544) baseStart_5783544 baseEnd_5783544 := by
    simpa [prefixWord, tailWord_5783544, baseEnd_5783544] using wordTrace_append hprefix tailTrace_5783544
  have hstable : (prefixWord ++ tailWord_5783544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783544).length < 2 ^ (prefixWord ++ tailWord_5783544).sum := by decide
  have hdescent : baseEnd_5783544 < baseStart_5783544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783548 : List Nat := [2, 2, 2, 1, 2, 2, 4, 1, 1, 4, 2]
def baseStart_5783548 : Nat := 118140960795 + 5783548 * 2 ^ 59
def prefixEnd_5783548 : Nat := 4983230072969 + 3 ^ 40 * 5783548 * 2
def baseEnd_5783548 : Nat := 2969740012349643075551953

theorem tailTrace_5783548 : CollatzResearch.WordTrace tailWord_5783548 prefixEnd_5783548 2969740012349643075551953 := by
  unfold tailWord_5783548
  simp only [CollatzResearch.WordTrace]
  refine ⟨105471662625600411102303649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140628883500800548136404865 105471662625600411102303649)
  ·
    refine ⟨79103746969200308326727737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105471662625600411102303649 79103746969200308326727737)
    ·
      refine ⟨59327810226900231245045803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79103746969200308326727737 59327810226900231245045803)
      ·
        refine ⟨88991715340350346867568705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59327810226900231245045803 88991715340350346867568705)
        ·
          refine ⟨66743786505262760150676529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88991715340350346867568705 66743786505262760150676529)
          ·
            refine ⟨50057839878947070113007397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66743786505262760150676529 50057839878947070113007397)
            ·
              refine ⟨9385844977302575646188887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50057839878947070113007397 9385844977302575646188887)
              ·
                refine ⟨14078767465953863469283331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9385844977302575646188887 14078767465953863469283331)
                ·
                  refine ⟨21118151198930795203924997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14078767465953863469283331 21118151198930795203924997)
                  ·
                    refine ⟨3959653349799524100735937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21118151198930795203924997 3959653349799524100735937)
                    ·
                      refine ⟨2969740012349643075551953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959653349799524100735937 2969740012349643075551953)
                      ·
                        rfl

theorem cell23_5783548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_5783548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783548 prefixEnd_5783548 := by exact prefixLift 5783548
  have htrace : WordTrace (prefixWord ++ tailWord_5783548) baseStart_5783548 baseEnd_5783548 := by
    simpa [prefixWord, tailWord_5783548, baseEnd_5783548] using wordTrace_append hprefix tailTrace_5783548
  have hstable : (prefixWord ++ tailWord_5783548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783548).length < 2 ^ (prefixWord ++ tailWord_5783548).sum := by decide
  have hdescent : baseEnd_5783548 < baseStart_5783548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783571 : List Nat := [1, 1, 1, 2, 1, 4, 3, 5, 5]
def baseStart_5783571 : Nat := 118140960795 + 5783571 * 2 ^ 59
def prefixEnd_5783571 : Nat := 4983230072969 + 3 ^ 40 * 5783571 * 2
def baseEnd_5783571 : Nat := 329972424711632942840483

theorem tailTrace_5783571 : CollatzResearch.WordTrace tailWord_5783571 prefixEnd_5783571 329972424711632942840483 := by
  unfold tailWord_5783571
  simp only [CollatzResearch.WordTrace]
  refine ⟨210944164130117497132694567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140629442753411664755129711 210944164130117497132694567)
  ·
    refine ⟨316416246195176245699041851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210944164130117497132694567 316416246195176245699041851)
    ·
      refine ⟨474624369292764368548562777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 316416246195176245699041851 474624369292764368548562777)
      ·
        refine ⟨355968276969573276411422083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 474624369292764368548562777 355968276969573276411422083)
        ·
          refine ⟨533952415454359914617133125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355968276969573276411422083 533952415454359914617133125)
          ·
            refine ⟨100116077897692483990712461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 533952415454359914617133125 100116077897692483990712461)
            ·
              refine ⟨37543529211634681496517173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100116077897692483990712461 37543529211634681496517173)
              ·
                refine ⟨3519705863590751390298485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37543529211634681496517173 3519705863590751390298485)
                ·
                  refine ⟨329972424711632942840483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3519705863590751390298485 329972424711632942840483)
                  ·
                    rfl

theorem cell23_5783571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 5, 5].length) (baseStart_5783571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783571 prefixEnd_5783571 := by exact prefixLift 5783571
  have htrace : WordTrace (prefixWord ++ tailWord_5783571) baseStart_5783571 baseEnd_5783571 := by
    simpa [prefixWord, tailWord_5783571, baseEnd_5783571] using wordTrace_append hprefix tailTrace_5783571
  have hstable : (prefixWord ++ tailWord_5783571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783571).length < 2 ^ (prefixWord ++ tailWord_5783571).sum := by decide
  have hdescent : baseEnd_5783571 < baseStart_5783571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783588 : List Nat := [2, 3, 1, 4, 2, 1, 2, 1, 7]
def baseStart_5783588 : Nat := 118140960795 + 5783588 * 2 ^ 59
def prefixEnd_5783588 : Nat := 4983230072969 + 3 ^ 40 * 5783588 * 2
def baseEnd_5783588 : Nat := 329973394619535879894641

theorem tailTrace_5783588 : CollatzResearch.WordTrace tailWord_5783588 prefixEnd_5783588 329973394619535879894641 := by
  unfold tailWord_5783588
  simp only [CollatzResearch.WordTrace]
  refine ⟨105472392085527954518031709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140629856114037272690708945 105472392085527954518031709)
  ·
    refine ⟨39552147032072982944261891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105472392085527954518031709 39552147032072982944261891)
    ·
      refine ⟨59328220548109474416392837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39552147032072982944261891 59328220548109474416392837)
      ·
        refine ⟨11124041352770526453073657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59328220548109474416392837 11124041352770526453073657)
        ·
          refine ⟨8343031014577894839805243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11124041352770526453073657 8343031014577894839805243)
          ·
            refine ⟨12514546521866842259707865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8343031014577894839805243 12514546521866842259707865)
            ·
              refine ⟨9385909891400131694780899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12514546521866842259707865 9385909891400131694780899)
              ·
                refine ⟨14078864837100197542171349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9385909891400131694780899 14078864837100197542171349)
                ·
                  refine ⟨329973394619535879894641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14078864837100197542171349 329973394619535879894641)
                  ·
                    rfl

theorem cell23_5783588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_5783588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783588 prefixEnd_5783588 := by exact prefixLift 5783588
  have htrace : WordTrace (prefixWord ++ tailWord_5783588) baseStart_5783588 baseEnd_5783588 := by
    simpa [prefixWord, tailWord_5783588, baseEnd_5783588] using wordTrace_append hprefix tailTrace_5783588
  have hstable : (prefixWord ++ tailWord_5783588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783588).length < 2 ^ (prefixWord ++ tailWord_5783588).sum := by decide
  have hdescent : baseEnd_5783588 < baseStart_5783588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783598 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_5783598 : Nat := 118140960795 + 5783598 * 2 ^ 59
def prefixEnd_5783598 : Nat := 4983230072969 + 3 ^ 40 * 5783598 * 2
def baseEnd_5783598 : Nat := 2969765686382367879926723

theorem tailTrace_5783598 : CollatzResearch.WordTrace tailWord_5783598 prefixEnd_5783598 2969765686382367879926723 := by
  unfold tailWord_5783598
  simp only [CollatzResearch.WordTrace]
  refine ⟨26368143612627460092990931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140630099267346453829284965 26368143612627460092990931)
  ·
    refine ⟨39552215418941190139486397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26368143612627460092990931 39552215418941190139486397)
    ·
      refine ⟨14832080782102946302307399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39552215418941190139486397 14832080782102946302307399)
      ·
        refine ⟨22248121173154419453461099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14832080782102946302307399 22248121173154419453461099)
        ·
          refine ⟨33372181759731629180191649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22248121173154419453461099 33372181759731629180191649)
          ·
            refine ⟨25029136319798721885143737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33372181759731629180191649 25029136319798721885143737)
            ·
              refine ⟨18771852239849041413857803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25029136319798721885143737 18771852239849041413857803)
              ·
                refine ⟨28157778359773562120786705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18771852239849041413857803 28157778359773562120786705)
                ·
                  refine ⟨21118333769830171590590029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28157778359773562120786705 21118333769830171590590029)
                  ·
                    refine ⟨7919375163686314346471261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21118333769830171590590029 7919375163686314346471261)
                    ·
                      refine ⟨2969765686382367879926723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7919375163686314346471261 2969765686382367879926723)
                      ·
                        rfl

theorem cell23_5783598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_5783598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783598 prefixEnd_5783598 := by exact prefixLift 5783598
  have htrace : WordTrace (prefixWord ++ tailWord_5783598) baseStart_5783598 baseEnd_5783598 := by
    simpa [prefixWord, tailWord_5783598, baseEnd_5783598] using wordTrace_append hprefix tailTrace_5783598
  have hstable : (prefixWord ++ tailWord_5783598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783598).length < 2 ^ (prefixWord ++ tailWord_5783598).sum := by decide
  have hdescent : baseEnd_5783598 < baseStart_5783598 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783621 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_5783621 : Nat := 118140960795 + 5783621 * 2 ^ 59
def prefixEnd_5783621 : Nat := 4983230072969 + 3 ^ 40 * 5783621 * 2
def baseEnd_5783621 : Nat := 2969777496437421289939117

theorem tailTrace_5783621 : CollatzResearch.WordTrace tailWord_5783621 prefixEnd_5783621 2969777496437421289939117 := by
  unfold tailWord_5783621
  simp only [CollatzResearch.WordTrace]
  refine ⟨210945987779936355672014717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140630658519957570448009811 210945987779936355672014717)
  ·
    refine ⟨79104745417476133377005519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210945987779936355672014717 79104745417476133377005519)
    ·
      refine ⟨118657118126214200065508279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79104745417476133377005519 118657118126214200065508279)
      ·
        refine ⟨177985677189321300098262419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118657118126214200065508279 177985677189321300098262419)
        ·
          refine ⟨266978515783981950147393629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177985677189321300098262419 266978515783981950147393629)
          ·
            refine ⟨100116943418993231305272611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 266978515783981950147393629 100116943418993231305272611)
            ·
              refine ⟨150175415128489846957908917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100116943418993231305272611 150175415128489846957908917)
              ·
                refine ⟨14078945168295923152303961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150175415128489846957908917 14078945168295923152303961)
                ·
                  refine ⟨10559208876221942364227971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14078945168295923152303961 10559208876221942364227971)
                  ·
                    refine ⟨15838813314332913546341957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10559208876221942364227971 15838813314332913546341957)
                    ·
                      refine ⟨2969777496437421289939117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15838813314332913546341957 2969777496437421289939117)
                      ·
                        rfl

theorem cell23_5783621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_5783621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783621 prefixEnd_5783621 := by exact prefixLift 5783621
  have htrace : WordTrace (prefixWord ++ tailWord_5783621) baseStart_5783621 baseEnd_5783621 := by
    simpa [prefixWord, tailWord_5783621, baseEnd_5783621] using wordTrace_append hprefix tailTrace_5783621
  have hstable : (prefixWord ++ tailWord_5783621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783621).length < 2 ^ (prefixWord ++ tailWord_5783621).sum := by decide
  have hdescent : baseEnd_5783621 < baseStart_5783621 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783648 : List Nat := [2, 1, 1, 3, 2, 3, 3, 1, 3, 4]
def baseStart_5783648 : Nat := 118140960795 + 5783648 * 2 ^ 59
def prefixEnd_5783648 : Nat := 4983230072969 + 3 ^ 40 * 5783648 * 2
def baseEnd_5783648 : Nat := 989930453471697561433831

theorem tailTrace_5783648 : CollatzResearch.WordTrace tailWord_5783648 prefixEnd_5783648 989930453471697561433831 := by
  unfold tailWord_5783648
  simp only [CollatzResearch.WordTrace]
  refine ⟨105473486275419269641623799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140631315033892359522165065 105473486275419269641623799)
  ·
    refine ⟨158210229413128904462435699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105473486275419269641623799 158210229413128904462435699)
    ·
      refine ⟨237315344119693356693653549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158210229413128904462435699 237315344119693356693653549)
      ·
        refine ⟨88993254044885008760120081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237315344119693356693653549 88993254044885008760120081)
        ·
          refine ⟨66744940533663756570090061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88993254044885008760120081 66744940533663756570090061)
          ·
            refine ⟨25029352700123908713783773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66744940533663756570090061 25029352700123908713783773)
            ·
              refine ⟨9386007262546465767668915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25029352700123908713783773 9386007262546465767668915)
              ·
                refine ⟨14079010893819698651503373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9386007262546465767668915 14079010893819698651503373)
                ·
                  refine ⟨5279629085182386994313765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14079010893819698651503373 5279629085182386994313765)
                  ·
                    refine ⟨989930453471697561433831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279629085182386994313765 989930453471697561433831)
                    ·
                      rfl

theorem cell23_5783648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 1, 3, 4].length) (baseStart_5783648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783648 prefixEnd_5783648 := by exact prefixLift 5783648
  have htrace : WordTrace (prefixWord ++ tailWord_5783648) baseStart_5783648 baseEnd_5783648 := by
    simpa [prefixWord, tailWord_5783648, baseEnd_5783648] using wordTrace_append hprefix tailTrace_5783648
  have hstable : (prefixWord ++ tailWord_5783648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783648).length < 2 ^ (prefixWord ++ tailWord_5783648).sum := by decide
  have hdescent : baseEnd_5783648 < baseStart_5783648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783726 : List Nat := [4, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5783726 : Nat := 118140960795 + 5783726 * 2 ^ 59
def prefixEnd_5783726 : Nat := 4983230072969 + 3 ^ 40 * 5783726 * 2
def baseEnd_5783726 : Nat := 2969831411906143379126135

theorem tailTrace_5783726 : CollatzResearch.WordTrace tailWord_5783726 prefixEnd_5783726 2969831411906143379126135 := by
  unfold tailWord_5783726
  simp only [CollatzResearch.WordTrace]
  refine ⟨26368727180569494825573379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 140633211629703972403058021 26368727180569494825573379)
  ·
    refine ⟨39553090770854242238360069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26368727180569494825573379 39553090770854242238360069)
    ·
      refine ⟨7416204519535170419692513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39553090770854242238360069 7416204519535170419692513)
      ·
        refine ⟨5562153389651377814769385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7416204519535170419692513 5562153389651377814769385)
        ·
          refine ⟨4171615042238533361077039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5562153389651377814769385 4171615042238533361077039)
          ·
            refine ⟨6257422563357800041615559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4171615042238533361077039 6257422563357800041615559)
            ·
              refine ⟨9386133845036700062423339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257422563357800041615559 9386133845036700062423339)
              ·
                refine ⟨14079200767555050093635009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9386133845036700062423339 14079200767555050093635009)
                ·
                  refine ⟨10559400575666287570226257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14079200767555050093635009 10559400575666287570226257)
                  ·
                    refine ⟨7919550431749715677669693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10559400575666287570226257 7919550431749715677669693)
                    ·
                      refine ⟨2969831411906143379126135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7919550431749715677669693 2969831411906143379126135)
                      ·
                        rfl

theorem cell23_5783726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5783726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783726 prefixEnd_5783726 := by exact prefixLift 5783726
  have htrace : WordTrace (prefixWord ++ tailWord_5783726) baseStart_5783726 baseEnd_5783726 := by
    simpa [prefixWord, tailWord_5783726, baseEnd_5783726] using wordTrace_append hprefix tailTrace_5783726
  have hstable : (prefixWord ++ tailWord_5783726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783726).length < 2 ^ (prefixWord ++ tailWord_5783726).sum := by decide
  have hdescent : baseEnd_5783726 < baseStart_5783726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783741 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_5783741 : Nat := 118140960795 + 5783741 * 2 ^ 59
def prefixEnd_5783741 : Nat := 4983230072969 + 3 ^ 40 * 5783741 * 2
def baseEnd_5783741 : Nat := 2969839114115960820438565

theorem tailTrace_5783741 : CollatzResearch.WordTrace tailWord_5783741 prefixEnd_5783741 2969839114115960820438565 := by
  unfold tailWord_5783741
  simp only [CollatzResearch.WordTrace]
  refine ⟨210950364539501616166383077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140633576359667744110922051 210950364539501616166383077)
  ·
    refine ⟨39553193351156553031196827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210950364539501616166383077 39553193351156553031196827)
    ·
      refine ⟨59329790026734829546795241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39553193351156553031196827 59329790026734829546795241)
      ·
        refine ⟨44497342520051122160096431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59329790026734829546795241 44497342520051122160096431)
        ·
          refine ⟨66746013780076683240144647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44497342520051122160096431 66746013780076683240144647)
          ·
            refine ⟨100119020670115024860216971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66746013780076683240144647 100119020670115024860216971)
            ·
              refine ⟨150178531005172537290325457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100119020670115024860216971 150178531005172537290325457)
              ·
                refine ⟨112633898253879402967744093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150178531005172537290325457 112633898253879402967744093)
                ·
                  refine ⟨42237711845204776112904035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 112633898253879402967744093 42237711845204776112904035)
                  ·
                    refine ⟨63356567767807164169356053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42237711845204776112904035 63356567767807164169356053)
                    ·
                      refine ⟨2969839114115960820438565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 63356567767807164169356053 2969839114115960820438565)
                      ·
                        rfl

theorem cell23_5783741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_5783741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783741 prefixEnd_5783741 := by exact prefixLift 5783741
  have htrace : WordTrace (prefixWord ++ tailWord_5783741) baseStart_5783741 baseEnd_5783741 := by
    simpa [prefixWord, tailWord_5783741, baseEnd_5783741] using wordTrace_append hprefix tailTrace_5783741
  have hstable : (prefixWord ++ tailWord_5783741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783741).length < 2 ^ (prefixWord ++ tailWord_5783741).sum := by decide
  have hdescent : baseEnd_5783741 < baseStart_5783741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783762 : List Nat := [3, 2, 2, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_5783762 : Nat := 118140960795 + 5783762 * 2 ^ 59
def prefixEnd_5783762 : Nat := 4983230072969 + 3 ^ 40 * 5783762 * 2
def baseEnd_5783762 : Nat := 2969849897209705238275969

theorem tailTrace_5783762 : CollatzResearch.WordTrace tailWord_5783762 prefixEnd_5783762 2969849897209705238275969 := by
  unfold tailWord_5783762
  simp only [CollatzResearch.WordTrace]
  refine ⟨52737782618106384188224385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 140634086981617024501931693 52737782618106384188224385)
  ·
    refine ⟨39553336963579788141168289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52737782618106384188224385 39553336963579788141168289)
    ·
      refine ⟨29665002722684841105876217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39553336963579788141168289 29665002722684841105876217)
      ·
        refine ⟨22248752042013630829407163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29665002722684841105876217 22248752042013630829407163)
        ·
          refine ⟨33373128063020446244110745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22248752042013630829407163 33373128063020446244110745)
          ·
            refine ⟨25029846047265334683083059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33373128063020446244110745 25029846047265334683083059)
            ·
              refine ⟨37544769070898002024624589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25029846047265334683083059 37544769070898002024624589)
              ·
                refine ⟨14079288401586750759234221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37544769070898002024624589 14079288401586750759234221)
                ·
                  refine ⟨5279733150595031534712833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14079288401586750759234221 5279733150595031534712833)
                  ·
                    refine ⟨3959799862946273651034625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5279733150595031534712833 3959799862946273651034625)
                    ·
                      refine ⟨2969849897209705238275969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959799862946273651034625 2969849897209705238275969)
                      ·
                        rfl

theorem cell23_5783762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_5783762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783762 prefixEnd_5783762 := by exact prefixLift 5783762
  have htrace : WordTrace (prefixWord ++ tailWord_5783762) baseStart_5783762 baseEnd_5783762 := by
    simpa [prefixWord, tailWord_5783762, baseEnd_5783762] using wordTrace_append hprefix tailTrace_5783762
  have hstable : (prefixWord ++ tailWord_5783762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783762).length < 2 ^ (prefixWord ++ tailWord_5783762).sum := by decide
  have hdescent : baseEnd_5783762 < baseStart_5783762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783765 : List Nat := [1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_5783765 : Nat := 118140960795 + 5783765 * 2 ^ 59
def prefixEnd_5783765 : Nat := 4983230072969 + 3 ^ 40 * 5783765 * 2
def baseEnd_5783765 : Nat := 2969851437651668726538455

theorem tailTrace_5783765 : CollatzResearch.WordTrace tailWord_5783765 prefixEnd_5783765 2969851437651668726538455 := by
  unfold tailWord_5783765
  simp only [CollatzResearch.WordTrace]
  refine ⟨210951239891414668265256749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140634159927609778843504499 210951239891414668265256749)
  ·
    refine ⟨79106714959280500599471281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 210951239891414668265256749 79106714959280500599471281)
    ·
      refine ⟨59330036219460375449603461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79106714959280500599471281 59330036219460375449603461)
      ·
        refine ⟨11124381791148820396800649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59330036219460375449603461 11124381791148820396800649)
        ·
          refine ⟨8343286343361615297600487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11124381791148820396800649 8343286343361615297600487)
          ·
            refine ⟨12514929515042422946400731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8343286343361615297600487 12514929515042422946400731)
            ·
              refine ⟨18772394272563634419601097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12514929515042422946400731 18772394272563634419601097)
              ·
                refine ⟨14079295704422725814700823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18772394272563634419601097 14079295704422725814700823)
                ·
                  refine ⟨21118943556634088722051235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14079295704422725814700823 21118943556634088722051235)
                  ·
                    refine ⟨31678415334951133083076853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21118943556634088722051235 31678415334951133083076853)
                    ·
                      refine ⟨2969851437651668726538455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 31678415334951133083076853 2969851437651668726538455)
                      ·
                        rfl

theorem cell23_5783765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_5783765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783765 prefixEnd_5783765 := by exact prefixLift 5783765
  have htrace : WordTrace (prefixWord ++ tailWord_5783765) baseStart_5783765 baseEnd_5783765 := by
    simpa [prefixWord, tailWord_5783765, baseEnd_5783765] using wordTrace_append hprefix tailTrace_5783765
  have hstable : (prefixWord ++ tailWord_5783765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783765).length < 2 ^ (prefixWord ++ tailWord_5783765).sum := by decide
  have hdescent : baseEnd_5783765 < baseStart_5783765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783839 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 1, 3, 2]
def baseStart_5783839 : Nat := 118140960795 + 5783839 * 2 ^ 59
def prefixEnd_5783839 : Nat := 4983230072969 + 3 ^ 40 * 5783839 * 2
def baseEnd_5783839 : Nat := 2969889435220101437013115

theorem tailTrace_5783839 : CollatzResearch.WordTrace tailWord_5783839 prefixEnd_5783839 2969889435220101437013115 := by
  unfold tailWord_5783839
  simp only [CollatzResearch.WordTrace]
  refine ⟨210953938893146578903450571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140635959262097719268967047 210953938893146578903450571)
  ·
    refine ⟨316430908339719868355175857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210953938893146578903450571 316430908339719868355175857)
    ·
      refine ⟨237323181254789901266381893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 316430908339719868355175857 237323181254789901266381893)
      ·
        refine ⟨44498096485273106487446605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237323181254789901266381893 44498096485273106487446605)
        ·
          refine ⟨16686786181977414932792477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44498096485273106487446605 16686786181977414932792477)
          ·
            refine ⟨6257544818241530599797179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16686786181977414932792477 6257544818241530599797179)
            ·
              refine ⟨9386317227362295899695769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257544818241530599797179 9386317227362295899695769)
              ·
                refine ⟨7039737920521721924771827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9386317227362295899695769 7039737920521721924771827)
                ·
                  refine ⟨10559606880782582887157741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7039737920521721924771827 10559606880782582887157741)
                  ·
                    refine ⟨3959852580293468582684153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10559606880782582887157741 3959852580293468582684153)
                    ·
                      refine ⟨2969889435220101437013115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959852580293468582684153 2969889435220101437013115)
                      ·
                        rfl

theorem cell23_5783839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 1, 3, 2].length) (baseStart_5783839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783839 prefixEnd_5783839 := by exact prefixLift 5783839
  have htrace : WordTrace (prefixWord ++ tailWord_5783839) baseStart_5783839 baseEnd_5783839 := by
    simpa [prefixWord, tailWord_5783839, baseEnd_5783839] using wordTrace_append hprefix tailTrace_5783839
  have hstable : (prefixWord ++ tailWord_5783839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783839).length < 2 ^ (prefixWord ++ tailWord_5783839).sum := by decide
  have hdescent : baseEnd_5783839 < baseStart_5783839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783895 : List Nat := [1, 1, 3, 2, 3, 1, 1, 2, 2, 5, 2]
def baseStart_5783895 : Nat := 118140960795 + 5783895 * 2 ^ 59
def prefixEnd_5783895 : Nat := 4983230072969 + 3 ^ 40 * 5783895 * 2
def baseEnd_5783895 : Nat := 2969918190136753217912857

theorem tailTrace_5783895 : CollatzResearch.WordTrace tailWord_5783895 prefixEnd_5783895 2969918190136753217912857 := by
  unfold tailWord_5783895
  simp only [CollatzResearch.WordTrace]
  refine ⟨210955981380943700467489139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140637320920629133644992759 210955981380943700467489139)
  ·
    refine ⟨316433972071415550701233709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 210955981380943700467489139 316433972071415550701233709)
    ·
      refine ⟨118662739526780831512962641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 316433972071415550701233709 118662739526780831512962641)
      ·
        refine ⟨88997054645085623634721981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118662739526780831512962641 88997054645085623634721981)
        ·
          refine ⟨33373895491907108863020743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88997054645085623634721981 33373895491907108863020743)
          ·
            refine ⟨50060843237860663294531115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33373895491907108863020743 50060843237860663294531115)
            ·
              refine ⟨75091264856790994941796673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50060843237860663294531115 75091264856790994941796673)
              ·
                refine ⟨56318448642593246206347505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75091264856790994941796673 56318448642593246206347505)
                ·
                  refine ⟨42238836481944934654760629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56318448642593246206347505 42238836481944934654760629)
                  ·
                    refine ⟨3959890920182337623883809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42238836481944934654760629 3959890920182337623883809)
                    ·
                      refine ⟨2969918190136753217912857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3959890920182337623883809 2969918190136753217912857)
                      ·
                        rfl

theorem cell23_5783895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_5783895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783895 prefixEnd_5783895 := by exact prefixLift 5783895
  have htrace : WordTrace (prefixWord ++ tailWord_5783895) baseStart_5783895 baseEnd_5783895 := by
    simpa [prefixWord, tailWord_5783895, baseEnd_5783895] using wordTrace_append hprefix tailTrace_5783895
  have hstable : (prefixWord ++ tailWord_5783895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783895).length < 2 ^ (prefixWord ++ tailWord_5783895).sum := by decide
  have hdescent : baseEnd_5783895 < baseStart_5783895 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5783945 : List Nat := [1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 3]
def baseStart_5783945 : Nat := 118140960795 + 5783945 * 2 ^ 59
def prefixEnd_5783945 : Nat := 4983230072969 + 3 ^ 40 * 5783945 * 2
def baseEnd_5783945 : Nat := 2969943864169478022287627

theorem tailTrace_5783945 : CollatzResearch.WordTrace tailWord_5783945 prefixEnd_5783945 2969943864169478022287627 := by
  unfold tailWord_5783945
  simp only [CollatzResearch.WordTrace]
  refine ⟨210957805030762559006809289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140638536687175039337872859 210957805030762559006809289)
  ·
    refine ⟨158218353773071919255106967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210957805030762559006809289 158218353773071919255106967)
    ·
      refine ⟨237327530659607878882660451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158218353773071919255106967 237327530659607878882660451)
      ·
        refine ⟨355991295989411818323990677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237327530659607878882660451 355991295989411818323990677)
        ·
          refine ⟨16687091999503678983937063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 355991295989411818323990677 16687091999503678983937063)
          ·
            refine ⟨25030637999255518475905595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16687091999503678983937063 25030637999255518475905595)
            ·
              refine ⟨37545956998883277713858393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25030637999255518475905595 37545956998883277713858393)
              ·
                refine ⟨28159467749162458285393795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37545956998883277713858393 28159467749162458285393795)
                ·
                  refine ⟨42239201623743687428090693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28159467749162458285393795 42239201623743687428090693)
                  ·
                    refine ⟨7919850304451941392767005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42239201623743687428090693 7919850304451941392767005)
                    ·
                      refine ⟨2969943864169478022287627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7919850304451941392767005 2969943864169478022287627)
                      ·
                        rfl

theorem cell23_5783945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_5783945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5783945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5783945 prefixEnd_5783945 := by exact prefixLift 5783945
  have htrace : WordTrace (prefixWord ++ tailWord_5783945) baseStart_5783945 baseEnd_5783945 := by
    simpa [prefixWord, tailWord_5783945, baseEnd_5783945] using wordTrace_append hprefix tailTrace_5783945
  have hstable : (prefixWord ++ tailWord_5783945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5783945).length < 2 ^ (prefixWord ++ tailWord_5783945).sum := by decide
  have hdescent : baseEnd_5783945 < baseStart_5783945 := by decide
  rcases family_descends (prefixWord ++ tailWord_5783945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784012 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 3, 5]
def baseStart_5784012 : Nat := 118140960795 + 5784012 * 2 ^ 59
def prefixEnd_5784012 : Nat := 4983230072969 + 3 ^ 40 * 5784012 * 2
def baseEnd_5784012 : Nat := 989992755791109753383273

theorem tailTrace_5784012 : CollatzResearch.WordTrace tailWord_5784012 prefixEnd_5784012 989992755791109753383273 := by
  unfold tailWord_5784012
  simp only [CollatzResearch.WordTrace]
  refine ⟨105480124360759914724749145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 140640165814346552966332193 105480124360759914724749145)
  ·
    refine ⟨79110093270569936043561859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105480124360759914724749145 79110093270569936043561859)
    ·
      refine ⟨118665139905854904065342789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79110093270569936043561859 118665139905854904065342789)
      ·
        refine ⟨22249713732347794512251773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118665139905854904065342789 22249713732347794512251773)
        ·
          refine ⟨8343642649630422942094415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22249713732347794512251773 8343642649630422942094415)
          ·
            refine ⟨12515463974445634413141623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8343642649630422942094415 12515463974445634413141623)
            ·
              refine ⟨18773195961668451619712435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12515463974445634413141623 18773195961668451619712435)
              ·
                refine ⟨28159793942502677429568653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18773195961668451619712435 28159793942502677429568653)
                ·
                  refine ⟨10559922728438504036088245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28159793942502677429568653 10559922728438504036088245)
                  ·
                    refine ⟨989992755791109753383273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10559922728438504036088245 989992755791109753383273)
                    ·
                      rfl

theorem cell23_5784012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 3, 5].length) (baseStart_5784012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784012 prefixEnd_5784012 := by exact prefixLift 5784012
  have htrace : WordTrace (prefixWord ++ tailWord_5784012) baseStart_5784012 baseEnd_5784012 := by
    simpa [prefixWord, tailWord_5784012, baseEnd_5784012] using wordTrace_append hprefix tailTrace_5784012
  have hstable : (prefixWord ++ tailWord_5784012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784012).length < 2 ^ (prefixWord ++ tailWord_5784012).sum := by decide
  have hdescent : baseEnd_5784012 < baseStart_5784012 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784025 : List Nat := [1, 2, 1, 2, 4, 1, 3, 2, 1, 6]
def baseStart_5784025 : Nat := 118140960795 + 5784025 * 2 ^ 59
def prefixEnd_5784025 : Nat := 4983230072969 + 3 ^ 40 * 5784025 * 2
def baseEnd_5784025 : Nat := 989994980873945903095753

theorem tailTrace_5784025 : CollatzResearch.WordTrace tailWord_5784025 prefixEnd_5784025 989994980873945903095753 := by
  unfold tailWord_5784025
  simp only [CollatzResearch.WordTrace]
  refine ⟨210960722870472732669721529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140640481913648488446481019 210960722870472732669721529)
  ·
    refine ⟨158220542152854549502291147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 210960722870472732669721529 158220542152854549502291147)
    ·
      refine ⟨237330813229281824253436721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158220542152854549502291147 237330813229281824253436721)
      ·
        refine ⟨177998109921961368190077541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 237330813229281824253436721 177998109921961368190077541)
        ·
          refine ⟨33374645610367756535639539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177998109921961368190077541 33374645610367756535639539)
          ·
            refine ⟨50061968415551634803459309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33374645610367756535639539 50061968415551634803459309)
            ·
              refine ⟨18773238155831863051297241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50061968415551634803459309 18773238155831863051297241)
              ·
                refine ⟨14079928616873897288472931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18773238155831863051297241 14079928616873897288472931)
                ·
                  refine ⟨21119892925310845932709397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14079928616873897288472931 21119892925310845932709397)
                  ·
                    refine ⟨989994980873945903095753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21119892925310845932709397 989994980873945903095753)
                    ·
                      rfl

theorem cell23_5784025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_5784025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784025 prefixEnd_5784025 := by exact prefixLift 5784025
  have htrace : WordTrace (prefixWord ++ tailWord_5784025) baseStart_5784025 baseEnd_5784025 := by
    simpa [prefixWord, tailWord_5784025, baseEnd_5784025] using wordTrace_append hprefix tailTrace_5784025
  have hstable : (prefixWord ++ tailWord_5784025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784025).length < 2 ^ (prefixWord ++ tailWord_5784025).sum := by decide
  have hdescent : baseEnd_5784025 < baseStart_5784025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5784029 : List Nat := [1, 4, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_5784029 : Nat := 118140960795 + 5784029 * 2 ^ 59
def prefixEnd_5784029 : Nat := 4983230072969 + 3 ^ 40 * 5784029 * 2
def baseEnd_5784029 : Nat := 989995665514818564545747

theorem tailTrace_5784029 : CollatzResearch.WordTrace tailWord_5784029 prefixEnd_5784029 989995665514818564545747 := by
  unfold tailWord_5784029
  simp only [CollatzResearch.WordTrace]
  refine ⟨210960868762458241352867141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 140640579174972160901911427 210960868762458241352867141)
  ·
    refine ⟨39555162892960920253662589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 210960868762458241352867141 39555162892960920253662589)
    ·
      refine ⟨14833186084860345095123471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39555162892960920253662589 14833186084860345095123471)
      ·
        refine ⟨22249779127290517642685207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14833186084860345095123471 22249779127290517642685207)
        ·
          refine ⟨33374668690935776464027811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22249779127290517642685207 33374668690935776464027811)
          ·
            refine ⟨50062003036403664696041717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33374668690935776464027811 50062003036403664696041717)
            ·
              refine ⟨4693312784662843565253911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50062003036403664696041717 4693312784662843565253911)
              ·
                refine ⟨7039969176994265347880867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4693312784662843565253911 7039969176994265347880867)
                ·
                  refine ⟨10559953765491398021821301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7039969176994265347880867 10559953765491398021821301)
                  ·
                    refine ⟨989995665514818564545747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10559953765491398021821301 989995665514818564545747)
                    ·
                      rfl

theorem cell23_5784029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_5784029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5784029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5784029 prefixEnd_5784029 := by exact prefixLift 5784029
  have htrace : WordTrace (prefixWord ++ tailWord_5784029) baseStart_5784029 baseEnd_5784029 := by
    simpa [prefixWord, tailWord_5784029, baseEnd_5784029] using wordTrace_append hprefix tailTrace_5784029
  have hstable : (prefixWord ++ tailWord_5784029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5784029).length < 2 ^ (prefixWord ++ tailWord_5784029).sum := by decide
  have hdescent : baseEnd_5784029 < baseStart_5784029 := by decide
  rcases family_descends (prefixWord ++ tailWord_5784029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
