import V185TrunkScan23Chunk1360

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8059733 : List Nat := [1, 3, 2, 2, 2, 1, 1, 6, 1, 2, 2]
def baseStart_8059733 : Nat := 118140960795 + 8059733 * 2 ^ 59
def prefixEnd_8059733 : Nat := 4983230072969 + 3 ^ 40 * 8059733 * 2
def baseEnd_8059733 : Nat := 4138516975903819991271469

theorem tailTrace_8059733 : CollatzResearch.WordTrace tailWord_8059733 prefixEnd_8059733 4138516975903819991271469 := by
  unfold tailWord_8059733
  simp only [CollatzResearch.WordTrace]
  refine ⟨293962612509971308653319853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195975075006647539102213235 293962612509971308653319853)
  ·
    refine ⟨110235979691239240744994945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293962612509971308653319853 110235979691239240744994945)
    ·
      refine ⟨82676984768429430558746209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110235979691239240744994945 82676984768429430558746209)
      ·
        refine ⟨62007738576322072919059657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82676984768429430558746209 62007738576322072919059657)
        ·
          refine ⟨46505803932241554689294743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62007738576322072919059657 46505803932241554689294743)
          ·
            refine ⟨69758705898362332033942115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46505803932241554689294743 69758705898362332033942115)
            ·
              refine ⟨104638058847543498050913173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69758705898362332033942115 104638058847543498050913173)
              ·
                refine ⟨4904909008478601471136555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104638058847543498050913173 4904909008478601471136555)
                ·
                  refine ⟨7357363512717902206704833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4904909008478601471136555 7357363512717902206704833)
                  ·
                    refine ⟨5518022634538426655028625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7357363512717902206704833 5518022634538426655028625)
                    ·
                      refine ⟨4138516975903819991271469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518022634538426655028625 4138516975903819991271469)
                      ·
                        rfl

theorem cell23_8059733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 6, 1, 2, 2].length) (baseStart_8059733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059733 prefixEnd_8059733 := by exact prefixLift 8059733
  have htrace : WordTrace (prefixWord ++ tailWord_8059733) baseStart_8059733 baseEnd_8059733 := by
    simpa [prefixWord, tailWord_8059733, baseEnd_8059733] using wordTrace_append hprefix tailTrace_8059733
  have hstable : (prefixWord ++ tailWord_8059733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059733).length < 2 ^ (prefixWord ++ tailWord_8059733).sum := by decide
  have hdescent : baseEnd_8059733 < baseStart_8059733 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059749 : List Nat := [1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 3]
def baseStart_8059749 : Nat := 118140960795 + 8059749 * 2 ^ 59
def prefixEnd_8059749 : Nat := 4983230072969 + 3 ^ 40 * 8059749 * 2
def baseEnd_8059749 : Nat := 4138525191594291928671395

theorem tailTrace_8059749 : CollatzResearch.WordTrace tailWord_8059749 prefixEnd_8059749 4138525191594291928671395 := by
  unfold tailWord_8059749
  simp only [CollatzResearch.WordTrace]
  refine ⟨293963196077913343385902301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195975464051942228923934867 293963196077913343385902301)
  ·
    refine ⟨110236198529217503769713363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293963196077913343385902301 110236198529217503769713363)
    ·
      refine ⟨165354297793826255654570045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110236198529217503769713363 165354297793826255654570045)
      ·
        refine ⟨62007861672684845870463767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165354297793826255654570045 62007861672684845870463767)
        ·
          refine ⟨93011792509027268805695651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62007861672684845870463767 93011792509027268805695651)
          ·
            refine ⟨139517688763540903208543477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93011792509027268805695651 139517688763540903208543477)
            ·
              refine ⟨13079783321581959675800951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139517688763540903208543477 13079783321581959675800951)
              ·
                refine ⟨19619674982372939513701427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13079783321581959675800951 19619674982372939513701427)
                ·
                  refine ⟨29429512473559409270552141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19619674982372939513701427 29429512473559409270552141)
                  ·
                    refine ⟨11036067177584778476457053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29429512473559409270552141 11036067177584778476457053)
                    ·
                      refine ⟨4138525191594291928671395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11036067177584778476457053 4138525191594291928671395)
                      ·
                        rfl

theorem cell23_8059749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 3, 3].length) (baseStart_8059749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059749 prefixEnd_8059749 := by exact prefixLift 8059749
  have htrace : WordTrace (prefixWord ++ tailWord_8059749) baseStart_8059749 baseEnd_8059749 := by
    simpa [prefixWord, tailWord_8059749, baseEnd_8059749] using wordTrace_append hprefix tailTrace_8059749
  have hstable : (prefixWord ++ tailWord_8059749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059749).length < 2 ^ (prefixWord ++ tailWord_8059749).sum := by decide
  have hdescent : baseEnd_8059749 < baseStart_8059749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059759 : List Nat := [1, 1, 2, 1, 3, 1, 1, 5, 3, 3, 2]
def baseStart_8059759 : Nat := 118140960795 + 8059759 * 2 ^ 59
def prefixEnd_8059759 : Nat := 4983230072969 + 3 ^ 40 * 8059759 * 2
def baseEnd_8059759 : Nat := 4138530326400836889546349

theorem tailTrace_8059759 : CollatzResearch.WordTrace tailWord_8059759 prefixEnd_8059759 4138530326400836889546349 := by
  unfold tailWord_8059759
  simp only [CollatzResearch.WordTrace]
  refine ⟨293963560807877115093766331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195975707205251410062510887 293963560807877115093766331)
  ·
    refine ⟨440945341211815672640649497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293963560807877115093766331 440945341211815672640649497)
    ·
      refine ⟨330709005908861754480487123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440945341211815672640649497 330709005908861754480487123)
      ·
        refine ⟨496063508863292631720730685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330709005908861754480487123 496063508863292631720730685)
        ·
          refine ⟨186023815823734736895274007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496063508863292631720730685 186023815823734736895274007)
          ·
            refine ⟨279035723735602105342911011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186023815823734736895274007 279035723735602105342911011)
            ·
              refine ⟨418553585603403158014366517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279035723735602105342911011 418553585603403158014366517)
              ·
                refine ⟨39239398650319046063846861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 418553585603403158014366517 39239398650319046063846861)
                ·
                  refine ⟨14714774493869642273942573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39239398650319046063846861 14714774493869642273942573)
                  ·
                    refine ⟨5518040435201115852728465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14714774493869642273942573 5518040435201115852728465)
                    ·
                      refine ⟨4138530326400836889546349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518040435201115852728465 4138530326400836889546349)
                      ·
                        rfl

theorem cell23_8059759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 5, 3, 3, 2].length) (baseStart_8059759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059759 prefixEnd_8059759 := by exact prefixLift 8059759
  have htrace : WordTrace (prefixWord ++ tailWord_8059759) baseStart_8059759 baseEnd_8059759 := by
    simpa [prefixWord, tailWord_8059759, baseEnd_8059759] using wordTrace_append hprefix tailTrace_8059759
  have hstable : (prefixWord ++ tailWord_8059759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059759).length < 2 ^ (prefixWord ++ tailWord_8059759).sum := by decide
  have hdescent : baseEnd_8059759 < baseStart_8059759 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059762 : List Nat := [3, 2, 1, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_8059762 : Nat := 118140960795 + 8059762 * 2 ^ 59
def prefixEnd_8059762 : Nat := 4983230072969 + 3 ^ 40 * 8059762 * 2
def baseEnd_8059762 : Nat := 4138531866842800377808835

theorem tailTrace_8059762 : CollatzResearch.WordTrace tailWord_8059762 prefixEnd_8059762 4138531866842800377808835 := by
  unfold tailWord_8059762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73490917556716561651531385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195975780151244164404083693 73490917556716561651531385)
  ·
    refine ⟨55118188167537421238648539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73490917556716561651531385 55118188167537421238648539)
    ·
      refine ⟨82677282251306131857972809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55118188167537421238648539 82677282251306131857972809)
      ·
        refine ⟨62007961688479598893479607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82677282251306131857972809 62007961688479598893479607)
        ·
          refine ⟨93011942532719398340219411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62007961688479598893479607 93011942532719398340219411)
          ·
            refine ⟨139517913799079097510329117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93011942532719398340219411 139517913799079097510329117)
            ·
              refine ⟨52319217674654661566373419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139517913799079097510329117 52319217674654661566373419)
              ·
                refine ⟨78478826511981992349560129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52319217674654661566373419 78478826511981992349560129)
                ·
                  refine ⟨58859119883986494262170097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78478826511981992349560129 58859119883986494262170097)
                  ·
                    refine ⟨44144339912989870696627573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58859119883986494262170097 44144339912989870696627573)
                    ·
                      refine ⟨4138531866842800377808835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44144339912989870696627573 4138531866842800377808835)
                      ·
                        rfl

theorem cell23_8059762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_8059762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059762 prefixEnd_8059762 := by exact prefixLift 8059762
  have htrace : WordTrace (prefixWord ++ tailWord_8059762) baseStart_8059762 baseEnd_8059762 := by
    simpa [prefixWord, tailWord_8059762, baseEnd_8059762] using wordTrace_append hprefix tailTrace_8059762
  have hstable : (prefixWord ++ tailWord_8059762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059762).length < 2 ^ (prefixWord ++ tailWord_8059762).sum := by decide
  have hdescent : baseEnd_8059762 < baseStart_8059762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059809 : List Nat := [1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 5]
def baseStart_8059809 : Nat := 118140960795 + 8059809 * 2 ^ 59
def prefixEnd_8059809 : Nat := 4983230072969 + 3 ^ 40 * 8059809 * 2
def baseEnd_8059809 : Nat := 4138556000433561693921119

theorem tailTrace_8059809 : CollatzResearch.WordTrace tailWord_8059809 prefixEnd_8059809 4138556000433561693921119 := by
  unfold tailWord_8059809
  simp only [CollatzResearch.WordTrace]
  refine ⟨293965384457695973633086481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195976922971797315755390987 293965384457695973633086481)
  ·
    refine ⟨220474038343271980224814861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293965384457695973633086481 220474038343271980224814861)
    ·
      refine ⟨82677764378726992584305573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220474038343271980224814861 82677764378726992584305573)
      ·
        refine ⟨15502080821011311109557295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82677764378726992584305573 15502080821011311109557295)
        ·
          refine ⟨23253121231516966664335943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15502080821011311109557295 23253121231516966664335943)
          ·
            refine ⟨34879681847275449996503915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23253121231516966664335943 34879681847275449996503915)
            ·
              refine ⟨52319522770913174994755873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34879681847275449996503915 52319522770913174994755873)
              ·
                refine ⟨39239642078184881246066905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52319522770913174994755873 39239642078184881246066905)
                ·
                  refine ⟨29429731558638660934550179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39239642078184881246066905 29429731558638660934550179)
                  ·
                    refine ⟨44144597337957991401825269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29429731558638660934550179 44144597337957991401825269)
                    ·
                      refine ⟨4138556000433561693921119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44144597337957991401825269 4138556000433561693921119)
                      ·
                        rfl

theorem cell23_8059809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_8059809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059809 prefixEnd_8059809 := by exact prefixLift 8059809
  have htrace : WordTrace (prefixWord ++ tailWord_8059809) baseStart_8059809 baseEnd_8059809 := by
    simpa [prefixWord, tailWord_8059809, baseEnd_8059809] using wordTrace_append hprefix tailTrace_8059809
  have hstable : (prefixWord ++ tailWord_8059809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059809).length < 2 ^ (prefixWord ++ tailWord_8059809).sum := by decide
  have hdescent : baseEnd_8059809 < baseStart_8059809 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059810 : List Nat := [3, 3, 1, 2, 2, 3, 1, 2, 1, 3, 2]
def baseStart_8059810 : Nat := 118140960795 + 8059810 * 2 ^ 59
def prefixEnd_8059810 : Nat := 4983230072969 + 3 ^ 40 * 8059810 * 2
def baseEnd_8059810 : Nat := 4138556513914216190008615

theorem tailTrace_8059810 : CollatzResearch.WordTrace tailWord_8059810 prefixEnd_8059810 4138556513914216190008615 := by
  unfold tailWord_8059810
  simp only [CollatzResearch.WordTrace]
  refine ⟨73491355232673087700968221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195976947287128233869248589 73491355232673087700968221)
  ·
    refine ⟨27559258212252407887863083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73491355232673087700968221 27559258212252407887863083)
    ·
      refine ⟨41338887318378611831794625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27559258212252407887863083 41338887318378611831794625)
      ·
        refine ⟨31004165488783958873845969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41338887318378611831794625 31004165488783958873845969)
        ·
          refine ⟨23253124116587969155384477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31004165488783958873845969 23253124116587969155384477)
          ·
            refine ⟨8719921543720488433269179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23253124116587969155384477 8719921543720488433269179)
            ·
              refine ⟨13079882315580732649903769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8719921543720488433269179 13079882315580732649903769)
              ·
                refine ⟨9809911736685549487427827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13079882315580732649903769 9809911736685549487427827)
                ·
                  refine ⟨14714867605028324231141741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9809911736685549487427827 14714867605028324231141741)
                  ·
                    refine ⟨5518075351885621586678153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14714867605028324231141741 5518075351885621586678153)
                    ·
                      refine ⟨4138556513914216190008615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518075351885621586678153 4138556513914216190008615)
                      ·
                        rfl

theorem cell23_8059810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_8059810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059810 prefixEnd_8059810 := by exact prefixLift 8059810
  have htrace : WordTrace (prefixWord ++ tailWord_8059810) baseStart_8059810 baseEnd_8059810 := by
    simpa [prefixWord, tailWord_8059810, baseEnd_8059810] using wordTrace_append hprefix tailTrace_8059810
  have hstable : (prefixWord ++ tailWord_8059810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059810).length < 2 ^ (prefixWord ++ tailWord_8059810).sum := by decide
  have hdescent : baseEnd_8059810 < baseStart_8059810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059812 : List Nat := [2, 3, 1, 2, 1, 2, 2, 1, 9]
def baseStart_8059812 : Nat := 118140960795 + 8059812 * 2 ^ 59
def prefixEnd_8059812 : Nat := 4983230072969 + 3 ^ 40 * 8059812 * 2
def baseEnd_8059812 : Nat := 459839726763947242464845

theorem tailTrace_8059812 : CollatzResearch.WordTrace tailWord_8059812 prefixEnd_8059812 459839726763947242464845 := by
  unfold tailWord_8059812
  simp only [CollatzResearch.WordTrace]
  refine ⟨146982746938342552572722845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195976995917790070096963793 146982746938342552572722845)
  ·
    refine ⟨55118530101878457214771067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146982746938342552572722845 55118530101878457214771067)
    ·
      refine ⟨82677795152817685822156601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55118530101878457214771067 82677795152817685822156601)
      ·
        refine ⟨62008346364613264366617451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82677795152817685822156601 62008346364613264366617451)
        ·
          refine ⟨93012519546919896549926177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62008346364613264366617451 93012519546919896549926177)
          ·
            refine ⟨69759389660189922412444633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93012519546919896549926177 69759389660189922412444633)
            ·
              refine ⟨52319542245142441809333475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69759389660189922412444633 52319542245142441809333475)
              ·
                refine ⟨78479313367713662714000213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52319542245142441809333475 78479313367713662714000213)
                ·
                  refine ⟨459839726763947242464845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78479313367713662714000213 459839726763947242464845)
                  ·
                    rfl

theorem cell23_8059812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_8059812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059812 prefixEnd_8059812 := by exact prefixLift 8059812
  have htrace : WordTrace (prefixWord ++ tailWord_8059812) baseStart_8059812 baseEnd_8059812 := by
    simpa [prefixWord, tailWord_8059812, baseEnd_8059812] using wordTrace_append hprefix tailTrace_8059812
  have hstable : (prefixWord ++ tailWord_8059812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059812).length < 2 ^ (prefixWord ++ tailWord_8059812).sum := by decide
  have hdescent : baseEnd_8059812 < baseStart_8059812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059899 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 3]
def baseStart_8059899 : Nat := 118140960795 + 8059899 * 2 ^ 59
def prefixEnd_8059899 : Nat := 4983230072969 + 3 ^ 40 * 8059899 * 2
def baseEnd_8059899 : Nat := 4138602213692466341795705

theorem tailTrace_8059899 : CollatzResearch.WordTrace tailWord_8059899 prefixEnd_8059899 4138602213692466341795705 := by
  unfold tailWord_8059899
  simp only [CollatzResearch.WordTrace]
  refine ⟨293968667027369919003862751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195979111351579946002575167 293968667027369919003862751)
  ·
    refine ⟨440953000541054878505794127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293968667027369919003862751 440953000541054878505794127)
    ·
      refine ⟨661429500811582317758691191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440953000541054878505794127 661429500811582317758691191)
      ·
        refine ⟨992144251217373476638036787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661429500811582317758691191 992144251217373476638036787)
        ·
          refine ⟨1488216376826060214957055181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992144251217373476638036787 1488216376826060214957055181)
          ·
            refine ⟨558081141309772580608895693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1488216376826060214957055181 558081141309772580608895693)
            ·
              refine ⟨209280427991164717728335885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558081141309772580608895693 209280427991164717728335885)
              ·
                refine ⟨78480160496686769148125957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209280427991164717728335885 78480160496686769148125957)
                ·
                  refine ⟨14715030093128769215273617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78480160496686769148125957 14715030093128769215273617)
                  ·
                    refine ⟨11036272569846576911455213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14715030093128769215273617 11036272569846576911455213)
                    ·
                      refine ⟨4138602213692466341795705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11036272569846576911455213 4138602213692466341795705)
                      ·
                        rfl

theorem cell23_8059899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 3].length) (baseStart_8059899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059899 prefixEnd_8059899 := by exact prefixLift 8059899
  have htrace : WordTrace (prefixWord ++ tailWord_8059899) baseStart_8059899 baseEnd_8059899 := by
    simpa [prefixWord, tailWord_8059899, baseEnd_8059899] using wordTrace_append hprefix tailTrace_8059899
  have hstable : (prefixWord ++ tailWord_8059899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059899).length < 2 ^ (prefixWord ++ tailWord_8059899).sum := by decide
  have hdescent : baseEnd_8059899 < baseStart_8059899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059940 : List Nat := [2, 3, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_8059940 : Nat := 118140960795 + 8059940 * 2 ^ 59
def prefixEnd_8059940 : Nat := 4983230072969 + 3 ^ 40 * 8059940 * 2
def baseEnd_8059940 : Nat := 1379541088799766893794339

theorem tailTrace_8059940 : CollatzResearch.WordTrace tailWord_8059940 prefixEnd_8059940 1379541088799766893794339 := by
  unfold tailWord_8059940
  simp only [CollatzResearch.WordTrace]
  refine ⟨146985081210110691503052637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195980108280147588670736849 146985081210110691503052637)
  ·
    refine ⟨55119405453791509313644739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146985081210110691503052637 55119405453791509313644739)
    ·
      refine ⟨82679108180687263970467109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55119405453791509313644739 82679108180687263970467109)
      ·
        refine ⟨15502332783878861994462583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82679108180687263970467109 15502332783878861994462583)
        ·
          refine ⟨23253499175818292991693875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15502332783878861994462583 23253499175818292991693875)
          ·
            refine ⟨34880248763727439487540813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23253499175818292991693875 34880248763727439487540813)
            ·
              refine ⟨13080093286397789807827805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34880248763727439487540813 13080093286397789807827805)
              ·
                refine ⟨4905034982399171177935427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13080093286397789807827805 4905034982399171177935427)
                ·
                  refine ⟨7357552473598756766903141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905034982399171177935427 7357552473598756766903141)
                  ·
                    refine ⟨1379541088799766893794339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357552473598756766903141 1379541088799766893794339)
                    ·
                      rfl

theorem cell23_8059940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_8059940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059940 prefixEnd_8059940 := by exact prefixLift 8059940
  have htrace : WordTrace (prefixWord ++ tailWord_8059940) baseStart_8059940 baseEnd_8059940 := by
    simpa [prefixWord, tailWord_8059940, baseEnd_8059940] using wordTrace_append hprefix tailTrace_8059940
  have hstable : (prefixWord ++ tailWord_8059940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059940).length < 2 ^ (prefixWord ++ tailWord_8059940).sum := by decide
  have hdescent : baseEnd_8059940 < baseStart_8059940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8059996 : List Nat := [2, 2, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_8059996 : Nat := 118140960795 + 8059996 * 2 ^ 59
def prefixEnd_8059996 : Nat := 4983230072969 + 3 ^ 40 * 8059996 * 2
def baseEnd_8059996 : Nat := 1379550673771984154094253

theorem tailTrace_8059996 : CollatzResearch.WordTrace tailWord_8059996 prefixEnd_8059996 1379550673771984154094253 := by
  unfold tailWord_8059996
  simp only [CollatzResearch.WordTrace]
  refine ⟨146986102454009252285071921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195981469938679003046762561 146986102454009252285071921)
  ·
    refine ⟨110239576840506939213803941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146986102454009252285071921 110239576840506939213803941)
    ·
      refine ⟨20669920657595051102588239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110239576840506939213803941 20669920657595051102588239)
      ·
        refine ⟨31004880986392576653882359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20669920657595051102588239 31004880986392576653882359)
        ·
          refine ⟨46507321479588864980823539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31004880986392576653882359 46507321479588864980823539)
          ·
            refine ⟨69760982219383297471235309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46507321479588864980823539 69760982219383297471235309)
            ·
              refine ⟨26160368332268736551713241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69760982219383297471235309 26160368332268736551713241)
              ·
                refine ⟨19620276249201552413784931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26160368332268736551713241 19620276249201552413784931)
                ·
                  refine ⟨29430414373802328620677397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19620276249201552413784931 29430414373802328620677397)
                  ·
                    refine ⟨1379550673771984154094253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29430414373802328620677397 1379550673771984154094253)
                    ·
                      rfl

theorem cell23_8059996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_8059996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8059996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8059996 prefixEnd_8059996 := by exact prefixLift 8059996
  have htrace : WordTrace (prefixWord ++ tailWord_8059996) baseStart_8059996 baseEnd_8059996 := by
    simpa [prefixWord, tailWord_8059996, baseEnd_8059996] using wordTrace_append hprefix tailTrace_8059996
  have hstable : (prefixWord ++ tailWord_8059996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8059996).length < 2 ^ (prefixWord ++ tailWord_8059996).sum := by decide
  have hdescent : baseEnd_8059996 < baseStart_8059996 := by decide
  rcases family_descends (prefixWord ++ tailWord_8059996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060013 : List Nat := [1, 5, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_8060013 : Nat := 118140960795 + 8060013 * 2 ^ 59
def prefixEnd_8060013 : Nat := 4983230072969 + 3 ^ 40 * 8060013 * 2
def baseEnd_8060013 : Nat := 1379553583495692965256727

theorem tailTrace_8060013 : CollatzResearch.WordTrace tailWord_8060013 prefixEnd_8060013 1379553583495692965256727 := by
  unfold tailWord_8060013
  simp only [CollatzResearch.WordTrace]
  refine ⟨293972824948956916473512693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195981883299304610982341795 293972824948956916473512693)
  ·
    refine ⟨27559952338964710919391815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293972824948956916473512693 27559952338964710919391815)
    ·
      refine ⟨41339928508447066379087723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27559952338964710919391815 41339928508447066379087723)
      ·
        refine ⟨62009892762670599568631585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41339928508447066379087723 62009892762670599568631585)
        ·
          refine ⟨46507419572002949676473689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62009892762670599568631585 46507419572002949676473689)
          ·
            refine ⟨34880564679002212257355267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46507419572002949676473689 34880564679002212257355267)
            ·
              refine ⟨52320847018503318386032901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34880564679002212257355267 52320847018503318386032901)
              ·
                refine ⟨9810158815969372197381169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52320847018503318386032901 9810158815969372197381169)
                ·
                  refine ⟨7357619111977029148035877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9810158815969372197381169 7357619111977029148035877)
                  ·
                    refine ⟨1379553583495692965256727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357619111977029148035877 1379553583495692965256727)
                    ·
                      rfl

theorem cell23_8060013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_8060013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060013 prefixEnd_8060013 := by exact prefixLift 8060013
  have htrace : WordTrace (prefixWord ++ tailWord_8060013) baseStart_8060013 baseEnd_8060013 := by
    simpa [prefixWord, tailWord_8060013, baseEnd_8060013] using wordTrace_append hprefix tailTrace_8060013
  have hstable : (prefixWord ++ tailWord_8060013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060013).length < 2 ^ (prefixWord ++ tailWord_8060013).sum := by decide
  have hdescent : baseEnd_8060013 < baseStart_8060013 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060014 : List Nat := [4, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_8060014 : Nat := 118140960795 + 8060014 * 2 ^ 59
def prefixEnd_8060014 : Nat := 4983230072969 + 3 ^ 40 * 8060014 * 2
def baseEnd_8060014 : Nat := 4138661263967733391857677

theorem tailTrace_8060014 : CollatzResearch.WordTrace tailWord_8060014 prefixEnd_8060014 4138661263967733391857677 := by
  unfold tailWord_8060014
  simp only [CollatzResearch.WordTrace]
  refine ⟨36746607677744161705537387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195981907614635529096199397 36746607677744161705537387)
  ·
    refine ⟨55119911516616242558306081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36746607677744161705537387 55119911516616242558306081)
    ·
      refine ⟨41339933637462181918729561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55119911516616242558306081 41339933637462181918729561)
      ·
        refine ⟨31004950228096636439047171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41339933637462181918729561 31004950228096636439047171)
        ·
          refine ⟨46507425342144954658570757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31004950228096636439047171 46507425342144954658570757)
          ·
            refine ⟨8720142251652178998482017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46507425342144954658570757 8720142251652178998482017)
            ·
              refine ⟨6540106688739134248861513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8720142251652178998482017 6540106688739134248861513)
              ·
                refine ⟨4905080016554350686646135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6540106688739134248861513 4905080016554350686646135)
                ·
                  refine ⟨7357620024831526029969203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905080016554350686646135 7357620024831526029969203)
                  ·
                    refine ⟨11036430037247289044953805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7357620024831526029969203 11036430037247289044953805)
                    ·
                      refine ⟨4138661263967733391857677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11036430037247289044953805 4138661263967733391857677)
                      ·
                        rfl

theorem cell23_8060014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_8060014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060014 prefixEnd_8060014 := by exact prefixLift 8060014
  have htrace : WordTrace (prefixWord ++ tailWord_8060014) baseStart_8060014 baseEnd_8060014 := by
    simpa [prefixWord, tailWord_8060014, baseEnd_8060014] using wordTrace_append hprefix tailTrace_8060014
  have hstable : (prefixWord ++ tailWord_8060014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060014).length < 2 ^ (prefixWord ++ tailWord_8060014).sum := by decide
  have hdescent : baseEnd_8060014 < baseStart_8060014 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060033 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 4]
def baseStart_8060033 : Nat := 118140960795 + 8060033 * 2 ^ 59
def prefixEnd_8060033 : Nat := 4983230072969 + 3 ^ 40 * 8060033 * 2
def baseEnd_8060033 : Nat := 4138671020100168817520089

theorem tailTrace_8060033 : CollatzResearch.WordTrace tailWord_8060033 prefixEnd_8060033 4138671020100168817520089 := by
  unfold tailWord_8060033
  simp only [CollatzResearch.WordTrace]
  refine ⟨293973554408884459889240753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195982369605922973259493835 293973554408884459889240753)
  ·
    refine ⟨220480165806663344916930565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293973554408884459889240753 220480165806663344916930565)
    ·
      refine ⟨41340031088749377171924481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220480165806663344916930565 41340031088749377171924481)
      ·
        refine ⟨31005023316562032878943361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41340031088749377171924481 31005023316562032878943361)
        ·
          refine ⟨23253767487421524659207521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31005023316562032878943361 23253767487421524659207521)
          ·
            refine ⟨17440325615566143494405641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23253767487421524659207521 17440325615566143494405641)
            ·
              refine ⟨13080244211674607620804231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17440325615566143494405641 13080244211674607620804231)
              ·
                refine ⟨19620366317511911431206347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13080244211674607620804231 19620366317511911431206347)
                ·
                  refine ⟨29430549476267867146809521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19620366317511911431206347 29430549476267867146809521)
                  ·
                    refine ⟨22072912107200900360107141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29430549476267867146809521 22072912107200900360107141)
                    ·
                      refine ⟨4138671020100168817520089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22072912107200900360107141 4138671020100168817520089)
                      ·
                        rfl

theorem cell23_8060033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_8060033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060033 prefixEnd_8060033 := by exact prefixLift 8060033
  have htrace : WordTrace (prefixWord ++ tailWord_8060033) baseStart_8060033 baseEnd_8060033 := by
    simpa [prefixWord, tailWord_8060033, baseEnd_8060033] using wordTrace_append hprefix tailTrace_8060033
  have hstable : (prefixWord ++ tailWord_8060033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060033).length < 2 ^ (prefixWord ++ tailWord_8060033).sum := by decide
  have hdescent : baseEnd_8060033 < baseStart_8060033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060039 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 4, 7]
def baseStart_8060039 : Nat := 118140960795 + 8060039 * 2 ^ 59
def prefixEnd_8060039 : Nat := 4983230072969 + 3 ^ 40 * 8060039 * 2
def baseEnd_8060039 : Nat := 1379558033661365264681687

theorem tailTrace_8060039 : CollatzResearch.WordTrace tailWord_8060039 prefixEnd_8060039 1379558033661365264681687 := by
  unfold tailWord_8060039
  simp only [CollatzResearch.WordTrace]
  refine ⟨293973773246862722913959171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195982515497908481942639447 293973773246862722913959171)
  ·
    refine ⟨440960659870294084370938757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293973773246862722913959171 440960659870294084370938757)
    ·
      refine ⟨82680123725680140819551017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440960659870294084370938757 82680123725680140819551017)
      ·
        refine ⟨62010092794260105614663263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82680123725680140819551017 62010092794260105614663263)
        ·
          refine ⟨93015139191390158421994895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62010092794260105614663263 93015139191390158421994895)
          ·
            refine ⟨139522708787085237632992343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93015139191390158421994895 139522708787085237632992343)
            ·
              refine ⟨209284063180627856449488515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139522708787085237632992343 209284063180627856449488515)
              ·
                refine ⟨313926094770941784674232773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209284063180627856449488515 313926094770941784674232773)
                ·
                  refine ⟨58861142769551584626418645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313926094770941784674232773 58861142769551584626418645)
                  ·
                    refine ⟨1379558033661365264681687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58861142769551584626418645 1379558033661365264681687)
                    ·
                      rfl

theorem cell23_8060039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_8060039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060039 prefixEnd_8060039 := by exact prefixLift 8060039
  have htrace : WordTrace (prefixWord ++ tailWord_8060039) baseStart_8060039 baseEnd_8060039 := by
    simpa [prefixWord, tailWord_8060039, baseEnd_8060039] using wordTrace_append hprefix tailTrace_8060039
  have hstable : (prefixWord ++ tailWord_8060039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060039).length < 2 ^ (prefixWord ++ tailWord_8060039).sum := by decide
  have hdescent : baseEnd_8060039 < baseStart_8060039 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060059 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 4]
def baseStart_8060059 : Nat := 118140960795 + 8060059 * 2 ^ 59
def prefixEnd_8060059 : Nat := 4983230072969 + 3 ^ 40 * 8060059 * 2
def baseEnd_8060059 : Nat := 4138684370597185715794969

theorem tailTrace_8060059 : CollatzResearch.WordTrace tailWord_8060059 prefixEnd_8060059 4138684370597185715794969 := by
  unfold tailWord_8060059
  simp only [CollatzResearch.WordTrace]
  refine ⟨293974502706790266329687231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195983001804526844219791487 293974502706790266329687231)
  ·
    refine ⟨440961754060185399494530847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293974502706790266329687231 440961754060185399494530847)
    ·
      refine ⟨661442631090278099241796271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440961754060185399494530847 661442631090278099241796271)
      ·
        refine ⟨992163946635417148862694407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661442631090278099241796271 992163946635417148862694407)
        ·
          refine ⟨1488245919953125723294041611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992163946635417148862694407 1488245919953125723294041611)
          ·
            refine ⟨2232368879929688584941062417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488245919953125723294041611 2232368879929688584941062417)
            ·
              refine ⟨1674276659947266438705796813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232368879929688584941062417 1674276659947266438705796813)
              ·
                refine ⟨627853747480224914514673805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1674276659947266438705796813 627853747480224914514673805)
                ·
                  refine ⟨235445155305084342943002677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 627853747480224914514673805 235445155305084342943002677)
                  ·
                    refine ⟨22072983309851657150906501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 235445155305084342943002677 22072983309851657150906501)
                    ·
                      refine ⟨4138684370597185715794969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22072983309851657150906501 4138684370597185715794969)
                      ·
                        rfl

theorem cell23_8060059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 4].length) (baseStart_8060059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060059 prefixEnd_8060059 := by exact prefixLift 8060059
  have htrace : WordTrace (prefixWord ++ tailWord_8060059) baseStart_8060059 baseEnd_8060059 := by
    simpa [prefixWord, tailWord_8060059, baseEnd_8060059] using wordTrace_append hprefix tailTrace_8060059
  have hstable : (prefixWord ++ tailWord_8060059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060059).length < 2 ^ (prefixWord ++ tailWord_8060059).sum := by decide
  have hdescent : baseEnd_8060059 < baseStart_8060059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060097 : List Nat := [1, 2, 6, 1, 1, 1, 1, 4, 1, 3, 2]
def baseStart_8060097 : Nat := 118140960795 + 8060097 * 2 ^ 59
def prefixEnd_8060097 : Nat := 4983230072969 + 3 ^ 40 * 8060097 * 2
def baseEnd_8060097 : Nat := 4138703882862056567119795

theorem tailTrace_8060097 : CollatzResearch.WordTrace tailWord_8060097 prefixEnd_8060097 4138703882862056567119795 := by
  unfold tailWord_8060097
  simp only [CollatzResearch.WordTrace]
  refine ⟨293975888680652598819570545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195983925787101732546380363 293975888680652598819570545)
  ·
    refine ⟨220481916510489449114677909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293975888680652598819570545 220481916510489449114677909)
    ·
      refine ⟨10335089836429192927250527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 220481916510489449114677909 10335089836429192927250527)
      ·
        refine ⟨15502634754643789390875791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335089836429192927250527 15502634754643789390875791)
        ·
          refine ⟨23253952131965684086313687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15502634754643789390875791 23253952131965684086313687)
          ·
            refine ⟨34880928197948526129470531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23253952131965684086313687 34880928197948526129470531)
            ·
              refine ⟨52321392296922789194205797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34880928197948526129470531 52321392296922789194205797)
              ·
                refine ⟨9810261055673022973913587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52321392296922789194205797 9810261055673022973913587)
                ·
                  refine ⟨14715391583509534460870381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9810261055673022973913587 14715391583509534460870381)
                  ·
                    refine ⟨5518271843816075422826393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14715391583509534460870381 5518271843816075422826393)
                    ·
                      refine ⟨4138703882862056567119795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518271843816075422826393 4138703882862056567119795)
                      ·
                        rfl

theorem cell23_8060097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 4, 1, 3, 2].length) (baseStart_8060097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060097 prefixEnd_8060097 := by exact prefixLift 8060097
  have htrace : WordTrace (prefixWord ++ tailWord_8060097) baseStart_8060097 baseEnd_8060097 := by
    simpa [prefixWord, tailWord_8060097, baseEnd_8060097] using wordTrace_append hprefix tailTrace_8060097
  have hstable : (prefixWord ++ tailWord_8060097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060097).length < 2 ^ (prefixWord ++ tailWord_8060097).sum := by decide
  have hdescent : baseEnd_8060097 < baseStart_8060097 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060099 : List Nat := [1, 1, 1, 3, 1, 1, 1, 5, 9]
def baseStart_8060099 : Nat := 118140960795 + 8060099 * 2 ^ 59
def prefixEnd_8060099 : Nat := 4983230072969 + 3 ^ 40 * 8060099 * 2
def baseEnd_8060099 : Nat := 459856101091485062143865

theorem tailTrace_8060099 : CollatzResearch.WordTrace tailWord_8060099 prefixEnd_8060099 459856101091485062143865 := by
  unfold tailWord_8060099
  simp only [CollatzResearch.WordTrace]
  refine ⟨293975961626645353161143351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195983974417763568774095567 293975961626645353161143351)
  ·
    refine ⟨440963942439968029741715027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293975961626645353161143351 440963942439968029741715027)
    ·
      refine ⟨661445913659952044612572541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440963942439968029741715027 661445913659952044612572541)
      ·
        refine ⟨248042217622482016729714703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661445913659952044612572541 248042217622482016729714703)
        ·
          refine ⟨372063326433723025094572055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248042217622482016729714703 372063326433723025094572055)
          ·
            refine ⟨558094989650584537641858083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372063326433723025094572055 558094989650584537641858083)
            ·
              refine ⟨837142484475876806462787125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558094989650584537641858083 837142484475876806462787125)
              ·
                refine ⟨78482107919613450605886293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 837142484475876806462787125 78482107919613450605886293)
                ·
                  refine ⟨459856101091485062143865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78482107919613450605886293 459856101091485062143865)
                  ·
                    rfl

theorem cell23_8060099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 5, 9].length) (baseStart_8060099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060099 prefixEnd_8060099 := by exact prefixLift 8060099
  have htrace : WordTrace (prefixWord ++ tailWord_8060099) baseStart_8060099 baseEnd_8060099 := by
    simpa [prefixWord, tailWord_8060099, baseEnd_8060099] using wordTrace_append hprefix tailTrace_8060099
  have hstable : (prefixWord ++ tailWord_8060099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060099).length < 2 ^ (prefixWord ++ tailWord_8060099).sum := by decide
  have hdescent : baseEnd_8060099 < baseStart_8060099 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060148 : List Nat := [2, 6, 1, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_8060148 : Nat := 118140960795 + 8060148 * 2 ^ 59
def prefixEnd_8060148 : Nat := 4983230072969 + 3 ^ 40 * 8060148 * 2
def baseEnd_8060148 : Nat := 4138730070375435867582061

theorem tailTrace_8060148 : CollatzResearch.WordTrace tailWord_8060148 prefixEnd_8060148 4138730070375435867582061 := by
  unfold tailWord_8060148
  simp only [CollatzResearch.WordTrace]
  refine ⟨146988874401733917264838549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195985165868978556353118065 146988874401733917264838549)
  ·
    refine ⟨6890103487581277371789307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 146988874401733917264838549 6890103487581277371789307)
    ·
      refine ⟨10335155231371916057683961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6890103487581277371789307 10335155231371916057683961)
      ·
        refine ⟨7751366423528937043262971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10335155231371916057683961 7751366423528937043262971)
        ·
          refine ⟨11627049635293405564894457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7751366423528937043262971 11627049635293405564894457)
          ·
            refine ⟨8720287226470054173670843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11627049635293405564894457 8720287226470054173670843)
            ·
              refine ⟨13080430839705081260506265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720287226470054173670843 13080430839705081260506265)
              ·
                refine ⟨9810323129778810945379699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13080430839705081260506265 9810323129778810945379699)
                ·
                  refine ⟨14715484694668216418069549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9810323129778810945379699 14715484694668216418069549)
                  ·
                    refine ⟨5518306760500581156776081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14715484694668216418069549 5518306760500581156776081)
                    ·
                      refine ⟨4138730070375435867582061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518306760500581156776081 4138730070375435867582061)
                      ·
                        rfl

theorem cell23_8060148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_8060148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060148 prefixEnd_8060148 := by exact prefixLift 8060148
  have htrace : WordTrace (prefixWord ++ tailWord_8060148) baseStart_8060148 baseEnd_8060148 := by
    simpa [prefixWord, tailWord_8060148, baseEnd_8060148] using wordTrace_append hprefix tailTrace_8060148
  have hstable : (prefixWord ++ tailWord_8060148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060148).length < 2 ^ (prefixWord ++ tailWord_8060148).sum := by decide
  have hdescent : baseEnd_8060148 < baseStart_8060148 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060163 : List Nat := [1, 1, 1, 3, 2, 5, 2, 1, 2, 5]
def baseStart_8060163 : Nat := 118140960795 + 8060163 * 2 ^ 59
def prefixEnd_8060163 : Nat := 4983230072969 + 3 ^ 40 * 8060163 * 2
def baseEnd_8060163 : Nat := 1379579257528417769631497

theorem tailTrace_8060163 : CollatzResearch.WordTrace tailWord_8060163 prefixEnd_8060163 1379579257528417769631497 := by
  unfold tailWord_8060163
  simp only [CollatzResearch.WordTrace]
  refine ⟨293978295898413492091473143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195985530598942328060982095 293978295898413492091473143)
  ·
    refine ⟨440967443847620238137209715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293978295898413492091473143 440967443847620238137209715)
    ·
      refine ⟨661451165771430357205814573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440967443847620238137209715 661451165771430357205814573)
      ·
        refine ⟨248044187164286383952180465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661451165771430357205814573 248044187164286383952180465)
        ·
          refine ⟨186033140373214787964135349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248044187164286383952180465 186033140373214787964135349)
          ·
            refine ⟨17440606909988886371637689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186033140373214787964135349 17440606909988886371637689)
            ·
              refine ⟨13080455182491664778728267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17440606909988886371637689 13080455182491664778728267)
              ·
                refine ⟨19620682773737497168092401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13080455182491664778728267 19620682773737497168092401)
                ·
                  refine ⟨14715512080303122876069301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19620682773737497168092401 14715512080303122876069301)
                  ·
                    refine ⟨1379579257528417769631497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14715512080303122876069301 1379579257528417769631497)
                    ·
                      rfl

theorem cell23_8060163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 1, 2, 5].length) (baseStart_8060163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060163 prefixEnd_8060163 := by exact prefixLift 8060163
  have htrace : WordTrace (prefixWord ++ tailWord_8060163) baseStart_8060163 baseEnd_8060163 := by
    simpa [prefixWord, tailWord_8060163, baseEnd_8060163] using wordTrace_append hprefix tailTrace_8060163
  have hstable : (prefixWord ++ tailWord_8060163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060163).length < 2 ^ (prefixWord ++ tailWord_8060163).sum := by decide
  have hdescent : baseEnd_8060163 < baseStart_8060163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060183 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_8060183 : Nat := 118140960795 + 8060183 * 2 ^ 59
def prefixEnd_8060183 : Nat := 4983230072969 + 3 ^ 40 * 8060183 * 2
def baseEnd_8060183 : Nat := 4138748042198343230644399

theorem tailTrace_8060183 : CollatzResearch.WordTrace tailWord_8060183 prefixEnd_8060183 4138748042198343230644399 := by
  unfold tailWord_8060183
  simp only [CollatzResearch.WordTrace]
  refine ⟨293979025358341035507201203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195986016905560690338134135 293979025358341035507201203)
  ·
    refine ⟨440968538037511553260801805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293979025358341035507201203 440968538037511553260801805)
    ·
      refine ⟨165363201764066832472800677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440968538037511553260801805 165363201764066832472800677)
      ·
        refine ⟨31005600330762531088650127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165363201764066832472800677 31005600330762531088650127)
        ·
          refine ⟨46508400496143796632975191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31005600330762531088650127 46508400496143796632975191)
          ·
            refine ⟨69762600744215694949462787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46508400496143796632975191 69762600744215694949462787)
            ·
              refine ⟨104643901116323542424194181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69762600744215694949462787 104643901116323542424194181)
              ·
                refine ⟨19620731459310664204536409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104643901116323542424194181 19620731459310664204536409)
                ·
                  refine ⟨14715548594482998153402307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19620731459310664204536409 14715548594482998153402307)
                  ·
                    refine ⟨22073322891724497230103461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14715548594482998153402307 22073322891724497230103461)
                    ·
                      refine ⟨4138748042198343230644399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22073322891724497230103461 4138748042198343230644399)
                      ·
                        rfl

theorem cell23_8060183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_8060183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060183 prefixEnd_8060183 := by exact prefixLift 8060183
  have htrace : WordTrace (prefixWord ++ tailWord_8060183) baseStart_8060183 baseEnd_8060183 := by
    simpa [prefixWord, tailWord_8060183, baseEnd_8060183] using wordTrace_append hprefix tailTrace_8060183
  have hstable : (prefixWord ++ tailWord_8060183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060183).length < 2 ^ (prefixWord ++ tailWord_8060183).sum := by decide
  have hdescent : baseEnd_8060183 < baseStart_8060183 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060193 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 3, 4]
def baseStart_8060193 : Nat := 118140960795 + 8060193 * 2 ^ 59
def prefixEnd_8060193 : Nat := 4983230072969 + 3 ^ 40 * 8060193 * 2
def baseEnd_8060193 : Nat := 1379584392334962730506451

theorem tailTrace_8060193 : CollatzResearch.WordTrace tailWord_8060193 prefixEnd_8060193 1379584392334962730506451 := by
  unfold tailWord_8060193
  simp only [CollatzResearch.WordTrace]
  refine ⟨293979390088304807215065233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195986260058869871476710155 293979390088304807215065233)
  ·
    refine ⟨220484542566228605411298925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293979390088304807215065233 220484542566228605411298925)
    ·
      refine ⟨82681703462335727029237097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220484542566228605411298925 82681703462335727029237097)
      ·
        refine ⟨62011277596751795271927823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82681703462335727029237097 62011277596751795271927823)
        ·
          refine ⟨93016916395127692907891735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62011277596751795271927823 93016916395127692907891735)
          ·
            refine ⟨139525374592691539361837603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93016916395127692907891735 139525374592691539361837603)
            ·
              refine ⟨209288061889037309042756405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139525374592691539361837603 209288061889037309042756405)
              ·
                refine ⟨19620755802097247722758413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209288061889037309042756405 19620755802097247722758413)
                ·
                  refine ⟨7357783425786467896034405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19620755802097247722758413 7357783425786467896034405)
                  ·
                    refine ⟨1379584392334962730506451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357783425786467896034405 1379584392334962730506451)
                    ·
                      rfl

theorem cell23_8060193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_8060193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060193 prefixEnd_8060193 := by exact prefixLift 8060193
  have htrace : WordTrace (prefixWord ++ tailWord_8060193) baseStart_8060193 baseEnd_8060193 := by
    simpa [prefixWord, tailWord_8060193, baseEnd_8060193] using wordTrace_append hprefix tailTrace_8060193
  have hstable : (prefixWord ++ tailWord_8060193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060193).length < 2 ^ (prefixWord ++ tailWord_8060193).sum := by decide
  have hdescent : baseEnd_8060193 < baseStart_8060193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060200 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 1, 6, 2]
def baseStart_8060200 : Nat := 118140960795 + 8060200 * 2 ^ 59
def prefixEnd_8060200 : Nat := 4983230072969 + 3 ^ 40 * 8060200 * 2
def baseEnd_8060200 : Nat := 4138756771369469664131821

theorem tailTrace_8060200 : CollatzResearch.WordTrace tailWord_8060200 prefixEnd_8060200 4138756771369469664131821 := by
  unfold tailWord_8060200
  simp only [CollatzResearch.WordTrace]
  refine ⟨146989822699639723705285027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195986430266186298273713369 146989822699639723705285027)
  ·
    refine ⟨220484734049459585557927541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146989822699639723705285027 220484734049459585557927541)
    ·
      refine ⟨20670443817136836146055707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220484734049459585557927541 20670443817136836146055707)
      ·
        refine ⟨31005665725705254219083561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20670443817136836146055707 31005665725705254219083561)
        ·
          refine ⟨23254249294278940664312671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31005665725705254219083561 23254249294278940664312671)
          ·
            refine ⟨34881373941418410996469007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23254249294278940664312671 34881373941418410996469007)
            ·
              refine ⟨52322060912127616494703511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34881373941418410996469007 52322060912127616494703511)
              ·
                refine ⟨78483091368191424742055267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52322060912127616494703511 78483091368191424742055267)
                ·
                  refine ⟨117724637052287137113082901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78483091368191424742055267 117724637052287137113082901)
                  ·
                    refine ⟨5518342361825959552175761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117724637052287137113082901 5518342361825959552175761)
                    ·
                      refine ⟨4138756771369469664131821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518342361825959552175761 4138756771369469664131821)
                      ·
                        rfl

theorem cell23_8060200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 1, 6, 2].length) (baseStart_8060200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060200 prefixEnd_8060200 := by exact prefixLift 8060200
  have htrace : WordTrace (prefixWord ++ tailWord_8060200) baseStart_8060200 baseEnd_8060200 := by
    simpa [prefixWord, tailWord_8060200, baseEnd_8060200] using wordTrace_append hprefix tailTrace_8060200
  have hstable : (prefixWord ++ tailWord_8060200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060200).length < 2 ^ (prefixWord ++ tailWord_8060200).sum := by decide
  have hdescent : baseEnd_8060200 < baseStart_8060200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060210 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_8060210 : Nat := 118140960795 + 8060210 * 2 ^ 59
def prefixEnd_8060210 : Nat := 4983230072969 + 3 ^ 40 * 8060210 * 2
def baseEnd_8060210 : Nat := 1379587302058671541668925

theorem tailTrace_8060210 : CollatzResearch.WordTrace tailWord_8060210 prefixEnd_8060210 1379587302058671541668925 := by
  unfold tailWord_8060210
  simp only [CollatzResearch.WordTrace]
  refine ⟨73495002532310804779608521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195986673419495479412289389 73495002532310804779608521)
  ·
    refine ⟨55121251899233103584706391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73495002532310804779608521 55121251899233103584706391)
    ·
      refine ⟨82681877848849655377059587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55121251899233103584706391 82681877848849655377059587)
      ·
        refine ⟨124022816773274483065589381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82681877848849655377059587 124022816773274483065589381)
        ·
          refine ⟨23254278144988965574798009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124022816773274483065589381 23254278144988965574798009)
          ·
            refine ⟨17440708608741724181098507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23254278144988965574798009 17440708608741724181098507)
            ·
              refine ⟨26161062913112586271647761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17440708608741724181098507 26161062913112586271647761)
              ·
                refine ⟨19620797184834439703735821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26161062913112586271647761 19620797184834439703735821)
                ·
                  refine ⟨7357798944312914888900933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19620797184834439703735821 7357798944312914888900933)
                  ·
                    refine ⟨1379587302058671541668925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357798944312914888900933 1379587302058671541668925)
                    ·
                      rfl

theorem cell23_8060210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_8060210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060210 prefixEnd_8060210 := by exact prefixLift 8060210
  have htrace : WordTrace (prefixWord ++ tailWord_8060210) baseStart_8060210 baseEnd_8060210 := by
    simpa [prefixWord, tailWord_8060210, baseEnd_8060210] using wordTrace_append hprefix tailTrace_8060210
  have hstable : (prefixWord ++ tailWord_8060210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060210).length < 2 ^ (prefixWord ++ tailWord_8060210).sum := by decide
  have hdescent : baseEnd_8060210 < baseStart_8060210 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060214 : List Nat := [5, 1, 2, 3, 1, 2, 1, 1, 2, 5]
def baseStart_8060214 : Nat := 118140960795 + 8060214 * 2 ^ 59
def prefixEnd_8060214 : Nat := 4983230072969 + 3 ^ 40 * 8060214 * 2
def baseEnd_8060214 : Nat := 1379587986699544203118919

theorem tailTrace_8060214 : CollatzResearch.WordTrace tailWord_8060214 prefixEnd_8060214 1379587986699544203118919 := by
  unfold tailWord_8060214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18373759751326795487598731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195986770680819151867719797 18373759751326795487598731)
  ·
    refine ⟨27560639626990193231398097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18373759751326795487598731 27560639626990193231398097)
    ·
      refine ⟨20670479720242644923548573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27560639626990193231398097 20670479720242644923548573)
      ·
        refine ⟨7751429895090991846330715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20670479720242644923548573 7751429895090991846330715)
        ·
          refine ⟨11627144842636487769496073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7751429895090991846330715 11627144842636487769496073)
          ·
            refine ⟨8720358631977365827122055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11627144842636487769496073 8720358631977365827122055)
            ·
              refine ⟨13080537947966048740683083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720358631977365827122055 13080537947966048740683083)
              ·
                refine ⟨19620806921949073111024625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13080537947966048740683083 19620806921949073111024625)
                ·
                  refine ⟨14715605191461804833268469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19620806921949073111024625 14715605191461804833268469)
                  ·
                    refine ⟨1379587986699544203118919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14715605191461804833268469 1379587986699544203118919)
                    ·
                      rfl

theorem cell23_8060214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_8060214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060214 prefixEnd_8060214 := by exact prefixLift 8060214
  have htrace : WordTrace (prefixWord ++ tailWord_8060214) baseStart_8060214 baseEnd_8060214 := by
    simpa [prefixWord, tailWord_8060214, baseEnd_8060214] using wordTrace_append hprefix tailTrace_8060214
  have hstable : (prefixWord ++ tailWord_8060214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060214).length < 2 ^ (prefixWord ++ tailWord_8060214).sum := by decide
  have hdescent : baseEnd_8060214 < baseStart_8060214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060217 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 4]
def baseStart_8060217 : Nat := 118140960795 + 8060217 * 2 ^ 59
def prefixEnd_8060217 : Nat := 4983230072969 + 3 ^ 40 * 8060217 * 2
def baseEnd_8060217 : Nat := 4138765500540596097619243

theorem tailTrace_8060217 : CollatzResearch.WordTrace tailWord_8060217 prefixEnd_8060217 4138765500540596097619243 := by
  unfold tailWord_8060217
  simp only [CollatzResearch.WordTrace]
  refine ⟨293980265440217859313938905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195986843626811906209292603 293980265440217859313938905)
  ·
    refine ⟨220485199080163394485454179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293980265440217859313938905 220485199080163394485454179)
    ·
      refine ⟨330727798620245091728181269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220485199080163394485454179 330727798620245091728181269)
      ·
        refine ⟨15502865560323988674758497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 330727798620245091728181269 15502865560323988674758497)
        ·
          refine ⟨11627149170242991506068873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15502865560323988674758497 11627149170242991506068873)
          ·
            refine ⟨8720361877682243629551655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11627149170242991506068873 8720361877682243629551655)
            ·
              refine ⟨13080542816523365444327483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720361877682243629551655 13080542816523365444327483)
              ·
                refine ⟨19620814224785048166491225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13080542816523365444327483 19620814224785048166491225)
                ·
                  refine ⟨14715610668588786124868419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19620814224785048166491225 14715610668588786124868419)
                  ·
                    refine ⟨22073416002883179187302629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14715610668588786124868419 22073416002883179187302629)
                    ·
                      refine ⟨4138765500540596097619243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22073416002883179187302629 4138765500540596097619243)
                      ·
                        rfl

theorem cell23_8060217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_8060217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060217 prefixEnd_8060217 := by exact prefixLift 8060217
  have htrace : WordTrace (prefixWord ++ tailWord_8060217) baseStart_8060217 baseEnd_8060217 := by
    simpa [prefixWord, tailWord_8060217, baseEnd_8060217] using wordTrace_append hprefix tailTrace_8060217
  have hstable : (prefixWord ++ tailWord_8060217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060217).length < 2 ^ (prefixWord ++ tailWord_8060217).sum := by decide
  have hdescent : baseEnd_8060217 < baseStart_8060217 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060220 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_8060220 : Nat := 118140960795 + 8060220 * 2 ^ 59
def prefixEnd_8060220 : Nat := 4983230072969 + 3 ^ 40 * 8060220 * 2
def baseEnd_8060220 : Nat := 4138767040982559585881729

theorem tailTrace_8060220 : CollatzResearch.WordTrace tailWord_8060220 prefixEnd_8060220 4138767040982559585881729 := by
  unfold tailWord_8060220
  simp only [CollatzResearch.WordTrace]
  refine ⟨146990187429603495413149057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195986916572804660550865409 146990187429603495413149057)
  ·
    refine ⟨110242640572202621559861793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146990187429603495413149057 110242640572202621559861793)
    ·
      refine ⟨82681980429151966169896345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110242640572202621559861793 82681980429151966169896345)
      ·
        refine ⟨62011485321863974627422259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82681980429151966169896345 62011485321863974627422259)
        ·
          refine ⟨93017227982795961941133389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62011485321863974627422259 93017227982795961941133389)
          ·
            refine ⟨34881460493548485727925021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93017227982795961941133389 34881460493548485727925021)
            ·
              refine ⟨13080547685080682147971883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34881460493548485727925021 13080547685080682147971883)
              ·
                refine ⟨19620821527621023221957825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13080547685080682147971883 19620821527621023221957825)
                ·
                  refine ⟨14715616145715767416468369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19620821527621023221957825 14715616145715767416468369)
                  ·
                    refine ⟨11036712109286825562351277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14715616145715767416468369 11036712109286825562351277)
                    ·
                      refine ⟨4138767040982559585881729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11036712109286825562351277 4138767040982559585881729)
                      ·
                        rfl

theorem cell23_8060220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_8060220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060220 prefixEnd_8060220 := by exact prefixLift 8060220
  have htrace : WordTrace (prefixWord ++ tailWord_8060220) baseStart_8060220 baseEnd_8060220 := by
    simpa [prefixWord, tailWord_8060220, baseEnd_8060220] using wordTrace_append hprefix tailTrace_8060220
  have hstable : (prefixWord ++ tailWord_8060220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060220).length < 2 ^ (prefixWord ++ tailWord_8060220).sum := by decide
  have hdescent : baseEnd_8060220 < baseStart_8060220 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060250 : List Nat := [3, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3]
def baseStart_8060250 : Nat := 118140960795 + 8060250 * 2 ^ 59
def prefixEnd_8060250 : Nat := 4983230072969 + 3 ^ 40 * 8060250 * 2
def baseEnd_8060250 : Nat := 4138782445402194468506591

theorem tailTrace_8060250 : CollatzResearch.WordTrace tailWord_8060250 prefixEnd_8060250 4138782445402194468506591 := by
  unfold tailWord_8060250
  simp only [CollatzResearch.WordTrace]
  refine ⟨73495367262274576487472551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195987646032732203966593469 73495367262274576487472551)
  ·
    refine ⟨110243050893411864731208827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73495367262274576487472551 110243050893411864731208827)
    ·
      refine ⟨165364576340117797096813241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110243050893411864731208827 165364576340117797096813241)
      ·
        refine ⟨124023432255088347822609931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165364576340117797096813241 124023432255088347822609931)
        ·
          refine ⟨186035148382632521733914897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124023432255088347822609931 186035148382632521733914897)
          ·
            refine ⟨139526361286974391300436173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186035148382632521733914897 139526361286974391300436173)
            ·
              refine ⟨52322385482615396737663565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139526361286974391300436173 52322385482615396737663565)
              ·
                refine ⟨19620894555980773776623837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52322385482615396737663565 19620894555980773776623837)
                ·
                  refine ⟨7357835458492790166233939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19620894555980773776623837 7357835458492790166233939)
                  ·
                    refine ⟨11036753187739185249350909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7357835458492790166233939 11036753187739185249350909)
                    ·
                      refine ⟨4138782445402194468506591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11036753187739185249350909 4138782445402194468506591)
                      ·
                        rfl

theorem cell23_8060250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 3, 3, 1, 3].length) (baseStart_8060250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060250 prefixEnd_8060250 := by exact prefixLift 8060250
  have htrace : WordTrace (prefixWord ++ tailWord_8060250) baseStart_8060250 baseEnd_8060250 := by
    simpa [prefixWord, tailWord_8060250, baseEnd_8060250] using wordTrace_append hprefix tailTrace_8060250
  have hstable : (prefixWord ++ tailWord_8060250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060250).length < 2 ^ (prefixWord ++ tailWord_8060250).sum := by decide
  have hdescent : baseEnd_8060250 < baseStart_8060250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060260 : List Nat := [2, 3, 1, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_8060260 : Nat := 118140960795 + 8060260 * 2 ^ 59
def prefixEnd_8060260 : Nat := 4983230072969 + 3 ^ 40 * 8060260 * 2
def baseEnd_8060260 : Nat := 4138787580208739429381545

theorem tailTrace_8060260 : CollatzResearch.WordTrace tailWord_8060260 prefixEnd_8060260 4138787580208739429381545 := by
  unfold tailWord_8060260
  simp only [CollatzResearch.WordTrace]
  refine ⟨146990916889531038828877117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195987889186041385105169489 146990916889531038828877117)
  ·
    refine ⟨55121593833574139560828919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146990916889531038828877117 55121593833574139560828919)
    ·
      refine ⟨82682390750361209341243379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55121593833574139560828919 82682390750361209341243379)
      ·
        refine ⟨124023586125541814011865069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82682390750361209341243379 124023586125541814011865069)
        ·
          refine ⟨46508844797078180254449401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124023586125541814011865069 46508844797078180254449401)
          ·
            refine ⟨34881633597808635190837051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46508844797078180254449401 34881633597808635190837051)
            ·
              refine ⟨52322450396712952786255577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34881633597808635190837051 52322450396712952786255577)
              ·
                refine ⟨39241837797534714589691683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52322450396712952786255577 39241837797534714589691683)
                ·
                  refine ⟨58862756696302071884537525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39241837797534714589691683 58862756696302071884537525)
                  ·
                    refine ⟨5518383440278319239175393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58862756696302071884537525 5518383440278319239175393)
                    ·
                      refine ⟨4138787580208739429381545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518383440278319239175393 4138787580208739429381545)
                      ·
                        rfl

theorem cell23_8060260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_8060260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060260 prefixEnd_8060260 := by exact prefixLift 8060260
  have htrace : WordTrace (prefixWord ++ tailWord_8060260) baseStart_8060260 baseEnd_8060260 := by
    simpa [prefixWord, tailWord_8060260, baseEnd_8060260] using wordTrace_append hprefix tailTrace_8060260
  have hstable : (prefixWord ++ tailWord_8060260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060260).length < 2 ^ (prefixWord ++ tailWord_8060260).sum := by decide
  have hdescent : baseEnd_8060260 < baseStart_8060260 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060273 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 4]
def baseStart_8060273 : Nat := 118140960795 + 8060273 * 2 ^ 59
def prefixEnd_8060273 : Nat := 4983230072969 + 3 ^ 40 * 8060273 * 2
def baseEnd_8060273 : Nat := 4138794255457247878518985

theorem tailTrace_8060273 : CollatzResearch.WordTrace tailWord_8060273 prefixEnd_8060273 4138794255457247878518985 := by
  unfold tailWord_8060273
  simp only [CollatzResearch.WordTrace]
  refine ⟨293982307928014980877977473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195988205285343320585318315 293982307928014980877977473)
  ·
    refine ⟨220486730946011235658483105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293982307928014980877977473 220486730946011235658483105)
    ·
      refine ⟨165365048209508426743862329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220486730946011235658483105 165365048209508426743862329)
      ·
        refine ⟨124023786157131320057896747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165365048209508426743862329 124023786157131320057896747)
        ·
          refine ⟨186035679235696980086845121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124023786157131320057896747 186035679235696980086845121)
          ·
            refine ⟨139526759426772735065133841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186035679235696980086845121 139526759426772735065133841)
            ·
              refine ⟨104645069570079551298850381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139526759426772735065133841 104645069570079551298850381)
              ·
                refine ⟨39241901088779831737068893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104645069570079551298850381 39241901088779831737068893)
                ·
                  refine ⟨14715712908292436901400835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39241901088779831737068893 14715712908292436901400835)
                  ·
                    refine ⟨22073569362438655352101253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14715712908292436901400835 22073569362438655352101253)
                    ·
                      refine ⟨4138794255457247878518985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22073569362438655352101253 4138794255457247878518985)
                      ·
                        rfl

theorem cell23_8060273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_8060273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060273 prefixEnd_8060273 := by exact prefixLift 8060273
  have htrace : WordTrace (prefixWord ++ tailWord_8060273) baseStart_8060273 baseEnd_8060273 := by
    simpa [prefixWord, tailWord_8060273, baseEnd_8060273] using wordTrace_append hprefix tailTrace_8060273
  have hstable : (prefixWord ++ tailWord_8060273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060273).length < 2 ^ (prefixWord ++ tailWord_8060273).sum := by decide
  have hdescent : baseEnd_8060273 < baseStart_8060273 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060283 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 6, 4]
def baseStart_8060283 : Nat := 118140960795 + 8060283 * 2 ^ 59
def prefixEnd_8060283 : Nat := 4983230072969 + 3 ^ 40 * 8060283 * 2
def baseEnd_8060283 : Nat := 1379599796754597613131313

theorem tailTrace_8060283 : CollatzResearch.WordTrace tailWord_8060283 prefixEnd_8060283 1379599796754597613131313 := by
  unfold tailWord_8060283
  simp only [CollatzResearch.WordTrace]
  refine ⟨293982672657978752585841503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195988448438652501723894335 293982672657978752585841503)
  ·
    refine ⟨440974008986968128878762255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293982672657978752585841503 440974008986968128878762255)
    ·
      refine ⟨661461013480452193318143383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440974008986968128878762255 661461013480452193318143383)
      ·
        refine ⟨992191520220678289977215075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661461013480452193318143383 992191520220678289977215075)
        ·
          refine ⟨1488287280331017434965822613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992191520220678289977215075 1488287280331017434965822613)
          ·
            refine ⟨69763466265516442264022935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1488287280331017434965822613 69763466265516442264022935)
            ·
              refine ⟨104645199398274663396034403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69763466265516442264022935 104645199398274663396034403)
              ·
                refine ⟨156967799097411995094051605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104645199398274663396034403 156967799097411995094051605)
                ·
                  refine ⟨7357865582691187270033669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156967799097411995094051605 7357865582691187270033669)
                  ·
                    refine ⟨1379599796754597613131313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357865582691187270033669 1379599796754597613131313)
                    ·
                      rfl

theorem cell23_8060283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 6, 4].length) (baseStart_8060283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060283 prefixEnd_8060283 := by exact prefixLift 8060283
  have htrace : WordTrace (prefixWord ++ tailWord_8060283) baseStart_8060283 baseEnd_8060283 := by
    simpa [prefixWord, tailWord_8060283, baseEnd_8060283] using wordTrace_append hprefix tailTrace_8060283
  have hstable : (prefixWord ++ tailWord_8060283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060283).length < 2 ^ (prefixWord ++ tailWord_8060283).sum := by decide
  have hdescent : baseEnd_8060283 < baseStart_8060283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060293 : List Nat := [1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 5]
def baseStart_8060293 : Nat := 118140960795 + 8060293 * 2 ^ 59
def prefixEnd_8060293 : Nat := 4983230072969 + 3 ^ 40 * 8060293 * 2
def baseEnd_8060293 : Nat := 4138804525070337800268893

theorem tailTrace_8060293 : CollatzResearch.WordTrace tailWord_8060293 prefixEnd_8060293 4138804525070337800268893 := by
  unfold tailWord_8060293
  simp only [CollatzResearch.WordTrace]
  refine ⟨293983037387942524293705533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195988691591961682862470355 293983037387942524293705533)
  ·
    refine ⟨110243639020478446610139575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293983037387942524293705533 110243639020478446610139575)
    ·
      refine ⟨165365458530717669915209363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110243639020478446610139575 165365458530717669915209363)
      ·
        refine ⟨248048187796076504872814045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165365458530717669915209363 248048187796076504872814045)
        ·
          refine ⟨93018070423528689327305267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248048187796076504872814045 93018070423528689327305267)
          ·
            refine ⟨139527105635293033990957901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93018070423528689327305267 139527105635293033990957901)
            ·
              refine ⟨52322664613234887746609213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139527105635293033990957901 52322664613234887746609213)
              ·
                refine ⟨19620999229963082904978455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52322664613234887746609213 19620999229963082904978455)
                ·
                  refine ⟨29431498844944624357467683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19620999229963082904978455 29431498844944624357467683)
                  ·
                    refine ⟨44147248267416936536201525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29431498844944624357467683 44147248267416936536201525)
                    ·
                      refine ⟨4138804525070337800268893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44147248267416936536201525 4138804525070337800268893)
                      ·
                        rfl

theorem cell23_8060293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 5].length) (baseStart_8060293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060293 prefixEnd_8060293 := by exact prefixLift 8060293
  have htrace : WordTrace (prefixWord ++ tailWord_8060293) baseStart_8060293 baseEnd_8060293 := by
    simpa [prefixWord, tailWord_8060293, baseEnd_8060293] using wordTrace_append hprefix tailTrace_8060293
  have hstable : (prefixWord ++ tailWord_8060293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060293).length < 2 ^ (prefixWord ++ tailWord_8060293).sum := by decide
  have hdescent : baseEnd_8060293 < baseStart_8060293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060300 : List Nat := [2, 2, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_8060300 : Nat := 118140960795 + 8060300 * 2 ^ 59
def prefixEnd_8060300 : Nat := 4983230072969 + 3 ^ 40 * 8060300 * 2
def baseEnd_8060300 : Nat := 1379602706478306424293787

theorem tailTrace_8060300 : CollatzResearch.WordTrace tailWord_8060300 prefixEnd_8060300 1379602706478306424293787 := by
  unfold tailWord_8060300
  simp only [CollatzResearch.WordTrace]
  refine ⟨146991646349458582244605177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195988861799278109659473569 146991646349458582244605177)
  ·
    refine ⟨110243734762093936683453883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146991646349458582244605177 110243734762093936683453883)
    ·
      refine ⟨165365602143140905025180825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110243734762093936683453883 165365602143140905025180825)
      ·
        refine ⟨124024201607355678768885619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165365602143140905025180825 124024201607355678768885619)
        ·
          refine ⟨186036302411033518153328429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124024201607355678768885619 186036302411033518153328429)
          ·
            refine ⟨69763613404137569307498161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186036302411033518153328429 69763613404137569307498161)
            ·
              refine ⟨52322710053103176980623621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69763613404137569307498161 52322710053103176980623621)
              ·
                refine ⟨9810508134956845683866929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52322710053103176980623621 9810508134956845683866929)
                ·
                  refine ⟨7357881101217634262900197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9810508134956845683866929 7357881101217634262900197)
                  ·
                    refine ⟨1379602706478306424293787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357881101217634262900197 1379602706478306424293787)
                    ·
                      rfl

theorem cell23_8060300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_8060300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060300 prefixEnd_8060300 := by exact prefixLift 8060300
  have htrace : WordTrace (prefixWord ++ tailWord_8060300) baseStart_8060300 baseEnd_8060300 := by
    simpa [prefixWord, tailWord_8060300, baseEnd_8060300] using wordTrace_append hprefix tailTrace_8060300
  have hstable : (prefixWord ++ tailWord_8060300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060300).length < 2 ^ (prefixWord ++ tailWord_8060300).sum := by decide
  have hdescent : baseEnd_8060300 < baseStart_8060300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060313 : List Nat := [1, 2, 1, 2, 1, 6, 2, 8]
def baseStart_8060313 : Nat := 118140960795 + 8060313 * 2 ^ 59
def prefixEnd_8060313 : Nat := 4983230072969 + 3 ^ 40 * 8060313 * 2
def baseEnd_8060313 : Nat := 153289436840126952667363

theorem tailTrace_8060313 : CollatzResearch.WordTrace tailWord_8060313 prefixEnd_8060313 153289436840126952667363 := by
  unfold tailWord_8060313
  simp only [CollatzResearch.WordTrace]
  refine ⟨293983766847870067709433593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195989177898580045139622395 293983766847870067709433593)
  ·
    refine ⟨220487825135902550782075195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293983766847870067709433593 220487825135902550782075195)
    ·
      refine ⟨330731737703853826173112793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220487825135902550782075195 330731737703853826173112793)
      ·
        refine ⟨248048803277890369629834595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330731737703853826173112793 248048803277890369629834595)
        ·
          refine ⟨372073204916835554444751893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248048803277890369629834595 372073204916835554444751893)
          ·
            refine ⟨17440931480476666614597745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 372073204916835554444751893 17440931480476666614597745)
            ·
              refine ⟨13080698610357499960948309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17440931480476666614597745 13080698610357499960948309)
              ·
                refine ⟨153289436840126952667363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13080698610357499960948309 153289436840126952667363)
                ·
                  rfl

theorem cell23_8060313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 2, 8].length) (baseStart_8060313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060313 prefixEnd_8060313 := by exact prefixLift 8060313
  have htrace : WordTrace (prefixWord ++ tailWord_8060313) baseStart_8060313 baseEnd_8060313 := by
    simpa [prefixWord, tailWord_8060313, baseEnd_8060313] using wordTrace_append hprefix tailTrace_8060313
  have hstable : (prefixWord ++ tailWord_8060313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060313).length < 2 ^ (prefixWord ++ tailWord_8060313).sum := by decide
  have hdescent : baseEnd_8060313 < baseStart_8060313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060317 : List Nat := [1, 4, 2, 1, 3, 2, 1, 3, 2, 4]
def baseStart_8060317 : Nat := 118140960795 + 8060317 * 2 ^ 59
def prefixEnd_8060317 : Nat := 4983230072969 + 3 ^ 40 * 8060317 * 2
def baseEnd_8060317 : Nat := 1379605616202015235456261

theorem tailTrace_8060317 : CollatzResearch.WordTrace tailWord_8060317 prefixEnd_8060317 1379605616202015235456261 := by
  unfold tailWord_8060317
  simp only [CollatzResearch.WordTrace]
  refine ⟨293983912739855576392579205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195989275159903717595052803 293983912739855576392579205)
  ·
    refine ⟨55121983638722920573608601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293983912739855576392579205 55121983638722920573608601)
    ·
      refine ⟨41341487729042190430206451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55121983638722920573608601 41341487729042190430206451)
      ·
        refine ⟨62012231593563285645309677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41341487729042190430206451 62012231593563285645309677)
        ·
          refine ⟨23254586847586232116991129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62012231593563285645309677 23254586847586232116991129)
          ·
            refine ⟨17440940135689674087743347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23254586847586232116991129 17440940135689674087743347)
            ·
              refine ⟨26161410203534511131615021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17440940135689674087743347 26161410203534511131615021)
              ·
                refine ⟨9810528826325441674355633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26161410203534511131615021 9810528826325441674355633)
                ·
                  refine ⟨7357896619744081255766725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9810528826325441674355633 7357896619744081255766725)
                  ·
                    refine ⟨1379605616202015235456261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7357896619744081255766725 1379605616202015235456261)
                    ·
                      rfl

theorem cell23_8060317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_8060317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060317 prefixEnd_8060317 := by exact prefixLift 8060317
  have htrace : WordTrace (prefixWord ++ tailWord_8060317) baseStart_8060317 baseEnd_8060317 := by
    simpa [prefixWord, tailWord_8060317, baseEnd_8060317] using wordTrace_append hprefix tailTrace_8060317
  have hstable : (prefixWord ++ tailWord_8060317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060317).length < 2 ^ (prefixWord ++ tailWord_8060317).sum := by decide
  have hdescent : baseEnd_8060317 < baseStart_8060317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060363 : List Nat := [1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 4]
def baseStart_8060363 : Nat := 118140960795 + 8060363 * 2 ^ 59
def prefixEnd_8060363 : Nat := 4983230072969 + 3 ^ 40 * 8060363 * 2
def baseEnd_8060363 : Nat := 4138840468716152526393571

theorem tailTrace_8060363 : CollatzResearch.WordTrace tailWord_8060363 prefixEnd_8060363 4138840468716152526393571 := by
  unfold tailWord_8060363
  simp only [CollatzResearch.WordTrace]
  refine ⟨293985590497688926248753743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195990393665125950832502495 293985590497688926248753743)
  ·
    refine ⟨440978385746533389373130615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293985590497688926248753743 440978385746533389373130615)
    ·
      refine ⟨661467578619800084059695923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440978385746533389373130615 661467578619800084059695923)
      ·
        refine ⟨992201367929700126089543885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661467578619800084059695923 992201367929700126089543885)
        ·
          refine ⟨372075512973637547283578957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 992201367929700126089543885 372075512973637547283578957)
          ·
            refine ⟨139528317365114080231342109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372075512973637547283578957 139528317365114080231342109)
            ·
              refine ⟨52323119011917780086753291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139528317365114080231342109 52323119011917780086753291)
              ·
                refine ⟨78484678517876670130129937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52323119011917780086753291 78484678517876670130129937)
                ·
                  refine ⟨58863508888407502597597453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78484678517876670130129937 58863508888407502597597453)
                  ·
                    refine ⟨22073815833152813474099045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58863508888407502597597453 22073815833152813474099045)
                    ·
                      refine ⟨4138840468716152526393571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22073815833152813474099045 4138840468716152526393571)
                      ·
                        rfl

theorem cell23_8060363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 3, 4].length) (baseStart_8060363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060363 prefixEnd_8060363 := by exact prefixLift 8060363
  have htrace : WordTrace (prefixWord ++ tailWord_8060363) baseStart_8060363 baseEnd_8060363 := by
    simpa [prefixWord, tailWord_8060363, baseEnd_8060363] using wordTrace_append hprefix tailTrace_8060363
  have hstable : (prefixWord ++ tailWord_8060363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060363).length < 2 ^ (prefixWord ++ tailWord_8060363).sum := by decide
  have hdescent : baseEnd_8060363 < baseStart_8060363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060374 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_8060374 : Nat := 118140960795 + 8060374 * 2 ^ 59
def prefixEnd_8060374 : Nat := 4983230072969 + 3 ^ 40 * 8060374 * 2
def baseEnd_8060374 : Nat := 4138846117003351983356021

theorem tailTrace_8060374 : CollatzResearch.WordTrace tailWord_8060374 prefixEnd_8060374 4138846117003351983356021 := by
  unfold tailWord_8060374
  simp only [CollatzResearch.WordTrace]
  refine ⟨18374124481290567195462761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195990661133766050084936117 18374124481290567195462761)
  ·
    refine ⟨13780593360967925396597071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18374124481290567195462761 13780593360967925396597071)
    ·
      refine ⟨20670890041451888094895607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13780593360967925396597071 20670890041451888094895607)
      ·
        refine ⟨31006335062177832142343411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20670890041451888094895607 31006335062177832142343411)
        ·
          refine ⟨46509502593266748213515117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31006335062177832142343411 46509502593266748213515117)
          ·
            refine ⟨17441063472475030580068169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46509502593266748213515117 17441063472475030580068169)
            ·
              refine ⟨13080797604356272935051127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17441063472475030580068169 13080797604356272935051127)
              ·
                refine ⟨19621196406534409402576691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13080797604356272935051127 19621196406534409402576691)
                ·
                  refine ⟨29431794609801614103865037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19621196406534409402576691 29431794609801614103865037)
                  ·
                    refine ⟨11036922978675605288949389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29431794609801614103865037 11036922978675605288949389)
                    ·
                      refine ⟨4138846117003351983356021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11036922978675605288949389 4138846117003351983356021)
                      ·
                        rfl

theorem cell23_8060374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_8060374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060374 prefixEnd_8060374 := by exact prefixLift 8060374
  have htrace : WordTrace (prefixWord ++ tailWord_8060374) baseStart_8060374 baseEnd_8060374 := by
    simpa [prefixWord, tailWord_8060374, baseEnd_8060374] using wordTrace_append hprefix tailTrace_8060374
  have hstable : (prefixWord ++ tailWord_8060374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060374).length < 2 ^ (prefixWord ++ tailWord_8060374).sum := by decide
  have hdescent : baseEnd_8060374 < baseStart_8060374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060401 : List Nat := [1, 2, 2, 2, 3, 4, 2, 1, 1, 3, 2]
def baseStart_8060401 : Nat := 118140960795 + 8060401 * 2 ^ 59
def prefixEnd_8060401 : Nat := 4983230072969 + 3 ^ 40 * 8060401 * 2
def baseEnd_8060401 : Nat := 4138859980981023377718397

theorem tailTrace_8060401 : CollatzResearch.WordTrace tailWord_8060401 prefixEnd_8060401 4138859980981023377718397 := by
  unfold tailWord_8060401
  simp only [CollatzResearch.WordTrace]
  refine ⟨293986976471551258738637057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195991317647700839159091371 293986976471551258738637057)
  ·
    refine ⟨220490232353663444053977793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293986976471551258738637057 220490232353663444053977793)
    ·
      refine ⟨165367674265247583040483345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220490232353663444053977793 165367674265247583040483345)
      ·
        refine ⟨124025755698935687280362509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165367674265247583040483345 124025755698935687280362509)
        ·
          refine ⟨46509658387100882730135941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124025755698935687280362509 46509658387100882730135941)
          ·
            refine ⟨8720560947581415511900489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46509658387100882730135941 8720560947581415511900489)
            ·
              refine ⟨6540420710686061633925367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8720560947581415511900489 6540420710686061633925367)
              ·
                refine ⟨9810631066029092450888051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6540420710686061633925367 9810631066029092450888051)
                ·
                  refine ⟨14715946599043638676332077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9810631066029092450888051 14715946599043638676332077)
                  ·
                    refine ⟨5518479974641364503624529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14715946599043638676332077 5518479974641364503624529)
                    ·
                      refine ⟨4138859980981023377718397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518479974641364503624529 4138859980981023377718397)
                      ·
                        rfl

theorem cell23_8060401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 2, 1, 1, 3, 2].length) (baseStart_8060401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060401 prefixEnd_8060401 := by exact prefixLift 8060401
  have htrace : WordTrace (prefixWord ++ tailWord_8060401) baseStart_8060401 baseEnd_8060401 := by
    simpa [prefixWord, tailWord_8060401, baseEnd_8060401] using wordTrace_append hprefix tailTrace_8060401
  have hstable : (prefixWord ++ tailWord_8060401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060401).length < 2 ^ (prefixWord ++ tailWord_8060401).sum := by decide
  have hdescent : baseEnd_8060401 < baseStart_8060401 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060433 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 3, 7]
def baseStart_8060433 : Nat := 118140960795 + 8060433 * 2 ^ 59
def prefixEnd_8060433 : Nat := 4983230072969 + 3 ^ 40 * 8060433 * 2
def baseEnd_8060433 : Nat := 1379625470787322417506083

theorem tailTrace_8060433 : CollatzResearch.WordTrace tailWord_8060433 prefixEnd_8060433 1379625470787322417506083 := by
  unfold tailWord_8060433
  simp only [CollatzResearch.WordTrace]
  refine ⟨293988143607435328203801953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195992095738290218802534635 293988143607435328203801953)
  ·
    refine ⟨220491107705576496152851465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293988143607435328203801953 220491107705576496152851465)
    ·
      refine ⟨165368330779182372114638599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220491107705576496152851465 165368330779182372114638599)
      ·
        refine ⟨248052496168773558171957899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165368330779182372114638599 248052496168773558171957899)
        ·
          refine ⟨372078744253160337257936849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248052496168773558171957899 372078744253160337257936849)
          ·
            refine ⟨279059058189870252943452637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372078744253160337257936849 279059058189870252943452637)
            ·
              refine ⟨104647146821201344853794739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279059058189870252943452637 104647146821201344853794739)
              ·
                refine ⟨156970720231802017280692109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104647146821201344853794739 156970720231802017280692109)
                ·
                  refine ⟨58864020086925756480259541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156970720231802017280692109 58864020086925756480259541)
                  ·
                    refine ⟨1379625470787322417506083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58864020086925756480259541 1379625470787322417506083)
                    ·
                      rfl

theorem cell23_8060433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_8060433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060433 prefixEnd_8060433 := by exact prefixLift 8060433
  have htrace : WordTrace (prefixWord ++ tailWord_8060433) baseStart_8060433 baseEnd_8060433 := by
    simpa [prefixWord, tailWord_8060433, baseEnd_8060433] using wordTrace_append hprefix tailTrace_8060433
  have hstable : (prefixWord ++ tailWord_8060433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060433).length < 2 ^ (prefixWord ++ tailWord_8060433).sum := by decide
  have hdescent : baseEnd_8060433 < baseStart_8060433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060450 : List Nat := [3, 3, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_8060450 : Nat := 118140960795 + 8060450 * 2 ^ 59
def prefixEnd_8060450 : Nat := 4983230072969 + 3 ^ 40 * 8060450 * 2
def baseEnd_8060450 : Nat := 1379628380511031228668557

theorem tailTrace_8060450 : CollatzResearch.WordTrace tailWord_8060450 prefixEnd_8060450 1379628380511031228668557 := by
  unfold tailWord_8060450
  simp only [CollatzResearch.WordTrace]
  refine ⟨73497190912093435026792701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195992509098915826738113869 73497190912093435026792701)
  ·
    refine ⟨27561446592035038135047263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73497190912093435026792701 27561446592035038135047263)
    ·
      refine ⟨41342169888052557202570895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27561446592035038135047263 41342169888052557202570895)
      ·
        refine ⟨62013254832078835803856343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41342169888052557202570895 62013254832078835803856343)
        ·
          refine ⟨93019882248118253705784515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62013254832078835803856343 93019882248118253705784515)
          ·
            refine ⟨139529823372177380558676773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93019882248118253705784515 139529823372177380558676773)
            ·
              refine ⟨26161841882283258854751895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139529823372177380558676773 26161841882283258854751895)
              ·
                refine ⟨39242762823424888282127843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26161841882283258854751895 39242762823424888282127843)
                ·
                  refine ⟨58864144235137332423191765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39242762823424888282127843 58864144235137332423191765)
                  ·
                    refine ⟨1379628380511031228668557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58864144235137332423191765 1379628380511031228668557)
                    ·
                      rfl

theorem cell23_8060450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_8060450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060450 prefixEnd_8060450 := by exact prefixLift 8060450
  have htrace : WordTrace (prefixWord ++ tailWord_8060450) baseStart_8060450 baseEnd_8060450 := by
    simpa [prefixWord, tailWord_8060450, baseEnd_8060450] using wordTrace_append hprefix tailTrace_8060450
  have hstable : (prefixWord ++ tailWord_8060450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060450).length < 2 ^ (prefixWord ++ tailWord_8060450).sum := by decide
  have hdescent : baseEnd_8060450 < baseStart_8060450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060477 : List Nat := [1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_8060477 : Nat := 118140960795 + 8060477 * 2 ^ 59
def prefixEnd_8060477 : Nat := 4983230072969 + 3 ^ 40 * 8060477 * 2
def baseEnd_8060477 : Nat := 4138899005510765080368047

theorem tailTrace_8060477 : CollatzResearch.WordTrace tailWord_8060477 prefixEnd_8060477 4138899005510765080368047 := by
  unfold tailWord_8060477
  simp only [CollatzResearch.WordTrace]
  refine ⟨293989748419275923718403685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195993165612850615812269123 293989748419275923718403685)
  ·
    refine ⟨55123077828614235697200691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293989748419275923718403685 55123077828614235697200691)
    ·
      refine ⟨82684616742921353545801037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55123077828614235697200691 82684616742921353545801037)
      ·
        refine ⟨31006731278595507579675389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82684616742921353545801037 31006731278595507579675389)
        ·
          refine ⟨11627524229473315342378271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31006731278595507579675389 11627524229473315342378271)
          ·
            refine ⟨17441286344209973013567407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11627524229473315342378271 17441286344209973013567407)
            ·
              refine ⟨26161929516314959520351111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17441286344209973013567407 26161929516314959520351111)
              ·
                refine ⟨39242894274472439280526667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26161929516314959520351111 39242894274472439280526667)
                ·
                  refine ⟨58864341411708658920790001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39242894274472439280526667 58864341411708658920790001)
                  ·
                    refine ⟨44148256058781494190592501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58864341411708658920790001 44148256058781494190592501)
                    ·
                      refine ⟨4138899005510765080368047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44148256058781494190592501 4138899005510765080368047)
                      ·
                        rfl

theorem cell23_8060477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_8060477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060477 prefixEnd_8060477 := by exact prefixLift 8060477
  have htrace : WordTrace (prefixWord ++ tailWord_8060477) baseStart_8060477 baseEnd_8060477 := by
    simpa [prefixWord, tailWord_8060477, baseEnd_8060477] using wordTrace_append hprefix tailTrace_8060477
  have hstable : (prefixWord ++ tailWord_8060477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060477).length < 2 ^ (prefixWord ++ tailWord_8060477).sum := by decide
  have hdescent : baseEnd_8060477 < baseStart_8060477 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060547 : List Nat := [1, 1, 1, 3, 3, 1, 1, 4, 1, 5, 2]
def baseStart_8060547 : Nat := 118140960795 + 8060547 * 2 ^ 59
def prefixEnd_8060547 : Nat := 4983230072969 + 3 ^ 40 * 8060547 * 2
def baseEnd_8060547 : Nat := 4138934949156579806492725

theorem tailTrace_8060547 : CollatzResearch.WordTrace tailWord_8060547 prefixEnd_8060547 4138934949156579806492725 := by
  unfold tailWord_8060547
  simp only [CollatzResearch.WordTrace]
  refine ⟨293992301529022325673451895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195994867686014883782301263 293992301529022325673451895)
  ·
    refine ⟨440988452293533488510177843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293992301529022325673451895 440988452293533488510177843)
    ·
      refine ⟨661482678440300232765266765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440988452293533488510177843 661482678440300232765266765)
      ·
        refine ⟨248056004415112587286975037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661482678440300232765266765 248056004415112587286975037)
        ·
          refine ⟨93021001655667220232615639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248056004415112587286975037 93021001655667220232615639)
          ·
            refine ⟨139531502483500830348923459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93021001655667220232615639 139531502483500830348923459)
            ·
              refine ⟨209297253725251245523385189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139531502483500830348923459 209297253725251245523385189)
              ·
                refine ⟨39243235073484608535634723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 209297253725251245523385189 39243235073484608535634723)
                ·
                  refine ⟨58864852610226912803452085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39243235073484608535634723 58864852610226912803452085)
                  ·
                    refine ⟨5518579932208773075323633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58864852610226912803452085 5518579932208773075323633)
                    ·
                      refine ⟨4138934949156579806492725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518579932208773075323633 4138934949156579806492725)
                      ·
                        rfl

theorem cell23_8060547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_8060547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060547 prefixEnd_8060547 := by exact prefixLift 8060547
  have htrace : WordTrace (prefixWord ++ tailWord_8060547) baseStart_8060547 baseEnd_8060547 := by
    simpa [prefixWord, tailWord_8060547, baseEnd_8060547] using wordTrace_append hprefix tailTrace_8060547
  have hstable : (prefixWord ++ tailWord_8060547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060547).length < 2 ^ (prefixWord ++ tailWord_8060547).sum := by decide
  have hdescent : baseEnd_8060547 < baseStart_8060547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060554 : List Nat := [3, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3]
def baseStart_8060554 : Nat := 118140960795 + 8060554 * 2 ^ 59
def prefixEnd_8060554 : Nat := 4983230072969 + 3 ^ 40 * 8060554 * 2
def baseEnd_8060554 : Nat := 4138938543521161279105193

theorem tailTrace_8060554 : CollatzResearch.WordTrace tailWord_8060554 prefixEnd_8060554 4138938543521161279105193 := by
  unfold tailWord_8060554
  simp only [CollatzResearch.WordTrace]
  refine ⟨73498139209999241467239179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195995037893331310579304477 73498139209999241467239179)
  ·
    refine ⟨110247208814998862200858769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73498139209999241467239179 110247208814998862200858769)
    ·
      refine ⟨82685406611249146650644077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110247208814998862200858769 82685406611249146650644077)
      ·
        refine ⟨31007027479218429993991529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82685406611249146650644077 31007027479218429993991529)
        ·
          refine ⟨23255270609413822495493647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31007027479218429993991529 23255270609413822495493647)
          ·
            refine ⟨34882905914120733743240471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23255270609413822495493647 34882905914120733743240471)
            ·
              refine ⟨52324358871181100614860707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34882905914120733743240471 52324358871181100614860707)
              ·
                refine ⟨78486538306771650922291061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52324358871181100614860707 78486538306771650922291061)
                ·
                  refine ⟨7358112966259842273964787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78486538306771650922291061 7358112966259842273964787)
                  ·
                    refine ⟨11037169449389763410947181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7358112966259842273964787 11037169449389763410947181)
                    ·
                      refine ⟨4138938543521161279105193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11037169449389763410947181 4138938543521161279105193)
                      ·
                        rfl

theorem cell23_8060554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_8060554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060554 prefixEnd_8060554 := by exact prefixLift 8060554
  have htrace : WordTrace (prefixWord ++ tailWord_8060554) baseStart_8060554 baseEnd_8060554 := by
    simpa [prefixWord, tailWord_8060554, baseEnd_8060554] using wordTrace_append hprefix tailTrace_8060554
  have hstable : (prefixWord ++ tailWord_8060554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060554).length < 2 ^ (prefixWord ++ tailWord_8060554).sum := by decide
  have hdescent : baseEnd_8060554 < baseStart_8060554 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060578 : List Nat := [3, 3, 1, 4, 2, 1, 1, 2, 6]
def baseStart_8060578 : Nat := 118140960795 + 8060578 * 2 ^ 59
def prefixEnd_8060578 : Nat := 4983230072969 + 3 ^ 40 * 8060578 * 2
def baseEnd_8060578 : Nat := 459883429672985465022787

theorem tailTrace_8060578 : CollatzResearch.WordTrace tailWord_8060578 prefixEnd_8060578 459883429672985465022787 := by
  unfold tailWord_8060578
  simp only [CollatzResearch.WordTrace]
  refine ⟨73498358047977504491957597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195995621461273345311886925 73498358047977504491957597)
  ·
    refine ⟨27561884267991564184484099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73498358047977504491957597 27561884267991564184484099)
    ·
      refine ⟨41342826401987346276726149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27561884267991564184484099 41342826401987346276726149)
      ·
        refine ⟨7751779950372627426886153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41342826401987346276726149 7751779950372627426886153)
        ·
          refine ⟨5813834962779470570164615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7751779950372627426886153 5813834962779470570164615)
          ·
            refine ⟨8720752444169205855246923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5813834962779470570164615 8720752444169205855246923)
            ·
              refine ⟨13081128666253808782870385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720752444169205855246923 13081128666253808782870385)
              ·
                refine ⟨9810846499690356587152789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13081128666253808782870385 9810846499690356587152789)
                ·
                  refine ⟨459883429672985465022787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9810846499690356587152789 459883429672985465022787)
                  ·
                    rfl

theorem cell23_8060578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_8060578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060578 prefixEnd_8060578 := by exact prefixLift 8060578
  have htrace : WordTrace (prefixWord ++ tailWord_8060578) baseStart_8060578 baseEnd_8060578 := by
    simpa [prefixWord, tailWord_8060578, baseEnd_8060578] using wordTrace_append hprefix tailTrace_8060578
  have hstable : (prefixWord ++ tailWord_8060578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060578).length < 2 ^ (prefixWord ++ tailWord_8060578).sum := by decide
  have hdescent : baseEnd_8060578 < baseStart_8060578 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060604 : List Nat := [2, 2, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_8060604 : Nat := 118140960795 + 8060604 * 2 ^ 59
def prefixEnd_8060604 : Nat := 4983230072969 + 3 ^ 40 * 8060604 * 2
def baseEnd_8060604 : Nat := 1379654739184628694493321

theorem tailTrace_8060604 : CollatzResearch.WordTrace tailWord_8060604 prefixEnd_8060604 1379654739184628694493321 := by
  unfold tailWord_8060604
  simp only [CollatzResearch.WordTrace]
  refine ⟨146997190244907912204138433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195996253659877216272184577 146997190244907912204138433)
  ·
    refine ⟨110247892683680934153103825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146997190244907912204138433 110247892683680934153103825)
    ·
      refine ⟨82685919512760700614827869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110247892683680934153103825 82685919512760700614827869)
      ·
        refine ⟨31007219817285262730560451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82685919512760700614827869 31007219817285262730560451)
        ·
          refine ⟨46510829725927894095840677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31007219817285262730560451 46510829725927894095840677)
          ·
            refine ⟨8720780573611480142970127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46510829725927894095840677 8720780573611480142970127)
            ·
              refine ⟨13081170860417220214455191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8720780573611480142970127 13081170860417220214455191)
              ·
                refine ⟨19621756290625830321682787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13081170860417220214455191 19621756290625830321682787)
                ·
                  refine ⟨29432634435938745482524181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19621756290625830321682787 29432634435938745482524181)
                  ·
                    refine ⟨1379654739184628694493321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29432634435938745482524181 1379654739184628694493321)
                    ·
                      rfl

theorem cell23_8060604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_8060604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060604 prefixEnd_8060604 := by exact prefixLift 8060604
  have htrace : WordTrace (prefixWord ++ tailWord_8060604) baseStart_8060604 baseEnd_8060604 := by
    simpa [prefixWord, tailWord_8060604, baseEnd_8060604] using wordTrace_append hprefix tailTrace_8060604
  have hstable : (prefixWord ++ tailWord_8060604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060604).length < 2 ^ (prefixWord ++ tailWord_8060604).sum := by decide
  have hdescent : baseEnd_8060604 < baseStart_8060604 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060621 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 4, 4]
def baseStart_8060621 : Nat := 118140960795 + 8060621 * 2 ^ 59
def prefixEnd_8060621 : Nat := 4983230072969 + 3 ^ 40 * 8060621 * 2
def baseEnd_8060621 : Nat := 1379657648908337505655795

theorem tailTrace_8060621 : CollatzResearch.WordTrace tailWord_8060621 prefixEnd_8060621 1379657648908337505655795 := by
  unfold tailWord_8060621
  simp only [CollatzResearch.WordTrace]
  refine ⟨293995000530754236311645717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195996667020502824207763811 293995000530754236311645717)
  ·
    refine ⟨13781015649879104827108393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293995000530754236311645717 13781015649879104827108393)
    ·
      refine ⟨10335761737409328620331295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13781015649879104827108393 10335761737409328620331295)
      ·
        refine ⟨15503642606113992930496943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10335761737409328620331295 15503642606113992930496943)
        ·
          refine ⟨23255463909170989395745415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15503642606113992930496943 23255463909170989395745415)
          ·
            refine ⟨34883195863756484093618123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23255463909170989395745415 34883195863756484093618123)
            ·
              refine ⟨52324793795634726140427185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34883195863756484093618123 52324793795634726140427185)
              ·
                refine ⟨39243595346726044605320389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52324793795634726140427185 39243595346726044605320389)
                ·
                  refine ⟨7358174127511133363497573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39243595346726044605320389 7358174127511133363497573)
                  ·
                    refine ⟨1379657648908337505655795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7358174127511133363497573 1379657648908337505655795)
                    ·
                      rfl

theorem cell23_8060621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_8060621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060621 prefixEnd_8060621 := by exact prefixLift 8060621
  have htrace : WordTrace (prefixWord ++ tailWord_8060621) baseStart_8060621 baseEnd_8060621 := by
    simpa [prefixWord, tailWord_8060621, baseEnd_8060621] using wordTrace_append hprefix tailTrace_8060621
  have hstable : (prefixWord ++ tailWord_8060621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060621).length < 2 ^ (prefixWord ++ tailWord_8060621).sum := by decide
  have hdescent : baseEnd_8060621 < baseStart_8060621 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060644 : List Nat := [2, 3, 1, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_8060644 : Nat := 118140960795 + 8060644 * 2 ^ 59
def prefixEnd_8060644 : Nat := 4983230072969 + 3 ^ 40 * 8060644 * 2
def baseEnd_8060644 : Nat := 4138984756780065926979779

theorem tailTrace_8060644 : CollatzResearch.WordTrace tailWord_8060644 prefixEnd_8060644 4138984756780065926979779 := by
  unfold tailWord_8060644
  simp only [CollatzResearch.WordTrace]
  refine ⟨146997919704835455619866493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195997226273113940826488657 146997919704835455619866493)
  ·
    refine ⟨55124219889313295857449935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146997919704835455619866493 55124219889313295857449935)
    ·
      refine ⟨82686329833969943786174903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55124219889313295857449935 82686329833969943786174903)
      ·
        refine ⟨124029494750954915679262355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82686329833969943786174903 124029494750954915679262355)
        ·
          refine ⟨186044242126432373518893533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124029494750954915679262355 186044242126432373518893533)
          ·
            refine ⟨69766590797412140069585075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186044242126432373518893533 69766590797412140069585075)
            ·
              refine ⟨104649886196118210104377613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69766590797412140069585075 104649886196118210104377613)
              ·
                refine ⟨39243707323544328789141605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104649886196118210104377613 39243707323544328789141605)
                ·
                  refine ⟨7358195123164561647964051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39243707323544328789141605 7358195123164561647964051)
                  ·
                    refine ⟨11037292684746842471946077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7358195123164561647964051 11037292684746842471946077)
                    ·
                      refine ⟨4138984756780065926979779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11037292684746842471946077 4138984756780065926979779)
                      ·
                        rfl

theorem cell23_8060644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_8060644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060644 prefixEnd_8060644 := by exact prefixLift 8060644
  have htrace : WordTrace (prefixWord ++ tailWord_8060644) baseStart_8060644 baseEnd_8060644 := by
    simpa [prefixWord, tailWord_8060644, baseEnd_8060644] using wordTrace_append hprefix tailTrace_8060644
  have hstable : (prefixWord ++ tailWord_8060644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060644).length < 2 ^ (prefixWord ++ tailWord_8060644).sum := by decide
  have hdescent : baseEnd_8060644 < baseStart_8060644 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060645 : List Nat := [1, 3, 1, 4, 1, 1, 5, 2, 1, 2, 2]
def baseStart_8060645 : Nat := 118140960795 + 8060645 * 2 ^ 59
def prefixEnd_8060645 : Nat := 4983230072969 + 3 ^ 40 * 8060645 * 2
def baseEnd_8060645 : Nat := 4138985270260720423067275

theorem tailTrace_8060645 : CollatzResearch.WordTrace tailWord_8060645 prefixEnd_8060645 4138985270260720423067275 := by
  unfold tailWord_8060645
  simp only [CollatzResearch.WordTrace]
  refine ⟨293995875882667288410519389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195997250588444858940346259 293995875882667288410519389)
  ·
    refine ⟨110248453456000233153944771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293995875882667288410519389 110248453456000233153944771)
    ·
      refine ⟨165372680184000349730917157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110248453456000233153944771 165372680184000349730917157)
      ·
        refine ⟨31007377534500065574546967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165372680184000349730917157 31007377534500065574546967)
        ·
          refine ⟨46511066301750098361820451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31007377534500065574546967 46511066301750098361820451)
          ·
            refine ⟨69766599452625147542730677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46511066301750098361820451 69766599452625147542730677)
            ·
              refine ⟨6540618698683607582131001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69766599452625147542730677 6540618698683607582131001)
              ·
                refine ⟨4905464024012705686598251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6540618698683607582131001 4905464024012705686598251)
                ·
                  refine ⟨7358196036019058529897377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905464024012705686598251 7358196036019058529897377)
                  ·
                    refine ⟨5518647027014293897423033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7358196036019058529897377 5518647027014293897423033)
                    ·
                      refine ⟨4138985270260720423067275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518647027014293897423033 4138985270260720423067275)
                      ·
                        rfl

theorem cell23_8060645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_8060645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060645 prefixEnd_8060645 := by exact prefixLift 8060645
  have htrace : WordTrace (prefixWord ++ tailWord_8060645) baseStart_8060645 baseEnd_8060645 := by
    simpa [prefixWord, tailWord_8060645, baseEnd_8060645] using wordTrace_append hprefix tailTrace_8060645
  have hstable : (prefixWord ++ tailWord_8060645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060645).length < 2 ^ (prefixWord ++ tailWord_8060645).sum := by decide
  have hdescent : baseEnd_8060645 < baseStart_8060645 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060671 : List Nat := [1, 1, 2, 2, 1, 3, 5, 2, 1, 3, 2]
def baseStart_8060671 : Nat := 118140960795 + 8060671 * 2 ^ 59
def prefixEnd_8060671 : Nat := 4983230072969 + 3 ^ 40 * 8060671 * 2
def baseEnd_8060671 : Nat := 4138998620757737321342155

theorem tailTrace_8060671 : CollatzResearch.WordTrace tailWord_8060671 prefixEnd_8060671 4138998620757737321342155 := by
  unfold tailWord_8060671
  simp only [CollatzResearch.WordTrace]
  refine ⟨293996824180573094850965867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195997882787048729900643911 293996824180573094850965867)
  ·
    refine ⟨440995236270859642276448801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293996824180573094850965867 440995236270859642276448801)
    ·
      refine ⟨330746427203144731707336601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440995236270859642276448801 330746427203144731707336601)
      ·
        refine ⟨248059820402358548780502451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330746427203144731707336601 248059820402358548780502451)
        ·
          refine ⟨372089730603537823170753677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248059820402358548780502451 372089730603537823170753677)
          ·
            refine ⟨139533648976326683689032629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372089730603537823170753677 139533648976326683689032629)
            ·
              refine ⟨13081279591530626595846809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139533648976326683689032629 13081279591530626595846809)
              ·
                refine ⟨9810959693647969946885107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13081279591530626595846809 9810959693647969946885107)
                ·
                  refine ⟨14716439540471954920327661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9810959693647969946885107 14716439540471954920327661)
                  ·
                    refine ⟨5518664827676983095122873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14716439540471954920327661 5518664827676983095122873)
                    ·
                      refine ⟨4138998620757737321342155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518664827676983095122873 4138998620757737321342155)
                      ·
                        rfl

theorem cell23_8060671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 2, 1, 3, 2].length) (baseStart_8060671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060671 prefixEnd_8060671 := by exact prefixLift 8060671
  have htrace : WordTrace (prefixWord ++ tailWord_8060671) baseStart_8060671 baseEnd_8060671 := by
    simpa [prefixWord, tailWord_8060671, baseEnd_8060671] using wordTrace_append hprefix tailTrace_8060671
  have hstable : (prefixWord ++ tailWord_8060671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060671).length < 2 ^ (prefixWord ++ tailWord_8060671).sum := by decide
  have hdescent : baseEnd_8060671 < baseStart_8060671 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060684 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 3, 4, 2]
def baseStart_8060684 : Nat := 118140960795 + 8060684 * 2 ^ 59
def prefixEnd_8060684 : Nat := 4983230072969 + 3 ^ 40 * 8060684 * 2
def baseEnd_8060684 : Nat := 4139005296006245770479595

theorem tailTrace_8060684 : CollatzResearch.WordTrace tailWord_8060684 prefixEnd_8060684 4139005296006245770479595 := by
  unfold tailWord_8060684
  simp only [CollatzResearch.WordTrace]
  refine ⟨146998649164762999035594553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195998198886350665380792737 146998649164762999035594553)
  ·
    refine ⟨110248986873572249276695915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146998649164762999035594553 110248986873572249276695915)
    ·
      refine ⟨165373480310358373915043873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110248986873572249276695915 165373480310358373915043873)
      ·
        refine ⟨124030110232768780436282905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165373480310358373915043873 124030110232768780436282905)
        ·
          refine ⟨93022582674576585327212179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124030110232768780436282905 93022582674576585327212179)
          ·
            refine ⟨139533874011864877990818269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93022582674576585327212179 139533874011864877990818269)
            ·
              refine ⟨52325202754449329246556851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139533874011864877990818269 52325202754449329246556851)
              ·
                refine ⟨78487804131673993869835277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52325202754449329246556851 78487804131673993869835277)
                ·
                  refine ⟨29432926549377747701188229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78487804131673993869835277 29432926549377747701188229)
                  ·
                    refine ⟨5518673728008327693972793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29432926549377747701188229 5518673728008327693972793)
                    ·
                      refine ⟨4139005296006245770479595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518673728008327693972793 4139005296006245770479595)
                      ·
                        rfl

theorem cell23_8060684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_8060684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060684 prefixEnd_8060684 := by exact prefixLift 8060684
  have htrace : WordTrace (prefixWord ++ tailWord_8060684) baseStart_8060684 baseEnd_8060684 := by
    simpa [prefixWord, tailWord_8060684, baseEnd_8060684] using wordTrace_append hprefix tailTrace_8060684
  have hstable : (prefixWord ++ tailWord_8060684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060684).length < 2 ^ (prefixWord ++ tailWord_8060684).sum := by decide
  have hdescent : baseEnd_8060684 < baseStart_8060684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060724 : List Nat := [2, 5, 1, 1, 2, 1, 1, 1, 9]
def baseStart_8060724 : Nat := 118140960795 + 8060724 * 2 ^ 59
def prefixEnd_8060724 : Nat := 4983230072969 + 3 ^ 40 * 8060724 * 2
def baseEnd_8060724 : Nat := 459891759470269512664379

theorem tailTrace_8060724 : CollatzResearch.WordTrace tailWord_8060724 prefixEnd_8060724 459891759470269512664379 := by
  unfold tailWord_8060724
  simp only [CollatzResearch.WordTrace]
  refine ⟨146999378624690542451322613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195999171499587389935096817 146999378624690542451322613)
  ·
    refine ⟨13781191746064738354811495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146999378624690542451322613 13781191746064738354811495)
    ·
      refine ⟨20671787619097107532217243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13781191746064738354811495 20671787619097107532217243)
      ·
        refine ⟨31007681428645661298325865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20671787619097107532217243 31007681428645661298325865)
        ·
          refine ⟨23255761071484245973744399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31007681428645661298325865 23255761071484245973744399)
          ·
            refine ⟨34883641607226368960616599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23255761071484245973744399 34883641607226368960616599)
            ·
              refine ⟨52325462410839553440924899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34883641607226368960616599 52325462410839553440924899)
              ·
                refine ⟨78488193616259330161387349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52325462410839553440924899 78488193616259330161387349)
                ·
                  refine ⟨459891759470269512664379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78488193616259330161387349 459891759470269512664379)
                  ·
                    rfl

theorem cell23_8060724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_8060724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060724 prefixEnd_8060724 := by exact prefixLift 8060724
  have htrace : WordTrace (prefixWord ++ tailWord_8060724) baseStart_8060724 baseEnd_8060724 := by
    simpa [prefixWord, tailWord_8060724, baseEnd_8060724] using wordTrace_append hprefix tailTrace_8060724
  have hstable : (prefixWord ++ tailWord_8060724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060724).length < 2 ^ (prefixWord ++ tailWord_8060724).sum := by decide
  have hdescent : baseEnd_8060724 < baseStart_8060724 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060787 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 4]
def baseStart_8060787 : Nat := 118140960795 + 8060787 * 2 ^ 59
def prefixEnd_8060787 : Nat := 4983230072969 + 3 ^ 40 * 8060787 * 2
def baseEnd_8060787 : Nat := 4139058184513658867491621

theorem tailTrace_8060787 : CollatzResearch.WordTrace tailWord_8060787 prefixEnd_8060787 4139058184513658867491621 := by
  unfold tailWord_8060787
  simp only [CollatzResearch.WordTrace]
  refine ⟨294001055048152846662188615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196000703365435231108125743 294001055048152846662188615)
  ·
    refine ⟨441001582572229269993282923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294001055048152846662188615 441001582572229269993282923)
    ·
      refine ⟨661502373858343904989924385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441001582572229269993282923 661502373858343904989924385)
      ·
        refine ⟨496126780393757928742443289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661502373858343904989924385 496126780393757928742443289)
        ·
          refine ⟨372095085295318446556832467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496126780393757928742443289 372095085295318446556832467)
          ·
            refine ⟨558142627942977669835248701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372095085295318446556832467 558142627942977669835248701)
            ·
              refine ⟨209303485478616626188218263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 558142627942977669835248701 209303485478616626188218263)
              ·
                refine ⟨313955228217924939282327395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209303485478616626188218263 313955228217924939282327395)
                ·
                  refine ⟨470932842326887408923491093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313955228217924939282327395 470932842326887408923491093)
                  ·
                    refine ⟨22074976984072847293288645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 470932842326887408923491093 22074976984072847293288645)
                    ·
                      refine ⟨4139058184513658867491621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22074976984072847293288645 4139058184513658867491621)
                      ·
                        rfl

theorem cell23_8060787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 6, 4].length) (baseStart_8060787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060787 prefixEnd_8060787 := by exact prefixLift 8060787
  have htrace : WordTrace (prefixWord ++ tailWord_8060787) baseStart_8060787 baseEnd_8060787 := by
    simpa [prefixWord, tailWord_8060787, baseEnd_8060787] using wordTrace_append hprefix tailTrace_8060787
  have hstable : (prefixWord ++ tailWord_8060787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060787).length < 2 ^ (prefixWord ++ tailWord_8060787).sum := by decide
  have hdescent : baseEnd_8060787 < baseStart_8060787 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060794 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3]
def baseStart_8060794 : Nat := 118140960795 + 8060794 * 2 ^ 59
def prefixEnd_8060794 : Nat := 4983230072969 + 3 ^ 40 * 8060794 * 2
def baseEnd_8060794 : Nat := 4139061778878240340104089

theorem tailTrace_8060794 : CollatzResearch.WordTrace tailWord_8060794 prefixEnd_8060794 4139061778878240340104089 := by
  unfold tailWord_8060794
  simp only [CollatzResearch.WordTrace]
  refine ⟨73500327589781871714423359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196000873572751657905128957 73500327589781871714423359)
  ·
    refine ⟨110250491384672807571635039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73500327589781871714423359 110250491384672807571635039)
    ·
      refine ⟨165375737077009211357452559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110250491384672807571635039 165375737077009211357452559)
      ·
        refine ⟨248063605615513817036178839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165375737077009211357452559 248063605615513817036178839)
        ·
          refine ⟨372095408423270725554268259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248063605615513817036178839 372095408423270725554268259)
          ·
            refine ⟨558143112634906088331402389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372095408423270725554268259 558143112634906088331402389)
            ·
              refine ⟨26162958404761222890534487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 558143112634906088331402389 26162958404761222890534487)
              ·
                refine ⟨39244437607141834335801731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26162958404761222890534487 39244437607141834335801731)
                ·
                  refine ⟨58866656410712751503702597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39244437607141834335801731 58866656410712751503702597)
                  ·
                    refine ⟨11037498077008640906944237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58866656410712751503702597 11037498077008640906944237)
                    ·
                      refine ⟨4139061778878240340104089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11037498077008640906944237 4139061778878240340104089)
                      ·
                        rfl

theorem cell23_8060794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 4, 3].length) (baseStart_8060794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060794 prefixEnd_8060794 := by exact prefixLift 8060794
  have htrace : WordTrace (prefixWord ++ tailWord_8060794) baseStart_8060794 baseEnd_8060794 := by
    simpa [prefixWord, tailWord_8060794, baseEnd_8060794] using wordTrace_append hprefix tailTrace_8060794
  have hstable : (prefixWord ++ tailWord_8060794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060794).length < 2 ^ (prefixWord ++ tailWord_8060794).sum := by decide
  have hdescent : baseEnd_8060794 < baseStart_8060794 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060817 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 8]
def baseStart_8060817 : Nat := 118140960795 + 8060817 * 2 ^ 59
def prefixEnd_8060817 : Nat := 4983230072969 + 3 ^ 40 * 8060817 * 2
def baseEnd_8060817 : Nat := 4139073588933293750116483

theorem tailTrace_8060817 : CollatzResearch.WordTrace tailWord_8060817 prefixEnd_8060817 4139073588933293750116483 := by
  unfold tailWord_8060817
  simp only [CollatzResearch.WordTrace]
  refine ⟨294002149238044161785780705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196001432825362774523853803 294002149238044161785780705)
  ·
    refine ⟨220501611928533121339335529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294002149238044161785780705 220501611928533121339335529)
    ·
      refine ⟨165376208946399841004501647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220501611928533121339335529 165376208946399841004501647)
      ·
        refine ⟨248064313419599761506752471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165376208946399841004501647 248064313419599761506752471)
        ·
          refine ⟨372096470129399642260128707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248064313419599761506752471 372096470129399642260128707)
          ·
            refine ⟨558144705194099463390193061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372096470129399642260128707 558144705194099463390193061)
            ·
              refine ⟨104652132223893649385661199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 558144705194099463390193061 104652132223893649385661199)
              ·
                refine ⟨156978198335840474078491799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104652132223893649385661199 156978198335840474078491799)
                ·
                  refine ⟨235467297503760711117737699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156978198335840474078491799 235467297503760711117737699)
                  ·
                    refine ⟨353200946255641066676606549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235467297503760711117737699 353200946255641066676606549)
                    ·
                      refine ⟨4139073588933293750116483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 353200946255641066676606549 4139073588933293750116483)
                      ·
                        rfl

theorem cell23_8060817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 8].length) (baseStart_8060817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060817 prefixEnd_8060817 := by exact prefixLift 8060817
  have htrace : WordTrace (prefixWord ++ tailWord_8060817) baseStart_8060817 baseEnd_8060817 := by
    simpa [prefixWord, tailWord_8060817, baseEnd_8060817] using wordTrace_append hprefix tailTrace_8060817
  have hstable : (prefixWord ++ tailWord_8060817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060817).length < 2 ^ (prefixWord ++ tailWord_8060817).sum := by decide
  have hdescent : baseEnd_8060817 < baseStart_8060817 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060818 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 3, 4]
def baseStart_8060818 : Nat := 118140960795 + 8060818 * 2 ^ 59
def prefixEnd_8060818 : Nat := 4983230072969 + 3 ^ 40 * 8060818 * 2
def baseEnd_8060818 : Nat := 1379691367471316082067993

theorem tailTrace_8060818 : CollatzResearch.WordTrace tailWord_8060818 prefixEnd_8060818 1379691367471316082067993 := by
  unfold tailWord_8060818
  simp only [CollatzResearch.WordTrace]
  refine ⟨73500546427760134739141777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196001457140693692637711405 73500546427760134739141777)
  ·
    refine ⟨55125409820820101054356333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73500546427760134739141777 55125409820820101054356333)
    ·
      refine ⟨20672028682807537895383625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55125409820820101054356333 20672028682807537895383625)
      ·
        refine ⟨15504021512105653421537719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20672028682807537895383625 15504021512105653421537719)
        ·
          refine ⟨23256032268158480132306579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15504021512105653421537719 23256032268158480132306579)
          ·
            refine ⟨34884048402237720198459869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23256032268158480132306579 34884048402237720198459869)
            ·
              refine ⟨13081518150839145074422451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34884048402237720198459869 13081518150839145074422451)
              ·
                refine ⟨19622277226258717611633677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13081518150839145074422451 19622277226258717611633677)
                ·
                  refine ⟨7358353959847019104362629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19622277226258717611633677 7358353959847019104362629)
                  ·
                    refine ⟨1379691367471316082067993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7358353959847019104362629 1379691367471316082067993)
                    ·
                      rfl

theorem cell23_8060818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 3, 4].length) (baseStart_8060818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060818 prefixEnd_8060818 := by exact prefixLift 8060818
  have htrace : WordTrace (prefixWord ++ tailWord_8060818) baseStart_8060818 baseEnd_8060818 := by
    simpa [prefixWord, tailWord_8060818, baseEnd_8060818] using wordTrace_append hprefix tailTrace_8060818
  have hstable : (prefixWord ++ tailWord_8060818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060818).length < 2 ^ (prefixWord ++ tailWord_8060818).sum := by decide
  have hdescent : baseEnd_8060818 < baseStart_8060818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060831 : List Nat := [1, 1, 2, 5, 3, 1, 1, 3, 6]
def baseStart_8060831 : Nat := 118140960795 + 8060831 * 2 ^ 59
def prefixEnd_8060831 : Nat := 4983230072969 + 3 ^ 40 * 8060831 * 2
def baseEnd_8060831 : Nat := 459897864184717410593491

theorem tailTrace_8060831 : CollatzResearch.WordTrace tailWord_8060831 prefixEnd_8060831 459897864184717410593491 := by
  unfold tailWord_8060831
  simp only [CollatzResearch.WordTrace]
  refine ⟨294002659859993442176790347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196001773239995628117860231 294002659859993442176790347)
  ·
    refine ⟨441003989789990163265185521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294002659859993442176790347 441003989789990163265185521)
    ·
      refine ⟨330752992342492622448889141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441003989789990163265185521 330752992342492622448889141)
      ·
        refine ⟨31008093032108683354583357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330752992342492622448889141 31008093032108683354583357)
        ·
          refine ⟨11628034887040756257968759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31008093032108683354583357 11628034887040756257968759)
          ·
            refine ⟨17442052330561134386953139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11628034887040756257968759 17442052330561134386953139)
            ·
              refine ⟨26163078495841701580429709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17442052330561134386953139 26163078495841701580429709)
              ·
                refine ⟨9811154435940638092661141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26163078495841701580429709 9811154435940638092661141)
                ·
                  refine ⟨459897864184717410593491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9811154435940638092661141 459897864184717410593491)
                  ·
                    rfl

theorem cell23_8060831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 3, 6].length) (baseStart_8060831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060831 prefixEnd_8060831 := by exact prefixLift 8060831
  have htrace : WordTrace (prefixWord ++ tailWord_8060831) baseStart_8060831 baseEnd_8060831 := by
    simpa [prefixWord, tailWord_8060831, baseEnd_8060831] using wordTrace_append hprefix tailTrace_8060831
  have hstable : (prefixWord ++ tailWord_8060831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060831).length < 2 ^ (prefixWord ++ tailWord_8060831).sum := by decide
  have hdescent : baseEnd_8060831 < baseStart_8060831 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060909 : List Nat := [1, 5, 1, 4, 1, 1, 2, 3, 1, 1, 3]
def baseStart_8060909 : Nat := 118140960795 + 8060909 * 2 ^ 59
def prefixEnd_8060909 : Nat := 4983230072969 + 3 ^ 40 * 8060909 * 2
def baseEnd_8060909 : Nat := 4139120829153507390166061

theorem tailTrace_8060909 : CollatzResearch.WordTrace tailWord_8060909 prefixEnd_8060909 4139120829153507390166061 := by
  unfold tailWord_8060909
  simp only [CollatzResearch.WordTrace]
  refine ⟨294005504753710861498129781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196003669835807240998753187 294005504753710861498129781)
  ·
    refine ⟨27563016070660393265449667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294005504753710861498129781 27563016070660393265449667)
    ·
      refine ⟨41344524105990589898174501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27563016070660393265449667 41344524105990589898174501)
      ·
        refine ⟨7752098269873235605907719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41344524105990589898174501 7752098269873235605907719)
        ·
          refine ⟨11628147404809853408861579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7752098269873235605907719 11628147404809853408861579)
          ·
            refine ⟨17442221107214780113292369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11628147404809853408861579 17442221107214780113292369)
            ·
              refine ⟨13081665830411085084969277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17442221107214780113292369 13081665830411085084969277)
              ·
                refine ⟨4905624686404156906863479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13081665830411085084969277 4905624686404156906863479)
                ·
                  refine ⟨7358437029606235360295219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905624686404156906863479 7358437029606235360295219)
                  ·
                    refine ⟨11037655544409353040442829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7358437029606235360295219 11037655544409353040442829)
                    ·
                      refine ⟨4139120829153507390166061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11037655544409353040442829 4139120829153507390166061)
                      ·
                        rfl

theorem cell23_8060909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_8060909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060909 prefixEnd_8060909 := by exact prefixLift 8060909
  have htrace : WordTrace (prefixWord ++ tailWord_8060909) baseStart_8060909 baseEnd_8060909 := by
    simpa [prefixWord, tailWord_8060909, baseEnd_8060909] using wordTrace_append hprefix tailTrace_8060909
  have hstable : (prefixWord ++ tailWord_8060909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060909).length < 2 ^ (prefixWord ++ tailWord_8060909).sum := by decide
  have hdescent : baseEnd_8060909 < baseStart_8060909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8060998 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 1, 8]
def baseStart_8060998 : Nat := 118140960795 + 8060998 * 2 ^ 59
def prefixEnd_8060998 : Nat := 4983230072969 + 3 ^ 40 * 8060998 * 2
def baseEnd_8060998 : Nat := 1379722176310585847317717

theorem tailTrace_8060998 : CollatzResearch.WordTrace tailWord_8060998 prefixEnd_8060998 1379722176310585847317717 := by
  unfold tailWord_8060998
  simp only [CollatzResearch.WordTrace]
  refine ⟨9187773464074638428066239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196005833900258953132079765 9187773464074638428066239)
  ·
    refine ⟨13781660196111957642099359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9187773464074638428066239 13781660196111957642099359)
    ·
      refine ⟨20672490294167936463149039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13781660196111957642099359 20672490294167936463149039)
      ·
        refine ⟨31008735441251904694723559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20672490294167936463149039 31008735441251904694723559)
        ·
          refine ⟨46513103161877857042085339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31008735441251904694723559 46513103161877857042085339)
          ·
            refine ⟨69769654742816785563128009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46513103161877857042085339 69769654742816785563128009)
            ·
              refine ⟨52327241057112589172346007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69769654742816785563128009 52327241057112589172346007)
              ·
                refine ⟨78490861585668883758519011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52327241057112589172346007 78490861585668883758519011)
                ·
                  refine ⟨117736292378503325637778517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78490861585668883758519011 117736292378503325637778517)
                  ·
                    refine ⟨1379722176310585847317717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117736292378503325637778517 1379722176310585847317717)
                    ·
                      rfl

theorem cell23_8060998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_8060998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8060998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8060998 prefixEnd_8060998 := by exact prefixLift 8060998
  have htrace : WordTrace (prefixWord ++ tailWord_8060998) baseStart_8060998 baseEnd_8060998 := by
    simpa [prefixWord, tailWord_8060998, baseEnd_8060998] using wordTrace_append hprefix tailTrace_8060998
  have hstable : (prefixWord ++ tailWord_8060998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8060998).length < 2 ^ (prefixWord ++ tailWord_8060998).sum := by decide
  have hdescent : baseEnd_8060998 < baseStart_8060998 := by decide
  rcases family_descends (prefixWord ++ tailWord_8060998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061005 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 1, 4, 2]
def baseStart_8061005 : Nat := 118140960795 + 8061005 * 2 ^ 59
def prefixEnd_8061005 : Nat := 4983230072969 + 3 ^ 40 * 8061005 * 2
def baseEnd_8061005 : Nat := 4139170123296339014565619

theorem tailTrace_8061005 : CollatzResearch.WordTrace tailWord_8061005 prefixEnd_8061005 4139170123296339014565619 := by
  unfold tailWord_8061005
  simp only [CollatzResearch.WordTrace]
  refine ⟨294009006161363069893624469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196006004107575379929082979 294009006161363069893624469)
  ·
    refine ⟨13781672163813893901263647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 294009006161363069893624469 13781672163813893901263647)
    ·
      refine ⟨20672508245720840851895471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13781672163813893901263647 20672508245720840851895471)
      ·
        refine ⟨31008762368581261277843207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20672508245720840851895471 31008762368581261277843207)
        ·
          refine ⟨46513143552871891916764811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31008762368581261277843207 46513143552871891916764811)
          ·
            refine ⟨69769715329307837875147217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46513143552871891916764811 69769715329307837875147217)
            ·
              refine ⟨52327286496980878406360413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69769715329307837875147217 52327286496980878406360413)
              ·
                refine ⟨19622732436367829402385155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52327286496980878406360413 19622732436367829402385155)
                ·
                  refine ⟨29434098654551744103577733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19622732436367829402385155 29434098654551744103577733)
                  ·
                    refine ⟨5518893497728452019420825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29434098654551744103577733 5518893497728452019420825)
                    ·
                      refine ⟨4139170123296339014565619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5518893497728452019420825 4139170123296339014565619)
                      ·
                        rfl

theorem cell23_8061005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 1, 4, 2].length) (baseStart_8061005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061005 prefixEnd_8061005 := by exact prefixLift 8061005
  have htrace : WordTrace (prefixWord ++ tailWord_8061005) baseStart_8061005 baseEnd_8061005 := by
    simpa [prefixWord, tailWord_8061005, baseEnd_8061005] using wordTrace_append hprefix tailTrace_8061005
  have hstable : (prefixWord ++ tailWord_8061005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061005).length < 2 ^ (prefixWord ++ tailWord_8061005).sum := by decide
  have hdescent : baseEnd_8061005 < baseStart_8061005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061038 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3]
def baseStart_8061038 : Nat := 118140960795 + 8061038 * 2 ^ 59
def prefixEnd_8061038 : Nat := 4983230072969 + 3 ^ 40 * 8061038 * 2
def baseEnd_8061038 : Nat := 4139187068157937385452967

theorem tailTrace_8061038 : CollatzResearch.WordTrace tailWord_8061038 prefixEnd_8061038 4139187068157937385452967 := by
  unfold tailWord_8061038
  simp only [CollatzResearch.WordTrace]
  refine ⟨36751276221280439566196971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196006806513495677686383845 36751276221280439566196971)
  ·
    refine ⟨55126914331920659349295457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36751276221280439566196971 55126914331920659349295457)
    ·
      refine ⟨41345185748940494511971593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55126914331920659349295457 41345185748940494511971593)
      ·
        refine ⟨31008889311705370883978695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41345185748940494511971593 31008889311705370883978695)
        ·
          refine ⟨46513333967558056325968043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31008889311705370883978695 46513333967558056325968043)
          ·
            refine ⟨69770000951337084488952065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46513333967558056325968043 69770000951337084488952065)
            ·
              refine ⟨52327500713502813366714049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69770000951337084488952065 52327500713502813366714049)
              ·
                refine ⟨39245625535127110025035537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52327500713502813366714049 39245625535127110025035537)
                ·
                  refine ⟨29434219151345332518776653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39245625535127110025035537 29434219151345332518776653)
                  ·
                    refine ⟨11037832181754499694541245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29434219151345332518776653 11037832181754499694541245)
                    ·
                      refine ⟨4139187068157937385452967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11037832181754499694541245 4139187068157937385452967)
                      ·
                        rfl

theorem cell23_8061038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_8061038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061038 prefixEnd_8061038 := by exact prefixLift 8061038
  have htrace : WordTrace (prefixWord ++ tailWord_8061038) baseStart_8061038 baseEnd_8061038 := by
    simpa [prefixWord, tailWord_8061038, baseEnd_8061038] using wordTrace_append hprefix tailTrace_8061038
  have hstable : (prefixWord ++ tailWord_8061038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061038).length < 2 ^ (prefixWord ++ tailWord_8061038).sum := by decide
  have hdescent : baseEnd_8061038 < baseStart_8061038 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061041 : List Nat := [1, 2, 2, 2, 1, 1, 3, 4, 2, 5]
def baseStart_8061041 : Nat := 118140960795 + 8061041 * 2 ^ 59
def prefixEnd_8061041 : Nat := 4983230072969 + 3 ^ 40 * 8061041 * 2
def baseEnd_8061041 : Nat := 1379729536199966957905151

theorem tailTrace_8061041 : CollatzResearch.WordTrace tailWord_8061041 prefixEnd_8061041 1379729536199966957905151 := by
  unfold tailWord_8061041
  simp only [CollatzResearch.WordTrace]
  refine ⟨294010319189232648041934977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196006879459488432027956651 294010319189232648041934977)
  ·
    refine ⟨220507739391924486031451233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294010319189232648041934977 220507739391924486031451233)
    ·
      refine ⟨165380804543943364523588425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220507739391924486031451233 165380804543943364523588425)
      ·
        refine ⟨124035603407957523392691319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165380804543943364523588425 124035603407957523392691319)
        ·
          refine ⟨186053405111936285089036979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124035603407957523392691319 186053405111936285089036979)
          ·
            refine ⟨279080107667904427633555469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186053405111936285089036979 279080107667904427633555469)
            ·
              refine ⟨104655040375464160362583301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279080107667904427633555469 104655040375464160362583301)
              ·
                refine ⟨19622820070399530067984369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104655040375464160362583301 19622820070399530067984369)
                ·
                  refine ⟨14717115052799647550988277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19622820070399530067984369 14717115052799647550988277)
                  ·
                    refine ⟨1379729536199966957905151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14717115052799647550988277 1379729536199966957905151)
                    ·
                      rfl

theorem cell23_8061041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_8061041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061041 prefixEnd_8061041 := by exact prefixLift 8061041
  have htrace : WordTrace (prefixWord ++ tailWord_8061041) baseStart_8061041 baseEnd_8061041 := by
    simpa [prefixWord, tailWord_8061041, baseEnd_8061041] using wordTrace_append hprefix tailTrace_8061041
  have hstable : (prefixWord ++ tailWord_8061041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061041).length < 2 ^ (prefixWord ++ tailWord_8061041).sum := by decide
  have hdescent : baseEnd_8061041 < baseStart_8061041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061161 : List Nat := [1, 2, 1, 1, 1, 2, 2, 4, 3, 6]
def baseStart_8061161 : Nat := 118140960795 + 8061161 * 2 ^ 59
def prefixEnd_8061161 : Nat := 4983230072969 + 3 ^ 40 * 8061161 * 2
def baseEnd_8061161 : Nat := 1379750075426146801404967

theorem tailTrace_8061161 : CollatzResearch.WordTrace tailWord_8061161 prefixEnd_8061161 1379750075426146801404967 := by
  unfold tailWord_8061161
  simp only [CollatzResearch.WordTrace]
  refine ⟨294014695948797908536303337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196009797299198605690868891 294014695948797908536303337)
  ·
    refine ⟨220511021961598431402227503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294014695948797908536303337 220511021961598431402227503)
    ·
      refine ⟨330766532942397647103341255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220511021961598431402227503 330766532942397647103341255)
      ·
        refine ⟨496149799413596470655011883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330766532942397647103341255 496149799413596470655011883)
        ·
          refine ⟨744224699120394705982517825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496149799413596470655011883 744224699120394705982517825)
          ·
            refine ⟨558168524340296029486888369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744224699120394705982517825 558168524340296029486888369)
            ·
              refine ⟨418626393255222022115166277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558168524340296029486888369 418626393255222022115166277)
              ·
                refine ⟨78492448735354129146593677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418626393255222022115166277 78492448735354129146593677)
                ·
                  refine ⟨29434668275757798429972629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78492448735354129146593677 29434668275757798429972629)
                  ·
                    refine ⟨1379750075426146801404967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29434668275757798429972629 1379750075426146801404967)
                    ·
                      rfl

theorem cell23_8061161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 3, 6].length) (baseStart_8061161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061161 prefixEnd_8061161 := by exact prefixLift 8061161
  have htrace : WordTrace (prefixWord ++ tailWord_8061161) baseStart_8061161 baseEnd_8061161 := by
    simpa [prefixWord, tailWord_8061161, baseEnd_8061161] using wordTrace_append hprefix tailTrace_8061161
  have hstable : (prefixWord ++ tailWord_8061161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061161).length < 2 ^ (prefixWord ++ tailWord_8061161).sum := by decide
  have hdescent : baseEnd_8061161 < baseStart_8061161 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061205 : List Nat := [1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 3]
def baseStart_8061205 : Nat := 118140960795 + 8061205 * 2 ^ 59
def prefixEnd_8061205 : Nat := 4983230072969 + 3 ^ 40 * 8061205 * 2
def baseEnd_8061205 : Nat := 4139272819427238232064699

theorem tailTrace_8061205 : CollatzResearch.WordTrace tailWord_8061205 prefixEnd_8061205 4139272819427238232064699 := by
  unfold tailWord_8061205
  simp only [CollatzResearch.WordTrace]
  refine ⟨294016300760638504050905069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196010867173759002700603379 294016300760638504050905069)
  ·
    refine ⟨110256112785239439019089401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294016300760638504050905069 110256112785239439019089401)
    ·
      refine ⟨82692084588929579264317051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110256112785239439019089401 82692084588929579264317051)
      ·
        refine ⟨124038126883394368896475577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82692084588929579264317051 124038126883394368896475577)
        ·
          refine ⟨93028595162545776672356683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124038126883394368896475577 93028595162545776672356683)
          ·
            refine ⟨139542892743818665008535025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93028595162545776672356683 139542892743818665008535025)
            ·
              refine ⟨104657169557863998756401269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139542892743818665008535025 104657169557863998756401269)
              ·
                refine ⟨9811609646049749883412619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104657169557863998756401269 9811609646049749883412619)
                ·
                  refine ⟨14717414469074624825118929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9811609646049749883412619 14717414469074624825118929)
                  ·
                    refine ⟨11038060851805968618839197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14717414469074624825118929 11038060851805968618839197)
                    ·
                      refine ⟨4139272819427238232064699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11038060851805968618839197 4139272819427238232064699)
                      ·
                        rfl

theorem cell23_8061205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_8061205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061205 prefixEnd_8061205 := by exact prefixLift 8061205
  have htrace : WordTrace (prefixWord ++ tailWord_8061205) baseStart_8061205 baseEnd_8061205 := by
    simpa [prefixWord, tailWord_8061205, baseEnd_8061205] using wordTrace_append hprefix tailTrace_8061205
  have hstable : (prefixWord ++ tailWord_8061205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061205).length < 2 ^ (prefixWord ++ tailWord_8061205).sum := by decide
  have hdescent : baseEnd_8061205 < baseStart_8061205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061213 : List Nat := [1, 4, 2, 3, 2, 2, 2, 2, 1, 1, 3]
def baseStart_8061213 : Nat := 118140960795 + 8061213 * 2 ^ 59
def prefixEnd_8061213 : Nat := 4983230072969 + 3 ^ 40 * 8061213 * 2
def baseEnd_8061213 : Nat := 4139276927272474200764663

theorem tailTrace_8061213 : CollatzResearch.WordTrace tailWord_8061213 prefixEnd_8061213 4139276927272474200764663 := by
  unfold tailWord_8061213
  simp only [CollatzResearch.WordTrace]
  refine ⟨294016592544609521417196293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196011061696406347611464195 294016592544609521417196293)
  ·
    refine ⟨55128111102114285265724305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294016592544609521417196293 55128111102114285265724305)
    ·
      refine ⟨41346083326585713949293229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55128111102114285265724305 41346083326585713949293229)
      ·
        refine ⟨15504781247469642730984961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41346083326585713949293229 15504781247469642730984961)
        ·
          refine ⟨11628585935602232048238721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15504781247469642730984961 11628585935602232048238721)
          ·
            refine ⟨8721439451701674036179041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11628585935602232048238721 8721439451701674036179041)
            ·
              refine ⟨6541079588776255527134281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8721439451701674036179041 6541079588776255527134281)
              ·
                refine ⟨4905809691582191645350711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6541079588776255527134281 4905809691582191645350711)
                ·
                  refine ⟨7358714537373287468026067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905809691582191645350711 7358714537373287468026067)
                  ·
                    refine ⟨11038071806059931202039101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7358714537373287468026067 11038071806059931202039101)
                    ·
                      refine ⟨4139276927272474200764663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11038071806059931202039101 4139276927272474200764663)
                      ·
                        rfl

theorem cell23_8061213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 2, 1, 1, 3].length) (baseStart_8061213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061213 prefixEnd_8061213 := by exact prefixLift 8061213
  have htrace : WordTrace (prefixWord ++ tailWord_8061213) baseStart_8061213 baseEnd_8061213 := by
    simpa [prefixWord, tailWord_8061213, baseEnd_8061213] using wordTrace_append hprefix tailTrace_8061213
  have hstable : (prefixWord ++ tailWord_8061213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061213).length < 2 ^ (prefixWord ++ tailWord_8061213).sum := by decide
  have hdescent : baseEnd_8061213 < baseStart_8061213 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061219 : List Nat := [1, 1, 1, 4, 2, 2, 3, 4, 1, 2, 2]
def baseStart_8061219 : Nat := 118140960795 + 8061219 * 2 ^ 59
def prefixEnd_8061219 : Nat := 4983230072969 + 3 ^ 40 * 8061219 * 2
def baseEnd_8061219 : Nat := 4139280008156401177289635

theorem tailTrace_8061219 : CollatzResearch.WordTrace tailWord_8061219 prefixEnd_8061219 4139280008156401177289635 := by
  unfold tailWord_8061219
  simp only [CollatzResearch.WordTrace]
  refine ⟨294016811382587784441914711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196011207588391856294609807 294016811382587784441914711)
  ·
    refine ⟨441025217073881676662872067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294016811382587784441914711 441025217073881676662872067)
    ·
      refine ⟨661537825610822514994308101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441025217073881676662872067 661537825610822514994308101)
      ·
        refine ⟨124038342302029221561432769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 661537825610822514994308101 124038342302029221561432769)
        ·
          refine ⟨93028756726521916171074577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124038342302029221561432769 93028756726521916171074577)
          ·
            refine ⟨69771567544891437128305933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93028756726521916171074577 69771567544891437128305933)
            ·
              refine ⟨26164337829334288923114725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69771567544891437128305933 26164337829334288923114725)
              ·
                refine ⟨4905813343000179173084011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26164337829334288923114725 4905813343000179173084011)
                ·
                  refine ⟨7358720014500268759626017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4905813343000179173084011 7358720014500268759626017)
                  ·
                    refine ⟨5519040010875201569719513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7358720014500268759626017 5519040010875201569719513)
                    ·
                      refine ⟨4139280008156401177289635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519040010875201569719513 4139280008156401177289635)
                      ·
                        rfl

theorem cell23_8061219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_8061219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061219 prefixEnd_8061219 := by exact prefixLift 8061219
  have htrace : WordTrace (prefixWord ++ tailWord_8061219) baseStart_8061219 baseEnd_8061219 := by
    simpa [prefixWord, tailWord_8061219, baseEnd_8061219] using wordTrace_append hprefix tailTrace_8061219
  have hstable : (prefixWord ++ tailWord_8061219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061219).length < 2 ^ (prefixWord ++ tailWord_8061219).sum := by decide
  have hdescent : baseEnd_8061219 < baseStart_8061219 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061235 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 3]
def baseStart_8061235 : Nat := 118140960795 + 8061235 * 2 ^ 59
def prefixEnd_8061235 : Nat := 4983230072969 + 3 ^ 40 * 8061235 * 2
def baseEnd_8061235 : Nat := 4139288223846873114689561

theorem tailTrace_8061235 : CollatzResearch.WordTrace tailWord_8061235 prefixEnd_8061235 4139288223846873114689561 := by
  unfold tailWord_8061235
  simp only [CollatzResearch.WordTrace]
  refine ⟨294017394950529819174497159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196011596633686546116331439 294017394950529819174497159)
  ·
    refine ⟨441026092425794728761745739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294017394950529819174497159 441026092425794728761745739)
    ·
      refine ⟨661539138638692093142618609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441026092425794728761745739 661539138638692093142618609)
      ·
        refine ⟨496154353979019069856963957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661539138638692093142618609 496154353979019069856963957)
        ·
          refine ⟨46514470685533037799090371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 496154353979019069856963957 46514470685533037799090371)
          ·
            refine ⟨69771706028299556698635557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46514470685533037799090371 69771706028299556698635557)
            ·
              refine ⟨13082194880306166880994167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69771706028299556698635557 13082194880306166880994167)
              ·
                refine ⟨19623292320459250321491251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13082194880306166880994167 19623292320459250321491251)
                ·
                  refine ⟨29434938480688875482236877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19623292320459250321491251 29434938480688875482236877)
                  ·
                    refine ⟨11038101930258328305838829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29434938480688875482236877 11038101930258328305838829)
                    ·
                      refine ⟨4139288223846873114689561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11038101930258328305838829 4139288223846873114689561)
                      ·
                        rfl

theorem cell23_8061235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 1, 3, 3].length) (baseStart_8061235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061235 prefixEnd_8061235 := by exact prefixLift 8061235
  have htrace : WordTrace (prefixWord ++ tailWord_8061235) baseStart_8061235 baseEnd_8061235 := by
    simpa [prefixWord, tailWord_8061235, baseEnd_8061235] using wordTrace_append hprefix tailTrace_8061235
  have hstable : (prefixWord ++ tailWord_8061235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061235).length < 2 ^ (prefixWord ++ tailWord_8061235).sum := by decide
  have hdescent : baseEnd_8061235 < baseStart_8061235 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061432 : List Nat := [2, 1, 2, 1, 1, 4, 1, 2, 5, 1, 3]
def baseStart_8061432 : Nat := 118140960795 + 8061432 * 2 ^ 59
def prefixEnd_8061432 : Nat := 4983230072969 + 3 ^ 40 * 8061432 * 2
def baseEnd_8061432 : Nat := 4139389379535808843926155

theorem tailTrace_8061432 : CollatzResearch.WordTrace tailWord_8061432 prefixEnd_8061432 4139389379535808843926155 := by
  unfold tailWord_8061432
  simp only [CollatzResearch.WordTrace]
  refine ⟨147012290065408060909709275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196016386753877414546279033 147012290065408060909709275)
  ·
    refine ⟨220518435098112091364563913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147012290065408060909709275 220518435098112091364563913)
    ·
      refine ⟨165388826323584068523422935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220518435098112091364563913 165388826323584068523422935)
      ·
        refine ⟨248083239485376102785134403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165388826323584068523422935 248083239485376102785134403)
        ·
          refine ⟨372124859228064154177701605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248083239485376102785134403 372124859228064154177701605)
          ·
            refine ⟨69773411105262028908319051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372124859228064154177701605 69773411105262028908319051)
            ·
              refine ⟨104660116657893043362478577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69773411105262028908319051 104660116657893043362478577)
              ·
                refine ⟨78495087493419782521858933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104660116657893043362478577 78495087493419782521858933)
                ·
                  refine ⟨7358914452508104611424275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78495087493419782521858933 7358914452508104611424275)
                  ·
                    refine ⟨11038371678762156917136413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7358914452508104611424275 11038371678762156917136413)
                    ·
                      refine ⟨4139389379535808843926155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11038371678762156917136413 4139389379535808843926155)
                      ·
                        rfl

theorem cell23_8061432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 2, 5, 1, 3].length) (baseStart_8061432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061432 prefixEnd_8061432 := by exact prefixLift 8061432
  have htrace : WordTrace (prefixWord ++ tailWord_8061432) baseStart_8061432 baseEnd_8061432 := by
    simpa [prefixWord, tailWord_8061432, baseEnd_8061432] using wordTrace_append hprefix tailTrace_8061432
  have hstable : (prefixWord ++ tailWord_8061432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061432).length < 2 ^ (prefixWord ++ tailWord_8061432).sum := by decide
  have hdescent : baseEnd_8061432 < baseStart_8061432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061469 : List Nat := [1, 4, 2, 2, 1, 3, 2, 2, 1, 5]
def baseStart_8061469 : Nat := 118140960795 + 8061469 * 2 ^ 59
def prefixEnd_8061469 : Nat := 4983230072969 + 3 ^ 40 * 8061469 * 2
def baseEnd_8061469 : Nat := 1379802792773341733054495

theorem tailTrace_8061469 : CollatzResearch.WordTrace tailWord_8061469 prefixEnd_8061469 1379802792773341733054495 := by
  unfold tailWord_8061469
  simp only [CollatzResearch.WordTrace]
  refine ⟨294025929631682077138515461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196017286421121384759010307 294025929631682077138515461)
  ·
    refine ⟨55129861805940389463471649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294025929631682077138515461 55129861805940389463471649)
    ·
      refine ⟨41347396354455292097603737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55129861805940389463471649 41347396354455292097603737)
      ·
        refine ⟨31010547265841469073202803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41347396354455292097603737 31010547265841469073202803)
        ·
          refine ⟨46515820898762203609804205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31010547265841469073202803 46515820898762203609804205)
          ·
            refine ⟨17443432837035826353676577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46515820898762203609804205 17443432837035826353676577)
            ·
              refine ⟨13082574627776869765257433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17443432837035826353676577 13082574627776869765257433)
              ·
                refine ⟨9811930970832652323943075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13082574627776869765257433 9811930970832652323943075)
                ·
                  refine ⟨14717896456248978485914613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9811930970832652323943075 14717896456248978485914613)
                  ·
                    refine ⟨1379802792773341733054495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14717896456248978485914613 1379802792773341733054495)
                    ·
                      rfl

theorem cell23_8061469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_8061469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061469 prefixEnd_8061469 := by exact prefixLift 8061469
  have htrace : WordTrace (prefixWord ++ tailWord_8061469) baseStart_8061469 baseEnd_8061469 := by
    simpa [prefixWord, tailWord_8061469, baseEnd_8061469] using wordTrace_append hprefix tailTrace_8061469
  have hstable : (prefixWord ++ tailWord_8061469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061469).length < 2 ^ (prefixWord ++ tailWord_8061469).sum := by decide
  have hdescent : baseEnd_8061469 < baseStart_8061469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061489 : List Nat := [1, 2, 2, 3, 1, 1, 2, 2, 5, 2, 2]
def baseStart_8061489 : Nat := 118140960795 + 8061489 * 2 ^ 59
def prefixEnd_8061489 : Nat := 4983230072969 + 3 ^ 40 * 8061489 * 2
def baseEnd_8061489 : Nat := 4139418647933115120913393

theorem tailTrace_8061489 : CollatzResearch.WordTrace tailWord_8061489 prefixEnd_8061489 4139418647933115120913393 := by
  unfold tailWord_8061489
  simp only [CollatzResearch.WordTrace]
  refine ⟨294026659091609620554243521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196017772727739747036162347 294026659091609620554243521)
  ·
    refine ⟨220519994318707215415682641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294026659091609620554243521 220519994318707215415682641)
    ·
      refine ⟨165389995739030411561761981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220519994318707215415682641 165389995739030411561761981)
      ·
        refine ⟨62021248402136404335660743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165389995739030411561761981 62021248402136404335660743)
        ·
          refine ⟨93031872603204606503491115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62021248402136404335660743 93031872603204606503491115)
          ·
            refine ⟨139547808904806909755236673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93031872603204606503491115 139547808904806909755236673)
            ·
              refine ⟨104660856678605182316427505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139547808904806909755236673 104660856678605182316427505)
              ·
                refine ⟨78495642508953886737320629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104660856678605182316427505 78495642508953886737320629)
                ·
                  refine ⟨7358966485214426881623809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78495642508953886737320629 7358966485214426881623809)
                  ·
                    refine ⟨5519224863910820161217857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7358966485214426881623809 5519224863910820161217857)
                    ·
                      refine ⟨4139418647933115120913393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519224863910820161217857 4139418647933115120913393)
                      ·
                        rfl

theorem cell23_8061489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_8061489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061489 prefixEnd_8061489 := by exact prefixLift 8061489
  have htrace : WordTrace (prefixWord ++ tailWord_8061489) baseStart_8061489 baseEnd_8061489 := by
    simpa [prefixWord, tailWord_8061489, baseEnd_8061489] using wordTrace_append hprefix tailTrace_8061489
  have hstable : (prefixWord ++ tailWord_8061489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061489).length < 2 ^ (prefixWord ++ tailWord_8061489).sum := by decide
  have hdescent : baseEnd_8061489 < baseStart_8061489 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061535 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_8061535 : Nat := 118140960795 + 8061535 * 2 ^ 59
def prefixEnd_8061535 : Nat := 4983230072969 + 3 ^ 40 * 8061535 * 2
def baseEnd_8061535 : Nat := 4139442268043221940938181

theorem tailTrace_8061535 : CollatzResearch.WordTrace tailWord_8061535 prefixEnd_8061535 4139442268043221940938181 := by
  unfold tailWord_8061535
  simp only [CollatzResearch.WordTrace]
  refine ⟨294028336849442970410418059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196018891232961980273612039 294028336849442970410418059)
  ·
    refine ⟨441042505274164455615627089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294028336849442970410418059 441042505274164455615627089)
    ·
      refine ⟨330781878955623341711720317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441042505274164455615627089 330781878955623341711720317)
      ·
        refine ⟨124043204608358753141895119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330781878955623341711720317 124043204608358753141895119)
        ·
          refine ⟨186064806912538129712842679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124043204608358753141895119 186064806912538129712842679)
          ·
            refine ⟨279097210368807194569264019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186064806912538129712842679 279097210368807194569264019)
            ·
              refine ⟨418645815553210791853896029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279097210368807194569264019 418645815553210791853896029)
              ·
                refine ⟨156992180832454046945211011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418645815553210791853896029 156992180832454046945211011)
                ·
                  refine ⟨235488271248681070417816517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156992180832454046945211011 235488271248681070417816517)
                  ·
                    refine ⟨44154050859127700703340597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235488271248681070417816517 44154050859127700703340597)
                    ·
                      refine ⟨4139442268043221940938181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44154050859127700703340597 4139442268043221940938181)
                      ·
                        rfl

theorem cell23_8061535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_8061535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061535 prefixEnd_8061535 := by exact prefixLift 8061535
  have htrace : WordTrace (prefixWord ++ tailWord_8061535) baseStart_8061535 baseEnd_8061535 := by
    simpa [prefixWord, tailWord_8061535, baseEnd_8061535] using wordTrace_append hprefix tailTrace_8061535
  have hstable : (prefixWord ++ tailWord_8061535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061535).length < 2 ^ (prefixWord ++ tailWord_8061535).sum := by decide
  have hdescent : baseEnd_8061535 < baseStart_8061535 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061570 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 1, 2, 4]
def baseStart_8061570 : Nat := 118140960795 + 8061570 * 2 ^ 59
def prefixEnd_8061570 : Nat := 4983230072969 + 3 ^ 40 * 8061570 * 2
def baseEnd_8061570 : Nat := 4139460239866129304000521

theorem tailTrace_8061570 : CollatzResearch.WordTrace tailWord_8061570 prefixEnd_8061570 4139460239866129304000521 := by
  unfold tailWord_8061570
  simp only [CollatzResearch.WordTrace]
  refine ⟨73507403351079042846985541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196019742269544114258628109 73507403351079042846985541)
  ·
    refine ⟨13782638128327320533809789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73507403351079042846985541 13782638128327320533809789)
    ·
      refine ⟨5168489298122745200178671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13782638128327320533809789 5168489298122745200178671)
      ·
        refine ⟨7752733947184117800268007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5168489298122745200178671 7752733947184117800268007)
        ·
          refine ⟨11629100920776176700402011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7752733947184117800268007 11629100920776176700402011)
          ·
            refine ⟨17443651381164265050603017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11629100920776176700402011 17443651381164265050603017)
            ·
              refine ⟨13082738535873198787952263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17443651381164265050603017 13082738535873198787952263)
              ·
                refine ⟨19624107803809798181928395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13082738535873198787952263 19624107803809798181928395)
                ·
                  refine ⟨29436161705714697272892593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19624107803809798181928395 29436161705714697272892593)
                  ·
                    refine ⟨22077121279286022954669445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29436161705714697272892593 22077121279286022954669445)
                    ·
                      refine ⟨4139460239866129304000521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22077121279286022954669445 4139460239866129304000521)
                      ·
                        rfl

theorem cell23_8061570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_8061570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061570 prefixEnd_8061570 := by exact prefixLift 8061570
  have htrace : WordTrace (prefixWord ++ tailWord_8061570) baseStart_8061570 baseEnd_8061570 := by
    simpa [prefixWord, tailWord_8061570, baseEnd_8061570] using wordTrace_append hprefix tailTrace_8061570
  have hstable : (prefixWord ++ tailWord_8061570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061570).length < 2 ^ (prefixWord ++ tailWord_8061570).sum := by decide
  have hdescent : baseEnd_8061570 < baseStart_8061570 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061572 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_8061572 : Nat := 118140960795 + 8061572 * 2 ^ 59
def prefixEnd_8061572 : Nat := 4983230072969 + 3 ^ 40 * 8061572 * 2
def baseEnd_8061572 : Nat := 1379820422275812765391837

theorem tailTrace_8061572 : CollatzResearch.WordTrace tailWord_8061572 prefixEnd_8061572 1379820422275812765391837 := by
  unfold tailWord_8061572
  simp only [CollatzResearch.WordTrace]
  refine ⟨147014843175154462864757485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196019790900205950486343313 147014843175154462864757485)
  ·
    refine ⟨55130566190682923574284057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147014843175154462864757485 55130566190682923574284057)
    ·
      refine ⟨41347924643012192680713043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55130566190682923574284057 41347924643012192680713043)
      ·
        refine ⟨62021886964518289021069565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41347924643012192680713043 62021886964518289021069565)
        ·
          refine ⟨23258207611694358382901087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62021886964518289021069565 23258207611694358382901087)
          ·
            refine ⟨34887311417541537574351631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23258207611694358382901087 34887311417541537574351631)
            ·
              refine ⟨52330967126312306361527447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34887311417541537574351631 52330967126312306361527447)
              ·
                refine ⟨78496450689468459542291171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52330967126312306361527447 78496450689468459542291171)
                ·
                  refine ⟨117744676034202689313436757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78496450689468459542291171 117744676034202689313436757)
                  ·
                    refine ⟨1379820422275812765391837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117744676034202689313436757 1379820422275812765391837)
                    ·
                      rfl

theorem cell23_8061572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_8061572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061572 prefixEnd_8061572 := by exact prefixLift 8061572
  have htrace : WordTrace (prefixWord ++ tailWord_8061572) baseStart_8061572 baseEnd_8061572 := by
    simpa [prefixWord, tailWord_8061572, baseEnd_8061572] using wordTrace_append hprefix tailTrace_8061572
  have hstable : (prefixWord ++ tailWord_8061572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061572).length < 2 ^ (prefixWord ++ tailWord_8061572).sum := by decide
  have hdescent : baseEnd_8061572 < baseStart_8061572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061592 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_8061592 : Nat := 118140960795 + 8061592 * 2 ^ 59
def prefixEnd_8061592 : Nat := 4983230072969 + 3 ^ 40 * 8061592 * 2
def baseEnd_8061592 : Nat := 4139471536440528217925419

theorem tailTrace_8061592 : CollatzResearch.WordTrace tailWord_8061592 prefixEnd_8061592 4139471536440528217925419 := by
  unfold tailWord_8061592
  simp only [CollatzResearch.WordTrace]
  refine ⟨147015207905118234572621515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196020277206824312763495353 147015207905118234572621515)
  ·
    refine ⟨220522811857677351858932273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147015207905118234572621515 220522811857677351858932273)
    ·
      refine ⟨165392108893258013894199205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220522811857677351858932273 165392108893258013894199205)
      ·
        refine ⟨31011020417485877605162351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165392108893258013894199205 31011020417485877605162351)
        ·
          refine ⟨46516530626228816407743527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31011020417485877605162351 46516530626228816407743527)
          ·
            refine ⟨69774795939343224611615291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46516530626228816407743527 69774795939343224611615291)
            ·
              refine ⟨104662193909014836917422937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69774795939343224611615291 104662193909014836917422937)
              ·
                refine ⟨78496645431761127688067203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104662193909014836917422937 78496645431761127688067203)
                ·
                  refine ⟨117744968147641691532100805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78496645431761127688067203 117744968147641691532100805)
                  ·
                    refine ⟨22077181527682817162268901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117744968147641691532100805 22077181527682817162268901)
                    ·
                      refine ⟨4139471536440528217925419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22077181527682817162268901 4139471536440528217925419)
                      ·
                        rfl

theorem cell23_8061592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_8061592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061592 prefixEnd_8061592 := by exact prefixLift 8061592
  have htrace : WordTrace (prefixWord ++ tailWord_8061592) baseStart_8061592 baseEnd_8061592 := by
    simpa [prefixWord, tailWord_8061592, baseEnd_8061592] using wordTrace_append hprefix tailTrace_8061592
  have hstable : (prefixWord ++ tailWord_8061592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061592).length < 2 ^ (prefixWord ++ tailWord_8061592).sum := by decide
  have hdescent : baseEnd_8061592 < baseStart_8061592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061595 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 9]
def baseStart_8061595 : Nat := 118140960795 + 8061595 * 2 ^ 59
def prefixEnd_8061595 : Nat := 4983230072969 + 3 ^ 40 * 8061595 * 2
def baseEnd_8061595 : Nat := 4139473076882491706187905

theorem tailTrace_8061595 : CollatzResearch.WordTrace tailWord_8061595 prefixEnd_8061595 4139473076882491706187905 := by
  unfold tailWord_8061595
  simp only [CollatzResearch.WordTrace]
  refine ⟨294030525229225600657602239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196020350152817067105068159 294030525229225600657602239)
  ·
    refine ⟨441045787843838400986403359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294030525229225600657602239 441045787843838400986403359)
    ·
      refine ⟨661568681765757601479605039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441045787843838400986403359 661568681765757601479605039)
      ·
        refine ⟨992353022648636402219407559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661568681765757601479605039 992353022648636402219407559)
        ·
          refine ⟨1488529533972954603329111339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992353022648636402219407559 1488529533972954603329111339)
          ·
            refine ⟨2232794300959431904993667009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1488529533972954603329111339 2232794300959431904993667009)
            ·
              refine ⟨1674595725719573928745250257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2232794300959431904993667009 1674595725719573928745250257)
              ·
                refine ⟨1255946794289680446558937693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1674595725719573928745250257 1255946794289680446558937693)
                ·
                  refine ⟨470980047858630167459601635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1255946794289680446558937693 470980047858630167459601635)
                  ·
                    refine ⟨706470071787945251189402453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 470980047858630167459601635 706470071787945251189402453)
                    ·
                      refine ⟨4139473076882491706187905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 706470071787945251189402453 4139473076882491706187905)
                      ·
                        rfl

theorem cell23_8061595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 9].length) (baseStart_8061595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061595 prefixEnd_8061595 := by exact prefixLift 8061595
  have htrace : WordTrace (prefixWord ++ tailWord_8061595) baseStart_8061595 baseEnd_8061595 := by
    simpa [prefixWord, tailWord_8061595, baseEnd_8061595] using wordTrace_append hprefix tailTrace_8061595
  have hstable : (prefixWord ++ tailWord_8061595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061595).length < 2 ^ (prefixWord ++ tailWord_8061595).sum := by decide
  have hdescent : baseEnd_8061595 < baseStart_8061595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061596 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_8061596 : Nat := 118140960795 + 8061596 * 2 ^ 59
def prefixEnd_8061596 : Nat := 4983230072969 + 3 ^ 40 * 8061596 * 2
def baseEnd_8061596 : Nat := 4139473590363146202275401

theorem tailTrace_8061596 : CollatzResearch.WordTrace tailWord_8061596 prefixEnd_8061596 4139473590363146202275401 := by
  unfold tailWord_8061596
  simp only [CollatzResearch.WordTrace]
  refine ⟨147015280851110988914194321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196020374468147985218925761 147015280851110988914194321)
  ·
    refine ⟨110261460638333241685645741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147015280851110988914194321 110261460638333241685645741)
    ·
      refine ⟨41348047739374965632117153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110261460638333241685645741 41348047739374965632117153)
      ·
        refine ⟨31011035804531224224087865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41348047739374965632117153 31011035804531224224087865)
        ·
          refine ⟨23258276853398418168065899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31011035804531224224087865 23258276853398418168065899)
          ·
            refine ⟨34887415280097627252098849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23258276853398418168065899 34887415280097627252098849)
            ·
              refine ⟨26165561460073220439074137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34887415280097627252098849 26165561460073220439074137)
              ·
                refine ⟨19624171095054915329305603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26165561460073220439074137 19624171095054915329305603)
                ·
                  refine ⟨29436256642582372993958405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19624171095054915329305603 29436256642582372993958405)
                  ·
                    refine ⟨5519298120484194936367201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29436256642582372993958405 5519298120484194936367201)
                    ·
                      refine ⟨4139473590363146202275401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519298120484194936367201 4139473590363146202275401)
                      ·
                        rfl

theorem cell23_8061596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_8061596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061596 prefixEnd_8061596 := by exact prefixLift 8061596
  have htrace : WordTrace (prefixWord ++ tailWord_8061596) baseStart_8061596 baseEnd_8061596 := by
    simpa [prefixWord, tailWord_8061596, baseEnd_8061596] using wordTrace_append hprefix tailTrace_8061596
  have hstable : (prefixWord ++ tailWord_8061596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061596).length < 2 ^ (prefixWord ++ tailWord_8061596).sum := by decide
  have hdescent : baseEnd_8061596 < baseStart_8061596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061600 : List Nat := [2, 1, 1, 4, 4, 2, 2, 1, 1, 3, 2]
def baseStart_8061600 : Nat := 118140960795 + 8061600 * 2 ^ 59
def prefixEnd_8061600 : Nat := 4983230072969 + 3 ^ 40 * 8061600 * 2
def baseEnd_8061600 : Nat := 4139475644285764186625383

theorem tailTrace_8061600 : CollatzResearch.WordTrace tailWord_8061600 prefixEnd_8061600 4139475644285764186625383 := by
  unfold tailWord_8061600
  simp only [CollatzResearch.WordTrace]
  refine ⟨147015353797103743255767127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196020471729471657674356169 147015353797103743255767127)
  ·
    refine ⟨220523030695655614883650691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147015353797103743255767127 220523030695655614883650691)
    ·
      refine ⟨330784546043483422325476037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220523030695655614883650691 330784546043483422325476037)
      ·
        refine ⟨62022102383153141686026757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330784546043483422325476037 62022102383153141686026757)
        ·
          refine ⟨11629144196841214066130017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 62022102383153141686026757 11629144196841214066130017)
          ·
            refine ⟨8721858147630910549597513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11629144196841214066130017 8721858147630910549597513)
            ·
              refine ⟨6541393610723182912198135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8721858147630910549597513 6541393610723182912198135)
              ·
                refine ⟨9812090416084774368297203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6541393610723182912198135 9812090416084774368297203)
                ·
                  refine ⟨14718135624127161552445805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9812090416084774368297203 14718135624127161552445805)
                  ·
                    refine ⟨5519300859047685582167177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14718135624127161552445805 5519300859047685582167177)
                    ·
                      refine ⟨4139475644285764186625383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519300859047685582167177 4139475644285764186625383)
                      ·
                        rfl

theorem cell23_8061600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 1, 1, 3, 2].length) (baseStart_8061600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061600 prefixEnd_8061600 := by exact prefixLift 8061600
  have htrace : WordTrace (prefixWord ++ tailWord_8061600) baseStart_8061600 baseEnd_8061600 := by
    simpa [prefixWord, tailWord_8061600, baseEnd_8061600] using wordTrace_append hprefix tailTrace_8061600
  have hstable : (prefixWord ++ tailWord_8061600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061600).length < 2 ^ (prefixWord ++ tailWord_8061600).sum := by decide
  have hdescent : baseEnd_8061600 < baseStart_8061600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061607 : List Nat := [1, 1, 6, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_8061607 : Nat := 118140960795 + 8061607 * 2 ^ 59
def prefixEnd_8061607 : Nat := 4983230072969 + 3 ^ 40 * 8061607 * 2
def baseEnd_8061607 : Nat := 4139479238650345659237851

theorem tailTrace_8061607 : CollatzResearch.WordTrace tailWord_8061607 prefixEnd_8061607 4139479238650345659237851 := by
  unfold tailWord_8061607
  simp only [CollatzResearch.WordTrace]
  refine ⟨294030962905182126707039075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196020641936788084471359383 294030962905182126707039075)
  ·
    refine ⟨441046444357773190060558613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294030962905182126707039075 441046444357773190060558613)
    ·
      refine ⟨20674052079270618284088685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 441046444357773190060558613 20674052079270618284088685)
      ·
        refine ⟨7752769529726481856533257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20674052079270618284088685 7752769529726481856533257)
        ·
          refine ⟨5814577147294861392399943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7752769529726481856533257 5814577147294861392399943)
          ·
            refine ⟨8721865720942292088599915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5814577147294861392399943 8721865720942292088599915)
            ·
              refine ⟨13082798581413438132899873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8721865720942292088599915 13082798581413438132899873)
              ·
                refine ⟨9812098936060078599674905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13082798581413438132899873 9812098936060078599674905)
                ·
                  refine ⟨7359074202045058949756179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9812098936060078599674905 7359074202045058949756179)
                  ·
                    refine ⟨11038611303067588424634269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7359074202045058949756179 11038611303067588424634269)
                    ·
                      refine ⟨4139479238650345659237851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11038611303067588424634269 4139479238650345659237851)
                      ·
                        rfl

theorem cell23_8061607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_8061607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061607 prefixEnd_8061607 := by exact prefixLift 8061607
  have htrace : WordTrace (prefixWord ++ tailWord_8061607) baseStart_8061607 baseEnd_8061607 := by
    simpa [prefixWord, tailWord_8061607, baseEnd_8061607] using wordTrace_append hprefix tailTrace_8061607
  have hstable : (prefixWord ++ tailWord_8061607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061607).length < 2 ^ (prefixWord ++ tailWord_8061607).sum := by decide
  have hdescent : baseEnd_8061607 < baseStart_8061607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061613 : List Nat := [1, 5, 2, 1, 1, 3, 1, 1, 4, 2, 2]
def baseStart_8061613 : Nat := 118140960795 + 8061613 * 2 ^ 59
def prefixEnd_8061613 : Nat := 4983230072969 + 3 ^ 40 * 8061613 * 2
def baseEnd_8061613 : Nat := 4139482319534272635762823

theorem tailTrace_8061613 : CollatzResearch.WordTrace tailWord_8061613 prefixEnd_8061613 4139482319534272635762823 := by
  unfold tailWord_8061613
  simp only [CollatzResearch.WordTrace]
  refine ⟨294031181743160389731757493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196020787828773593154504995 294031181743160389731757493)
  ·
    refine ⟨27565423288421286537352265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294031181743160389731757493 27565423288421286537352265)
    ·
      refine ⟨20674067466315964903014199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27565423288421286537352265 20674067466315964903014199)
      ·
        refine ⟨31011101199473947354521299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20674067466315964903014199 31011101199473947354521299)
        ·
          refine ⟨46516651799210921031781949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31011101199473947354521299 46516651799210921031781949)
          ·
            refine ⟨17443744424704095386918231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46516651799210921031781949 17443744424704095386918231)
            ·
              refine ⟨26165616637056143080377347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17443744424704095386918231 26165616637056143080377347)
              ·
                refine ⟨39248424955584214620566021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26165616637056143080377347 39248424955584214620566021)
                ·
                  refine ⟨7359079679172040241356129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39248424955584214620566021 7359079679172040241356129)
                  ·
                    refine ⟨5519309759379030181017097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7359079679172040241356129 5519309759379030181017097)
                    ·
                      refine ⟨4139482319534272635762823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519309759379030181017097 4139482319534272635762823)
                      ·
                        rfl

theorem cell23_8061613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_8061613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061613 prefixEnd_8061613 := by exact prefixLift 8061613
  have htrace : WordTrace (prefixWord ++ tailWord_8061613) baseStart_8061613 baseEnd_8061613 := by
    simpa [prefixWord, tailWord_8061613, baseEnd_8061613] using wordTrace_append hprefix tailTrace_8061613
  have hstable : (prefixWord ++ tailWord_8061613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061613).length < 2 ^ (prefixWord ++ tailWord_8061613).sum := by decide
  have hdescent : baseEnd_8061613 < baseStart_8061613 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061619 : List Nat := [1, 1, 1, 2, 3, 4, 2, 4, 5]
def baseStart_8061619 : Nat := 118140960795 + 8061619 * 2 ^ 59
def prefixEnd_8061619 : Nat := 4983230072969 + 3 ^ 40 * 8061619 * 2
def baseEnd_8061619 : Nat := 459942822268688845809755

theorem tailTrace_8061619 : CollatzResearch.WordTrace tailWord_8061619 prefixEnd_8061619 459942822268688845809755 := by
  unfold tailWord_8061619
  simp only [CollatzResearch.WordTrace]
  refine ⟨294031400581138652756475911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196020933720759101837650607 294031400581138652756475911)
  ·
    refine ⟨441047100871707979134713867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294031400581138652756475911 441047100871707979134713867)
    ·
      refine ⟨661570651307561968702070801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441047100871707979134713867 661570651307561968702070801)
      ·
        refine ⟨496177988480671476526553101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661570651307561968702070801 496177988480671476526553101)
        ·
          refine ⟨186066745680251803697457413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496177988480671476526553101 186066745680251803697457413)
          ·
            refine ⟨34887514815047213193273265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186066745680251803697457413 34887514815047213193273265)
            ·
              refine ⟨26165636111285409894954949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34887514815047213193273265 26165636111285409894954949)
              ·
                refine ⟨4906056770866014355304053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26165636111285409894954949 4906056770866014355304053)
                ·
                  refine ⟨459942822268688845809755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4906056770866014355304053 459942822268688845809755)
                  ·
                    rfl

theorem cell23_8061619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 2, 4, 5].length) (baseStart_8061619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061619 prefixEnd_8061619 := by exact prefixLift 8061619
  have htrace : WordTrace (prefixWord ++ tailWord_8061619) baseStart_8061619 baseEnd_8061619 := by
    simpa [prefixWord, tailWord_8061619, baseEnd_8061619] using wordTrace_append hprefix tailTrace_8061619
  have hstable : (prefixWord ++ tailWord_8061619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061619).length < 2 ^ (prefixWord ++ tailWord_8061619).sum := by decide
  have hdescent : baseEnd_8061619 < baseStart_8061619 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061629 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_8061629 : Nat := 118140960795 + 8061629 * 2 ^ 59
def prefixEnd_8061629 : Nat := 4983230072969 + 3 ^ 40 * 8061629 * 2
def baseEnd_8061629 : Nat := 4139490535224744573162749

theorem tailTrace_8061629 : CollatzResearch.WordTrace tailWord_8061629 prefixEnd_8061629 4139490535224744573162749 := by
  unfold tailWord_8061629
  simp only [CollatzResearch.WordTrace]
  refine ⟨294031765311102424464339941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196021176874068282976226627 294031765311102424464339941)
  ·
    refine ⟨55130955995831704587063739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294031765311102424464339941 55130955995831704587063739)
    ·
      refine ⟨82696433993747556880595609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55130955995831704587063739 82696433993747556880595609)
      ·
        refine ⟨62022325495310667660446707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82696433993747556880595609 62022325495310667660446707)
        ·
          refine ⟨93033488242966001490670061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62022325495310667660446707 93033488242966001490670061)
          ·
            refine ⟨34887558091112250559001273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93033488242966001490670061 34887558091112250559001273)
            ·
              refine ⟨26165668568334187919250955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34887558091112250559001273 26165668568334187919250955)
              ·
                refine ⟨39248502852501281878876433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26165668568334187919250955 39248502852501281878876433)
                ·
                  refine ⟨29436377139375961409157325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39248502852501281878876433 29436377139375961409157325)
                  ·
                    refine ⟨11038641427265985528433997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29436377139375961409157325 11038641427265985528433997)
                    ·
                      refine ⟨4139490535224744573162749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11038641427265985528433997 4139490535224744573162749)
                      ·
                        rfl

theorem cell23_8061629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_8061629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061629 prefixEnd_8061629 := by exact prefixLift 8061629
  have htrace : WordTrace (prefixWord ++ tailWord_8061629) baseStart_8061629 baseEnd_8061629 := by
    simpa [prefixWord, tailWord_8061629, baseEnd_8061629] using wordTrace_append hprefix tailTrace_8061629
  have hstable : (prefixWord ++ tailWord_8061629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061629).length < 2 ^ (prefixWord ++ tailWord_8061629).sum := by decide
  have hdescent : baseEnd_8061629 < baseStart_8061629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061630 : List Nat := [4, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2]
def baseStart_8061630 : Nat := 118140960795 + 8061630 * 2 ^ 59
def prefixEnd_8061630 : Nat := 4983230072969 + 3 ^ 40 * 8061630 * 2
def baseEnd_8061630 : Nat := 4139491048705399069250245

theorem tailTrace_8061630 : CollatzResearch.WordTrace tailWord_8061630 prefixEnd_8061630 4139491048705399069250245 := by
  unfold tailWord_8061630
  simp only [CollatzResearch.WordTrace]
  refine ⟨36753975223012350204390793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196021201189399201090084229 36753975223012350204390793)
  ·
    refine ⟨27565481417259262653293095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36753975223012350204390793 27565481417259262653293095)
    ·
      refine ⟨41348222125888893979939643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27565481417259262653293095 41348222125888893979939643)
      ·
        refine ⟨62022333188833340969909465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41348222125888893979939643 62022333188833340969909465)
        ·
          refine ⟨46516749891625005727432099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62022333188833340969909465 46516749891625005727432099)
          ·
            refine ⟨69775124837437508591148149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46516749891625005727432099 69775124837437508591148149)
            ·
              refine ⟨6541417953509766430420139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69775124837437508591148149 6541417953509766430420139)
              ·
                refine ⟨9812126930264649645630209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6541417953509766430420139 9812126930264649645630209)
                ·
                  refine ⟨7359095197698487234222657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9812126930264649645630209 7359095197698487234222657)
                  ·
                    refine ⟨5519321398273865425666993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7359095197698487234222657 5519321398273865425666993)
                    ·
                      refine ⟨4139491048705399069250245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519321398273865425666993 4139491048705399069250245)
                      ·
                        rfl

theorem cell23_8061630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 1, 2, 2, 2].length) (baseStart_8061630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061630 prefixEnd_8061630 := by exact prefixLift 8061630
  have htrace : WordTrace (prefixWord ++ tailWord_8061630) baseStart_8061630 baseEnd_8061630 := by
    simpa [prefixWord, tailWord_8061630, baseEnd_8061630] using wordTrace_append hprefix tailTrace_8061630
  have hstable : (prefixWord ++ tailWord_8061630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061630).length < 2 ^ (prefixWord ++ tailWord_8061630).sum := by decide
  have hdescent : baseEnd_8061630 < baseStart_8061630 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061632 : List Nat := [2, 1, 1, 2, 4, 2, 1, 2, 1, 7]
def baseStart_8061632 : Nat := 118140960795 + 8061632 * 2 ^ 59
def prefixEnd_8061632 : Nat := 4983230072969 + 3 ^ 40 * 8061632 * 2
def baseEnd_8061632 : Nat := 1379830691888902687141745

theorem tailTrace_8061632 : CollatzResearch.WordTrace tailWord_8061632 prefixEnd_8061632 1379830691888902687141745 := by
  unfold tailWord_8061632
  simp only [CollatzResearch.WordTrace]
  refine ⟨147015937365045777988349575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196021249820061037317799433 147015937365045777988349575)
  ·
    refine ⟨220523906047568666982524363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147015937365045777988349575 220523906047568666982524363)
    ·
      refine ⟨330785859071353000473786545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220523906047568666982524363 330785859071353000473786545)
      ·
        refine ⟨248089394303514750355339909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330785859071353000473786545 248089394303514750355339909)
        ·
          refine ⟨46516761431909015691626233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248089394303514750355339909 46516761431909015691626233)
          ·
            refine ⟨34887571073931761768719675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46516761431909015691626233 34887571073931761768719675)
            ·
              refine ⟨52331356610897642653079513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34887571073931761768719675 52331356610897642653079513)
              ·
                refine ⟨39248517458173231989809635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52331356610897642653079513 39248517458173231989809635)
                ·
                  refine ⟨58872776187259847984714453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39248517458173231989809635 58872776187259847984714453)
                  ·
                    refine ⟨1379830691888902687141745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58872776187259847984714453 1379830691888902687141745)
                    ·
                      rfl

theorem cell23_8061632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_8061632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061632 prefixEnd_8061632 := by exact prefixLift 8061632
  have htrace : WordTrace (prefixWord ++ tailWord_8061632) baseStart_8061632 baseEnd_8061632 := by
    simpa [prefixWord, tailWord_8061632, baseEnd_8061632] using wordTrace_append hprefix tailTrace_8061632
  have hstable : (prefixWord ++ tailWord_8061632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061632).length < 2 ^ (prefixWord ++ tailWord_8061632).sum := by decide
  have hdescent : baseEnd_8061632 < baseStart_8061632 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061669 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 4]
def baseStart_8061669 : Nat := 118140960795 + 8061669 * 2 ^ 59
def prefixEnd_8061669 : Nat := 4983230072969 + 3 ^ 40 * 8061669 * 2
def baseEnd_8061669 : Nat := 4139511074450924416662565

theorem tailTrace_8061669 : CollatzResearch.WordTrace tailWord_8061669 prefixEnd_8061669 4139511074450924416662565 := by
  unfold tailWord_8061669
  simp only [CollatzResearch.WordTrace]
  refine ⟨294033224230957511295796061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196022149487305007530530707 294033224230957511295796061)
  ·
    refine ⟨110262459086609066735923523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294033224230957511295796061 110262459086609066735923523)
    ·
      refine ⟨165393688629913600103885285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110262459086609066735923523 165393688629913600103885285)
      ·
        refine ⟨31011316618108800019478491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165393688629913600103885285 31011316618108800019478491)
        ·
          refine ⟨46516974927163200029217737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31011316618108800019478491 46516974927163200029217737)
          ·
            refine ⟨34887731195372400021913303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46516974927163200029217737 34887731195372400021913303)
            ·
              refine ⟨52331596793058600032869955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34887731195372400021913303 52331596793058600032869955)
              ·
                refine ⟨78497395189587900049304933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52331596793058600032869955 78497395189587900049304933)
                ·
                  refine ⟨14718261598047731259244675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78497395189587900049304933 14718261598047731259244675)
                  ·
                    refine ⟨22077392397071596888867013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14718261598047731259244675 22077392397071596888867013)
                    ·
                      refine ⟨4139511074450924416662565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22077392397071596888867013 4139511074450924416662565)
                      ·
                        rfl

theorem cell23_8061669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_8061669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061669 prefixEnd_8061669 := by exact prefixLift 8061669
  have htrace : WordTrace (prefixWord ++ tailWord_8061669) baseStart_8061669 baseEnd_8061669 := by
    simpa [prefixWord, tailWord_8061669, baseEnd_8061669] using wordTrace_append hprefix tailTrace_8061669
  have hstable : (prefixWord ++ tailWord_8061669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061669).length < 2 ^ (prefixWord ++ tailWord_8061669).sum := by decide
  have hdescent : baseEnd_8061669 < baseStart_8061669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061686 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2]
def baseStart_8061686 : Nat := 118140960795 + 8061686 * 2 ^ 59
def prefixEnd_8061686 : Nat := 4983230072969 + 3 ^ 40 * 8061686 * 2
def baseEnd_8061686 : Nat := 4139519803622050850149987

theorem tailTrace_8061686 : CollatzResearch.WordTrace tailWord_8061686 prefixEnd_8061686 4139519803622050850149987 := by
  unfold tailWord_8061686
  simp only [CollatzResearch.WordTrace]
  refine ⟨18377115266993495199947807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196022562847930615466109941 18377115266993495199947807)
  ·
    refine ⟨27565672900490242799921711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18377115266993495199947807 27565672900490242799921711)
    ·
      refine ⟨41348509350735364199882567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27565672900490242799921711 41348509350735364199882567)
      ·
        refine ⟨62022764026103046299823851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41348509350735364199882567 62022764026103046299823851)
        ·
          refine ⟨93034146039154569449735777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62022764026103046299823851 93034146039154569449735777)
          ·
            refine ⟨69775609529365927087301833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93034146039154569449735777 69775609529365927087301833)
            ·
              refine ⟨52331707147024445315476375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69775609529365927087301833 52331707147024445315476375)
              ·
                refine ⟨78497560720536667973214563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52331707147024445315476375 78497560720536667973214563)
                ·
                  refine ⟨117746341080805001959821845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78497560720536667973214563 117746341080805001959821845)
                  ·
                    refine ⟨5519359738162734466866649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117746341080805001959821845 5519359738162734466866649)
                    ·
                      refine ⟨4139519803622050850149987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519359738162734466866649 4139519803622050850149987)
                      ·
                        rfl

theorem cell23_8061686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 1, 6, 2].length) (baseStart_8061686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061686 prefixEnd_8061686 := by exact prefixLift 8061686
  have htrace : WordTrace (prefixWord ++ tailWord_8061686) baseStart_8061686 baseEnd_8061686 := by
    simpa [prefixWord, tailWord_8061686, baseEnd_8061686] using wordTrace_append hprefix tailTrace_8061686
  have hstable : (prefixWord ++ tailWord_8061686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061686).length < 2 ^ (prefixWord ++ tailWord_8061686).sum := by decide
  have hdescent : baseEnd_8061686 < baseStart_8061686 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061706 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3]
def baseStart_8061706 : Nat := 118140960795 + 8061706 * 2 ^ 59
def prefixEnd_8061706 : Nat := 4983230072969 + 3 ^ 40 * 8061706 * 2
def baseEnd_8061706 : Nat := 4139530073235140771899895

theorem tailTrace_8061706 : CollatzResearch.WordTrace tailWord_8061706 prefixEnd_8061706 4139530073235140771899895 := by
  unfold tailWord_8061706
  simp only [CollatzResearch.WordTrace]
  refine ⟨73508643432955866653723243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196023049154548977743261981 73508643432955866653723243)
  ·
    refine ⟨110262965149433799980584865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73508643432955866653723243 110262965149433799980584865)
    ·
      refine ⟨82697223862075349985438649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110262965149433799980584865 82697223862075349985438649)
      ·
        refine ⟨62022917896556512489078987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82697223862075349985438649 62022917896556512489078987)
        ·
          refine ⟨93034376844834768733618481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62022917896556512489078987 93034376844834768733618481)
          ·
            refine ⟨69775782633626076550213861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93034376844834768733618481 69775782633626076550213861)
            ·
              refine ⟨13082959243804889353165099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69775782633626076550213861 13082959243804889353165099)
              ·
                refine ⟨19624438865707334029747649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13082959243804889353165099 19624438865707334029747649)
                ·
                  refine ⟨14718329149280500522310737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19624438865707334029747649 14718329149280500522310737)
                  ·
                    refine ⟨11038746861960375391733053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14718329149280500522310737 11038746861960375391733053)
                    ·
                      refine ⟨4139530073235140771899895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11038746861960375391733053 4139530073235140771899895)
                      ·
                        rfl

theorem cell23_8061706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 2, 2, 3].length) (baseStart_8061706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061706 prefixEnd_8061706 := by exact prefixLift 8061706
  have htrace : WordTrace (prefixWord ++ tailWord_8061706) baseStart_8061706 baseEnd_8061706 := by
    simpa [prefixWord, tailWord_8061706, baseEnd_8061706] using wordTrace_append hprefix tailTrace_8061706
  have hstable : (prefixWord ++ tailWord_8061706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061706).length < 2 ^ (prefixWord ++ tailWord_8061706).sum := by decide
  have hdescent : baseEnd_8061706 < baseStart_8061706 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061730 : List Nat := [3, 3, 1, 1, 2, 2, 4, 2, 1, 4]
def baseStart_8061730 : Nat := 118140960795 + 8061730 * 2 ^ 59
def prefixEnd_8061730 : Nat := 4983230072969 + 3 ^ 40 * 8061730 * 2
def baseEnd_8061730 : Nat := 1379847465590282892666595

theorem tailTrace_8061730 : CollatzResearch.WordTrace tailWord_8061730 prefixEnd_8061730 1379847465590282892666595 := by
  unfold tailWord_8061730
  simp only [CollatzResearch.WordTrace]
  refine ⟨73508862270934129678441661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196023632722491012475844429 73508862270934129678441661)
  ·
    refine ⟨27565823351600298629415623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73508862270934129678441661 27565823351600298629415623)
    ·
      refine ⟨41348735027400447944123435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27565823351600298629415623 41348735027400447944123435)
      ·
        refine ⟨62023102541100671916185153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41348735027400447944123435 62023102541100671916185153)
        ·
          refine ⟨46517326905825503937138865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62023102541100671916185153 46517326905825503937138865)
          ·
            refine ⟨34887995179369127952854149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46517326905825503937138865 34887995179369127952854149)
            ·
              refine ⟨6541499096131711491160153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34887995179369127952854149 6541499096131711491160153)
              ·
                refine ⟨4906124322098783618370115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6541499096131711491160153 4906124322098783618370115)
                ·
                  refine ⟨7359186483148175427555173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906124322098783618370115 7359186483148175427555173)
                  ·
                    refine ⟨1379847465590282892666595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7359186483148175427555173 1379847465590282892666595)
                    ·
                      rfl

theorem cell23_8061730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 1, 4].length) (baseStart_8061730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061730 prefixEnd_8061730 := by exact prefixLift 8061730
  have htrace : WordTrace (prefixWord ++ tailWord_8061730) baseStart_8061730 baseEnd_8061730 := by
    simpa [prefixWord, tailWord_8061730, baseEnd_8061730] using wordTrace_append hprefix tailTrace_8061730
  have hstable : (prefixWord ++ tailWord_8061730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061730).length < 2 ^ (prefixWord ++ tailWord_8061730).sum := by decide
  have hdescent : baseEnd_8061730 < baseStart_8061730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061746 : List Nat := [3, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2]
def baseStart_8061746 : Nat := 118140960795 + 8061746 * 2 ^ 59
def prefixEnd_8061746 : Nat := 4983230072969 + 3 ^ 40 * 8061746 * 2
def baseEnd_8061746 : Nat := 4139550612461320615399711

theorem tailTrace_8061746 : CollatzResearch.WordTrace tailWord_8061746 prefixEnd_8061746 4139550612461320615399711 := by
  unfold tailWord_8061746
  simp only [CollatzResearch.WordTrace]
  refine ⟨73509008162919638361587273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196024021767785702297566061 73509008162919638361587273)
  ·
    refine ⟨55131756122189728771190455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73509008162919638361587273 55131756122189728771190455)
    ·
      refine ⟨82697634183284593156785683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55131756122189728771190455 82697634183284593156785683)
      ·
        refine ⟨124046451274926889735178525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82697634183284593156785683 124046451274926889735178525)
        ·
          refine ⟨46517419228097583650691947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124046451274926889735178525 46517419228097583650691947)
          ·
            refine ⟨69776128842146375476037921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46517419228097583650691947 69776128842146375476037921)
            ·
              refine ⟨52332096631609781607028441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69776128842146375476037921 52332096631609781607028441)
              ·
                refine ⟨39249072473707336205271331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52332096631609781607028441 39249072473707336205271331)
                ·
                  refine ⟨58873608710561004307906997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39249072473707336205271331 58873608710561004307906997)
                  ·
                    refine ⟨5519400816615094153866281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58873608710561004307906997 5519400816615094153866281)
                    ·
                      refine ⟨4139550612461320615399711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519400816615094153866281 4139550612461320615399711)
                      ·
                        rfl

theorem cell23_8061746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2].length) (baseStart_8061746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061746 prefixEnd_8061746 := by exact prefixLift 8061746
  have htrace : WordTrace (prefixWord ++ tailWord_8061746) baseStart_8061746 baseEnd_8061746 := by
    simpa [prefixWord, tailWord_8061746, baseEnd_8061746] using wordTrace_append hprefix tailTrace_8061746
  have hstable : (prefixWord ++ tailWord_8061746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061746).length < 2 ^ (prefixWord ++ tailWord_8061746).sum := by decide
  have hdescent : baseEnd_8061746 < baseStart_8061746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061769 : List Nat := [1, 2, 1, 1, 2, 5, 2, 2, 1, 6]
def baseStart_8061769 : Nat := 118140960795 + 8061769 * 2 ^ 59
def prefixEnd_8061769 : Nat := 4983230072969 + 3 ^ 40 * 8061769 * 2
def baseEnd_8061769 : Nat := 1379854140838791341804035

theorem tailTrace_8061769 : CollatzResearch.WordTrace tailWord_8061769 prefixEnd_8061769 1379854140838791341804035 := by
  unfold tailWord_8061769
  simp only [CollatzResearch.WordTrace]
  refine ⟨294036871530595228374436361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196024581020396818916290907 294036871530595228374436361)
  ·
    refine ⟨220527653647946421280827271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294036871530595228374436361 220527653647946421280827271)
    ·
      refine ⟨330791480471919631921240907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220527653647946421280827271 330791480471919631921240907)
      ·
        refine ⟨496187220707879447881861361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330791480471919631921240907 496187220707879447881861361)
        ·
          refine ⟨372140415530909585911396021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496187220707879447881861361 372140415530909585911396021)
          ·
            refine ⟨34888163956022773679193377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 372140415530909585911396021 34888163956022773679193377)
            ·
              refine ⟨26166122967017080259395033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34888163956022773679193377 26166122967017080259395033)
              ·
                refine ⟨19624592225262810194546275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26166122967017080259395033 19624592225262810194546275)
                ·
                  refine ⟨29436888337894215291819413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19624592225262810194546275 29436888337894215291819413)
                  ·
                    refine ⟨1379854140838791341804035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29436888337894215291819413 1379854140838791341804035)
                    ·
                      rfl

theorem cell23_8061769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 2, 1, 6].length) (baseStart_8061769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061769 prefixEnd_8061769 := by exact prefixLift 8061769
  have htrace : WordTrace (prefixWord ++ tailWord_8061769) baseStart_8061769 baseEnd_8061769 := by
    simpa [prefixWord, tailWord_8061769, baseEnd_8061769] using wordTrace_append hprefix tailTrace_8061769
  have hstable : (prefixWord ++ tailWord_8061769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061769).length < 2 ^ (prefixWord ++ tailWord_8061769).sum := by decide
  have hdescent : baseEnd_8061769 < baseStart_8061769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061786 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 4, 4]
def baseStart_8061786 : Nat := 118140960795 + 8061786 * 2 ^ 59
def prefixEnd_8061786 : Nat := 4983230072969 + 3 ^ 40 * 8061786 * 2
def baseEnd_8061786 : Nat := 1379857050562500152966509

theorem tailTrace_8061786 : CollatzResearch.WordTrace tailWord_8061786 prefixEnd_8061786 1379857050562500152966509 := by
  unfold tailWord_8061786
  simp only [CollatzResearch.WordTrace]
  refine ⟨73509372892883410069451303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196024994381022426851870141 73509372892883410069451303)
  ·
    refine ⟨110264059339325115104176955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73509372892883410069451303 110264059339325115104176955)
    ·
      refine ⟨165396089008987672656265433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110264059339325115104176955 165396089008987672656265433)
      ·
        refine ⟨124047066756740754492199075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165396089008987672656265433 124047066756740754492199075)
        ·
          refine ⟨186070600135111131738298613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124047066756740754492199075 186070600135111131738298613)
          ·
            refine ⟨17444118762666668600465495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186070600135111131738298613 17444118762666668600465495)
            ·
              refine ⟨26166178144000002900698243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17444118762666668600465495 26166178144000002900698243)
              ·
                refine ⟨39249267216000004351047365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26166178144000002900698243 39249267216000004351047365)
                ·
                  refine ⟨7359237603000000815821381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39249267216000004351047365 7359237603000000815821381)
                  ·
                    refine ⟨1379857050562500152966509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7359237603000000815821381 1379857050562500152966509)
                    ·
                      rfl

theorem cell23_8061786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 4, 4].length) (baseStart_8061786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061786 prefixEnd_8061786 := by exact prefixLift 8061786
  have htrace : WordTrace (prefixWord ++ tailWord_8061786) baseStart_8061786 baseEnd_8061786 := by
    simpa [prefixWord, tailWord_8061786, baseEnd_8061786] using wordTrace_append hprefix tailTrace_8061786
  have hstable : (prefixWord ++ tailWord_8061786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061786).length < 2 ^ (prefixWord ++ tailWord_8061786).sum := by decide
  have hdescent : baseEnd_8061786 < baseStart_8061786 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061796 : List Nat := [2, 3, 1, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_8061796 : Nat := 118140960795 + 8061796 * 2 ^ 59
def prefixEnd_8061796 : Nat := 4983230072969 + 3 ^ 40 * 8061796 * 2
def baseEnd_8061796 : Nat := 4139576286494045419774481

theorem tailTrace_8061796 : CollatzResearch.WordTrace tailWord_8061796 prefixEnd_8061796 4139576286494045419774481 := by
  unfold tailWord_8061796
  simp only [CollatzResearch.WordTrace]
  refine ⟨147018928150748705992834621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196025237534331607990446161 147018928150748705992834621)
  ·
    refine ⟨55132098056530764747312983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147018928150748705992834621 55132098056530764747312983)
    ·
      refine ⟨82698147084796147120969475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55132098056530764747312983 82698147084796147120969475)
      ·
        refine ⟨124047220627194220681454213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82698147084796147120969475 124047220627194220681454213)
        ·
          refine ⟨23258853867598916377772665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124047220627194220681454213 23258853867598916377772665)
          ·
            refine ⟨17444140400699187283329499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23258853867598916377772665 17444140400699187283329499)
            ·
              refine ⟨26166210601048780924994249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17444140400699187283329499 26166210601048780924994249)
              ·
                refine ⟨19624657950786585693745687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26166210601048780924994249 19624657950786585693745687)
                ·
                  refine ⟨29436986926179878540618531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19624657950786585693745687 29436986926179878540618531)
                  ·
                    refine ⟨44155480389269817810927797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29436986926179878540618531 44155480389269817810927797)
                    ·
                      refine ⟨4139576286494045419774481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44155480389269817810927797 4139576286494045419774481)
                      ·
                        rfl

theorem cell23_8061796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_8061796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061796 prefixEnd_8061796 := by exact prefixLift 8061796
  have htrace : WordTrace (prefixWord ++ tailWord_8061796) baseStart_8061796 baseEnd_8061796 := by
    simpa [prefixWord, tailWord_8061796, baseEnd_8061796] using wordTrace_append hprefix tailTrace_8061796
  have hstable : (prefixWord ++ tailWord_8061796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061796).length < 2 ^ (prefixWord ++ tailWord_8061796).sum := by decide
  have hdescent : baseEnd_8061796 < baseStart_8061796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061813 : List Nat := [1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 3]
def baseStart_8061813 : Nat := 118140960795 + 8061813 * 2 ^ 59
def prefixEnd_8061813 : Nat := 4983230072969 + 3 ^ 40 * 8061813 * 2
def baseEnd_8061813 : Nat := 4139585015665171853261903

theorem tailTrace_8061813 : CollatzResearch.WordTrace tailWord_8061813 prefixEnd_8061813 4139585015665171853261903 := by
  unfold tailWord_8061813
  simp only [CollatzResearch.WordTrace]
  refine ⟨294038476342435823889038093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196025650894957215926025395 294038476342435823889038093)
  ·
    refine ⟨110264428628413433958389285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294038476342435823889038093 110264428628413433958389285)
    ·
      refine ⟨20674580367827518867197991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110264428628413433958389285 20674580367827518867197991)
      ·
        refine ⟨31011870551741278300796987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20674580367827518867197991 31011870551741278300796987)
        ·
          refine ⟨46517805827611917451195481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31011870551741278300796987 46517805827611917451195481)
          ·
            refine ⟨34888354370708938088396611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46517805827611917451195481 34888354370708938088396611)
            ·
              refine ⟨52332531556063407132594917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34888354370708938088396611 52332531556063407132594917)
              ·
                refine ⟨9812349666761888837361547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52332531556063407132594917 9812349666761888837361547)
                ·
                  refine ⟨14718524500142833256042321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9812349666761888837361547 14718524500142833256042321)
                  ·
                    refine ⟨11038893375107124942031741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14718524500142833256042321 11038893375107124942031741)
                    ·
                      refine ⟨4139585015665171853261903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11038893375107124942031741 4139585015665171853261903)
                      ·
                        rfl

theorem cell23_8061813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_8061813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061813 prefixEnd_8061813 := by exact prefixLift 8061813
  have htrace : WordTrace (prefixWord ++ tailWord_8061813) baseStart_8061813 baseEnd_8061813 := by
    simpa [prefixWord, tailWord_8061813, baseEnd_8061813] using wordTrace_append hprefix tailTrace_8061813
  have hstable : (prefixWord ++ tailWord_8061813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061813).length < 2 ^ (prefixWord ++ tailWord_8061813).sum := by decide
  have hdescent : baseEnd_8061813 < baseStart_8061813 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061844 : List Nat := [2, 4, 2, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_8061844 : Nat := 118140960795 + 8061844 * 2 ^ 59
def prefixEnd_8061844 : Nat := 4983230072969 + 3 ^ 40 * 8061844 * 2
def baseEnd_8061844 : Nat := 4139600933565461231974261

theorem tailTrace_8061844 : CollatzResearch.WordTrace tailWord_8061844 prefixEnd_8061844 4139600933565461231974261 := by
  unfold tailWord_8061844
  simp only [CollatzResearch.WordTrace]
  refine ⟨147019803502661758091708293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196026404670215677455611057 147019803502661758091708293)
  ·
    refine ⟨27566213156749079642195305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147019803502661758091708293 27566213156749079642195305)
    ·
      refine ⟨20674659867561809731646479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27566213156749079642195305 20674659867561809731646479)
      ·
        refine ⟨31011989801342714597469719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20674659867561809731646479 31011989801342714597469719)
        ·
          refine ⟨46517984702014071896204579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31011989801342714597469719 46517984702014071896204579)
          ·
            refine ⟨69776977053021107844306869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46517984702014071896204579 69776977053021107844306869)
            ·
              refine ⟨6541591598720728860403769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69776977053021107844306869 6541591598720728860403769)
              ·
                refine ⟨4906193699040546645302827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6541591598720728860403769 4906193699040546645302827)
                ·
                  refine ⟨7359290548560819967954241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906193699040546645302827 7359290548560819967954241)
                  ·
                    refine ⟨5519467911420614975965681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7359290548560819967954241 5519467911420614975965681)
                    ·
                      refine ⟨4139600933565461231974261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519467911420614975965681 4139600933565461231974261)
                      ·
                        rfl

theorem cell23_8061844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_8061844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061844 prefixEnd_8061844 := by exact prefixLift 8061844
  have htrace : WordTrace (prefixWord ++ tailWord_8061844) baseStart_8061844 baseEnd_8061844 := by
    simpa [prefixWord, tailWord_8061844, baseEnd_8061844] using wordTrace_append hprefix tailTrace_8061844
  have hstable : (prefixWord ++ tailWord_8061844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061844).length < 2 ^ (prefixWord ++ tailWord_8061844).sum := by decide
  have hdescent : baseEnd_8061844 < baseStart_8061844 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061849 : List Nat := [1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 4]
def baseStart_8061849 : Nat := 118140960795 + 8061849 * 2 ^ 59
def prefixEnd_8061849 : Nat := 4983230072969 + 3 ^ 40 * 8061849 * 2
def baseEnd_8061849 : Nat := 4139603500968733712411737

theorem tailTrace_8061849 : CollatzResearch.WordTrace tailWord_8061849 prefixEnd_8061849 4139603500968733712411737 := by
  unfold tailWord_8061849
  simp only [CollatzResearch.WordTrace]
  refine ⟨294039789370305402037348601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196026526246870268024899067 294039789370305402037348601)
  ·
    refine ⟨220529842027729051528011451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294039789370305402037348601 220529842027729051528011451)
    ·
      refine ⟨330794763041593577292017177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220529842027729051528011451 330794763041593577292017177)
      ·
        refine ⟨248096072281195182969012883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330794763041593577292017177 248096072281195182969012883)
        ·
          refine ⟨372144108421792774453519325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248096072281195182969012883 372144108421792774453519325)
          ·
            refine ⟨139554040658172290420069747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372144108421792774453519325 139554040658172290420069747)
            ·
              refine ⟨209331060987258435630104621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139554040658172290420069747 209331060987258435630104621)
              ·
                refine ⟨78499147870221913361289233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209331060987258435630104621 78499147870221913361289233)
                ·
                  refine ⟨58874360902666435020966925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78499147870221913361289233 58874360902666435020966925)
                  ·
                    refine ⟨22077885338499913132862597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58874360902666435020966925 22077885338499913132862597)
                    ·
                      refine ⟨4139603500968733712411737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22077885338499913132862597 4139603500968733712411737)
                      ·
                        rfl

theorem cell23_8061849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_8061849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061849 prefixEnd_8061849 := by exact prefixLift 8061849
  have htrace : WordTrace (prefixWord ++ tailWord_8061849) baseStart_8061849 baseEnd_8061849 := by
    simpa [prefixWord, tailWord_8061849, baseEnd_8061849] using wordTrace_append hprefix tailTrace_8061849
  have hstable : (prefixWord ++ tailWord_8061849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061849).length < 2 ^ (prefixWord ++ tailWord_8061849).sum := by decide
  have hdescent : baseEnd_8061849 < baseStart_8061849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061853 : List Nat := [1, 4, 2, 1, 2, 1, 2, 2, 3, 3, 2]
def baseStart_8061853 : Nat := 118140960795 + 8061853 * 2 ^ 59
def prefixEnd_8061853 : Nat := 4983230072969 + 3 ^ 40 * 8061853 * 2
def baseEnd_8061853 : Nat := 4139605554891351696761719

theorem tailTrace_8061853 : CollatzResearch.WordTrace tailWord_8061853 prefixEnd_8061853 4139605554891351696761719 := by
  unfold tailWord_8061853
  simp only [CollatzResearch.WordTrace]
  refine ⟨294039935262290910720494213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196026623508193940480329475 294039935262290910720494213)
  ·
    refine ⟨55132487861679545760092665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294039935262290910720494213 55132487861679545760092665)
    ·
      refine ⟨41349365896259659320069499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55132487861679545760092665 41349365896259659320069499)
      ·
        refine ⟨62024048844389488980104249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41349365896259659320069499 62024048844389488980104249)
        ·
          refine ⟨46518036633292116735078187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62024048844389488980104249 46518036633292116735078187)
          ·
            refine ⟨69777054949938175102617281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46518036633292116735078187 69777054949938175102617281)
            ·
              refine ⟨52332791212453631326962961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69777054949938175102617281 52332791212453631326962961)
              ·
                refine ⟨39249593409340223495222221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52332791212453631326962961 39249593409340223495222221)
                ·
                  refine ⟨14718597528502583810708333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39249593409340223495222221 14718597528502583810708333)
                  ·
                    refine ⟨5519474073188468929015625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14718597528502583810708333 5519474073188468929015625)
                    ·
                      refine ⟨4139605554891351696761719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519474073188468929015625 4139605554891351696761719)
                      ·
                        rfl

theorem cell23_8061853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_8061853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061853 prefixEnd_8061853 := by exact prefixLift 8061853
  have htrace : WordTrace (prefixWord ++ tailWord_8061853) baseStart_8061853 baseEnd_8061853 := by
    simpa [prefixWord, tailWord_8061853, baseEnd_8061853] using wordTrace_append hprefix tailTrace_8061853
  have hstable : (prefixWord ++ tailWord_8061853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061853).length < 2 ^ (prefixWord ++ tailWord_8061853).sum := by decide
  have hdescent : baseEnd_8061853 < baseStart_8061853 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061859 : List Nat := [1, 1, 1, 4, 1, 2, 2, 3, 2, 6]
def baseStart_8061859 : Nat := 118140960795 + 8061859 * 2 ^ 59
def prefixEnd_8061859 : Nat := 4983230072969 + 3 ^ 40 * 8061859 * 2
def baseEnd_8061859 : Nat := 1379869545258426224428897

theorem tailTrace_8061859 : CollatzResearch.WordTrace tailWord_8061859 prefixEnd_8061859 1379869545258426224428897 := by
  unfold tailWord_8061859
  simp only [CollatzResearch.WordTrace]
  refine ⟨294040154100269173745212631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196026769400179449163475087 294040154100269173745212631)
  ·
    refine ⟨441060231150403760617818947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294040154100269173745212631 441060231150403760617818947)
    ·
      refine ⟨661590346725605640926728421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441060231150403760617818947 661590346725605640926728421)
      ·
        refine ⟨124048190011051057673761579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 661590346725605640926728421 124048190011051057673761579)
        ·
          refine ⟨186072285016576586510642369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124048190011051057673761579 186072285016576586510642369)
          ·
            refine ⟨139554213762432439882981777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186072285016576586510642369 139554213762432439882981777)
            ·
              refine ⟨104665660321824329912236333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139554213762432439882981777 104665660321824329912236333)
              ·
                refine ⟨39249622620684123717088625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104665660321824329912236333 39249622620684123717088625)
                ·
                  refine ⟨29437216965513092787816469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39249622620684123717088625 29437216965513092787816469)
                  ·
                    refine ⟨1379869545258426224428897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29437216965513092787816469 1379869545258426224428897)
                    ·
                      rfl

theorem cell23_8061859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 6].length) (baseStart_8061859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061859 prefixEnd_8061859 := by exact prefixLift 8061859
  have htrace : WordTrace (prefixWord ++ tailWord_8061859) baseStart_8061859 baseEnd_8061859 := by
    simpa [prefixWord, tailWord_8061859, baseEnd_8061859] using wordTrace_append hprefix tailTrace_8061859
  have hstable : (prefixWord ++ tailWord_8061859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061859).length < 2 ^ (prefixWord ++ tailWord_8061859).sum := by decide
  have hdescent : baseEnd_8061859 < baseStart_8061859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061886 : List Nat := [4, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_8061886 : Nat := 118140960795 + 8061886 * 2 ^ 59
def prefixEnd_8061886 : Nat := 4983230072969 + 3 ^ 40 * 8061886 * 2
def baseEnd_8061886 : Nat := 4139622499752950067649067

theorem tailTrace_8061886 : CollatzResearch.WordTrace tailWord_8061886 prefixEnd_8061886 4139622499752950067649067 := by
  unfold tailWord_8061886
  simp only [CollatzResearch.WordTrace]
  refine ⟨36755142358896419669555689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196027425914114238237630341 36755142358896419669555689)
  ·
    refine ⟨27566356769172314752166767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36755142358896419669555689 27566356769172314752166767)
    ·
      refine ⟨41349535153758472128250151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27566356769172314752166767 41349535153758472128250151)
      ·
        refine ⟨62024302730637708192375227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41349535153758472128250151 62024302730637708192375227)
        ·
          refine ⟨93036454095956562288562841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62024302730637708192375227 93036454095956562288562841)
          ·
            refine ⟨69777340571967421716422131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93036454095956562288562841 69777340571967421716422131)
            ·
              refine ⟨104666010857951132574633197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69777340571967421716422131 104666010857951132574633197)
              ·
                refine ⟨39249754071731674715487449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104666010857951132574633197 39249754071731674715487449)
                ·
                  refine ⟨29437315553798756036615587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39249754071731674715487449 29437315553798756036615587)
                  ·
                    refine ⟨44155973330698134054923381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29437315553798756036615587 44155973330698134054923381)
                    ·
                      refine ⟨4139622499752950067649067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44155973330698134054923381 4139622499752950067649067)
                      ·
                        rfl

theorem cell23_8061886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_8061886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061886 prefixEnd_8061886 := by exact prefixLift 8061886
  have htrace : WordTrace (prefixWord ++ tailWord_8061886) baseStart_8061886 baseEnd_8061886 := by
    simpa [prefixWord, tailWord_8061886, baseEnd_8061886] using wordTrace_append hprefix tailTrace_8061886
  have hstable : (prefixWord ++ tailWord_8061886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061886).length < 2 ^ (prefixWord ++ tailWord_8061886).sum := by decide
  have hdescent : baseEnd_8061886 < baseStart_8061886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061917 : List Nat := [1, 4, 3, 1, 2, 1, 2, 3, 2, 2, 2]
def baseStart_8061917 : Nat := 118140960795 + 8061917 * 2 ^ 59
def prefixEnd_8061917 : Nat := 4983230072969 + 3 ^ 40 * 8061917 * 2
def baseEnd_8061917 : Nat := 4139638417653239446361425

theorem tailTrace_8061917 : CollatzResearch.WordTrace tailWord_8061917 prefixEnd_8061917 4139638417653239446361425 := by
  unfold tailWord_8061917
  simp only [CollatzResearch.WordTrace]
  refine ⟨294042269534059049650824005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196028179689372699767216003 294042269534059049650824005)
  ·
    refine ⟨55132925537636071809529501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294042269534059049650824005 55132925537636071809529501)
    ·
      refine ⟨20674847076613526928573563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55132925537636071809529501 20674847076613526928573563)
      ·
        refine ⟨31012270614920290392860345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20674847076613526928573563 31012270614920290392860345)
        ·
          refine ⟨23259202961190217794645259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31012270614920290392860345 23259202961190217794645259)
          ·
            refine ⟨34888804441785326691967889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23259202961190217794645259 34888804441785326691967889)
            ·
              refine ⟨26166603331338995018975917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34888804441785326691967889 26166603331338995018975917)
              ·
                refine ⟨9812476249252123132115969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26166603331338995018975917 9812476249252123132115969)
                ·
                  refine ⟨7359357186939092349086977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9812476249252123132115969 7359357186939092349086977)
                  ·
                    refine ⟨5519517890204319261815233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7359357186939092349086977 5519517890204319261815233)
                    ·
                      refine ⟨4139638417653239446361425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519517890204319261815233 4139638417653239446361425)
                      ·
                        rfl

theorem cell23_8061917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 3, 2, 2, 2].length) (baseStart_8061917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061917 prefixEnd_8061917 := by exact prefixLift 8061917
  have htrace : WordTrace (prefixWord ++ tailWord_8061917) baseStart_8061917 baseEnd_8061917 := by
    simpa [prefixWord, tailWord_8061917, baseEnd_8061917] using wordTrace_append hprefix tailTrace_8061917
  have hstable : (prefixWord ++ tailWord_8061917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061917).length < 2 ^ (prefixWord ++ tailWord_8061917).sum := by decide
  have hdescent : baseEnd_8061917 < baseStart_8061917 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061929 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 5]
def baseStart_8061929 : Nat := 118140960795 + 8061929 * 2 ^ 59
def prefixEnd_8061929 : Nat := 4983230072969 + 3 ^ 40 * 8061929 * 2
def baseEnd_8061929 : Nat := 4139644579421093399411369

theorem tailTrace_8061929 : CollatzResearch.WordTrace tailWord_8061929 prefixEnd_8061929 4139644579421093399411369 := by
  unfold tailWord_8061929
  simp only [CollatzResearch.WordTrace]
  refine ⟨294042707210015575700260841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196028471473343717133507227 294042707210015575700260841)
  ·
    refine ⟨220532030407511681775195631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294042707210015575700260841 220532030407511681775195631)
    ·
      refine ⟨330798045611267522662793447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220532030407511681775195631 330798045611267522662793447)
      ·
        refine ⟨496197068416901283994190171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330798045611267522662793447 496197068416901283994190171)
        ·
          refine ⟨744295602625351925991285257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496197068416901283994190171 744295602625351925991285257)
          ·
            refine ⟨558221701969013944493463943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744295602625351925991285257 558221701969013944493463943)
            ·
              refine ⟨837332552953520916740195915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558221701969013944493463943 837332552953520916740195915)
              ·
                refine ⟨1255998829430281375110293873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837332552953520916740195915 1255998829430281375110293873)
                ·
                  refine ⟨941999122072711031332720405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1255998829430281375110293873 941999122072711031332720405)
                  ·
                    refine ⟨44156208847158329593721269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 941999122072711031332720405 44156208847158329593721269)
                    ·
                      refine ⟨4139644579421093399411369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44156208847158329593721269 4139644579421093399411369)
                      ·
                        rfl

theorem cell23_8061929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_8061929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061929 prefixEnd_8061929 := by exact prefixLift 8061929
  have htrace : WordTrace (prefixWord ++ tailWord_8061929) baseStart_8061929 baseEnd_8061929 := by
    simpa [prefixWord, tailWord_8061929, baseEnd_8061929] using wordTrace_append hprefix tailTrace_8061929
  have hstable : (prefixWord ++ tailWord_8061929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061929).length < 2 ^ (prefixWord ++ tailWord_8061929).sum := by decide
  have hdescent : baseEnd_8061929 < baseStart_8061929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8061983 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 3, 4]
def baseStart_8061983 : Nat := 118140960795 + 8061983 * 2 ^ 59
def prefixEnd_8061983 : Nat := 4983230072969 + 3 ^ 40 * 8061983 * 2
def baseEnd_8061983 : Nat := 1379890769125478729378707

theorem tailTrace_8061983 : CollatzResearch.WordTrace tailWord_8061983 prefixEnd_8061983 1379890769125478729378707 := by
  unfold tailWord_8061983
  simp only [CollatzResearch.WordTrace]
  refine ⟨294044676751819942922726603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196029784501213295281817735 294044676751819942922726603)
  ·
    refine ⟨441067015127729914384089905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294044676751819942922726603 441067015127729914384089905)
    ·
      refine ⟨330800261345797435788067429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441067015127729914384089905 330800261345797435788067429)
      ·
        refine ⟨62025049002337019210262643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330800261345797435788067429 62025049002337019210262643)
        ·
          refine ⟨93037573503505528815393965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62025049002337019210262643 93037573503505528815393965)
          ·
            refine ⟨34889090063814573305772737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93037573503505528815393965 34889090063814573305772737)
            ·
              refine ⟨26166817547860929979329553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34889090063814573305772737 26166817547860929979329553)
              ·
                refine ⟨19625113160895697484497165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26166817547860929979329553 19625113160895697484497165)
                ·
                  refine ⟨7359417435335886556686437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19625113160895697484497165 7359417435335886556686437)
                  ·
                    refine ⟨1379890769125478729378707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7359417435335886556686437 1379890769125478729378707)
                    ·
                      rfl

theorem cell23_8061983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 3, 4].length) (baseStart_8061983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8061983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8061983 prefixEnd_8061983 := by exact prefixLift 8061983
  have htrace : WordTrace (prefixWord ++ tailWord_8061983) baseStart_8061983 baseEnd_8061983 := by
    simpa [prefixWord, tailWord_8061983, baseEnd_8061983] using wordTrace_append hprefix tailTrace_8061983
  have hstable : (prefixWord ++ tailWord_8061983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8061983).length < 2 ^ (prefixWord ++ tailWord_8061983).sum := by decide
  have hdescent : baseEnd_8061983 < baseStart_8061983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8061983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062017 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 3, 4]
def baseStart_8062017 : Nat := 118140960795 + 8062017 * 2 ^ 59
def prefixEnd_8062017 : Nat := 4983230072969 + 3 ^ 40 * 8062017 * 2
def baseEnd_8062017 : Nat := 1379896588572896351703655

theorem tailTrace_8062017 : CollatzResearch.WordTrace tailWord_8062017 prefixEnd_8062017 1379896588572896351703655 := by
  unfold tailWord_8062017
  simp only [CollatzResearch.WordTrace]
  refine ⟨294045916833696766729464305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196030611222464511152976203 294045916833696766729464305)
  ·
    refine ⟨220534437625272575047098229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294045916833696766729464305 220534437625272575047098229)
    ·
      refine ⟨20675103527369303910665459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220534437625272575047098229 20675103527369303910665459)
      ·
        refine ⟨31012655291053955865998189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20675103527369303910665459 31012655291053955865998189)
        ·
          refine ⟨11629745734145233449749321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31012655291053955865998189 11629745734145233449749321)
          ·
            refine ⟨8722309300608925087311991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11629745734145233449749321 8722309300608925087311991)
            ·
              refine ⟨13083463950913387630967987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8722309300608925087311991 13083463950913387630967987)
              ·
                refine ⟨19625195926370081446451981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13083463950913387630967987 19625195926370081446451981)
                ·
                  refine ⟨7359448472388780542419493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19625195926370081446451981 7359448472388780542419493)
                  ·
                    refine ⟨1379896588572896351703655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7359448472388780542419493 1379896588572896351703655)
                    ·
                      rfl

theorem cell23_8062017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_8062017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062017 prefixEnd_8062017 := by exact prefixLift 8062017
  have htrace : WordTrace (prefixWord ++ tailWord_8062017) baseStart_8062017 baseEnd_8062017 := by
    simpa [prefixWord, tailWord_8062017, baseEnd_8062017] using wordTrace_append hprefix tailTrace_8062017
  have hstable : (prefixWord ++ tailWord_8062017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062017).length < 2 ^ (prefixWord ++ tailWord_8062017).sum := by decide
  have hdescent : baseEnd_8062017 < baseStart_8062017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062033 : List Nat := [1, 2, 2, 1, 3, 1, 2, 1, 3, 5, 2]
def baseStart_8062033 : Nat := 118140960795 + 8062033 * 2 ^ 59
def prefixEnd_8062033 : Nat := 4983230072969 + 3 ^ 40 * 8062033 * 2
def baseEnd_8062033 : Nat := 4139697981409160992510891

theorem tailTrace_8062033 : CollatzResearch.WordTrace tailWord_8062033 prefixEnd_8062033 4139697981409160992510891 := by
  unfold tailWord_8062033
  simp only [CollatzResearch.WordTrace]
  refine ⟨294046500401638801462046753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196031000267759200974697835 294046500401638801462046753)
  ·
    refine ⟨220534875301229101096535065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294046500401638801462046753 220534875301229101096535065)
    ·
      refine ⟨165401156475921825822401299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220534875301229101096535065 165401156475921825822401299)
      ·
        refine ⟨248101734713882738733601949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165401156475921825822401299 248101734713882738733601949)
        ·
          refine ⟨93038150517706027025100731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248101734713882738733601949 93038150517706027025100731)
          ·
            refine ⟨139557225776559040537651097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93038150517706027025100731 139557225776559040537651097)
            ·
              refine ⟨104667919332419280403238323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139557225776559040537651097 104667919332419280403238323)
              ·
                refine ⟨157001878998628920604857485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104667919332419280403238323 157001878998628920604857485)
                ·
                  refine ⟨58875704624485845226821557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157001878998628920604857485 58875704624485845226821557)
                  ·
                    refine ⟨5519597308545547990014521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58875704624485845226821557 5519597308545547990014521)
                    ·
                      refine ⟨4139697981409160992510891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519597308545547990014521 4139697981409160992510891)
                      ·
                        rfl

theorem cell23_8062033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 5, 2].length) (baseStart_8062033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062033 prefixEnd_8062033 := by exact prefixLift 8062033
  have htrace : WordTrace (prefixWord ++ tailWord_8062033) baseStart_8062033 baseEnd_8062033 := by
    simpa [prefixWord, tailWord_8062033, baseEnd_8062033] using wordTrace_append hprefix tailTrace_8062033
  have hstable : (prefixWord ++ tailWord_8062033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062033).length < 2 ^ (prefixWord ++ tailWord_8062033).sum := by decide
  have hdescent : baseEnd_8062033 < baseStart_8062033 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062060 : List Nat := [2, 2, 1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_8062060 : Nat := 118140960795 + 8062060 * 2 ^ 59
def prefixEnd_8062060 : Nat := 4983230072969 + 3 ^ 40 * 8062060 * 2
def baseEnd_8062060 : Nat := 1379903948462277462291089

theorem tailTrace_8062060 : CollatzResearch.WordTrace tailWord_8062060 prefixEnd_8062060 1379903948462277462291089 := by
  unfold tailWord_8062060
  simp only [CollatzResearch.WordTrace]
  refine ⟨147023742586270492536639817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196031656781693990048853089 147023742586270492536639817)
  ·
    refine ⟨110267806939702869402479863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147023742586270492536639817 110267806939702869402479863)
    ·
      refine ⟨165401710409554304103719795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110267806939702869402479863 165401710409554304103719795)
      ·
        refine ⟨248102565614331456155579693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165401710409554304103719795 248102565614331456155579693)
        ·
          refine ⟨93038462105374296058342385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248102565614331456155579693 93038462105374296058342385)
          ·
            refine ⟨69778846579030722043756789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93038462105374296058342385 69778846579030722043756789)
            ·
              refine ⟨6541766866784130191602199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69778846579030722043756789 6541766866784130191602199)
              ·
                refine ⟨9812650300176195287403299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6541766866784130191602199 9812650300176195287403299)
                ·
                  refine ⟨14718975450264292931104949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9812650300176195287403299 14718975450264292931104949)
                  ·
                    refine ⟨1379903948462277462291089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14718975450264292931104949 1379903948462277462291089)
                    ·
                      rfl

theorem cell23_8062060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_8062060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062060 prefixEnd_8062060 := by exact prefixLift 8062060
  have htrace : WordTrace (prefixWord ++ tailWord_8062060) baseStart_8062060 baseEnd_8062060 := by
    simpa [prefixWord, tailWord_8062060, baseEnd_8062060] using wordTrace_append hprefix tailTrace_8062060
  have hstable : (prefixWord ++ tailWord_8062060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062060).length < 2 ^ (prefixWord ++ tailWord_8062060).sum := by decide
  have hdescent : baseEnd_8062060 < baseStart_8062060 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062083 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 3]
def baseStart_8062083 : Nat := 118140960795 + 8062083 * 2 ^ 59
def prefixEnd_8062083 : Nat := 4983230072969 + 3 ^ 40 * 8062083 * 2
def baseEnd_8062083 : Nat := 4139723655441885796885661

theorem tailTrace_8062083 : CollatzResearch.WordTrace tailWord_8062083 prefixEnd_8062083 4139723655441885796885661 := by
  unfold tailWord_8062083
  simp only [CollatzResearch.WordTrace]
  refine ⟨294048324051457660001366903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196032216034305106667577935 294048324051457660001366903)
  ·
    refine ⟨441072486077186490002050355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294048324051457660001366903 441072486077186490002050355)
    ·
      refine ⟨661608729115779735003075533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441072486077186490002050355 661608729115779735003075533)
      ·
        refine ⟨248103273418417400626153325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661608729115779735003075533 248103273418417400626153325)
        ·
          refine ⟨93038727531906525234807497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248103273418417400626153325 93038727531906525234807497)
          ·
            refine ⟨69779045648929893926105623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93038727531906525234807497 69779045648929893926105623)
            ·
              refine ⟨104668568473394840889158435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69779045648929893926105623 104668568473394840889158435)
              ·
                refine ⟨157002852710092261333737653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104668568473394840889158435 157002852710092261333737653)
                ·
                  refine ⟨14719017441571149500037905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157002852710092261333737653 14719017441571149500037905)
                  ·
                    refine ⟨11039263081178362125028429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14719017441571149500037905 11039263081178362125028429)
                    ·
                      refine ⟨4139723655441885796885661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11039263081178362125028429 4139723655441885796885661)
                      ·
                        rfl

theorem cell23_8062083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_8062083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062083 prefixEnd_8062083 := by exact prefixLift 8062083
  have htrace : WordTrace (prefixWord ++ tailWord_8062083) baseStart_8062083 baseEnd_8062083 := by
    simpa [prefixWord, tailWord_8062083, baseEnd_8062083] using wordTrace_append hprefix tailTrace_8062083
  have hstable : (prefixWord ++ tailWord_8062083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062083).length < 2 ^ (prefixWord ++ tailWord_8062083).sum := by decide
  have hdescent : baseEnd_8062083 < baseStart_8062083 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062090 : List Nat := [3, 1, 2, 3, 1, 1, 1, 5, 2, 4]
def baseStart_8062090 : Nat := 118140960795 + 8062090 * 2 ^ 59
def prefixEnd_8062090 : Nat := 4983230072969 + 3 ^ 40 * 8062090 * 2
def baseEnd_8062090 : Nat := 1379909083268822423166043

theorem tailTrace_8062090 : CollatzResearch.WordTrace tailWord_8062090 prefixEnd_8062090 1379909083268822423166043 := by
  unfold tailWord_8062090
  simp only [CollatzResearch.WordTrace]
  refine ⟨73512144840608075049217931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196032386241621533464581149 73512144840608075049217931)
  ·
    refine ⟨110268217260912112573826897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73512144840608075049217931 110268217260912112573826897)
    ·
      refine ⟨82701162945684084430370173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110268217260912112573826897 82701162945684084430370173)
      ·
        refine ⟨31012936104631531661388815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82701162945684084430370173 31012936104631531661388815)
        ·
          refine ⟨46519404156947297492083223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31012936104631531661388815 46519404156947297492083223)
          ·
            refine ⟨69779106235420946238124835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46519404156947297492083223 69779106235420946238124835)
            ·
              refine ⟨104668659353131419357187253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69779106235420946238124835 104668659353131419357187253)
              ·
                refine ⟨9812686814356070564736305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104668659353131419357187253 9812686814356070564736305)
                ·
                  refine ⟨7359515110767052923552229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9812686814356070564736305 7359515110767052923552229)
                  ·
                    refine ⟨1379909083268822423166043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7359515110767052923552229 1379909083268822423166043)
                    ·
                      rfl

theorem cell23_8062090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_8062090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062090 prefixEnd_8062090 := by exact prefixLift 8062090
  have htrace : WordTrace (prefixWord ++ tailWord_8062090) baseStart_8062090 baseEnd_8062090 := by
    simpa [prefixWord, tailWord_8062090, baseEnd_8062090] using wordTrace_append hprefix tailTrace_8062090
  have hstable : (prefixWord ++ tailWord_8062090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062090).length < 2 ^ (prefixWord ++ tailWord_8062090).sum := by decide
  have hdescent : baseEnd_8062090 < baseStart_8062090 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062117 : List Nat := [1, 3, 1, 2, 1, 4, 4, 1, 1, 2, 3]
def baseStart_8062117 : Nat := 118140960795 + 8062117 * 2 ^ 59
def prefixEnd_8062117 : Nat := 4983230072969 + 3 ^ 40 * 8062117 * 2
def baseEnd_8062117 : Nat := 4139741113784138663860505

theorem tailTrace_8062117 : CollatzResearch.WordTrace tailWord_8062117 prefixEnd_8062117 4139741113784138663860505 := by
  unfold tailWord_8062117
  simp only [CollatzResearch.WordTrace]
  refine ⟨294049564133334483808104605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196033042755556322538736403 294049564133334483808104605)
  ·
    refine ⟨110268586550000431428039227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294049564133334483808104605 110268586550000431428039227)
    ·
      refine ⟨165402879825000647142058841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110268586550000431428039227 165402879825000647142058841)
      ·
        refine ⟨124052159868750485356544131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165402879825000647142058841 124052159868750485356544131)
        ·
          refine ⟨186078239803125728034816197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124052159868750485356544131 186078239803125728034816197)
          ·
            refine ⟨34889669963086074006528037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186078239803125728034816197 34889669963086074006528037)
            ·
              refine ⟨6541813118078638876224007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34889669963086074006528037 6541813118078638876224007)
              ·
                refine ⟨9812719677117958314336011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6541813118078638876224007 9812719677117958314336011)
                ·
                  refine ⟨14719079515676937471504017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9812719677117958314336011 14719079515676937471504017)
                  ·
                    refine ⟨11039309636757703103628013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14719079515676937471504017 11039309636757703103628013)
                    ·
                      refine ⟨4139741113784138663860505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11039309636757703103628013 4139741113784138663860505)
                      ·
                        rfl

theorem cell23_8062117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_8062117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062117 prefixEnd_8062117 := by exact prefixLift 8062117
  have htrace : WordTrace (prefixWord ++ tailWord_8062117) baseStart_8062117 baseEnd_8062117 := by
    simpa [prefixWord, tailWord_8062117, baseEnd_8062117] using wordTrace_append hprefix tailTrace_8062117
  have hstable : (prefixWord ++ tailWord_8062117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062117).length < 2 ^ (prefixWord ++ tailWord_8062117).sum := by decide
  have hdescent : baseEnd_8062117 < baseStart_8062117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062134 : List Nat := [5, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5]
def baseStart_8062134 : Nat := 118140960795 + 8062134 * 2 ^ 59
def prefixEnd_8062134 : Nat := 4983230072969 + 3 ^ 40 * 8062134 * 2
def baseEnd_8062134 : Nat := 4139749842955265097347927

theorem tailTrace_8062134 : CollatzResearch.WordTrace tailWord_8062134 prefixEnd_8062134 4139749842955265097347927 := by
  unfold tailWord_8062134
  simp only [CollatzResearch.WordTrace]
  refine ⟨18378136510892055981967091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196033456116181930474315637 18378136510892055981967091)
  ·
    refine ⟨27567204766338083972950637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18378136510892055981967091 27567204766338083972950637)
    ·
      refine ⟨10337701787376781489856489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27567204766338083972950637 10337701787376781489856489)
      ·
        refine ⟨7753276340532586117392367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10337701787376781489856489 7753276340532586117392367)
        ·
          refine ⟨11629914510798879176088551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7753276340532586117392367 11629914510798879176088551)
          ·
            refine ⟨17444871766198318764132827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11629914510798879176088551 17444871766198318764132827)
            ·
              refine ⟨26167307649297478146199241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17444871766198318764132827 26167307649297478146199241)
              ·
                refine ⟨19625480736973108609649431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26167307649297478146199241 19625480736973108609649431)
                ·
                  refine ⟨29438221105459662914474147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19625480736973108609649431 29438221105459662914474147)
                  ·
                    refine ⟨44157331658189494371711221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29438221105459662914474147 44157331658189494371711221)
                    ·
                      refine ⟨4139749842955265097347927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44157331658189494371711221 4139749842955265097347927)
                      ·
                        rfl

theorem cell23_8062134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_8062134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062134 prefixEnd_8062134 := by exact prefixLift 8062134
  have htrace : WordTrace (prefixWord ++ tailWord_8062134) baseStart_8062134 baseEnd_8062134 := by
    simpa [prefixWord, tailWord_8062134, baseEnd_8062134] using wordTrace_append hprefix tailTrace_8062134
  have hstable : (prefixWord ++ tailWord_8062134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062134).length < 2 ^ (prefixWord ++ tailWord_8062134).sum := by decide
  have hdescent : baseEnd_8062134 < baseStart_8062134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062170 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2]
def baseStart_8062170 : Nat := 118140960795 + 8062170 * 2 ^ 59
def prefixEnd_8062170 : Nat := 4983230072969 + 3 ^ 40 * 8062170 * 2
def baseEnd_8062170 : Nat := 4139768328258826956497761

theorem tailTrace_8062170 : CollatzResearch.WordTrace tailWord_8062170 prefixEnd_8062170 4139768328258826956497761 := by
  unfold tailWord_8062170
  simp only [CollatzResearch.WordTrace]
  refine ⟨73512874300535618464945991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196034331468094982573189309 73512874300535618464945991)
  ·
    refine ⟨110269311450803427697418987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73512874300535618464945991 110269311450803427697418987)
    ·
      refine ⟨165403967176205141546128481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110269311450803427697418987 165403967176205141546128481)
      ·
        refine ⟨124052975382153856159596361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165403967176205141546128481 124052975382153856159596361)
        ·
          refine ⟨93039731536615392119697271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124052975382153856159596361 93039731536615392119697271)
          ·
            refine ⟨139559597304923088179545907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93039731536615392119697271 139559597304923088179545907)
            ·
              refine ⟨209339395957384632269318861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139559597304923088179545907 209339395957384632269318861)
              ·
                refine ⟨78502273484019237100994573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209339395957384632269318861 78502273484019237100994573)
                ·
                  refine ⟨29438352556507213912872965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78502273484019237100994573 29438352556507213912872965)
                  ·
                    refine ⟨5519691104345102608663681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29438352556507213912872965 5519691104345102608663681)
                    ·
                      refine ⟨4139768328258826956497761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519691104345102608663681 4139768328258826956497761)
                      ·
                        rfl

theorem cell23_8062170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 2].length) (baseStart_8062170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062170 prefixEnd_8062170 := by exact prefixLift 8062170
  have htrace : WordTrace (prefixWord ++ tailWord_8062170) baseStart_8062170 baseEnd_8062170 := by
    simpa [prefixWord, tailWord_8062170, baseEnd_8062170] using wordTrace_append hprefix tailTrace_8062170
  have hstable : (prefixWord ++ tailWord_8062170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062170).length < 2 ^ (prefixWord ++ tailWord_8062170).sum := by decide
  have hdescent : baseEnd_8062170 < baseStart_8062170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062187 : List Nat := [1, 1, 1, 1, 2, 6, 2, 1, 4, 2, 2]
def baseStart_8062187 : Nat := 118140960795 + 8062187 * 2 ^ 59
def prefixEnd_8062187 : Nat := 4983230072969 + 3 ^ 40 * 8062187 * 2
def baseEnd_8062187 : Nat := 4139777057429953389985183

theorem tailTrace_8062187 : CollatzResearch.WordTrace tailWord_8062187 prefixEnd_8062187 4139777057429953389985183 := by
  unfold tailWord_8062187
  simp only [CollatzResearch.WordTrace]
  refine ⟨294052117243080885763152815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196034744828720590508768543 294052117243080885763152815)
  ·
    refine ⟨441078175864621328644729223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294052117243080885763152815 441078175864621328644729223)
    ·
      refine ⟨661617263796931992967093835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441078175864621328644729223 661617263796931992967093835)
      ·
        refine ⟨992425895695397989450640753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661617263796931992967093835 992425895695397989450640753)
        ·
          refine ⟨744319421771548492087980565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 992425895695397989450640753 744319421771548492087980565)
          ·
            refine ⟨34889972895541335566624089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 744319421771548492087980565 34889972895541335566624089)
            ·
              refine ⟨26167479671656001674968067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34889972895541335566624089 26167479671656001674968067)
              ·
                refine ⟨39251219507484002512452101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26167479671656001674968067 39251219507484002512452101)
                ·
                  refine ⟨7359603657653250471084769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39251219507484002512452101 7359603657653250471084769)
                  ·
                    refine ⟨5519702743239937853313577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7359603657653250471084769 5519702743239937853313577)
                    ·
                      refine ⟨4139777057429953389985183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519702743239937853313577 4139777057429953389985183)
                      ·
                        rfl

theorem cell23_8062187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 2, 1, 4, 2, 2].length) (baseStart_8062187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062187 prefixEnd_8062187 := by exact prefixLift 8062187
  have htrace : WordTrace (prefixWord ++ tailWord_8062187) baseStart_8062187 baseEnd_8062187 := by
    simpa [prefixWord, tailWord_8062187, baseEnd_8062187] using wordTrace_append hprefix tailTrace_8062187
  have hstable : (prefixWord ++ tailWord_8062187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062187).length < 2 ^ (prefixWord ++ tailWord_8062187).sum := by decide
  have hdescent : baseEnd_8062187 < baseStart_8062187 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062278 : List Nat := [6, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_8062278 : Nat := 118140960795 + 8062278 * 2 ^ 59
def prefixEnd_8062278 : Nat := 4983230072969 + 3 ^ 40 * 8062278 * 2
def baseEnd_8062278 : Nat := 459980420463279170438585

theorem tailTrace_8062278 : CollatzResearch.WordTrace tailWord_8062278 prefixEnd_8062278 459980420463279170438585 := by
  unfold tailWord_8062278
  simp only [CollatzResearch.WordTrace]
  refine ⟨9189232383929725259522359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196036957523834138869810325 9189232383929725259522359)
  ·
    refine ⟨13783848575894587889283539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9189232383929725259522359 13783848575894587889283539)
    ·
      refine ⟨20675772863841881833925309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13783848575894587889283539 20675772863841881833925309)
      ·
        refine ⟨7753414823940705687721991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20675772863841881833925309 7753414823940705687721991)
        ·
          refine ⟨11630122235911058531582987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7753414823940705687721991 11630122235911058531582987)
          ·
            refine ⟨17445183353866587797374481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11630122235911058531582987 17445183353866587797374481)
            ·
              refine ⟨13083887515399940848030861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17445183353866587797374481 13083887515399940848030861)
              ·
                refine ⟨4906457818274977818011573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13083887515399940848030861 4906457818274977818011573)
                ·
                  refine ⟨459980420463279170438585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4906457818274977818011573 459980420463279170438585)
                  ·
                    rfl

theorem cell23_8062278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_8062278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062278 prefixEnd_8062278 := by exact prefixLift 8062278
  have htrace : WordTrace (prefixWord ++ tailWord_8062278) baseStart_8062278 baseEnd_8062278 := by
    simpa [prefixWord, tailWord_8062278, baseEnd_8062278] using wordTrace_append hprefix tailTrace_8062278
  have hstable : (prefixWord ++ tailWord_8062278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062278).length < 2 ^ (prefixWord ++ tailWord_8062278).sum := by decide
  have hdescent : baseEnd_8062278 < baseStart_8062278 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062304 : List Nat := [2, 1, 1, 3, 4, 1, 2, 4, 1, 4]
def baseStart_8062304 : Nat := 118140960795 + 8062304 * 2 ^ 59
def prefixEnd_8062304 : Nat := 4983230072969 + 3 ^ 40 * 8062304 * 2
def baseEnd_8062304 : Nat := 1379945711555509810740715

theorem tailTrace_8062304 : CollatzResearch.WordTrace tailWord_8062304 prefixEnd_8062304 1379945711555509810740715 := by
  unfold tailWord_8062304
  simp only [CollatzResearch.WordTrace]
  refine ⟨147028192291828507372580983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196037589722438009830107977 147028192291828507372580983)
  ·
    refine ⟨220542288437742761058871475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147028192291828507372580983 220542288437742761058871475)
    ·
      refine ⟨330813432656614141588307213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220542288437742761058871475 330813432656614141588307213)
      ·
        refine ⟨124055037246230303095615205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330813432656614141588307213 124055037246230303095615205)
        ·
          refine ⟨23260319483668181830427851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124055037246230303095615205 23260319483668181830427851)
          ·
            refine ⟨34890479225502272745641777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23260319483668181830427851 34890479225502272745641777)
            ·
              refine ⟨26167859419126704559231333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34890479225502272745641777 26167859419126704559231333)
              ·
                refine ⟨4906473641086257104855875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26167859419126704559231333 4906473641086257104855875)
                ·
                  refine ⟨7359710461629385657283813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906473641086257104855875 7359710461629385657283813)
                  ·
                    refine ⟨1379945711555509810740715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7359710461629385657283813 1379945711555509810740715)
                    ·
                      rfl

theorem cell23_8062304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 4, 1, 4].length) (baseStart_8062304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062304 prefixEnd_8062304 := by exact prefixLift 8062304
  have htrace : WordTrace (prefixWord ++ tailWord_8062304) baseStart_8062304 baseEnd_8062304 := by
    simpa [prefixWord, tailWord_8062304, baseEnd_8062304] using wordTrace_append hprefix tailTrace_8062304
  have hstable : (prefixWord ++ tailWord_8062304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062304).length < 2 ^ (prefixWord ++ tailWord_8062304).sum := by decide
  have hdescent : baseEnd_8062304 < baseStart_8062304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062313 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 2, 9]
def baseStart_8062313 : Nat := 118140960795 + 8062313 * 2 ^ 59
def prefixEnd_8062313 : Nat := 4983230072969 + 3 ^ 40 * 8062313 * 2
def baseEnd_8062313 : Nat := 1379947251997473299003201

theorem tailTrace_8062313 : CollatzResearch.WordTrace tailWord_8062313 prefixEnd_8062313 1379947251997473299003201 := by
  unfold tailWord_8062313
  simp only [CollatzResearch.WordTrace]
  refine ⟨294056712840624409282239593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196037808560416272854826395 294056712840624409282239593)
  ·
    refine ⟨220542534630468306961679695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294056712840624409282239593 220542534630468306961679695)
    ·
      refine ⟨330813801945702460442519543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220542534630468306961679695 330813801945702460442519543)
      ·
        refine ⟨496220702918553690663779315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330813801945702460442519543 496220702918553690663779315)
        ·
          refine ⟨744331054377830535995668973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496220702918553690663779315 744331054377830535995668973)
          ·
            refine ⟨279124145391686450998375865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744331054377830535995668973 279124145391686450998375865)
            ·
              refine ⟨209343109043764838248781899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279124145391686450998375865 209343109043764838248781899)
              ·
                refine ⟨314014663565647257373172849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209343109043764838248781899 314014663565647257373172849)
                ·
                  refine ⟨235510997674235443029879637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314014663565647257373172849 235510997674235443029879637)
                  ·
                    refine ⟨1379947251997473299003201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 235510997674235443029879637 1379947251997473299003201)
                    ·
                      rfl

theorem cell23_8062313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 9].length) (baseStart_8062313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062313 prefixEnd_8062313 := by exact prefixLift 8062313
  have htrace : WordTrace (prefixWord ++ tailWord_8062313) baseStart_8062313 baseEnd_8062313 := by
    simpa [prefixWord, tailWord_8062313, baseEnd_8062313] using wordTrace_append hprefix tailTrace_8062313
  have hstable : (prefixWord ++ tailWord_8062313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062313).length < 2 ^ (prefixWord ++ tailWord_8062313).sum := by decide
  have hdescent : baseEnd_8062313 < baseStart_8062313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062327 : List Nat := [1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 3]
def baseStart_8062327 : Nat := 118140960795 + 8062327 * 2 ^ 59
def prefixEnd_8062327 : Nat := 4983230072969 + 3 ^ 40 * 8062327 * 2
def baseEnd_8062327 : Nat := 4139848944721582842234539

theorem tailTrace_8062327 : CollatzResearch.WordTrace tailWord_8062327 prefixEnd_8062327 4139848944721582842234539 := by
  unfold tailWord_8062327
  simp only [CollatzResearch.WordTrace]
  refine ⟨294057223462573689673249235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196038148975049126448832823 294057223462573689673249235)
  ·
    refine ⟨441085835193860534509873853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294057223462573689673249235 441085835193860534509873853)
    ·
      refine ⟨165407188197697700441202695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441085835193860534509873853 165407188197697700441202695)
      ·
        refine ⟨248110782296546550661804043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165407188197697700441202695 248110782296546550661804043)
        ·
          refine ⟨372166173444819825992706065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248110782296546550661804043 372166173444819825992706065)
          ·
            refine ⟨279124630083614869494529549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372166173444819825992706065 279124630083614869494529549)
            ·
              refine ⟨104671736281355576060448581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279124630083614869494529549 104671736281355576060448581)
              ·
                refine ⟨19625950552754170511334109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104671736281355576060448581 19625950552754170511334109)
                ·
                  refine ⟨7359731457282813941750291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19625950552754170511334109 7359731457282813941750291)
                  ·
                    refine ⟨11039597185924220912625437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7359731457282813941750291 11039597185924220912625437)
                    ·
                      refine ⟨4139848944721582842234539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11039597185924220912625437 4139848944721582842234539)
                      ·
                        rfl

theorem cell23_8062327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_8062327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062327 prefixEnd_8062327 := by exact prefixLift 8062327
  have htrace : WordTrace (prefixWord ++ tailWord_8062327) baseStart_8062327 baseEnd_8062327 := by
    simpa [prefixWord, tailWord_8062327, baseEnd_8062327] using wordTrace_append hprefix tailTrace_8062327
  have hstable : (prefixWord ++ tailWord_8062327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062327).length < 2 ^ (prefixWord ++ tailWord_8062327).sum := by decide
  have hdescent : baseEnd_8062327 < baseStart_8062327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062338 : List Nat := [3, 4, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_8062338 : Nat := 118140960795 + 8062338 * 2 ^ 59
def prefixEnd_8062338 : Nat := 4983230072969 + 3 ^ 40 * 8062338 * 2
def baseEnd_8062338 : Nat := 1379951531002927433065663

theorem tailTrace_8062338 : CollatzResearch.WordTrace tailWord_8062338 prefixEnd_8062338 1379951531002927433065663 := by
  unfold tailWord_8062338
  simp only [CollatzResearch.WordTrace]
  refine ⟨73514406166383459637974917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196038416443689225701266445 73514406166383459637974917)
  ·
    refine ⟨13783951156196898682120297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73514406166383459637974917 13783951156196898682120297)
    ·
      refine ⟨10337963367147674011590223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13783951156196898682120297 10337963367147674011590223)
      ·
        refine ⟨15506945050721511017385335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10337963367147674011590223 15506945050721511017385335)
        ·
          refine ⟨23260417576082266526078003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15506945050721511017385335 23260417576082266526078003)
          ·
            refine ⟨34890626364123399789117005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23260417576082266526078003 34890626364123399789117005)
            ·
              refine ⟨13083984886546274920918877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34890626364123399789117005 13083984886546274920918877)
              ·
                refine ⟨4906494332454853095344579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13083984886546274920918877 4906494332454853095344579)
                ·
                  refine ⟨7359741498682279643016869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906494332454853095344579 7359741498682279643016869)
                  ·
                    refine ⟨1379951531002927433065663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7359741498682279643016869 1379951531002927433065663)
                    ·
                      rfl

theorem cell23_8062338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_8062338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062338 prefixEnd_8062338 := by exact prefixLift 8062338
  have htrace : WordTrace (prefixWord ++ tailWord_8062338) baseStart_8062338 baseEnd_8062338 := by
    simpa [prefixWord, tailWord_8062338, baseEnd_8062338] using wordTrace_append hprefix tailTrace_8062338
  have hstable : (prefixWord ++ tailWord_8062338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062338).length < 2 ^ (prefixWord ++ tailWord_8062338).sum := by decide
  have hdescent : baseEnd_8062338 < baseStart_8062338 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062380 : List Nat := [2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_8062380 : Nat := 118140960795 + 8062380 * 2 ^ 59
def prefixEnd_8062380 : Nat := 4983230072969 + 3 ^ 40 * 8062380 * 2
def baseEnd_8062380 : Nat := 4139876159196271134871795

theorem tailTrace_8062380 : CollatzResearch.WordTrace tailWord_8062380 prefixEnd_8062380 4139876159196271134871795 := by
  unfold tailWord_8062380
  simp only [CollatzResearch.WordTrace]
  refine ⟨147029578265690839862464297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196039437687587786483285729 147029578265690839862464297)
  ·
    refine ⟨110272183699268129896848223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147029578265690839862464297 110272183699268129896848223)
    ·
      refine ⟨165408275548902194845272335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110272183699268129896848223 165408275548902194845272335)
      ·
        refine ⟨248112413323353292267908503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165408275548902194845272335 248112413323353292267908503)
        ·
          refine ⟨372168619985029938401862755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248112413323353292267908503 372168619985029938401862755)
          ·
            refine ⟨558252929977544907602794133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372168619985029938401862755 558252929977544907602794133)
            ·
              refine ⟨26168106092697417543880975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 558252929977544907602794133 26168106092697417543880975)
              ·
                refine ⟨39252159139046126315821463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26168106092697417543880975 39252159139046126315821463)
                ·
                  refine ⟨58878238708569189473732195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39252159139046126315821463 58878238708569189473732195)
                  ·
                    refine ⟨88317358062853784210598293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58878238708569189473732195 88317358062853784210598293)
                    ·
                      refine ⟨4139876159196271134871795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88317358062853784210598293 4139876159196271134871795)
                      ·
                        rfl

theorem cell23_8062380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_8062380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062380 prefixEnd_8062380 := by exact prefixLift 8062380
  have htrace : WordTrace (prefixWord ++ tailWord_8062380) baseStart_8062380 baseEnd_8062380 := by
    simpa [prefixWord, tailWord_8062380, baseEnd_8062380] using wordTrace_append hprefix tailTrace_8062380
  have hstable : (prefixWord ++ tailWord_8062380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062380).length < 2 ^ (prefixWord ++ tailWord_8062380).sum := by decide
  have hdescent : baseEnd_8062380 < baseStart_8062380 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062381 : List Nat := [1, 5, 2, 2, 1, 3, 1, 2, 1, 5]
def baseStart_8062381 : Nat := 118140960795 + 8062381 * 2 ^ 59
def prefixEnd_8062381 : Nat := 4983230072969 + 3 ^ 40 * 8062381 * 2
def baseEnd_8062381 : Nat := 1379958890892308543653097

theorem tailTrace_8062381 : CollatzResearch.WordTrace tailWord_8062381 prefixEnd_8062381 1379958890892308543653097 := by
  unfold tailWord_8062381
  simp only [CollatzResearch.WordTrace]
  refine ⟨294059193004378056895714997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196039462002918704597143331 294059193004378056895714997)
  ·
    refine ⟨27568049344160442833973281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 294059193004378056895714997 27568049344160442833973281)
    ·
      refine ⟨20676037008120332125479961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27568049344160442833973281 20676037008120332125479961)
      ·
        refine ⟨15507027756090249094109971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20676037008120332125479961 15507027756090249094109971)
        ·
          refine ⟨23260541634135373641164957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15507027756090249094109971 23260541634135373641164957)
          ·
            refine ⟨8722703112800765115436859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23260541634135373641164957 8722703112800765115436859)
            ·
              refine ⟨13084054669201147673155289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8722703112800765115436859 13084054669201147673155289)
              ·
                refine ⟨9813041001900860754866467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13084054669201147673155289 9813041001900860754866467)
                ·
                  refine ⟨14719561502851291132299701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9813041001900860754866467 14719561502851291132299701)
                  ·
                    refine ⟨1379958890892308543653097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14719561502851291132299701 1379958890892308543653097)
                    ·
                      rfl

theorem cell23_8062381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_8062381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062381 prefixEnd_8062381 := by exact prefixLift 8062381
  have htrace : WordTrace (prefixWord ++ tailWord_8062381) baseStart_8062381 baseEnd_8062381 := by
    simpa [prefixWord, tailWord_8062381, baseEnd_8062381] using wordTrace_append hprefix tailTrace_8062381
  have hstable : (prefixWord ++ tailWord_8062381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062381).length < 2 ^ (prefixWord ++ tailWord_8062381).sum := by decide
  have hdescent : baseEnd_8062381 < baseStart_8062381 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062397 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_8062397 : Nat := 118140960795 + 8062397 * 2 ^ 59
def prefixEnd_8062397 : Nat := 4983230072969 + 3 ^ 40 * 8062397 * 2
def baseEnd_8062397 : Nat := 4139884888367397568359217

theorem tailTrace_8062397 : CollatzResearch.WordTrace tailWord_8062397 prefixEnd_8062397 4139884888367397568359217 := by
  unfold tailWord_8062397
  simp only [CollatzResearch.WordTrace]
  refine ⟨294059776572320091628297445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196039851048213394418864963 294059776572320091628297445)
  ·
    refine ⟨55136208107310017180305771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294059776572320091628297445 55136208107310017180305771)
    ·
      refine ⟨82704312160965025770458657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55136208107310017180305771 82704312160965025770458657)
      ·
        refine ⟨62028234120723769327843993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82704312160965025770458657 62028234120723769327843993)
        ·
          refine ⟨46521175590542826995882995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62028234120723769327843993 46521175590542826995882995)
          ·
            refine ⟨69781763385814240493824493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46521175590542826995882995 69781763385814240493824493)
            ·
              refine ⟨26168161269680340185184185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69781763385814240493824493 26168161269680340185184185)
              ·
                refine ⟨19626120952260255138888139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26168161269680340185184185 19626120952260255138888139)
                ·
                  refine ⟨29439181428390382708332209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19626120952260255138888139 29439181428390382708332209)
                  ·
                    refine ⟨22079386071292787031249157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29439181428390382708332209 22079386071292787031249157)
                    ·
                      refine ⟨4139884888367397568359217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22079386071292787031249157 4139884888367397568359217)
                      ·
                        rfl

theorem cell23_8062397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_8062397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062397 prefixEnd_8062397 := by exact prefixLift 8062397
  have htrace : WordTrace (prefixWord ++ tailWord_8062397) baseStart_8062397 baseEnd_8062397 := by
    simpa [prefixWord, tailWord_8062397, baseEnd_8062397] using wordTrace_append hprefix tailTrace_8062397
  have hstable : (prefixWord ++ tailWord_8062397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062397).length < 2 ^ (prefixWord ++ tailWord_8062397).sum := by decide
  have hdescent : baseEnd_8062397 < baseStart_8062397 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062404 : List Nat := [2, 3, 3, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_8062404 : Nat := 118140960795 + 8062404 * 2 ^ 59
def prefixEnd_8062404 : Nat := 4983230072969 + 3 ^ 40 * 8062404 * 2
def baseEnd_8062404 : Nat := 4139888482731979040971685

theorem tailTrace_8062404 : CollatzResearch.WordTrace tailWord_8062404 prefixEnd_8062404 4139888482731979040971685 := by
  unfold tailWord_8062404
  simp only [CollatzResearch.WordTrace]
  refine ⟨147030015941647365911901133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196040021255529821215868177 147030015941647365911901133)
  ·
    refine ⟨55136255978117762216962925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147030015941647365911901133 55136255978117762216962925)
    ·
      refine ⟨20676095991794160831361097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55136255978117762216962925 20676095991794160831361097)
      ·
        refine ⟨15507071993845620623520823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20676095991794160831361097 15507071993845620623520823)
        ·
          refine ⟨23260607990768430935281235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15507071993845620623520823 23260607990768430935281235)
          ·
            refine ⟨34890911986152646402921853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23260607990768430935281235 34890911986152646402921853)
            ·
              refine ⟨13084091994807242401095695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34890911986152646402921853 13084091994807242401095695)
              ·
                refine ⟨19626137992210863601643543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13084091994807242401095695 19626137992210863601643543)
                ·
                  refine ⟨29439206988316295402465315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19626137992210863601643543 29439206988316295402465315)
                  ·
                    refine ⟨44158810482474443103697973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29439206988316295402465315 44158810482474443103697973)
                    ·
                      refine ⟨4139888482731979040971685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44158810482474443103697973 4139888482731979040971685)
                      ·
                        rfl

theorem cell23_8062404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_8062404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062404 prefixEnd_8062404 := by exact prefixLift 8062404
  have htrace : WordTrace (prefixWord ++ tailWord_8062404) baseStart_8062404 baseEnd_8062404 := by
    simpa [prefixWord, tailWord_8062404, baseEnd_8062404] using wordTrace_append hprefix tailTrace_8062404
  have hstable : (prefixWord ++ tailWord_8062404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062404).length < 2 ^ (prefixWord ++ tailWord_8062404).sum := by decide
  have hdescent : baseEnd_8062404 < baseStart_8062404 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062461 : List Nat := [1, 4, 1, 1, 1, 5, 1, 3, 1, 3, 2]
def baseStart_8062461 : Nat := 118140960795 + 8062461 * 2 ^ 59
def prefixEnd_8062461 : Nat := 4983230072969 + 3 ^ 40 * 8062461 * 2
def baseEnd_8062461 : Nat := 4139917751129285317958923

theorem tailTrace_8062461 : CollatzResearch.WordTrace tailWord_8062461 prefixEnd_8062461 4139917751129285317958923 := by
  unfold tailWord_8062461
  simp only [CollatzResearch.WordTrace]
  refine ⟨294062110844088230558627237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196041407229392153705751491 294062110844088230558627237)
  ·
    refine ⟨55136645783266543229742607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294062110844088230558627237 55136645783266543229742607)
    ·
      refine ⟨82704968674899814844613911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55136645783266543229742607 82704968674899814844613911)
      ·
        refine ⟨124057453012349722266920867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82704968674899814844613911 124057453012349722266920867)
        ·
          refine ⟨186086179518524583400381301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124057453012349722266920867 186086179518524583400381301)
          ·
            refine ⟨17445579329861679693785747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186086179518524583400381301 17445579329861679693785747)
            ·
              refine ⟨26168368994792519540678621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17445579329861679693785747 26168368994792519540678621)
              ·
                refine ⟨9813138373047194827754483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26168368994792519540678621 9813138373047194827754483)
                ·
                  refine ⟨14719707559570792241631725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9813138373047194827754483 14719707559570792241631725)
                  ·
                    refine ⟨5519890334839047090611897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14719707559570792241631725 5519890334839047090611897)
                    ·
                      refine ⟨4139917751129285317958923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5519890334839047090611897 4139917751129285317958923)
                      ·
                        rfl

theorem cell23_8062461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 3, 1, 3, 2].length) (baseStart_8062461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062461 prefixEnd_8062461 := by exact prefixLift 8062461
  have htrace : WordTrace (prefixWord ++ tailWord_8062461) baseStart_8062461 baseEnd_8062461 := by
    simpa [prefixWord, tailWord_8062461, baseEnd_8062461] using wordTrace_append hprefix tailTrace_8062461
  have hstable : (prefixWord ++ tailWord_8062461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062461).length < 2 ^ (prefixWord ++ tailWord_8062461).sum := by decide
  have hdescent : baseEnd_8062461 < baseStart_8062461 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062497 : List Nat := [1, 2, 3, 2, 2, 2, 2, 2, 7]
def baseStart_8062497 : Nat := 118140960795 + 8062497 * 2 ^ 59
def prefixEnd_8062497 : Nat := 4983230072969 + 3 ^ 40 * 8062497 * 2
def baseEnd_8062497 : Nat := 459992915159205241900973

theorem tailTrace_8062497 : CollatzResearch.WordTrace tailWord_8062497 prefixEnd_8062497 459992915159205241900973 := by
  unfold tailWord_8062497
  simp only [CollatzResearch.WordTrace]
  refine ⟨294063423871957808706937745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196042282581305205804625163 294063423871957808706937745)
  ·
    refine ⟨220547567903968356530203309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294063423871957808706937745 220547567903968356530203309)
    ·
      refine ⟨82705337963988133698826241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220547567903968356530203309 82705337963988133698826241)
      ·
        refine ⟨62029003472991100274119681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82705337963988133698826241 62029003472991100274119681)
        ·
          refine ⟨46521752604743325205589761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62029003472991100274119681 46521752604743325205589761)
          ·
            refine ⟨34891314453557493904192321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46521752604743325205589761 34891314453557493904192321)
            ·
              refine ⟨26168485840168120428144241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34891314453557493904192321 26168485840168120428144241)
              ·
                refine ⟨19626364380126090321108181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26168485840168120428144241 19626364380126090321108181)
                ·
                  refine ⟨459992915159205241900973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19626364380126090321108181 459992915159205241900973)
                  ·
                    rfl

theorem cell23_8062497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 2, 7].length) (baseStart_8062497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062497 prefixEnd_8062497 := by exact prefixLift 8062497
  have htrace : WordTrace (prefixWord ++ tailWord_8062497) baseStart_8062497 baseEnd_8062497 := by
    simpa [prefixWord, tailWord_8062497, baseEnd_8062497] using wordTrace_append hprefix tailTrace_8062497
  have hstable : (prefixWord ++ tailWord_8062497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062497).length < 2 ^ (prefixWord ++ tailWord_8062497).sum := by decide
  have hdescent : baseEnd_8062497 < baseStart_8062497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062527 : List Nat := [1, 1, 2, 2, 3, 3, 1, 1, 4, 5]
def baseStart_8062527 : Nat := 118140960795 + 8062527 * 2 ^ 59
def prefixEnd_8062527 : Nat := 4983230072969 + 3 ^ 40 * 8062527 * 2
def baseEnd_8062527 : Nat := 1379983880284160686577873

theorem tailTrace_8062527 : CollatzResearch.WordTrace tailWord_8062527 prefixEnd_8062527 1379983880284160686577873 := by
  unfold tailWord_8062527
  simp only [CollatzResearch.WordTrace]
  refine ⟨294064518061849123830529835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196043012041232749220353223 294064518061849123830529835)
  ·
    refine ⟨441096777092773685745794753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294064518061849123830529835 441096777092773685745794753)
    ·
      refine ⟨330822582819580264309346065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441096777092773685745794753 330822582819580264309346065)
      ·
        refine ⟨248116937114685198232009549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330822582819580264309346065 248116937114685198232009549)
        ·
          refine ⟨93043851418006949337003581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248116937114685198232009549 93043851418006949337003581)
          ·
            refine ⟨34891444281752606001376343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93043851418006949337003581 34891444281752606001376343)
            ·
              refine ⟨52337166422628909002064515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34891444281752606001376343 52337166422628909002064515)
              ·
                refine ⟨78505749633943363503096773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52337166422628909002064515 78505749633943363503096773)
                ·
                  refine ⟨14719828056364380656830645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78505749633943363503096773 14719828056364380656830645)
                  ·
                    refine ⟨1379983880284160686577873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14719828056364380656830645 1379983880284160686577873)
                    ·
                      rfl

theorem cell23_8062527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_8062527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062527 prefixEnd_8062527 := by exact prefixLift 8062527
  have htrace : WordTrace (prefixWord ++ tailWord_8062527) baseStart_8062527 baseEnd_8062527 := by
    simpa [prefixWord, tailWord_8062527, baseEnd_8062527] using wordTrace_append hprefix tailTrace_8062527
  have hstable : (prefixWord ++ tailWord_8062527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062527).length < 2 ^ (prefixWord ++ tailWord_8062527).sum := by decide
  have hdescent : baseEnd_8062527 < baseStart_8062527 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062564 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_8062564 : Nat := 118140960795 + 8062564 * 2 ^ 59
def prefixEnd_8062564 : Nat := 4983230072969 + 3 ^ 40 * 8062564 * 2
def baseEnd_8062564 : Nat := 4139970639636698414970949

theorem tailTrace_8062564 : CollatzResearch.WordTrace tailWord_8062564 prefixEnd_8062564 4139970639636698414970949 := by
  unfold tailWord_8062564
  simp only [CollatzResearch.WordTrace]
  refine ⟨147032933781357539574813373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196043911708476719433084497 147032933781357539574813373)
  ·
    refine ⟨55137350168009077340555015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147032933781357539574813373 55137350168009077340555015)
    ·
      refine ⟨82706025252013616010832523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55137350168009077340555015 82706025252013616010832523)
      ·
        refine ⟨124059037878020424016248785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82706025252013616010832523 124059037878020424016248785)
        ·
          refine ⟨93044278408515318012186589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124059037878020424016248785 93044278408515318012186589)
          ·
            refine ⟨34891604403193244254569971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93044278408515318012186589 34891604403193244254569971)
            ·
              refine ⟨52337406604789866381854957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34891604403193244254569971 52337406604789866381854957)
              ·
                refine ⟨19626527476796199893195609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52337406604789866381854957 19626527476796199893195609)
                ·
                  refine ⟨14719895607597149919896707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19626527476796199893195609 14719895607597149919896707)
                  ·
                    refine ⟨22079843411395724879845061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14719895607597149919896707 22079843411395724879845061)
                    ·
                      refine ⟨4139970639636698414970949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22079843411395724879845061 4139970639636698414970949)
                      ·
                        rfl

theorem cell23_8062564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_8062564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062564 prefixEnd_8062564 := by exact prefixLift 8062564
  have htrace : WordTrace (prefixWord ++ tailWord_8062564) baseStart_8062564 baseEnd_8062564 := by
    simpa [prefixWord, tailWord_8062564, baseEnd_8062564] using wordTrace_append hprefix tailTrace_8062564
  have hstable : (prefixWord ++ tailWord_8062564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062564).length < 2 ^ (prefixWord ++ tailWord_8062564).sum := by decide
  have hdescent : baseEnd_8062564 < baseStart_8062564 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062581 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 4]
def baseStart_8062581 : Nat := 118140960795 + 8062581 * 2 ^ 59
def prefixEnd_8062581 : Nat := 4983230072969 + 3 ^ 40 * 8062581 * 2
def baseEnd_8062581 : Nat := 4139979368807824848458371

theorem tailTrace_8062581 : CollatzResearch.WordTrace tailWord_8062581 prefixEnd_8062581 4139979368807824848458371 := by
  unfold tailWord_8062581
  simp only [CollatzResearch.WordTrace]
  refine ⟨294066487603653491052995597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196044325069102327368663731 294066487603653491052995597)
  ·
    refine ⟨110274932851370059144873349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294066487603653491052995597 110274932851370059144873349)
    ·
      refine ⟨20676549909631886089663753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110274932851370059144873349 20676549909631886089663753)
      ·
        refine ⟨15507412432223914567247815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20676549909631886089663753 15507412432223914567247815)
        ·
          refine ⟨23261118648335871850871723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15507412432223914567247815 23261118648335871850871723)
          ·
            refine ⟨34891677972503807776307585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23261118648335871850871723 34891677972503807776307585)
            ·
              refine ⟨26168758479377855832230689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34891677972503807776307585 26168758479377855832230689)
              ·
                refine ⟨19626568859533391874173017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26168758479377855832230689 19626568859533391874173017)
                ·
                  refine ⟨14719926644650043905629763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19626568859533391874173017 14719926644650043905629763)
                  ·
                    refine ⟨22079889966975065858444645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14719926644650043905629763 22079889966975065858444645)
                    ·
                      refine ⟨4139979368807824848458371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22079889966975065858444645 4139979368807824848458371)
                      ·
                        rfl

theorem cell23_8062581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_8062581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062581 prefixEnd_8062581 := by exact prefixLift 8062581
  have htrace : WordTrace (prefixWord ++ tailWord_8062581) baseStart_8062581 baseEnd_8062581 := by
    simpa [prefixWord, tailWord_8062581, baseEnd_8062581] using wordTrace_append hprefix tailTrace_8062581
  have hstable : (prefixWord ++ tailWord_8062581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062581).length < 2 ^ (prefixWord ++ tailWord_8062581).sum := by decide
  have hdescent : baseEnd_8062581 < baseStart_8062581 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062668 : List Nat := [2, 2, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_8062668 : Nat := 118140960795 + 8062668 * 2 ^ 59
def prefixEnd_8062668 : Nat := 4983230072969 + 3 ^ 40 * 8062668 * 2
def baseEnd_8062668 : Nat := 1380008013874922002690157

theorem tailTrace_8062668 : CollatzResearch.WordTrace tailWord_8062668 prefixEnd_8062668 1380008013874922002690157 := by
  unfold tailWord_8062668
  simp only [CollatzResearch.WordTrace]
  refine ⟨147034830377169152455706329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196046440502892203274275105 147034830377169152455706329)
  ·
    refine ⟨110276122782876864341779747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147034830377169152455706329 110276122782876864341779747)
    ·
      refine ⟨165414184174315296512669621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110276122782876864341779747 165414184174315296512669621)
      ·
        refine ⟨15507579766342059048062777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165414184174315296512669621 15507579766342059048062777)
        ·
          refine ⟨11630684824756544286047083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15507579766342059048062777 11630684824756544286047083)
          ·
            refine ⟨17446027237134816429070625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11630684824756544286047083 17446027237134816429070625)
            ·
              refine ⟨13084520427851112321802969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17446027237134816429070625 13084520427851112321802969)
              ·
                refine ⟨9813390320888334241352227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13084520427851112321802969 9813390320888334241352227)
                ·
                  refine ⟨14720085481332501362028341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9813390320888334241352227 14720085481332501362028341)
                  ·
                    refine ⟨1380008013874922002690157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14720085481332501362028341 1380008013874922002690157)
                    ·
                      rfl

theorem cell23_8062668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_8062668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062668 prefixEnd_8062668 := by exact prefixLift 8062668
  have htrace : WordTrace (prefixWord ++ tailWord_8062668) baseStart_8062668 baseEnd_8062668 := by
    simpa [prefixWord, tailWord_8062668, baseEnd_8062668] using wordTrace_append hprefix tailTrace_8062668
  have hstable : (prefixWord ++ tailWord_8062668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062668).length < 2 ^ (prefixWord ++ tailWord_8062668).sum := by decide
  have hdescent : baseEnd_8062668 < baseStart_8062668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062704 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 3]
def baseStart_8062704 : Nat := 118140960795 + 8062704 * 2 ^ 59
def prefixEnd_8062704 : Nat := 4983230072969 + 3 ^ 40 * 8062704 * 2
def baseEnd_8062704 : Nat := 4140042526928327867220305

theorem tailTrace_8062704 : CollatzResearch.WordTrace tailWord_8062704 prefixEnd_8062704 4140042526928327867220305 := by
  unfold tailWord_8062704
  simp only [CollatzResearch.WordTrace]
  refine ⟨147035486891103941529861583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196047315854805255373148777 147035486891103941529861583)
  ·
    refine ⟨220553230336655912294792375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147035486891103941529861583 220553230336655912294792375)
    ·
      refine ⟨330829845504983868442188563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220553230336655912294792375 330829845504983868442188563)
      ·
        refine ⟨496244768257475802663282845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330829845504983868442188563 496244768257475802663282845)
        ·
          refine ⟨186091788096553425998731067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496244768257475802663282845 186091788096553425998731067)
          ·
            refine ⟨279137682144830138998096601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186091788096553425998731067 279137682144830138998096601)
            ·
              refine ⟨209353261608622604248572451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279137682144830138998096601 209353261608622604248572451)
              ·
                refine ⟨314029892412933906372858677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209353261608622604248572451 314029892412933906372858677)
                ·
                  refine ⟨29440302413712553722455501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314029892412933906372858677 29440302413712553722455501)
                  ·
                    refine ⟨11040113405142207645920813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29440302413712553722455501 11040113405142207645920813)
                    ·
                      refine ⟨4140042526928327867220305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11040113405142207645920813 4140042526928327867220305)
                      ·
                        rfl

theorem cell23_8062704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 3].length) (baseStart_8062704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062704 prefixEnd_8062704 := by exact prefixLift 8062704
  have htrace : WordTrace (prefixWord ++ tailWord_8062704) baseStart_8062704 baseEnd_8062704 := by
    simpa [prefixWord, tailWord_8062704, baseEnd_8062704] using wordTrace_append hprefix tailTrace_8062704
  have hstable : (prefixWord ++ tailWord_8062704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062704).length < 2 ^ (prefixWord ++ tailWord_8062704).sum := by decide
  have hdescent : baseEnd_8062704 < baseStart_8062704 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062705 : List Nat := [1, 2, 2, 2, 2, 5, 1, 1, 3, 2, 2]
def baseStart_8062705 : Nat := 118140960795 + 8062705 * 2 ^ 59
def prefixEnd_8062705 : Nat := 4983230072969 + 3 ^ 40 * 8062705 * 2
def baseEnd_8062705 : Nat := 4140043040408982363307801

theorem tailTrace_8062705 : CollatzResearch.WordTrace tailWord_8062705 prefixEnd_8062705 4140043040408982363307801 := by
  unfold tailWord_8062705
  simp only [CollatzResearch.WordTrace]
  refine ⟨294071010255204260230509569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196047340170136173487006379 294071010255204260230509569)
  ·
    refine ⟨220553257691403195172882177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294071010255204260230509569 220553257691403195172882177)
    ·
      refine ⟨165414943268552396379661633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220553257691403195172882177 165414943268552396379661633)
      ·
        refine ⟨124061207451414297284746225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165414943268552396379661633 124061207451414297284746225)
        ·
          refine ⟨93045905588560722963559669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124061207451414297284746225 93045905588560722963559669)
          ·
            refine ⟨8723053648927567777833719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93045905588560722963559669 8723053648927567777833719)
            ·
              refine ⟨13084580473391351666750579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8723053648927567777833719 13084580473391351666750579)
              ·
                refine ⟨19626870710087027500125869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13084580473391351666750579 19626870710087027500125869)
                ·
                  refine ⟨7360076516282635312547201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19626870710087027500125869 7360076516282635312547201)
                  ·
                    refine ⟨5520057387211976484410401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7360076516282635312547201 5520057387211976484410401)
                    ·
                      refine ⟨4140043040408982363307801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520057387211976484410401 4140043040408982363307801)
                      ·
                        rfl

theorem cell23_8062705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_8062705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062705 prefixEnd_8062705 := by exact prefixLift 8062705
  have htrace : WordTrace (prefixWord ++ tailWord_8062705) baseStart_8062705 baseEnd_8062705 := by
    simpa [prefixWord, tailWord_8062705, baseEnd_8062705] using wordTrace_append hprefix tailTrace_8062705
  have hstable : (prefixWord ++ tailWord_8062705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062705).length < 2 ^ (prefixWord ++ tailWord_8062705).sum := by decide
  have hdescent : baseEnd_8062705 < baseStart_8062705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062734 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5]
def baseStart_8062734 : Nat := 118140960795 + 8062734 * 2 ^ 59
def prefixEnd_8062734 : Nat := 4983230072969 + 3 ^ 40 * 8062734 * 2
def baseEnd_8062734 : Nat := 4140057931347962749845167

theorem tailTrace_8062734 : CollatzResearch.WordTrace tailWord_8062734 prefixEnd_8062734 4140057931347962749845167 := by
  unfold tailWord_8062734
  simp only [CollatzResearch.WordTrace]
  refine ⟨36759008496512399772914407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196048045314732798788876837 36759008496512399772914407)
  ·
    refine ⟨55138512744768599659371611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36759008496512399772914407 55138512744768599659371611)
    ·
      refine ⟨82707769117152899489057417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55138512744768599659371611 82707769117152899489057417)
      ·
        refine ⟨62030826837864674616793063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82707769117152899489057417 62030826837864674616793063)
        ·
          refine ⟨93046240256797011925189595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62030826837864674616793063 93046240256797011925189595)
          ·
            refine ⟨139569360385195517887784393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93046240256797011925189595 139569360385195517887784393)
            ·
              refine ⟨104677020288896638415838295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139569360385195517887784393 104677020288896638415838295)
              ·
                refine ⟨157015530433344957623757443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104677020288896638415838295 157015530433344957623757443)
                ·
                  refine ⟨235523295650017436435636165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157015530433344957623757443 235523295650017436435636165)
                  ·
                    refine ⟨44160617934378269331681781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235523295650017436435636165 44160617934378269331681781)
                    ·
                      refine ⟨4140057931347962749845167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44160617934378269331681781 4140057931347962749845167)
                      ·
                        rfl

theorem cell23_8062734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_8062734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062734 prefixEnd_8062734 := by exact prefixLift 8062734
  have htrace : WordTrace (prefixWord ++ tailWord_8062734) baseStart_8062734 baseEnd_8062734 := by
    simpa [prefixWord, tailWord_8062734, baseEnd_8062734] using wordTrace_append hprefix tailTrace_8062734
  have hstable : (prefixWord ++ tailWord_8062734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062734).length < 2 ^ (prefixWord ++ tailWord_8062734).sum := by decide
  have hdescent : baseEnd_8062734 < baseStart_8062734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062738 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_8062738 : Nat := 118140960795 + 8062738 * 2 ^ 59
def prefixEnd_8062738 : Nat := 4983230072969 + 3 ^ 40 * 8062738 * 2
def baseEnd_8062738 : Nat := 4140059985270580734195149

theorem tailTrace_8062738 : CollatzResearch.WordTrace tailWord_8062738 prefixEnd_8062738 4140059985270580734195149 := by
  unfold tailWord_8062738
  simp only [CollatzResearch.WordTrace]
  refine ⟨73518053466021176716615217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196048142576056471244307245 73518053466021176716615217)
  ·
    refine ⟨55138540099515882537461413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73518053466021176716615217 55138540099515882537461413)
    ·
      refine ⟨10338476268659227975774015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55138540099515882537461413 10338476268659227975774015)
      ·
        refine ⟨15507714402988841963661023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10338476268659227975774015 15507714402988841963661023)
        ·
          refine ⟨23261571604483262945491535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15507714402988841963661023 23261571604483262945491535)
          ·
            refine ⟨34892357406724894418237303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23261571604483262945491535 34892357406724894418237303)
            ·
              refine ⟨52338536110087341627355955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34892357406724894418237303 52338536110087341627355955)
              ·
                refine ⟨78507804165131012441033933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52338536110087341627355955 78507804165131012441033933)
                ·
                  refine ⟨29440426561924129665387725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78507804165131012441033933 29440426561924129665387725)
                  ·
                    refine ⟨11040159960721548624520397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29440426561924129665387725 11040159960721548624520397)
                    ·
                      refine ⟨4140059985270580734195149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11040159960721548624520397 4140059985270580734195149)
                      ·
                        rfl

theorem cell23_8062738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_8062738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062738 prefixEnd_8062738 := by exact prefixLift 8062738
  have htrace : WordTrace (prefixWord ++ tailWord_8062738) baseStart_8062738 baseEnd_8062738 := by
    simpa [prefixWord, tailWord_8062738, baseEnd_8062738] using wordTrace_append hprefix tailTrace_8062738
  have hstable : (prefixWord ++ tailWord_8062738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062738).length < 2 ^ (prefixWord ++ tailWord_8062738).sum := by decide
  have hdescent : baseEnd_8062738 < baseStart_8062738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062771 : List Nat := [1, 1, 1, 2, 7, 1, 1, 1, 2, 6]
def baseStart_8062771 : Nat := 118140960795 + 8062771 * 2 ^ 59
def prefixEnd_8062771 : Nat := 4983230072969 + 3 ^ 40 * 8062771 * 2
def baseEnd_8062771 : Nat := 1380025643377393035027499

theorem tailTrace_8062771 : CollatzResearch.WordTrace tailWord_8062771 prefixEnd_8062771 1380025643377393035027499 := by
  unfold tailWord_8062771
  simp only [CollatzResearch.WordTrace]
  refine ⟨294073417472965153502412167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196048944981976769001608111 294073417472965153502412167)
  ·
    refine ⟨441110126209447730253618251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294073417472965153502412167 441110126209447730253618251)
    ·
      refine ⟨661665189314171595380427377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441110126209447730253618251 661665189314171595380427377)
      ·
        refine ⟨496248891985628696535320533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661665189314171595380427377 496248891985628696535320533)
        ·
          refine ⟨11630833405913172575046575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 496248891985628696535320533 11630833405913172575046575)
          ·
            refine ⟨17446250108869758862569863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11630833405913172575046575 17446250108869758862569863)
            ·
              refine ⟨26169375163304638293854795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17446250108869758862569863 26169375163304638293854795)
              ·
                refine ⟨39254062744956957440782193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26169375163304638293854795 39254062744956957440782193)
                ·
                  refine ⟨29440547058717718080586645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39254062744956957440782193 29440547058717718080586645)
                  ·
                    refine ⟨1380025643377393035027499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29440547058717718080586645 1380025643377393035027499)
                    ·
                      rfl

theorem cell23_8062771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 6].length) (baseStart_8062771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062771 prefixEnd_8062771 := by exact prefixLift 8062771
  have htrace : WordTrace (prefixWord ++ tailWord_8062771) baseStart_8062771 baseEnd_8062771 := by
    simpa [prefixWord, tailWord_8062771, baseEnd_8062771] using wordTrace_append hprefix tailTrace_8062771
  have hstable : (prefixWord ++ tailWord_8062771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062771).length < 2 ^ (prefixWord ++ tailWord_8062771).sum := by decide
  have hdescent : baseEnd_8062771 < baseStart_8062771 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062778 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2]
def baseStart_8062778 : Nat := 118140960795 + 8062778 * 2 ^ 59
def prefixEnd_8062778 : Nat := 4983230072969 + 3 ^ 40 * 8062778 * 2
def baseEnd_8062778 : Nat := 4140080524496760577694965

theorem tailTrace_8062778 : CollatzResearch.WordTrace tailWord_8062778 prefixEnd_8062778 4140080524496760577694965 := by
  unfold tailWord_8062778
  simp only [CollatzResearch.WordTrace]
  refine ⟨73518418195984948424479247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196049115189293195798611325 73518418195984948424479247)
  ·
    refine ⟨110277627293977422636718871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73518418195984948424479247 110277627293977422636718871)
    ·
      refine ⟨165416440940966133955078307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110277627293977422636718871 165416440940966133955078307)
      ·
        refine ⟨248124661411449200932617461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165416440940966133955078307 248124661411449200932617461)
        ·
          refine ⟨23261687007323362587432887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 248124661411449200932617461 23261687007323362587432887)
          ·
            refine ⟨34892530510985043881149331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23261687007323362587432887 34892530510985043881149331)
            ·
              refine ⟨52338795766477565821723997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34892530510985043881149331 52338795766477565821723997)
              ·
                refine ⟨19627048412429087183146499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52338795766477565821723997 19627048412429087183146499)
                ·
                  refine ⟨29440572618643630774719749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19627048412429087183146499 29440572618643630774719749)
                  ·
                    refine ⟨5520107365995680770259953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29440572618643630774719749 5520107365995680770259953)
                    ·
                      refine ⟨4140080524496760577694965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520107365995680770259953 4140080524496760577694965)
                      ·
                        rfl

theorem cell23_8062778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 1, 4, 2].length) (baseStart_8062778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062778 prefixEnd_8062778 := by exact prefixLift 8062778
  have htrace : WordTrace (prefixWord ++ tailWord_8062778) baseStart_8062778 baseEnd_8062778 := by
    simpa [prefixWord, tailWord_8062778, baseEnd_8062778] using wordTrace_append hprefix tailTrace_8062778
  have hstable : (prefixWord ++ tailWord_8062778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062778).length < 2 ^ (prefixWord ++ tailWord_8062778).sum := by decide
  have hdescent : baseEnd_8062778 < baseStart_8062778 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062812 : List Nat := [2, 2, 4, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_8062812 : Nat := 118140960795 + 8062812 * 2 ^ 59
def prefixEnd_8062812 : Nat := 4983230072969 + 3 ^ 40 * 8062812 * 2
def baseEnd_8062812 : Nat := 4140097982839013444669809

theorem tailTrace_8062812 : CollatzResearch.WordTrace tailWord_8062812 prefixEnd_8062812 4140097982839013444669809 := by
  unfold tailWord_8062812
  simp only [CollatzResearch.WordTrace]
  refine ⟨147037456432908308752327345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196049941910544411669769793 147037456432908308752327345)
  ·
    refine ⟨110278092324681231564245509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147037456432908308752327345 110278092324681231564245509)
    ·
      refine ⟨20677142310877730918296033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110278092324681231564245509 20677142310877730918296033)
      ·
        refine ⟨15507856733158298188722025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20677142310877730918296033 15507856733158298188722025)
        ·
          refine ⟨11630892549868723641541519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15507856733158298188722025 11630892549868723641541519)
          ·
            refine ⟨17446338824803085462312279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11630892549868723641541519 17446338824803085462312279)
            ·
              refine ⟨26169508237204628193468419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17446338824803085462312279 26169508237204628193468419)
              ·
                refine ⟨39254262355806942290202629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26169508237204628193468419 39254262355806942290202629)
                ·
                  refine ⟨7360174191713801679412993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39254262355806942290202629 7360174191713801679412993)
                  ·
                    refine ⟨5520130643785351259559745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7360174191713801679412993 5520130643785351259559745)
                    ·
                      refine ⟨4140097982839013444669809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520130643785351259559745 4140097982839013444669809)
                      ·
                        rfl

theorem cell23_8062812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_8062812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062812 prefixEnd_8062812 := by exact prefixLift 8062812
  have htrace : WordTrace (prefixWord ++ tailWord_8062812) baseStart_8062812 baseEnd_8062812 := by
    simpa [prefixWord, tailWord_8062812, baseEnd_8062812] using wordTrace_append hprefix tailTrace_8062812
  have hstable : (prefixWord ++ tailWord_8062812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062812).length < 2 ^ (prefixWord ++ tailWord_8062812).sum := by decide
  have hdescent : baseEnd_8062812 < baseStart_8062812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062818 : List Nat := [3, 3, 2, 1, 2, 2, 2, 1, 7]
def baseStart_8062818 : Nat := 118140960795 + 8062818 * 2 ^ 59
def prefixEnd_8062818 : Nat := 4983230072969 + 3 ^ 40 * 8062818 * 2
def baseEnd_8062818 : Nat := 460011229302548935688309

theorem tailTrace_8062818 : CollatzResearch.WordTrace tailWord_8062818 prefixEnd_8062818 460011229302548935688309 := by
  unfold tailWord_8062818
  simp only [CollatzResearch.WordTrace]
  refine ⟨73518782925948720132343277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196050087802529920352915405 73518782925948720132343277)
  ·
    refine ⟨27569543597230770049628729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73518782925948720132343277 27569543597230770049628729)
    ·
      refine ⟨20677157697923077537221547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27569543597230770049628729 20677157697923077537221547)
      ·
        refine ⟨31015736546884616305832321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20677157697923077537221547 31015736546884616305832321)
        ·
          refine ⟨23261802410163462229374241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31015736546884616305832321 23261802410163462229374241)
          ·
            refine ⟨17446351807622596672030681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23261802410163462229374241 17446351807622596672030681)
            ·
              refine ⟨13084763855716947504023011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17446351807622596672030681 13084763855716947504023011)
              ·
                refine ⟨19627145783575421256034517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13084763855716947504023011 19627145783575421256034517)
                ·
                  refine ⟨460011229302548935688309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19627145783575421256034517 460011229302548935688309)
                  ·
                    rfl

theorem cell23_8062818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 2, 1, 7].length) (baseStart_8062818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062818 prefixEnd_8062818 := by exact prefixLift 8062818
  have htrace : WordTrace (prefixWord ++ tailWord_8062818) baseStart_8062818 baseEnd_8062818 := by
    simpa [prefixWord, tailWord_8062818, baseEnd_8062818] using wordTrace_append hprefix tailTrace_8062818
  have hstable : (prefixWord ++ tailWord_8062818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062818).length < 2 ^ (prefixWord ++ tailWord_8062818).sum := by decide
  have hdescent : baseEnd_8062818 < baseStart_8062818 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062851 : List Nat := [1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 4]
def baseStart_8062851 : Nat := 118140960795 + 8062851 * 2 ^ 59
def prefixEnd_8062851 : Nat := 4983230072969 + 3 ^ 40 * 8062851 * 2
def baseEnd_8062851 : Nat := 4140118008584538792082129

theorem tailTrace_8062851 : CollatzResearch.WordTrace tailWord_8062851 prefixEnd_8062851 4140118008584538792082129 := by
  unfold tailWord_8062851
  simp only [CollatzResearch.WordTrace]
  refine ⟨294076335312675327165324407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196050890208450218110216271 294076335312675327165324407)
  ·
    refine ⟨441114502969012990747986611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294076335312675327165324407 441114502969012990747986611)
    ·
      refine ⟨661671754453519486121979917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441114502969012990747986611 661671754453519486121979917)
      ·
        refine ⟨248126907920069807295742469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 661671754453519486121979917 248126907920069807295742469)
        ·
          refine ⟨46523795235013088867951713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248126907920069807295742469 46523795235013088867951713)
          ·
            refine ⟨34892846426259816650963785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46523795235013088867951713 34892846426259816650963785)
            ·
              refine ⟨26169634819694862488222839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34892846426259816650963785 26169634819694862488222839)
              ·
                refine ⟨39254452229542293732334259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26169634819694862488222839 39254452229542293732334259)
                ·
                  refine ⟨58881678344313440598501389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39254452229542293732334259 58881678344313440598501389)
                  ·
                    refine ⟨22080629379117540224438021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58881678344313440598501389 22080629379117540224438021)
                    ·
                      refine ⟨4140118008584538792082129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22080629379117540224438021 4140118008584538792082129)
                      ·
                        rfl

theorem cell23_8062851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_8062851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062851 prefixEnd_8062851 := by exact prefixLift 8062851
  have htrace : WordTrace (prefixWord ++ tailWord_8062851) baseStart_8062851 baseEnd_8062851 := by
    simpa [prefixWord, tailWord_8062851, baseEnd_8062851] using wordTrace_append hprefix tailTrace_8062851
  have hstable : (prefixWord ++ tailWord_8062851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062851).length < 2 ^ (prefixWord ++ tailWord_8062851).sum := by decide
  have hdescent : baseEnd_8062851 < baseStart_8062851 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062868 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_8062868 : Nat := 118140960795 + 8062868 * 2 ^ 59
def prefixEnd_8062868 : Nat := 4983230072969 + 3 ^ 40 * 8062868 * 2
def baseEnd_8062868 : Nat := 4140126737755665225569551

theorem tailTrace_8062868 : CollatzResearch.WordTrace tailWord_8062868 prefixEnd_8062868 4140126737755665225569551 := by
  unfold tailWord_8062868
  simp only [CollatzResearch.WordTrace]
  refine ⟨147038477676806869534346629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196051303569075826045795505 147038477676806869534346629)
  ·
    refine ⟨27569714564401288037689993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147038477676806869534346629 27569714564401288037689993)
    ·
      refine ⟨20677285923300966028267495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27569714564401288037689993 20677285923300966028267495)
      ·
        refine ⟨31015928884951449042401243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20677285923300966028267495 31015928884951449042401243)
        ·
          refine ⟨46523893327427173563601865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31015928884951449042401243 46523893327427173563601865)
          ·
            refine ⟨34892919995570380172701399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46523893327427173563601865 34892919995570380172701399)
            ·
              refine ⟨52339379993355570259052099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34892919995570380172701399 52339379993355570259052099)
              ·
                refine ⟨78509069990033355388578149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52339379993355570259052099 78509069990033355388578149)
                ·
                  refine ⟨14720450623131254135358403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78509069990033355388578149 14720450623131254135358403)
                  ·
                    refine ⟨22080675934696881203037605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14720450623131254135358403 22080675934696881203037605)
                    ·
                      refine ⟨4140126737755665225569551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22080675934696881203037605 4140126737755665225569551)
                      ·
                        rfl

theorem cell23_8062868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_8062868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062868 prefixEnd_8062868 := by exact prefixLift 8062868
  have htrace : WordTrace (prefixWord ++ tailWord_8062868) baseStart_8062868 baseEnd_8062868 := by
    simpa [prefixWord, tailWord_8062868, baseEnd_8062868] using wordTrace_append hprefix tailTrace_8062868
  have hstable : (prefixWord ++ tailWord_8062868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062868).length < 2 ^ (prefixWord ++ tailWord_8062868).sum := by decide
  have hdescent : baseEnd_8062868 < baseStart_8062868 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8062981 : List Nat := [1, 3, 1, 1, 2, 5, 10]
def baseStart_8062981 : Nat := 118140960795 + 8062981 * 2 ^ 59
def prefixEnd_8062981 : Nat := 4983230072969 + 3 ^ 40 * 8062981 * 2
def baseEnd_8062981 : Nat := 51113392111970657820451

theorem tailTrace_8062981 : CollatzResearch.WordTrace tailWord_8062981 prefixEnd_8062981 51113392111970657820451 := by
  unfold tailWord_8062981
  simp only [CollatzResearch.WordTrace]
  refine ⟨294081076802204359367556797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196054051201469572911704531 294081076802204359367556797)
  ·
    refine ⟨110280403800826634762833799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294081076802204359367556797 110280403800826634762833799)
    ·
      refine ⟨165420605701239952144250699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110280403800826634762833799 165420605701239952144250699)
      ·
        refine ⟨248130908551859928216376049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165420605701239952144250699 248130908551859928216376049)
        ·
          refine ⟨186098181413894946162282037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248130908551859928216376049 186098181413894946162282037)
          ·
            refine ⟨17446704507552651202713941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186098181413894946162282037 17446704507552651202713941)
            ·
              refine ⟨51113392111970657820451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 17446704507552651202713941 51113392111970657820451)
              ·
                rfl

theorem cell23_8062981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 10].length) (baseStart_8062981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8062981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8062981 prefixEnd_8062981 := by exact prefixLift 8062981
  have htrace : WordTrace (prefixWord ++ tailWord_8062981) baseStart_8062981 baseEnd_8062981 := by
    simpa [prefixWord, tailWord_8062981, baseEnd_8062981] using wordTrace_append hprefix tailTrace_8062981
  have hstable : (prefixWord ++ tailWord_8062981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8062981).length < 2 ^ (prefixWord ++ tailWord_8062981).sum := by decide
  have hdescent : baseEnd_8062981 < baseStart_8062981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8062981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063002 : List Nat := [3, 1, 1, 3, 1, 4, 3, 1, 2, 4]
def baseStart_8063002 : Nat := 118140960795 + 8063002 * 2 ^ 59
def prefixEnd_8063002 : Nat := 4983230072969 + 3 ^ 40 * 8063002 * 2
def baseEnd_8063002 : Nat := 1380065181387789233764645

theorem tailTrace_8063002 : CollatzResearch.WordTrace tailWord_8063002 prefixEnd_8063002 1380065181387789233764645 := by
  unfold tailWord_8063002
  simp only [CollatzResearch.WordTrace]
  refine ⟨73520460683782069988517815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196054561823418853302714173 73520460683782069988517815)
  ·
    refine ⟨110280691025673104982776723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73520460683782069988517815 110280691025673104982776723)
    ·
      refine ⟨165421036538509657474165085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110280691025673104982776723 165421036538509657474165085)
      ·
        refine ⟨62032888701941121552811907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165421036538509657474165085 62032888701941121552811907)
        ·
          refine ⟨93049333052911682329217861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62032888701941121552811907 93049333052911682329217861)
          ·
            refine ⟨17446749947420940436728349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93049333052911682329217861 17446749947420940436728349)
            ·
              refine ⟨6542531230282852663773131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17446749947420940436728349 6542531230282852663773131)
              ·
                refine ⟨9813796845424278995659697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6542531230282852663773131 9813796845424278995659697)
                ·
                  refine ⟨7360347634068209246744773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9813796845424278995659697 7360347634068209246744773)
                  ·
                    refine ⟨1380065181387789233764645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7360347634068209246744773 1380065181387789233764645)
                    ·
                      rfl

theorem cell23_8063002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 3, 1, 2, 4].length) (baseStart_8063002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063002 prefixEnd_8063002 := by exact prefixLift 8063002
  have htrace : WordTrace (prefixWord ++ tailWord_8063002) baseStart_8063002 baseEnd_8063002 := by
    simpa [prefixWord, tailWord_8063002, baseEnd_8063002] using wordTrace_append hprefix tailTrace_8063002
  have hstable : (prefixWord ++ tailWord_8063002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063002).length < 2 ^ (prefixWord ++ tailWord_8063002).sum := by decide
  have hdescent : baseEnd_8063002 < baseStart_8063002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063005 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_8063005 : Nat := 118140960795 + 8063005 * 2 ^ 59
def prefixEnd_8063005 : Nat := 4983230072969 + 3 ^ 40 * 8063005 * 2
def baseEnd_8063005 : Nat := 4140197084605331189556421

theorem tailTrace_8063005 : CollatzResearch.WordTrace tailWord_8063005 prefixEnd_8063005 4140197084605331189556421 := by
  unfold tailWord_8063005
  simp only [CollatzResearch.WordTrace]
  refine ⟨294081952154117411466430469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196054634769411607644286979 294081952154117411466430469)
  ·
    refine ⟨55140366028897014649955713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294081952154117411466430469 55140366028897014649955713)
    ·
      refine ⟨41355274521672760987466785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55140366028897014649955713 41355274521672760987466785)
      ·
        refine ⟨31016455891254570740600089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41355274521672760987466785 31016455891254570740600089)
        ·
          refine ⟨23262341918440928055450067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31016455891254570740600089 23262341918440928055450067)
          ·
            refine ⟨34893512877661392083175101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23262341918440928055450067 34893512877661392083175101)
            ·
              refine ⟨13085067329123022031190663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34893512877661392083175101 13085067329123022031190663)
              ·
                refine ⟨19627600993684533046785995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13085067329123022031190663 19627600993684533046785995)
                ·
                  refine ⟨29441401490526799570178993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19627600993684533046785995 29441401490526799570178993)
                  ·
                    refine ⟨22081051117895099677634245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29441401490526799570178993 22081051117895099677634245)
                    ·
                      refine ⟨4140197084605331189556421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22081051117895099677634245 4140197084605331189556421)
                      ·
                        rfl

theorem cell23_8063005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_8063005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063005 prefixEnd_8063005 := by exact prefixLift 8063005
  have htrace : WordTrace (prefixWord ++ tailWord_8063005) baseStart_8063005 baseEnd_8063005 := by
    simpa [prefixWord, tailWord_8063005, baseEnd_8063005] using wordTrace_append hprefix tailTrace_8063005
  have hstable : (prefixWord ++ tailWord_8063005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063005).length < 2 ^ (prefixWord ++ tailWord_8063005).sum := by decide
  have hdescent : baseEnd_8063005 < baseStart_8063005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063015 : List Nat := [1, 1, 7, 1, 2, 1, 1, 9]
def baseStart_8063015 : Nat := 118140960795 + 8063015 * 2 ^ 59
def prefixEnd_8063015 : Nat := 4983230072969 + 3 ^ 40 * 8063015 * 2
def baseEnd_8063015 : Nat := 153340822941180598164125

theorem tailTrace_8063015 : CollatzResearch.WordTrace tailWord_8063015 prefixEnd_8063015 153340822941180598164125 := by
  unfold tailWord_8063015
  simp only [CollatzResearch.WordTrace]
  refine ⟨294082316884081183174294499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196054877922720788782862999 294082316884081183174294499)
  ·
    refine ⟨441123475326121774761441749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294082316884081183174294499 441123475326121774761441749)
    ·
      refine ⟨10338831452955979095971291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 441123475326121774761441749 10338831452955979095971291)
      ·
        refine ⟨15508247179433968643956937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10338831452955979095971291 15508247179433968643956937)
        ·
          refine ⟨11631185384575476482967703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15508247179433968643956937 11631185384575476482967703)
          ·
            refine ⟨17446778076863214724451555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11631185384575476482967703 17446778076863214724451555)
            ·
              refine ⟨26170167115294822086677333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17446778076863214724451555 26170167115294822086677333)
              ·
                refine ⟨153340822941180598164125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26170167115294822086677333 153340822941180598164125)
                ·
                  rfl

theorem cell23_8063015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 9].length) (baseStart_8063015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063015 prefixEnd_8063015 := by exact prefixLift 8063015
  have htrace : WordTrace (prefixWord ++ tailWord_8063015) baseStart_8063015 baseEnd_8063015 := by
    simpa [prefixWord, tailWord_8063015, baseEnd_8063015] using wordTrace_append hprefix tailTrace_8063015
  have hstable : (prefixWord ++ tailWord_8063015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063015).length < 2 ^ (prefixWord ++ tailWord_8063015).sum := by decide
  have hdescent : baseEnd_8063015 < baseStart_8063015 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063025 : List Nat := [1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 3]
def baseStart_8063025 : Nat := 118140960795 + 8063025 * 2 ^ 59
def prefixEnd_8063025 : Nat := 4983230072969 + 3 ^ 40 * 8063025 * 2
def baseEnd_8063025 : Nat := 4140207354218421111306329

theorem tailTrace_8063025 : CollatzResearch.WordTrace tailWord_8063025 prefixEnd_8063025 4140207354218421111306329 := by
  unfold tailWord_8063025
  simp only [CollatzResearch.WordTrace]
  refine ⟨294082681614044954882158529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196055121076029969921439019 294082681614044954882158529)
  ·
    refine ⟨220562011210533716161618897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294082681614044954882158529 220562011210533716161618897)
    ·
      refine ⟨165421508407900287121214173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220562011210533716161618897 165421508407900287121214173)
      ·
        refine ⟨62033065652962607670455315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165421508407900287121214173 62033065652962607670455315)
        ·
          refine ⟨93049598479443911505682973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62033065652962607670455315 93049598479443911505682973)
          ·
            refine ⟨34893599429791466814631115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93049598479443911505682973 34893599429791466814631115)
            ·
              refine ⟨52340399144687200221946673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34893599429791466814631115 52340399144687200221946673)
              ·
                refine ⟨39255299358515400166460005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52340399144687200221946673 39255299358515400166460005)
                ·
                  refine ⟨7360368629721637531211251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39255299358515400166460005 7360368629721637531211251)
                  ·
                    refine ⟨11040552944582456296816877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7360368629721637531211251 11040552944582456296816877)
                    ·
                      refine ⟨4140207354218421111306329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11040552944582456296816877 4140207354218421111306329)
                      ·
                        rfl

theorem cell23_8063025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_8063025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063025 prefixEnd_8063025 := by exact prefixLift 8063025
  have htrace : WordTrace (prefixWord ++ tailWord_8063025) baseStart_8063025 baseEnd_8063025 := by
    simpa [prefixWord, tailWord_8063025, baseEnd_8063025] using wordTrace_append hprefix tailTrace_8063025
  have hstable : (prefixWord ++ tailWord_8063025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063025).length < 2 ^ (prefixWord ++ tailWord_8063025).sum := by decide
  have hdescent : baseEnd_8063025 < baseStart_8063025 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063026 : List Nat := [3, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2]
def baseStart_8063026 : Nat := 118140960795 + 8063026 * 2 ^ 59
def prefixEnd_8063026 : Nat := 4983230072969 + 3 ^ 40 * 8063026 * 2
def baseEnd_8063026 : Nat := 4140207867699075607393825

theorem tailTrace_8063026 : CollatzResearch.WordTrace tailWord_8063026 prefixEnd_8063026 4140207867699075607393825 := by
  unfold tailWord_8063026
  simp only [CollatzResearch.WordTrace]
  refine ⟨73520679521760333013236233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196055145391360888035296621 73520679521760333013236233)
  ·
    refine ⟨55140509641320249759927175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73520679521760333013236233 55140509641320249759927175)
    ·
      refine ⟨82710764461980374639890763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55140509641320249759927175 82710764461980374639890763)
      ·
        refine ⟨124066146692970561959836145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82710764461980374639890763 124066146692970561959836145)
        ·
          refine ⟨93049610019727921469877109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124066146692970561959836145 93049610019727921469877109)
          ·
            refine ⟨8723400939349492637800979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 93049610019727921469877109 8723400939349492637800979)
            ·
              refine ⟨13085101409024238956701469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8723400939349492637800979 13085101409024238956701469)
              ·
                refine ⟨4906913028384089608763051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13085101409024238956701469 4906913028384089608763051)
                ·
                  refine ⟨7360369542576134413144577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4906913028384089608763051 7360369542576134413144577)
                  ·
                    refine ⟨5520277156932100809858433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7360369542576134413144577 5520277156932100809858433)
                    ·
                      refine ⟨4140207867699075607393825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520277156932100809858433 4140207867699075607393825)
                      ·
                        rfl

theorem cell23_8063026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 1, 3, 1, 2, 2].length) (baseStart_8063026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063026 prefixEnd_8063026 := by exact prefixLift 8063026
  have htrace : WordTrace (prefixWord ++ tailWord_8063026) baseStart_8063026 baseEnd_8063026 := by
    simpa [prefixWord, tailWord_8063026, baseEnd_8063026] using wordTrace_append hprefix tailTrace_8063026
  have hstable : (prefixWord ++ tailWord_8063026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063026).length < 2 ^ (prefixWord ++ tailWord_8063026).sum := by decide
  have hdescent : baseEnd_8063026 < baseStart_8063026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063065 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 1, 4, 2]
def baseStart_8063065 : Nat := 118140960795 + 8063065 * 2 ^ 59
def prefixEnd_8063065 : Nat := 4983230072969 + 3 ^ 40 * 8063065 * 2
def baseEnd_8063065 : Nat := 4140227893444600954806145

theorem tailTrace_8063065 : CollatzResearch.WordTrace tailWord_8063065 prefixEnd_8063065 4140227893444600954806145 := by
  unfold tailWord_8063065
  simp only [CollatzResearch.WordTrace]
  refine ⟨294084140533900041713614649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196056093689266694475743099 294084140533900041713614649)
  ·
    refine ⟨220563105400425031285210987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294084140533900041713614649 220563105400425031285210987)
    ·
      refine ⟨330844658100637546927816481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220563105400425031285210987 330844658100637546927816481)
      ·
        refine ⟨248133493575478160195862361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330844658100637546927816481 248133493575478160195862361)
        ·
          refine ⟨186100120181608620146896771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248133493575478160195862361 186100120181608620146896771)
          ·
            refine ⟨279150180272412930220345157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186100120181608620146896771 279150180272412930220345157)
            ·
              refine ⟨52340658801077424416314717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279150180272412930220345157 52340658801077424416314717)
              ·
                refine ⟨19627747050404034156118019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52340658801077424416314717 19627747050404034156118019)
                ·
                  refine ⟨29441620575606051234177029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19627747050404034156118019 29441620575606051234177029)
                  ·
                    refine ⟨5520303857926134606408193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29441620575606051234177029 5520303857926134606408193)
                    ·
                      refine ⟨4140227893444600954806145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520303857926134606408193 4140227893444600954806145)
                      ·
                        rfl

theorem cell23_8063065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 1, 4, 2].length) (baseStart_8063065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063065 prefixEnd_8063065 := by exact prefixLift 8063065
  have htrace : WordTrace (prefixWord ++ tailWord_8063065) baseStart_8063065 baseEnd_8063065 := by
    simpa [prefixWord, tailWord_8063065, baseEnd_8063065] using wordTrace_append hprefix tailTrace_8063065
  have hstable : (prefixWord ++ tailWord_8063065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063065).length < 2 ^ (prefixWord ++ tailWord_8063065).sum := by decide
  have hdescent : baseEnd_8063065 < baseStart_8063065 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063069 : List Nat := [1, 4, 4, 1, 1, 2, 1, 1, 3, 3, 2]
def baseStart_8063069 : Nat := 118140960795 + 8063069 * 2 ^ 59
def prefixEnd_8063069 : Nat := 4983230072969 + 3 ^ 40 * 8063069 * 2
def baseEnd_8063069 : Nat := 4140229947367218939156127

theorem tailTrace_8063069 : CollatzResearch.WordTrace tailWord_8063069 prefixEnd_8063069 4140229947367218939156127 := by
  unfold tailWord_8063069
  simp only [CollatzResearch.WordTrace]
  refine ⟨294084286425885550396760261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196056190950590366931173507 294084286425885550396760261)
  ·
    refine ⟨55140803704853540699392549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294084286425885550396760261 55140803704853540699392549)
    ·
      refine ⟨10338900694660038881136103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55140803704853540699392549 10338900694660038881136103)
      ·
        refine ⟨15508351041990058321704155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10338900694660038881136103 15508351041990058321704155)
        ·
          refine ⟨23262526562985087482556233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15508351041990058321704155 23262526562985087482556233)
          ·
            refine ⟨17446894922238815611917175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23262526562985087482556233 17446894922238815611917175)
            ·
              refine ⟨26170342383358223417875763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17446894922238815611917175 26170342383358223417875763)
              ·
                refine ⟨39255513575037335126813645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26170342383358223417875763 39255513575037335126813645)
                ·
                  refine ⟨14720817590639000672555117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39255513575037335126813645 14720817590639000672555117)
                  ·
                    refine ⟨5520306596489625252208169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14720817590639000672555117 5520306596489625252208169)
                    ·
                      refine ⟨4140229947367218939156127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520306596489625252208169 4140229947367218939156127)
                      ·
                        rfl

theorem cell23_8063069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_8063069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063069 prefixEnd_8063069 := by exact prefixLift 8063069
  have htrace : WordTrace (prefixWord ++ tailWord_8063069) baseStart_8063069 baseEnd_8063069 := by
    simpa [prefixWord, tailWord_8063069, baseEnd_8063069] using wordTrace_append hprefix tailTrace_8063069
  have hstable : (prefixWord ++ tailWord_8063069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063069).length < 2 ^ (prefixWord ++ tailWord_8063069).sum := by decide
  have hdescent : baseEnd_8063069 < baseStart_8063069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063098 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3]
def baseStart_8063098 : Nat := 118140960795 + 8063098 * 2 ^ 59
def prefixEnd_8063098 : Nat := 4983230072969 + 3 ^ 40 * 8063098 * 2
def baseEnd_8063098 : Nat := 4140244838306199325693493

theorem tailTrace_8063098 : CollatzResearch.WordTrace tailWord_8063098 prefixEnd_8063098 4140244838306199325693493 := by
  unfold tailWord_8063098
  simp only [CollatzResearch.WordTrace]
  refine ⟨73521336035695122087391487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196056896095186992233043965 73521336035695122087391487)
  ·
    refine ⟨110282004053542683131087231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73521336035695122087391487 110282004053542683131087231)
    ·
      refine ⟨165423006080314024696630847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110282004053542683131087231 165423006080314024696630847)
      ·
        refine ⟨248134509120471037044946271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165423006080314024696630847 248134509120471037044946271)
        ·
          refine ⟨372201763680706555567419407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248134509120471037044946271 372201763680706555567419407)
          ·
            refine ⟨558302645521059833351129111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372201763680706555567419407 558302645521059833351129111)
            ·
              refine ⟨837453968281589750026693667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558302645521059833351129111 837453968281589750026693667)
              ·
                refine ⟨1256180952422384625040040501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837453968281589750026693667 1256180952422384625040040501)
                ·
                  refine ⟨117766964289598558597503797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1256180952422384625040040501 117766964289598558597503797)
                  ·
                    refine ⟨11040652902149864868515981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117766964289598558597503797 11040652902149864868515981)
                    ·
                      refine ⟨4140244838306199325693493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11040652902149864868515981 4140244838306199325693493)
                      ·
                        rfl

theorem cell23_8063098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 5, 3].length) (baseStart_8063098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063098 prefixEnd_8063098 := by exact prefixLift 8063098
  have htrace : WordTrace (prefixWord ++ tailWord_8063098) baseStart_8063098 baseEnd_8063098 := by
    simpa [prefixWord, tailWord_8063098, baseEnd_8063098] using wordTrace_append hprefix tailTrace_8063098
  have hstable : (prefixWord ++ tailWord_8063098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063098).length < 2 ^ (prefixWord ++ tailWord_8063098).sum := by decide
  have hdescent : baseEnd_8063098 < baseStart_8063098 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063125 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 2, 5, 2]
def baseStart_8063125 : Nat := 118140960795 + 8063125 * 2 ^ 59
def prefixEnd_8063125 : Nat := 4983230072969 + 3 ^ 40 * 8063125 * 2
def baseEnd_8063125 : Nat := 4140258702283870720055869

theorem tailTrace_8063125 : CollatzResearch.WordTrace tailWord_8063125 prefixEnd_8063125 4140258702283870720055869 := by
  unfold tailWord_8063125
  simp only [CollatzResearch.WordTrace]
  refine ⟨294086328913682671960798829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196057552609121781307199219 294086328913682671960798829)
  ·
    refine ⟨110282373342631001985299561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294086328913682671960798829 110282373342631001985299561)
    ·
      refine ⟨82711780006973251488974671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110282373342631001985299561 82711780006973251488974671)
      ·
        refine ⟨124067670010459877233462007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82711780006973251488974671 124067670010459877233462007)
        ·
          refine ⟨186101505015689815850193011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124067670010459877233462007 186101505015689815850193011)
          ·
            refine ⟨279152257523534723775289517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186101505015689815850193011 279152257523534723775289517)
            ·
              refine ⟨104682096571325521415733569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 279152257523534723775289517 104682096571325521415733569)
              ·
                refine ⟨78511572428494141061800177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104682096571325521415733569 78511572428494141061800177)
                ·
                  refine ⟨58883679321370605796350133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78511572428494141061800177 58883679321370605796350133)
                  ·
                    refine ⟨5520344936378494293407825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58883679321370605796350133 5520344936378494293407825)
                    ·
                      refine ⟨4140258702283870720055869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520344936378494293407825 4140258702283870720055869)
                      ·
                        rfl

theorem cell23_8063125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 2, 5, 2].length) (baseStart_8063125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063125 prefixEnd_8063125 := by exact prefixLift 8063125
  have htrace : WordTrace (prefixWord ++ tailWord_8063125) baseStart_8063125 baseEnd_8063125 := by
    simpa [prefixWord, tailWord_8063125, baseEnd_8063125] using wordTrace_append hprefix tailTrace_8063125
  have hstable : (prefixWord ++ tailWord_8063125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063125).length < 2 ^ (prefixWord ++ tailWord_8063125).sum := by decide
  have hdescent : baseEnd_8063125 < baseStart_8063125 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063135 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 1, 7]
def baseStart_8063135 : Nat := 118140960795 + 8063135 * 2 ^ 59
def prefixEnd_8063135 : Nat := 4983230072969 + 3 ^ 40 * 8063135 * 2
def baseEnd_8063135 : Nat := 1380087945696805226976941

theorem tailTrace_8063135 : CollatzResearch.WordTrace tailWord_8063135 prefixEnd_8063135 1380087945696805226976941 := by
  unfold tailWord_8063135
  simp only [CollatzResearch.WordTrace]
  refine ⟨294086693643646443668662859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196057795762430962445775239 294086693643646443668662859)
  ·
    refine ⟨441130040465469665502994289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294086693643646443668662859 441130040465469665502994289)
    ·
      refine ⟨330847530349102249127245717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441130040465469665502994289 330847530349102249127245717)
      ·
        refine ⟨15508477985114167927839643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 330847530349102249127245717 15508477985114167927839643)
        ·
          refine ⟨23262716977671251891759465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15508477985114167927839643 23262716977671251891759465)
          ·
            refine ⟨17447037733253438918819599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23262716977671251891759465 17447037733253438918819599)
            ·
              refine ⟨26170556599880158378229399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17447037733253438918819599 26170556599880158378229399)
              ·
                refine ⟨39255834899820237567344099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26170556599880158378229399 39255834899820237567344099)
                ·
                  refine ⟨58883752349730356351016149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39255834899820237567344099 58883752349730356351016149)
                  ·
                    refine ⟨1380087945696805226976941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58883752349730356351016149 1380087945696805226976941)
                    ·
                      rfl

theorem cell23_8063135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_8063135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063135 prefixEnd_8063135 := by exact prefixLift 8063135
  have htrace : WordTrace (prefixWord ++ tailWord_8063135) baseStart_8063135 baseEnd_8063135 := by
    simpa [prefixWord, tailWord_8063135, baseEnd_8063135] using wordTrace_append hprefix tailTrace_8063135
  have hstable : (prefixWord ++ tailWord_8063135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063135).length < 2 ^ (prefixWord ++ tailWord_8063135).sum := by decide
  have hdescent : baseEnd_8063135 < baseStart_8063135 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063150 : List Nat := [4, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2]
def baseStart_8063150 : Nat := 118140960795 + 8063150 * 2 ^ 59
def prefixEnd_8063150 : Nat := 4983230072969 + 3 ^ 40 * 8063150 * 2
def baseEnd_8063150 : Nat := 4140271539300233122243255

theorem tailTrace_8063150 : CollatzResearch.WordTrace tailWord_8063150 prefixEnd_8063150 4140271539300233122243255 := by
  unfold tailWord_8063150
  simp only [CollatzResearch.WordTrace]
  refine ⟨36760905092324012653807363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196058160492394734153639269 36760905092324012653807363)
  ·
    refine ⟨55141357638486018980711045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36760905092324012653807363 55141357638486018980711045)
    ·
      refine ⟨10339004557216128558883321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55141357638486018980711045 10339004557216128558883321)
      ·
        refine ⟨7754253417912096419162491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10339004557216128558883321 7754253417912096419162491)
        ·
          refine ⟨11631380126868144628743737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754253417912096419162491 11631380126868144628743737)
          ·
            refine ⟨8723535095151108471557803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11631380126868144628743737 8723535095151108471557803)
            ·
              refine ⟨13085302642726662707336705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8723535095151108471557803 13085302642726662707336705)
              ·
                refine ⟨9813976982044997030502529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13085302642726662707336705 9813976982044997030502529)
                ·
                  refine ⟨7360482736533747772876897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9813976982044997030502529 7360482736533747772876897)
                  ·
                    refine ⟨5520362052400310829657673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7360482736533747772876897 5520362052400310829657673)
                    ·
                      refine ⟨4140271539300233122243255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520362052400310829657673 4140271539300233122243255)
                      ·
                        rfl

theorem cell23_8063150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_8063150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063150 prefixEnd_8063150 := by exact prefixLift 8063150
  have htrace : WordTrace (prefixWord ++ tailWord_8063150) baseStart_8063150 baseEnd_8063150 := by
    simpa [prefixWord, tailWord_8063150, baseEnd_8063150] using wordTrace_append hprefix tailTrace_8063150
  have hstable : (prefixWord ++ tailWord_8063150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063150).length < 2 ^ (prefixWord ++ tailWord_8063150).sum := by decide
  have hdescent : baseEnd_8063150 < baseStart_8063150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063156 : List Nat := [2, 5, 3, 1, 1, 1, 2, 1, 7]
def baseStart_8063156 : Nat := 118140960795 + 8063156 * 2 ^ 59
def prefixEnd_8063156 : Nat := 4983230072969 + 3 ^ 40 * 8063156 * 2
def baseEnd_8063156 : Nat := 460030513353795566529803

theorem tailTrace_8063156 : CollatzResearch.WordTrace tailWord_8063156 prefixEnd_8063156 460030513353795566529803 := by
  unfold tailWord_8063156
  simp only [CollatzResearch.WordTrace]
  refine ⟨147043729788285182127588661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196058306384380242836784881 147043729788285182127588661)
  ·
    refine ⟨13785349667651735824461437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147043729788285182127588661 13785349667651735824461437)
    ·
      refine ⟨5169506125369400934173039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13785349667651735824461437 5169506125369400934173039)
      ·
        refine ⟨7754259188054101401259559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5169506125369400934173039 7754259188054101401259559)
        ·
          refine ⟨11631388782081152101889339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7754259188054101401259559 11631388782081152101889339)
          ·
            refine ⟨17447083173121728152834009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11631388782081152101889339 17447083173121728152834009)
            ·
              refine ⟨13085312379841296114625507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17447083173121728152834009 13085312379841296114625507)
              ·
                refine ⟨19627968569761944171938261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13085312379841296114625507 19627968569761944171938261)
                ·
                  refine ⟨460030513353795566529803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19627968569761944171938261 460030513353795566529803)
                  ·
                    rfl

theorem cell23_8063156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_8063156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063156 prefixEnd_8063156 := by exact prefixLift 8063156
  have htrace : WordTrace (prefixWord ++ tailWord_8063156) baseStart_8063156 baseEnd_8063156 := by
    simpa [prefixWord, tailWord_8063156, baseEnd_8063156] using wordTrace_append hprefix tailTrace_8063156
  have hstable : (prefixWord ++ tailWord_8063156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063156).length < 2 ^ (prefixWord ++ tailWord_8063156).sum := by decide
  have hdescent : baseEnd_8063156 < baseStart_8063156 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063182 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 3, 4]
def baseStart_8063182 : Nat := 118140960795 + 8063182 * 2 ^ 59
def prefixEnd_8063182 : Nat := 4983230072969 + 3 ^ 40 * 8063182 * 2
def baseEnd_8063182 : Nat := 1380095990227058999014369

theorem tailTrace_8063182 : CollatzResearch.WordTrace tailWord_8063182 prefixEnd_8063182 1380095990227058999014369 := by
  unfold tailWord_8063182
  simp only [CollatzResearch.WordTrace]
  refine ⟨36761050984309521336952975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196058938582984113797082533 36761050984309521336952975)
  ·
    refine ⟨55141576476464282005429463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36761050984309521336952975 55141576476464282005429463)
    ·
      refine ⟨82712364714696423008144195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55141576476464282005429463 82712364714696423008144195)
      ·
        refine ⟨124068547072044634512216293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82712364714696423008144195 124068547072044634512216293)
        ·
          refine ⟨23262852576008368971040555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124068547072044634512216293 23262852576008368971040555)
          ·
            refine ⟨34894278864012553456560833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23262852576008368971040555 34894278864012553456560833)
            ·
              refine ⟨26170709148009415092420625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34894278864012553456560833 26170709148009415092420625)
              ·
                refine ⟨19628031861007061319315469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26170709148009415092420625 19628031861007061319315469)
                ·
                  refine ⟨7360511947877647994743301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19628031861007061319315469 7360511947877647994743301)
                  ·
                    refine ⟨1380095990227058999014369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7360511947877647994743301 1380095990227058999014369)
                    ·
                      rfl

theorem cell23_8063182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 3, 4].length) (baseStart_8063182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063182 prefixEnd_8063182 := by exact prefixLift 8063182
  have htrace : WordTrace (prefixWord ++ tailWord_8063182) baseStart_8063182 baseEnd_8063182 := by
    simpa [prefixWord, tailWord_8063182, baseEnd_8063182] using wordTrace_append hprefix tailTrace_8063182
  have hstable : (prefixWord ++ tailWord_8063182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063182).length < 2 ^ (prefixWord ++ tailWord_8063182).sum := by decide
  have hdescent : baseEnd_8063182 < baseStart_8063182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063242 : List Nat := [3, 1, 2, 2, 1, 1, 5, 2, 1, 5]
def baseStart_8063242 : Nat := 118140960795 + 8063242 * 2 ^ 59
def prefixEnd_8063242 : Nat := 4983230072969 + 3 ^ 40 * 8063242 * 2
def baseEnd_8063242 : Nat := 1380106259840148920764277

theorem tailTrace_8063242 : CollatzResearch.WordTrace tailWord_8063242 prefixEnd_8063242 1380106259840148920764277 := by
  unfold tailWord_8063242
  simp only [CollatzResearch.WordTrace]
  refine ⟨73522649063564700235701995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196060397502839200628538653 73522649063564700235701995)
  ·
    refine ⟨110283973595347050353552993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73522649063564700235701995 110283973595347050353552993)
    ·
      refine ⟨82712980196510287765164745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110283973595347050353552993 82712980196510287765164745)
      ·
        refine ⟨62034735147382715823873559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82712980196510287765164745 62034735147382715823873559)
        ·
          refine ⟨93052102721074073735810339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62034735147382715823873559 93052102721074073735810339)
          ·
            refine ⟨139578154081611110603715509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93052102721074073735810339 139578154081611110603715509)
            ·
              refine ⟨13085451945151041619098329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 139578154081611110603715509 13085451945151041619098329)
              ·
                refine ⟨9814088958863281214323747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13085451945151041619098329 9814088958863281214323747)
                ·
                  refine ⟨14721133438294921821485621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9814088958863281214323747 14721133438294921821485621)
                  ·
                    refine ⟨1380106259840148920764277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14721133438294921821485621 1380106259840148920764277)
                    ·
                      rfl

theorem cell23_8063242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 5, 2, 1, 5].length) (baseStart_8063242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063242 prefixEnd_8063242 := by exact prefixLift 8063242
  have htrace : WordTrace (prefixWord ++ tailWord_8063242) baseStart_8063242 baseEnd_8063242 := by
    simpa [prefixWord, tailWord_8063242, baseEnd_8063242] using wordTrace_append hprefix tailTrace_8063242
  have hstable : (prefixWord ++ tailWord_8063242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063242).length < 2 ^ (prefixWord ++ tailWord_8063242).sum := by decide
  have hdescent : baseEnd_8063242 < baseStart_8063242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063248 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 11]
def baseStart_8063248 : Nat := 118140960795 + 8063248 * 2 ^ 59
def prefixEnd_8063248 : Nat := 4983230072969 + 3 ^ 40 * 8063248 * 2
def baseEnd_8063248 : Nat := 4140321860404373738817803

theorem tailTrace_8063248 : CollatzResearch.WordTrace tailWord_8063248 prefixEnd_8063248 4140321860404373738817803 := by
  unfold tailWord_8063248
  simp only [CollatzResearch.WordTrace]
  refine ⟨147045407546118531983763199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196060543394824709311684265 147045407546118531983763199)
  ·
    refine ⟨220568111319177797975644799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147045407546118531983763199 220568111319177797975644799)
    ·
      refine ⟨330852166978766696963467199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220568111319177797975644799 330852166978766696963467199)
      ·
        refine ⟨496278250468150045445200799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330852166978766696963467199 496278250468150045445200799)
        ·
          refine ⟨744417375702225068167801199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496278250468150045445200799 744417375702225068167801199)
          ·
            refine ⟨1116626063553337602251701799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744417375702225068167801199 1116626063553337602251701799)
            ·
              refine ⟨1674939095330006403377552699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116626063553337602251701799 1674939095330006403377552699)
              ·
                refine ⟨2512408642995009605066329049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1674939095330006403377552699 2512408642995009605066329049)
                ·
                  refine ⟨1884306482246257203799746787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2512408642995009605066329049 1884306482246257203799746787)
                  ·
                    refine ⟨2826459723369385805699620181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1884306482246257203799746787 2826459723369385805699620181)
                    ·
                      refine ⟨4140321860404373738817803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 2826459723369385805699620181 4140321860404373738817803)
                      ·
                        rfl

theorem cell23_8063248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 11].length) (baseStart_8063248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063248 prefixEnd_8063248 := by exact prefixLift 8063248
  have htrace : WordTrace (prefixWord ++ tailWord_8063248) baseStart_8063248 baseEnd_8063248 := by
    simpa [prefixWord, tailWord_8063248, baseEnd_8063248] using wordTrace_append hprefix tailTrace_8063248
  have hstable : (prefixWord ++ tailWord_8063248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063248).length < 2 ^ (prefixWord ++ tailWord_8063248).sum := by decide
  have hdescent : baseEnd_8063248 < baseStart_8063248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063249 : List Nat := [1, 2, 2, 1, 1, 6, 2, 1, 2, 3, 2]
def baseStart_8063249 : Nat := 118140960795 + 8063249 * 2 ^ 59
def prefixEnd_8063249 : Nat := 4983230072969 + 3 ^ 40 * 8063249 * 2
def baseEnd_8063249 : Nat := 4140322373885028234905299

theorem tailTrace_8063249 : CollatzResearch.WordTrace tailWord_8063249 prefixEnd_8063249 4140322373885028234905299 := by
  unfold tailWord_8063249
  simp only [CollatzResearch.WordTrace]
  refine ⟨294090851565233441138312801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196060567710155627425541867 294090851565233441138312801)
  ·
    refine ⟨220568138673925080853734601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294090851565233441138312801 220568138673925080853734601)
    ·
      refine ⟨165426104005443810640300951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220568138673925080853734601 165426104005443810640300951)
      ·
        refine ⟨248139156008165715960451427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165426104005443810640300951 248139156008165715960451427)
        ·
          refine ⟨372208734012248573940677141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248139156008165715960451427 372208734012248573940677141)
          ·
            refine ⟨17447284406824151903469241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 372208734012248573940677141 17447284406824151903469241)
            ·
              refine ⟨13085463305118113927601931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17447284406824151903469241 13085463305118113927601931)
              ·
                refine ⟨19628194957677170891402897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13085463305118113927601931 19628194957677170891402897)
                ·
                  refine ⟨14721146218257878168552173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19628194957677170891402897 14721146218257878168552173)
                  ·
                    refine ⟨5520429831846704313207065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14721146218257878168552173 5520429831846704313207065)
                    ·
                      refine ⟨4140322373885028234905299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520429831846704313207065 4140322373885028234905299)
                      ·
                        rfl

theorem cell23_8063249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 3, 2].length) (baseStart_8063249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063249 prefixEnd_8063249 := by exact prefixLift 8063249
  have htrace : WordTrace (prefixWord ++ tailWord_8063249) baseStart_8063249 baseEnd_8063249 := by
    simpa [prefixWord, tailWord_8063249, baseEnd_8063249] using wordTrace_append hprefix tailTrace_8063249
  have hstable : (prefixWord ++ tailWord_8063249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063249).length < 2 ^ (prefixWord ++ tailWord_8063249).sum := by decide
  have hdescent : baseEnd_8063249 < baseStart_8063249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063255 : List Nat := [1, 1, 3, 4, 1, 2, 1, 1, 3, 6]
def baseStart_8063255 : Nat := 118140960795 + 8063255 * 2 ^ 59
def prefixEnd_8063255 : Nat := 4983230072969 + 3 ^ 40 * 8063255 * 2
def baseEnd_8063255 : Nat := 1380108484922985070476757

theorem tailTrace_8063255 : CollatzResearch.WordTrace tailWord_8063255 prefixEnd_8063255 1380108484922985070476757 := by
  unfold tailWord_8063255
  simp only [CollatzResearch.WordTrace]
  refine ⟨294091070403211704163031219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196060713602141136108687479 294091070403211704163031219)
  ·
    refine ⟨441136605604817556244546829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294091070403211704163031219 441136605604817556244546829)
    ·
      refine ⟨165426227101806583591705061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441136605604817556244546829 165426227101806583591705061)
      ·
        refine ⟨31017417581588734423444699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165426227101806583591705061 31017417581588734423444699)
        ·
          refine ⟨46526126372383101635167049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31017417581588734423444699 46526126372383101635167049)
          ·
            refine ⟨34894594779287326226375287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46526126372383101635167049 34894594779287326226375287)
            ·
              refine ⟨52341892168930989339562931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34894594779287326226375287 52341892168930989339562931)
              ·
                refine ⟨78512838253396484009344397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52341892168930989339562931 78512838253396484009344397)
                ·
                  refine ⟨29442314345023681503504149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78512838253396484009344397 29442314345023681503504149)
                  ·
                    refine ⟨1380108484922985070476757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29442314345023681503504149 1380108484922985070476757)
                    ·
                      rfl

theorem cell23_8063255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_8063255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063255 prefixEnd_8063255 := by exact prefixLift 8063255
  have htrace : WordTrace (prefixWord ++ tailWord_8063255) baseStart_8063255 baseEnd_8063255 := by
    simpa [prefixWord, tailWord_8063255, baseEnd_8063255] using wordTrace_append hprefix tailTrace_8063255
  have hstable : (prefixWord ++ tailWord_8063255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063255).length < 2 ^ (prefixWord ++ tailWord_8063255).sum := by decide
  have hdescent : baseEnd_8063255 < baseStart_8063255 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063289 : List Nat := [1, 2, 1, 6, 1, 1, 2, 3, 2, 4]
def baseStart_8063289 : Nat := 118140960795 + 8063289 * 2 ^ 59
def prefixEnd_8063289 : Nat := 4983230072969 + 3 ^ 40 * 8063289 * 2
def baseEnd_8063289 : Nat := 1380114304370402692801705

theorem tailTrace_8063289 : CollatzResearch.WordTrace tailWord_8063289 prefixEnd_8063289 1380114304370402692801705 := by
  unfold tailWord_8063289
  simp only [CollatzResearch.WordTrace]
  refine ⟨294092310485088527969768921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196061540323392351979845947 294092310485088527969768921)
  ·
    refine ⟨220569232863816395977326691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294092310485088527969768921 220569232863816395977326691)
    ·
      refine ⟨330853849295724593965990037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220569232863816395977326691 330853849295724593965990037)
      ·
        refine ⟨15508774185737090342155783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 330853849295724593965990037 15508774185737090342155783)
        ·
          refine ⟨23263161278605635513233675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15508774185737090342155783 23263161278605635513233675)
          ·
            refine ⟨34894741917908453269850513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23263161278605635513233675 34894741917908453269850513)
            ·
              refine ⟨26171056438431339952387885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34894741917908453269850513 26171056438431339952387885)
              ·
                refine ⟨9814146164411752482145457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26171056438431339952387885 9814146164411752482145457)
                ·
                  refine ⟨7360609623308814361609093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9814146164411752482145457 7360609623308814361609093)
                  ·
                    refine ⟨1380114304370402692801705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7360609623308814361609093 1380114304370402692801705)
                    ·
                      rfl

theorem cell23_8063289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 3, 2, 4].length) (baseStart_8063289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063289 prefixEnd_8063289 := by exact prefixLift 8063289
  have htrace : WordTrace (prefixWord ++ tailWord_8063289) baseStart_8063289 baseEnd_8063289 := by
    simpa [prefixWord, tailWord_8063289, baseEnd_8063289] using wordTrace_append hprefix tailTrace_8063289
  have hstable : (prefixWord ++ tailWord_8063289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063289).length < 2 ^ (prefixWord ++ tailWord_8063289).sum := by decide
  have hdescent : baseEnd_8063289 < baseStart_8063289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063292 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_8063292 : Nat := 118140960795 + 8063292 * 2 ^ 59
def prefixEnd_8063292 : Nat := 4983230072969 + 3 ^ 40 * 8063292 * 2
def baseEnd_8063292 : Nat := 4140344453553171566667601

theorem tailTrace_8063292 : CollatzResearch.WordTrace tailWord_8063292 prefixEnd_8063292 4140344453553171566667601 := by
  unfold tailWord_8063292
  simp only [CollatzResearch.WordTrace]
  refine ⟨147046209952038829741064065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196061613269385106321418753 147046209952038829741064065)
  ·
    refine ⟨110284657464029122305798049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147046209952038829741064065 110284657464029122305798049)
    ·
      refine ⟨82713493098021841729348537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110284657464029122305798049 82713493098021841729348537)
      ·
        refine ⟨62035119823516381297011403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82713493098021841729348537 62035119823516381297011403)
        ·
          refine ⟨93052679735274571945517105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62035119823516381297011403 93052679735274571945517105)
          ·
            refine ⟨69789509801455928959137829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93052679735274571945517105 69789509801455928959137829)
            ·
              refine ⟨13085533087772986679838343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69789509801455928959137829 13085533087772986679838343)
              ·
                refine ⟨19628299631659480019757515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13085533087772986679838343 19628299631659480019757515)
                ·
                  refine ⟨29442449447489220029636273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19628299631659480019757515 29442449447489220029636273)
                  ·
                    refine ⟨22081837085616915022227205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29442449447489220029636273 22081837085616915022227205)
                    ·
                      refine ⟨4140344453553171566667601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22081837085616915022227205 4140344453553171566667601)
                      ·
                        rfl

theorem cell23_8063292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_8063292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063292 prefixEnd_8063292 := by exact prefixLift 8063292
  have htrace : WordTrace (prefixWord ++ tailWord_8063292) baseStart_8063292 baseEnd_8063292 := by
    simpa [prefixWord, tailWord_8063292, baseEnd_8063292] using wordTrace_append hprefix tailTrace_8063292
  have hstable : (prefixWord ++ tailWord_8063292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063292).length < 2 ^ (prefixWord ++ tailWord_8063292).sum := by decide
  have hdescent : baseEnd_8063292 < baseStart_8063292 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063300 : List Nat := [2, 3, 4, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_8063300 : Nat := 118140960795 + 8063300 * 2 ^ 59
def prefixEnd_8063300 : Nat := 4983230072969 + 3 ^ 40 * 8063300 * 2
def baseEnd_8063300 : Nat := 4140348561398407535367565

theorem tailTrace_8063300 : CollatzResearch.WordTrace tailWord_8063300 prefixEnd_8063300 4140348561398407535367565 := by
  unfold tailWord_8063300
  simp only [CollatzResearch.WordTrace]
  refine ⟨147046355844024338424209677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196061807792032451232279569 147046355844024338424209677)
  ·
    refine ⟨55142383441509126909078629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 147046355844024338424209677 55142383441509126909078629)
    ·
      refine ⟨10339196895282961295452243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55142383441509126909078629 10339196895282961295452243)
      ·
        refine ⟨15508795342924441943178365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10339196895282961295452243 15508795342924441943178365)
        ·
          refine ⟨5815798253596665728691887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15508795342924441943178365 5815798253596665728691887)
          ·
            refine ⟨8723697380394998593037831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5815798253596665728691887 8723697380394998593037831)
            ·
              refine ⟨13085546070592497889556747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8723697380394998593037831 13085546070592497889556747)
              ·
                refine ⟨19628319105888746834335121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13085546070592497889556747 19628319105888746834335121)
                ·
                  refine ⟨14721239329416560125751341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19628319105888746834335121 14721239329416560125751341)
                  ·
                    refine ⟨5520464748531210047156753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14721239329416560125751341 5520464748531210047156753)
                    ·
                      refine ⟨4140348561398407535367565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520464748531210047156753 4140348561398407535367565)
                      ·
                        rfl

theorem cell23_8063300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_8063300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063300 prefixEnd_8063300 := by exact prefixLift 8063300
  have htrace : WordTrace (prefixWord ++ tailWord_8063300) baseStart_8063300 baseEnd_8063300 := by
    simpa [prefixWord, tailWord_8063300, baseEnd_8063300] using wordTrace_append hprefix tailTrace_8063300
  have hstable : (prefixWord ++ tailWord_8063300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063300).length < 2 ^ (prefixWord ++ tailWord_8063300).sum := by decide
  have hdescent : baseEnd_8063300 < baseStart_8063300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063312 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 3]
def baseStart_8063312 : Nat := 118140960795 + 8063312 * 2 ^ 59
def prefixEnd_8063312 : Nat := 4983230072969 + 3 ^ 40 * 8063312 * 2
def baseEnd_8063312 : Nat := 4140354723166261488417509

theorem tailTrace_8063312 : CollatzResearch.WordTrace tailWord_8063312 prefixEnd_8063312 4140354723166261488417509 := by
  unfold tailWord_8063312
  simp only [CollatzResearch.WordTrace]
  refine ⟨147046574682002601448928095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196062099576003468598570793 147046574682002601448928095)
  ·
    refine ⟨220569862023003902173392143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147046574682002601448928095 220569862023003902173392143)
    ·
      refine ⟨330854793034505853260088215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220569862023003902173392143 330854793034505853260088215)
      ·
        refine ⟨496282189551758779890132323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330854793034505853260088215 496282189551758779890132323)
        ·
          refine ⟨744423284327638169835198485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496282189551758779890132323 744423284327638169835198485)
          ·
            refine ⟨34894841452858039211024929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 744423284327638169835198485 34894841452858039211024929)
            ·
              refine ⟨26171131089643529408268697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34894841452858039211024929 26171131089643529408268697)
              ·
                refine ⟨19628348317232647056201523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26171131089643529408268697 19628348317232647056201523)
                ·
                  refine ⟨29442522475848970584302285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19628348317232647056201523 29442522475848970584302285)
                  ·
                    refine ⟨11040945928443363969113357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29442522475848970584302285 11040945928443363969113357)
                    ·
                      refine ⟨4140354723166261488417509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11040945928443363969113357 4140354723166261488417509)
                      ·
                        rfl

theorem cell23_8063312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 3].length) (baseStart_8063312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063312 prefixEnd_8063312 := by exact prefixLift 8063312
  have htrace : WordTrace (prefixWord ++ tailWord_8063312) baseStart_8063312 baseEnd_8063312 := by
    simpa [prefixWord, tailWord_8063312, baseEnd_8063312] using wordTrace_append hprefix tailTrace_8063312
  have hstable : (prefixWord ++ tailWord_8063312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063312).length < 2 ^ (prefixWord ++ tailWord_8063312).sum := by decide
  have hdescent : baseEnd_8063312 < baseStart_8063312 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063313 : List Nat := [1, 2, 2, 1, 4, 3, 2, 3, 1, 2, 2]
def baseStart_8063313 : Nat := 118140960795 + 8063313 * 2 ^ 59
def prefixEnd_8063313 : Nat := 4983230072969 + 3 ^ 40 * 8063313 * 2
def baseEnd_8063313 : Nat := 4140355236646915984505005

theorem tailTrace_8063313 : CollatzResearch.WordTrace tailWord_8063313 prefixEnd_8063313 4140355236646915984505005 := by
  unfold tailWord_8063313
  simp only [CollatzResearch.WordTrace]
  refine ⟨294093185837001580068642593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196062123891334386712428395 294093185837001580068642593)
  ·
    refine ⟨220569889377751185051481945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294093185837001580068642593 220569889377751185051481945)
    ·
      refine ⟨165427417033313388788611459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220569889377751185051481945 165427417033313388788611459)
      ·
        refine ⟨248141125549970083182917189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165427417033313388788611459 248141125549970083182917189)
        ·
          refine ⟨46526461040619390596796973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248141125549970083182917189 46526461040619390596796973)
          ·
            refine ⟨17447422890232271473798865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46526461040619390596796973 17447422890232271473798865)
            ·
              refine ⟨13085567167674203605349149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17447422890232271473798865 13085567167674203605349149)
              ·
                refine ⟨4907087687877826352005931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13085567167674203605349149 4907087687877826352005931)
                ·
                  refine ⟨7360631531816739528008897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907087687877826352005931 7360631531816739528008897)
                  ·
                    refine ⟨5520473648862554646006673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7360631531816739528008897 5520473648862554646006673)
                    ·
                      refine ⟨4140355236646915984505005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520473648862554646006673 4140355236646915984505005)
                      ·
                        rfl

theorem cell23_8063313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3, 1, 2, 2].length) (baseStart_8063313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063313 prefixEnd_8063313 := by exact prefixLift 8063313
  have htrace : WordTrace (prefixWord ++ tailWord_8063313) baseStart_8063313 baseEnd_8063313 := by
    simpa [prefixWord, tailWord_8063313, baseEnd_8063313] using wordTrace_append hprefix tailTrace_8063313
  have hstable : (prefixWord ++ tailWord_8063313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063313).length < 2 ^ (prefixWord ++ tailWord_8063313).sum := by decide
  have hdescent : baseEnd_8063313 < baseStart_8063313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063316 : List Nat := [2, 4, 1, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_8063316 : Nat := 118140960795 + 8063316 * 2 ^ 59
def prefixEnd_8063316 : Nat := 4983230072969 + 3 ^ 40 * 8063316 * 2
def baseEnd_8063316 : Nat := 4140356777088879472767491

theorem tailTrace_8063316 : CollatzResearch.WordTrace tailWord_8063316 prefixEnd_8063316 4140356777088879472767491 := by
  unfold tailWord_8063316
  simp only [CollatzResearch.WordTrace]
  refine ⟨147046647627995355790500901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196062196837327141054001201 147046647627995355790500901)
  ·
    refine ⟨27571246430249129210718919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 147046647627995355790500901 27571246430249129210718919)
    ·
      refine ⟨41356869645373693816078379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27571246430249129210718919 41356869645373693816078379)
      ·
        refine ⟨62035304468060540724117569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41356869645373693816078379 62035304468060540724117569)
        ·
          refine ⟨46526478351045405543088177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62035304468060540724117569 46526478351045405543088177)
          ·
            refine ⟨34894858763284054157316133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46526478351045405543088177 34894858763284054157316133)
            ·
              refine ⟨6542786018115760154496775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34894858763284054157316133 6542786018115760154496775)
              ·
                refine ⟨9814179027173640231745163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6542786018115760154496775 9814179027173640231745163)
                ·
                  refine ⟨14721268540760460347617745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9814179027173640231745163 14721268540760460347617745)
                  ·
                    refine ⟨11040951405570345260713309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14721268540760460347617745 11040951405570345260713309)
                    ·
                      refine ⟨4140356777088879472767491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11040951405570345260713309 4140356777088879472767491)
                      ·
                        rfl

theorem cell23_8063316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_8063316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063316 prefixEnd_8063316 := by exact prefixLift 8063316
  have htrace : WordTrace (prefixWord ++ tailWord_8063316) baseStart_8063316 baseEnd_8063316 := by
    simpa [prefixWord, tailWord_8063316, baseEnd_8063316] using wordTrace_append hprefix tailTrace_8063316
  have hstable : (prefixWord ++ tailWord_8063316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063316).length < 2 ^ (prefixWord ++ tailWord_8063316).sum := by decide
  have hdescent : baseEnd_8063316 < baseStart_8063316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063372 : List Nat := [2, 2, 1, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_8063372 : Nat := 118140960795 + 8063372 * 2 ^ 59
def prefixEnd_8063372 : Nat := 4983230072969 + 3 ^ 40 * 8063372 * 2
def baseEnd_8063372 : Nat := 4140385532005531253667233

theorem tailTrace_8063372 : CollatzResearch.WordTrace tailWord_8063372 prefixEnd_8063372 4140385532005531253667233 := by
  unfold tailWord_8063372
  simp only [CollatzResearch.WordTrace]
  refine ⟨147047668871893916572520185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196063558495858555430026913 147047668871893916572520185)
  ·
    refine ⟨110285751653920437429390139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147047668871893916572520185 110285751653920437429390139)
    ·
      refine ⟨165428627480880656144085209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110285751653920437429390139 165428627480880656144085209)
      ·
        refine ⟨124071470610660492108063907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165428627480880656144085209 124071470610660492108063907)
        ·
          refine ⟨186107205915990738162095861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124071470610660492108063907 186107205915990738162095861)
          ·
            refine ⟨17447550554624131702696487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186107205915990738162095861 17447550554624131702696487)
            ·
              refine ⟨26171325831936197554044731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17447550554624131702696487 26171325831936197554044731)
              ·
                refine ⟨39256988747904296331067097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26171325831936197554044731 39256988747904296331067097)
                ·
                  refine ⟨29442741560928222248300323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39256988747904296331067097 29442741560928222248300323)
                  ·
                    refine ⟨44164112341392333372450485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29442741560928222248300323 44164112341392333372450485)
                    ·
                      refine ⟨4140385532005531253667233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44164112341392333372450485 4140385532005531253667233)
                      ·
                        rfl

theorem cell23_8063372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_8063372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063372 prefixEnd_8063372 := by exact prefixLift 8063372
  have htrace : WordTrace (prefixWord ++ tailWord_8063372) baseStart_8063372 baseEnd_8063372 := by
    simpa [prefixWord, tailWord_8063372, baseEnd_8063372] using wordTrace_append hprefix tailTrace_8063372
  have hstable : (prefixWord ++ tailWord_8063372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063372).length < 2 ^ (prefixWord ++ tailWord_8063372).sum := by decide
  have hdescent : baseEnd_8063372 < baseStart_8063372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063385 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 7]
def baseStart_8063385 : Nat := 118140960795 + 8063385 * 2 ^ 59
def prefixEnd_8063385 : Nat := 4983230072969 + 3 ^ 40 * 8063385 * 2
def baseEnd_8063385 : Nat := 4140392207254039702804673

theorem tailTrace_8063385 : CollatzResearch.WordTrace tailWord_8063385 prefixEnd_8063385 4140392207254039702804673 := by
  unfold tailWord_8063385
  simp only [CollatzResearch.WordTrace]
  refine ⟨294095811892740736365263609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196063874595160490910175739 294095811892740736365263609)
  ·
    refine ⟨220571858919555552273947707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294095811892740736365263609 220571858919555552273947707)
    ·
      refine ⟨330857788379333328410921561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220571858919555552273947707 330857788379333328410921561)
      ·
        refine ⟨248143341284499996308191171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330857788379333328410921561 248143341284499996308191171)
        ·
          refine ⟨372215011926749994462286757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248143341284499996308191171 372215011926749994462286757)
          ·
            refine ⟨69790314736265623961678767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372215011926749994462286757 69790314736265623961678767)
            ·
              refine ⟨104685472104398435942518151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69790314736265623961678767 104685472104398435942518151)
              ·
                refine ⟨157028208156597653913777227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104685472104398435942518151 157028208156597653913777227)
                ·
                  refine ⟨235542312234896480870665841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157028208156597653913777227 235542312234896480870665841)
                  ·
                    refine ⟨176656734176172360652999381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 235542312234896480870665841 176656734176172360652999381)
                    ·
                      refine ⟨4140392207254039702804673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176656734176172360652999381 4140392207254039702804673)
                      ·
                        rfl

theorem cell23_8063385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_8063385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063385 prefixEnd_8063385 := by exact prefixLift 8063385
  have htrace : WordTrace (prefixWord ++ tailWord_8063385) baseStart_8063385 baseEnd_8063385 := by
    simpa [prefixWord, tailWord_8063385, baseEnd_8063385] using wordTrace_append hprefix tailTrace_8063385
  have hstable : (prefixWord ++ tailWord_8063385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063385).length < 2 ^ (prefixWord ++ tailWord_8063385).sum := by decide
  have hdescent : baseEnd_8063385 < baseStart_8063385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063386 : List Nat := [3, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2]
def baseStart_8063386 : Nat := 118140960795 + 8063386 * 2 ^ 59
def prefixEnd_8063386 : Nat := 4983230072969 + 3 ^ 40 * 8063386 * 2
def baseEnd_8063386 : Nat := 4140392720734694198892169

theorem tailTrace_8063386 : CollatzResearch.WordTrace tailWord_8063386 prefixEnd_8063386 4140392720734694198892169 := by
  unfold tailWord_8063386
  simp only [CollatzResearch.WordTrace]
  refine ⟨73523962091434278384012503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196063898910491409024033341 73523962091434278384012503)
  ·
    refine ⟨110285943137151417576018755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73523962091434278384012503 110285943137151417576018755)
    ·
      refine ⟨165428914705727126364028133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110285943137151417576018755 165428914705727126364028133)
      ·
        refine ⟨31017921507323836193255275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165428914705727126364028133 31017921507323836193255275)
        ·
          refine ⟨46526882260985754289882913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31017921507323836193255275 46526882260985754289882913)
          ·
            refine ⟨34895161695739315717412185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46526882260985754289882913 34895161695739315717412185)
            ·
              refine ⟨26171371271804486788059139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34895161695739315717412185 26171371271804486788059139)
              ·
                refine ⟨39257056907706730182088709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26171371271804486788059139 39257056907706730182088709)
                ·
                  refine ⟨7360698170195011909141633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39257056907706730182088709 7360698170195011909141633)
                  ·
                    refine ⟨5520523627646258931856225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7360698170195011909141633 5520523627646258931856225)
                    ·
                      refine ⟨4140392720734694198892169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520523627646258931856225 4140392720734694198892169)
                      ·
                        rfl

theorem cell23_8063386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_8063386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063386 prefixEnd_8063386 := by exact prefixLift 8063386
  have htrace : WordTrace (prefixWord ++ tailWord_8063386) baseStart_8063386 baseEnd_8063386 := by
    simpa [prefixWord, tailWord_8063386, baseEnd_8063386] using wordTrace_append hprefix tailTrace_8063386
  have hstable : (prefixWord ++ tailWord_8063386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063386).length < 2 ^ (prefixWord ++ tailWord_8063386).sum := by decide
  have hdescent : baseEnd_8063386 < baseStart_8063386 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063392 : List Nat := [2, 1, 1, 4, 1, 3, 3, 1, 7]
def baseStart_8063392 : Nat := 118140960795 + 8063392 * 2 ^ 59
def prefixEnd_8063392 : Nat := 4983230072969 + 3 ^ 40 * 8063392 * 2
def baseEnd_8063392 : Nat := 460043977957624575046349

theorem tailTrace_8063392 : CollatzResearch.WordTrace tailWord_8063392 prefixEnd_8063392 460043977957624575046349 := by
  unfold tailWord_8063392
  simp only [CollatzResearch.WordTrace]
  refine ⟨147048033601857688280384215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196064044802476917707178953 147048033601857688280384215)
  ·
    refine ⟨220572050402786532420576323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147048033601857688280384215 220572050402786532420576323)
    ·
      refine ⟨330858075604179798630864485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220572050402786532420576323 330858075604179798630864485)
      ·
        refine ⟨62035889175783712243287091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330858075604179798630864485 62035889175783712243287091)
        ·
          refine ⟨93053833763675568364930637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62035889175783712243287091 93053833763675568364930637)
          ·
            refine ⟨34895187661378338136848989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93053833763675568364930637 34895187661378338136848989)
            ·
              refine ⟨13085695373016876801318371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34895187661378338136848989 13085695373016876801318371)
              ·
                refine ⟨19628543059525315201977557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13085695373016876801318371 19628543059525315201977557)
                ·
                  refine ⟨460043977957624575046349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19628543059525315201977557 460043977957624575046349)
                  ·
                    rfl

theorem cell23_8063392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 1, 7].length) (baseStart_8063392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063392 prefixEnd_8063392 := by exact prefixLift 8063392
  have htrace : WordTrace (prefixWord ++ tailWord_8063392) baseStart_8063392 baseEnd_8063392 := by
    simpa [prefixWord, tailWord_8063392, baseEnd_8063392] using wordTrace_append hprefix tailTrace_8063392
  have hstable : (prefixWord ++ tailWord_8063392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063392).length < 2 ^ (prefixWord ++ tailWord_8063392).sum := by decide
  have hdescent : baseEnd_8063392 < baseStart_8063392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063422 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 1, 7]
def baseStart_8063422 : Nat := 118140960795 + 8063422 * 2 ^ 59
def prefixEnd_8063422 : Nat := 4983230072969 + 3 ^ 40 * 8063422 * 2
def baseEnd_8063422 : Nat := 1380137068679418686014001

theorem tailTrace_8063422 : CollatzResearch.WordTrace tailWord_8063422 prefixEnd_8063422 1380137068679418686014001 := by
  unfold tailWord_8063422
  simp only [CollatzResearch.WordTrace]
  refine ⟨36762145174200836460545065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196064774262404461122907013 36762145174200836460545065)
  ·
    refine ⟨27571608880650627345408799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36762145174200836460545065 27571608880650627345408799)
    ·
      refine ⟨41357413320975941018113199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27571608880650627345408799 41357413320975941018113199)
      ·
        refine ⟨62036119981463911527169799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41357413320975941018113199 62036119981463911527169799)
        ·
          refine ⟨93054179972195867290754699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62036119981463911527169799 93054179972195867290754699)
          ·
            refine ⟨139581269958293800936132049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93054179972195867290754699 139581269958293800936132049)
            ·
              refine ⟨104685952468720350702099037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139581269958293800936132049 104685952468720350702099037)
              ·
                refine ⟨39257232175770131513287139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104685952468720350702099037 39257232175770131513287139)
                ·
                  refine ⟨58885848263655197269930709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39257232175770131513287139 58885848263655197269930709)
                  ·
                    refine ⟨1380137068679418686014001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58885848263655197269930709 1380137068679418686014001)
                    ·
                      rfl

theorem cell23_8063422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_8063422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063422 prefixEnd_8063422 := by exact prefixLift 8063422
  have htrace : WordTrace (prefixWord ++ tailWord_8063422) baseStart_8063422 baseEnd_8063422 := by
    simpa [prefixWord, tailWord_8063422, baseEnd_8063422] using wordTrace_append hprefix tailTrace_8063422
  have hstable : (prefixWord ++ tailWord_8063422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063422).length < 2 ^ (prefixWord ++ tailWord_8063422).sum := by decide
  have hdescent : baseEnd_8063422 < baseStart_8063422 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063432 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_8063432 : Nat := 118140960795 + 8063432 * 2 ^ 59
def prefixEnd_8063432 : Nat := 4983230072969 + 3 ^ 40 * 8063432 * 2
def baseEnd_8063432 : Nat := 4140416340844801018916957

theorem tailTrace_8063432 : CollatzResearch.WordTrace tailWord_8063432 prefixEnd_8063432 4140416340844801018916957 := by
  unfold tailWord_8063432
  simp only [CollatzResearch.WordTrace]
  refine ⟨147048763061785231696112275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196065017415713642261483033 147048763061785231696112275)
  ·
    refine ⟨220573144592677847544168413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147048763061785231696112275 220573144592677847544168413)
    ·
      refine ⟨82714929222254192829063155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220573144592677847544168413 82714929222254192829063155)
      ·
        refine ⟨124072393833381289243594733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82714929222254192829063155 124072393833381289243594733)
        ·
          refine ⟨46527147687517983466348025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124072393833381289243594733 46527147687517983466348025)
          ·
            refine ⟨34895360765638487599761019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46527147687517983466348025 34895360765638487599761019)
            ·
              refine ⟨52343041148457731399641529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34895360765638487599761019 52343041148457731399641529)
              ·
                refine ⟨39257280861343298549731147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52343041148457731399641529 39257280861343298549731147)
                ·
                  refine ⟨58885921292014947824596721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39257280861343298549731147 58885921292014947824596721)
                  ·
                    refine ⟨44164440969011210868447541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58885921292014947824596721 44164440969011210868447541)
                    ·
                      refine ⟨4140416340844801018916957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44164440969011210868447541 4140416340844801018916957)
                      ·
                        rfl

theorem cell23_8063432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_8063432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063432 prefixEnd_8063432 := by exact prefixLift 8063432
  have htrace : WordTrace (prefixWord ++ tailWord_8063432) baseStart_8063432 baseEnd_8063432 := by
    simpa [prefixWord, tailWord_8063432, baseEnd_8063432] using wordTrace_append hprefix tailTrace_8063432
  have hstable : (prefixWord ++ tailWord_8063432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063432).length < 2 ^ (prefixWord ++ tailWord_8063432).sum := by decide
  have hdescent : baseEnd_8063432 < baseStart_8063432 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063446 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_8063446 : Nat := 118140960795 + 8063446 * 2 ^ 59
def prefixEnd_8063446 : Nat := 4983230072969 + 3 ^ 40 * 8063446 * 2
def baseEnd_8063446 : Nat := 4140423529573963964141893

theorem tailTrace_8063446 : CollatzResearch.WordTrace tailWord_8063446 prefixEnd_8063446 4140423529573963964141893 := by
  unfold tailWord_8063446
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381127296594983986452137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196065357830346495855489461 18381127296594983986452137)
  ·
    refine ⟨13785845472446237989839103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18381127296594983986452137 13785845472446237989839103)
    ·
      refine ⟨20678768208669356984758655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13785845472446237989839103 20678768208669356984758655)
      ·
        refine ⟨31018152313004035477137983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20678768208669356984758655 31018152313004035477137983)
        ·
          refine ⟨46527228469506053215706975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31018152313004035477137983 46527228469506053215706975)
          ·
            refine ⟨69790842704259079823560463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46527228469506053215706975 69790842704259079823560463)
            ·
              refine ⟨104686264056388619735340695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69790842704259079823560463 104686264056388619735340695)
              ·
                refine ⟨157029396084582929603011043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104686264056388619735340695 157029396084582929603011043)
                ·
                  refine ⟨235544094126874394404516565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157029396084582929603011043 235544094126874394404516565)
                  ·
                    refine ⟨5520564706098618618855857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 235544094126874394404516565 5520564706098618618855857)
                    ·
                      refine ⟨4140423529573963964141893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520564706098618618855857 4140423529573963964141893)
                      ·
                        rfl

theorem cell23_8063446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_8063446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063446 prefixEnd_8063446 := by exact prefixLift 8063446
  have htrace : WordTrace (prefixWord ++ tailWord_8063446) baseStart_8063446 baseEnd_8063446 := by
    simpa [prefixWord, tailWord_8063446, baseEnd_8063446] using wordTrace_append hprefix tailTrace_8063446
  have hstable : (prefixWord ++ tailWord_8063446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063446).length < 2 ^ (prefixWord ++ tailWord_8063446).sum := by decide
  have hdescent : baseEnd_8063446 < baseStart_8063446 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063499 : List Nat := [1, 1, 1, 1, 7, 1, 3, 2, 6]
def baseStart_8063499 : Nat := 118140960795 + 8063499 * 2 ^ 59
def prefixEnd_8063499 : Nat := 4983230072969 + 3 ^ 40 * 8063499 * 2
def baseEnd_8063499 : Nat := 460050082672072472975461

theorem tailTrace_8063499 : CollatzResearch.WordTrace tailWord_8063499 prefixEnd_8063499 460050082672072472975461 := by
  unfold tailWord_8063499
  simp only [CollatzResearch.WordTrace]
  refine ⟨294099969814327733834913551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196066646542885155889942367 294099969814327733834913551)
  ·
    refine ⟨441149954721491600752370327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294099969814327733834913551 441149954721491600752370327)
    ·
      refine ⟨661724932082237401128555491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441149954721491600752370327 661724932082237401128555491)
      ·
        refine ⟨992587398123356101692833237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661724932082237401128555491 992587398123356101692833237)
        ·
          refine ⟨23263767143516158633425779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 992587398123356101692833237 23263767143516158633425779)
          ·
            refine ⟨34895650715274237950138669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23263767143516158633425779 34895650715274237950138669)
            ·
              refine ⟨13085869018227839231302001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34895650715274237950138669 13085869018227839231302001)
              ·
                refine ⟨9814401763670879423476501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13085869018227839231302001 9814401763670879423476501)
                ·
                  refine ⟨460050082672072472975461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9814401763670879423476501 460050082672072472975461)
                  ·
                    rfl

theorem cell23_8063499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 3, 2, 6].length) (baseStart_8063499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063499 prefixEnd_8063499 := by exact prefixLift 8063499
  have htrace : WordTrace (prefixWord ++ tailWord_8063499) baseStart_8063499 baseEnd_8063499 := by
    simpa [prefixWord, tailWord_8063499, baseEnd_8063499] using wordTrace_append hprefix tailTrace_8063499
  have hstable : (prefixWord ++ tailWord_8063499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063499).length < 2 ^ (prefixWord ++ tailWord_8063499).sum := by decide
  have hdescent : baseEnd_8063499 < baseStart_8063499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063516 : List Nat := [2, 2, 3, 1, 2, 3, 3, 1, 6]
def baseStart_8063516 : Nat := 118140960795 + 8063516 * 2 ^ 59
def prefixEnd_8063516 : Nat := 4983230072969 + 3 ^ 40 * 8063516 * 2
def baseEnd_8063516 : Nat := 460051052579975410029619

theorem tailTrace_8063516 : CollatzResearch.WordTrace tailWord_8063516 prefixEnd_8063516 460051052579975410029619 := by
  unfold tailWord_8063516
  simp only [CollatzResearch.WordTrace]
  refine ⟨147050294927633072869141201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196067059903510763825521601 147050294927633072869141201)
  ·
    refine ⟨110287721195724804651855901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147050294927633072869141201 110287721195724804651855901)
    ·
      refine ⟨41357895448396801744445963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110287721195724804651855901 41357895448396801744445963)
      ·
        refine ⟨62036843172595202616668945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41357895448396801744445963 62036843172595202616668945)
        ·
          refine ⟨46527632379446401962501709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62036843172595202616668945 46527632379446401962501709)
          ·
            refine ⟨17447862142292400735938141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46527632379446401962501709 17447862142292400735938141)
            ·
              refine ⟨6542948303359650275976803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17447862142292400735938141 6542948303359650275976803)
              ·
                refine ⟨9814422455039475413965205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6542948303359650275976803 9814422455039475413965205)
                ·
                  refine ⟨460051052579975410029619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9814422455039475413965205 460051052579975410029619)
                  ·
                    rfl

theorem cell23_8063516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_8063516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063516 prefixEnd_8063516 := by exact prefixLift 8063516
  have htrace : WordTrace (prefixWord ++ tailWord_8063516) baseStart_8063516 baseEnd_8063516 := by
    simpa [prefixWord, tailWord_8063516, baseEnd_8063516] using wordTrace_append hprefix tailTrace_8063516
  have hstable : (prefixWord ++ tailWord_8063516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063516).length < 2 ^ (prefixWord ++ tailWord_8063516).sum := by decide
  have hdescent : baseEnd_8063516 < baseStart_8063516 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063532 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_8063532 : Nat := 118140960795 + 8063532 * 2 ^ 59
def prefixEnd_8063532 : Nat := 4983230072969 + 3 ^ 40 * 8063532 * 2
def baseEnd_8063532 : Nat := 4140467688910250627666497

theorem tailTrace_8063532 : CollatzResearch.WordTrace tailWord_8063532 prefixEnd_8063532 4140467688910250627666497 := by
  unfold tailWord_8063532
  simp only [CollatzResearch.WordTrace]
  refine ⟨147050586711604090235432425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196067448948805453647243233 147050586711604090235432425)
  ·
    refine ⟨110287940033703067676574319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147050586711604090235432425 110287940033703067676574319)
    ·
      refine ⟨165431910050554601514861479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110287940033703067676574319 165431910050554601514861479)
      ·
        refine ⟨248147865075831902272292219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165431910050554601514861479 248147865075831902272292219)
        ·
          refine ⟨372221797613747853408438329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248147865075831902272292219 372221797613747853408438329)
          ·
            refine ⟨279166348210310890056328747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372221797613747853408438329 279166348210310890056328747)
            ·
              refine ⟨418749522315466335084493121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279166348210310890056328747 418749522315466335084493121)
              ·
                refine ⟨314062141736599751313369841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418749522315466335084493121 314062141736599751313369841)
                ·
                  refine ⟨235546606302449813485027381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314062141736599751313369841 235546606302449813485027381)
                  ·
                    refine ⟨22082494340854670014221317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 235546606302449813485027381 22082494340854670014221317)
                    ·
                      refine ⟨4140467688910250627666497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22082494340854670014221317 4140467688910250627666497)
                      ·
                        rfl

theorem cell23_8063532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_8063532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063532 prefixEnd_8063532 := by exact prefixLift 8063532
  have htrace : WordTrace (prefixWord ++ tailWord_8063532) baseStart_8063532 baseEnd_8063532 := by
    simpa [prefixWord, tailWord_8063532, baseEnd_8063532] using wordTrace_append hprefix tailTrace_8063532
  have hstable : (prefixWord ++ tailWord_8063532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063532).length < 2 ^ (prefixWord ++ tailWord_8063532).sum := by decide
  have hdescent : baseEnd_8063532 < baseStart_8063532 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063553 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 2, 3, 2]
def baseStart_8063553 : Nat := 118140960795 + 8063553 * 2 ^ 59
def prefixEnd_8063553 : Nat := 4983230072969 + 3 ^ 40 * 8063553 * 2
def baseEnd_8063553 : Nat := 4140478472003995045503901

theorem tailTrace_8063553 : CollatzResearch.WordTrace tailWord_8063553 prefixEnd_8063553 4140478472003995045503901 := by
  unfold tailWord_8063553
  simp only [CollatzResearch.WordTrace]
  refine ⟨294101939356132101057379313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196067959570754734038252875 294101939356132101057379313)
  ·
    refine ⟨220576454517099075793034485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294101939356132101057379313 220576454517099075793034485)
    ·
      refine ⟨20679042610978038355596983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220576454517099075793034485 20679042610978038355596983)
      ·
        refine ⟨31018563916467057533395475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20679042610978038355596983 31018563916467057533395475)
        ·
          refine ⟨46527845874700586300093213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31018563916467057533395475 46527845874700586300093213)
          ·
            refine ⟨17447942203012719862534955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46527845874700586300093213 17447942203012719862534955)
            ·
              refine ⟨26171913304519079793802433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17447942203012719862534955 26171913304519079793802433)
              ·
                refine ⟨19628934978389309845351825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26171913304519079793802433 19628934978389309845351825)
                ·
                  refine ⟨14721701233791982384013869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19628934978389309845351825 14721701233791982384013869)
                  ·
                    refine ⟨5520637962671993394005201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14721701233791982384013869 5520637962671993394005201)
                    ·
                      refine ⟨4140478472003995045503901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520637962671993394005201 4140478472003995045503901)
                      ·
                        rfl

theorem cell23_8063553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 3, 2].length) (baseStart_8063553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063553 prefixEnd_8063553 := by exact prefixLift 8063553
  have htrace : WordTrace (prefixWord ++ tailWord_8063553) baseStart_8063553 baseEnd_8063553 := by
    simpa [prefixWord, tailWord_8063553, baseEnd_8063553] using wordTrace_append hprefix tailTrace_8063553
  have hstable : (prefixWord ++ tailWord_8063553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063553).length < 2 ^ (prefixWord ++ tailWord_8063553).sum := by decide
  have hdescent : baseEnd_8063553 < baseStart_8063553 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063569 : List Nat := [1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 5]
def baseStart_8063569 : Nat := 118140960795 + 8063569 * 2 ^ 59
def prefixEnd_8063569 : Nat := 4983230072969 + 3 ^ 40 * 8063569 * 2
def baseEnd_8063569 : Nat := 4140486687694466982903827

theorem tailTrace_8063569 : CollatzResearch.WordTrace tailWord_8063569 prefixEnd_8063569 4140486687694466982903827 := by
  unfold tailWord_8063569
  simp only [CollatzResearch.WordTrace]
  refine ⟨294102522924074135789961761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196068348616049423859974507 294102522924074135789961761)
  ·
    refine ⟨220576892193055601842471321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294102522924074135789961761 220576892193055601842471321)
    ·
      refine ⟨165432669144791701381853491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220576892193055601842471321 165432669144791701381853491)
      ·
        refine ⟨248149003717187552072780237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165432669144791701381853491 248149003717187552072780237)
        ·
          refine ⟨93055876393945332027292589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 248149003717187552072780237 93055876393945332027292589)
          ·
            refine ⟨34895953647729499510234721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93055876393945332027292589 34895953647729499510234721)
            ·
              refine ⟨26171965235797124632676041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34895953647729499510234721 26171965235797124632676041)
              ·
                refine ⟨19628973926847843474507031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26171965235797124632676041 19628973926847843474507031)
                ·
                  refine ⟨29443460890271765211760547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19628973926847843474507031 29443460890271765211760547)
                  ·
                    refine ⟨44165191335407647817640821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29443460890271765211760547 44165191335407647817640821)
                    ·
                      refine ⟨4140486687694466982903827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44165191335407647817640821 4140486687694466982903827)
                      ·
                        rfl

theorem cell23_8063569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 2, 1, 1, 5].length) (baseStart_8063569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063569 prefixEnd_8063569 := by exact prefixLift 8063569
  have htrace : WordTrace (prefixWord ++ tailWord_8063569) baseStart_8063569 baseEnd_8063569 := by
    simpa [prefixWord, tailWord_8063569, baseEnd_8063569] using wordTrace_append hprefix tailTrace_8063569
  have hstable : (prefixWord ++ tailWord_8063569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063569).length < 2 ^ (prefixWord ++ tailWord_8063569).sum := by decide
  have hdescent : baseEnd_8063569 < baseStart_8063569 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063580 : List Nat := [2, 2, 4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_8063580 : Nat := 118140960795 + 8063580 * 2 ^ 59
def prefixEnd_8063580 : Nat := 4983230072969 + 3 ^ 40 * 8063580 * 2
def baseEnd_8063580 : Nat := 1380164111993888813288759

theorem tailTrace_8063580 : CollatzResearch.WordTrace tailWord_8063580 prefixEnd_8063580 1380164111993888813288759 := by
  unfold tailWord_8063580
  simp only [CollatzResearch.WordTrace]
  refine ⟨147051462063517142334306097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196068616084689523112408129 147051462063517142334306097)
  ·
    refine ⟨110288596547637856750729573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147051462063517142334306097 110288596547637856750729573)
    ·
      refine ⟨20679111852682098140761795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110288596547637856750729573 20679111852682098140761795)
      ·
        refine ⟨31018667779023147211142693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20679111852682098140761795 31018667779023147211142693)
        ·
          refine ⟨5816000208566840102089255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31018667779023147211142693 5816000208566840102089255)
          ·
            refine ⟨8724000312850260153133883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5816000208566840102089255 8724000312850260153133883)
            ·
              refine ⟨13086000469275390229700825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8724000312850260153133883 13086000469275390229700825)
              ·
                refine ⟨9814500351956542672275619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13086000469275390229700825 9814500351956542672275619)
                ·
                  refine ⟨14721750527934814008413429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9814500351956542672275619 14721750527934814008413429)
                  ·
                    refine ⟨1380164111993888813288759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14721750527934814008413429 1380164111993888813288759)
                    ·
                      rfl

theorem cell23_8063580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_8063580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063580 prefixEnd_8063580 := by exact prefixLift 8063580
  have htrace : WordTrace (prefixWord ++ tailWord_8063580) baseStart_8063580 baseEnd_8063580 := by
    simpa [prefixWord, tailWord_8063580, baseEnd_8063580] using wordTrace_append hprefix tailTrace_8063580
  have hstable : (prefixWord ++ tailWord_8063580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063580).length < 2 ^ (prefixWord ++ tailWord_8063580).sum := by decide
  have hdescent : baseEnd_8063580 < baseStart_8063580 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063599 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 3]
def baseStart_8063599 : Nat := 118140960795 + 8063599 * 2 ^ 59
def prefixEnd_8063599 : Nat := 4983230072969 + 3 ^ 40 * 8063599 * 2
def baseEnd_8063599 : Nat := 4140502092114101865528689

theorem tailTrace_8063599 : CollatzResearch.WordTrace tailWord_8063599 prefixEnd_8063599 4140502092114101865528689 := by
  unfold tailWord_8063599
  simp only [CollatzResearch.WordTrace]
  refine ⟨294103617113965450913553851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196069078075976967275702567 294103617113965450913553851)
  ·
    refine ⟨441155425670948176370330777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294103617113965450913553851 441155425670948176370330777)
    ·
      refine ⟨330866569253211132277748083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441155425670948176370330777 330866569253211132277748083)
      ·
        refine ⟨496299853879816698416622125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330866569253211132277748083 496299853879816698416622125)
        ·
          refine ⟨186112445204931261906233297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496299853879816698416622125 186112445204931261906233297)
          ·
            refine ⟨139584333903698446429674973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186112445204931261906233297 139584333903698446429674973)
            ·
              refine ⟨52344125213886917411128115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139584333903698446429674973 52344125213886917411128115)
              ·
                refine ⟨78516187820830376116692173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52344125213886917411128115 78516187820830376116692173)
                ·
                  refine ⟨29443570432811391043759565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78516187820830376116692173 29443570432811391043759565)
                  ·
                    refine ⟨11041338912304271641409837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29443570432811391043759565 11041338912304271641409837)
                    ·
                      refine ⟨4140502092114101865528689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11041338912304271641409837 4140502092114101865528689)
                      ·
                        rfl

theorem cell23_8063599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_8063599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063599 prefixEnd_8063599 := by exact prefixLift 8063599
  have htrace : WordTrace (prefixWord ++ tailWord_8063599) baseStart_8063599 baseEnd_8063599 := by
    simpa [prefixWord, tailWord_8063599, baseEnd_8063599] using wordTrace_append hprefix tailTrace_8063599
  have hstable : (prefixWord ++ tailWord_8063599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063599).length < 2 ^ (prefixWord ++ tailWord_8063599).sum := by decide
  have hdescent : baseEnd_8063599 < baseStart_8063599 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063606 : List Nat := [5, 1, 1, 2, 4, 10]
def baseStart_8063606 : Nat := 118140960795 + 8063606 * 2 ^ 59
def prefixEnd_8063606 : Nat := 4983230072969 + 3 ^ 40 * 8063606 * 2
def baseEnd_8063606 : Nat := 17039118051352606329799

theorem tailTrace_8063606 : CollatzResearch.WordTrace tailWord_8063606 prefixEnd_8063606 17039118051352606329799 := by
  unfold tailWord_8063606
  simp only [CollatzResearch.WordTrace]
  refine ⟨18381492026558755694316167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196069248283293394072705781 18381492026558755694316167)
  ·
    refine ⟨27572238039838133541474251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18381492026558755694316167 27572238039838133541474251)
    ·
      refine ⟨41358357059757200312211377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27572238039838133541474251 41358357059757200312211377)
      ·
        refine ⟨31018767794817900234158533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41358357059757200312211377 31018767794817900234158533)
        ·
          refine ⟨5816018961528356293904725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31018767794817900234158533 5816018961528356293904725)
          ·
            refine ⟨17039118051352606329799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5816018961528356293904725 17039118051352606329799)
            ·
              rfl

theorem cell23_8063606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 10].length) (baseStart_8063606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063606 prefixEnd_8063606 := by exact prefixLift 8063606
  have htrace : WordTrace (prefixWord ++ tailWord_8063606) baseStart_8063606 baseEnd_8063606 := by
    simpa [prefixWord, tailWord_8063606, baseEnd_8063606] using wordTrace_append hprefix tailTrace_8063606
  have hstable : (prefixWord ++ tailWord_8063606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063606).length < 2 ^ (prefixWord ++ tailWord_8063606).sum := by decide
  have hdescent : baseEnd_8063606 < baseStart_8063606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063639 : List Nat := [1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_8063639 : Nat := 118140960795 + 8063639 * 2 ^ 59
def prefixEnd_8063639 : Nat := 4983230072969 + 3 ^ 40 * 8063639 * 2
def baseEnd_8063639 : Nat := 4140522631340281709028505

theorem tailTrace_8063639 : CollatzResearch.WordTrace tailWord_8063639 prefixEnd_8063639 4140522631340281709028505 := by
  unfold tailWord_8063639
  simp only [CollatzResearch.WordTrace]
  refine ⟨294105076033820537745009971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196070050689213691830006647 294105076033820537745009971)
  ·
    refine ⟨441157614050730806617514957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294105076033820537745009971 441157614050730806617514957)
    ·
      refine ⟨165434105269024052481568109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441157614050730806617514957 165434105269024052481568109)
      ·
        refine ⟨62037789475884019680588041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165434105269024052481568109 62037789475884019680588041)
        ·
          refine ⟨46528342106913014760441031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62037789475884019680588041 46528342106913014760441031)
          ·
            refine ⟨69792513160369522140661547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46528342106913014760441031 69792513160369522140661547)
            ·
              refine ⟨104688769740554283210992321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69792513160369522140661547 104688769740554283210992321)
              ·
                refine ⟨78516577305415712408244241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104688769740554283210992321 78516577305415712408244241)
                ·
                  refine ⟨58887432979061784306183181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78516577305415712408244241 58887432979061784306183181)
                  ·
                    refine ⟨22082787367148169114818693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58887432979061784306183181 22082787367148169114818693)
                    ·
                      refine ⟨4140522631340281709028505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22082787367148169114818693 4140522631340281709028505)
                      ·
                        rfl

theorem cell23_8063639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_8063639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063639 prefixEnd_8063639 := by exact prefixLift 8063639
  have htrace : WordTrace (prefixWord ++ tailWord_8063639) baseStart_8063639 baseEnd_8063639 := by
    simpa [prefixWord, tailWord_8063639, baseEnd_8063639] using wordTrace_append hprefix tailTrace_8063639
  have hstable : (prefixWord ++ tailWord_8063639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063639).length < 2 ^ (prefixWord ++ tailWord_8063639).sum := by decide
  have hdescent : baseEnd_8063639 < baseStart_8063639 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063646 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_8063646 : Nat := 118140960795 + 8063646 * 2 ^ 59
def prefixEnd_8063646 : Nat := 4983230072969 + 3 ^ 40 * 8063646 * 2
def baseEnd_8063646 : Nat := 4140526225704863181640973

theorem tailTrace_8063646 : CollatzResearch.WordTrace tailWord_8063646 prefixEnd_8063646 4140526225704863181640973 := by
  unfold tailWord_8063646
  simp only [CollatzResearch.WordTrace]
  refine ⟨36763166418099397242564349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196070220896530118627009861 36763166418099397242564349)
  ·
    refine ⟨13786187406787273965961631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 36763166418099397242564349 13786187406787273965961631)
    ·
      refine ⟨20679281110180910948942447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13786187406787273965961631 20679281110180910948942447)
      ·
        refine ⟨31018921665271366423413671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20679281110180910948942447 31018921665271366423413671)
        ·
          refine ⟨46528382497907049635120507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31018921665271366423413671 46528382497907049635120507)
          ·
            refine ⟨69792573746860574452680761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46528382497907049635120507 69792573746860574452680761)
            ·
              refine ⟨52344430310145430839510571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69792573746860574452680761 52344430310145430839510571)
              ·
                refine ⟨78516645465218146259265857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52344430310145430839510571 78516645465218146259265857)
                ·
                  refine ⟨58887484098913609694449393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78516645465218146259265857 58887484098913609694449393)
                  ·
                    refine ⟨44165613074185207270837045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58887484098913609694449393 44165613074185207270837045)
                    ·
                      refine ⟨4140526225704863181640973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44165613074185207270837045 4140526225704863181640973)
                      ·
                        rfl

theorem cell23_8063646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_8063646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063646 prefixEnd_8063646 := by exact prefixLift 8063646
  have htrace : WordTrace (prefixWord ++ tailWord_8063646) baseStart_8063646 baseEnd_8063646 := by
    simpa [prefixWord, tailWord_8063646, baseEnd_8063646] using wordTrace_append hprefix tailTrace_8063646
  have hstable : (prefixWord ++ tailWord_8063646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063646).length < 2 ^ (prefixWord ++ tailWord_8063646).sum := by decide
  have hdescent : baseEnd_8063646 < baseStart_8063646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063679 : List Nat := [1, 1, 2, 2, 2, 4, 1, 3, 7]
def baseStart_8063679 : Nat := 118140960795 + 8063679 * 2 ^ 59
def prefixEnd_8063679 : Nat := 4983230072969 + 3 ^ 40 * 8063679 * 2
def baseEnd_8063679 : Nat := 460060352285162394725369

theorem tailTrace_8063679 : CollatzResearch.WordTrace tailWord_8063679 prefixEnd_8063679 460060352285162394725369 := by
  unfold tailWord_8063679
  simp only [CollatzResearch.WordTrace]
  refine ⟨294106534953675624576466091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196071023302450416384310727 294106534953675624576466091)
  ·
    refine ⟨441159802430513436864699137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294106534953675624576466091 441159802430513436864699137)
    ·
      refine ⟨330869851822885077648524353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441159802430513436864699137 330869851822885077648524353)
      ·
        refine ⟨248152388867163808236393265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330869851822885077648524353 248152388867163808236393265)
        ·
          refine ⟨186114291650372856177294949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248152388867163808236393265 186114291650372856177294949)
          ·
            refine ⟨34896429684444910533242803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186114291650372856177294949 34896429684444910533242803)
            ·
              refine ⟨52344644526667365799864205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34896429684444910533242803 52344644526667365799864205)
              ·
                refine ⟨19629241697500262174949077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52344644526667365799864205 19629241697500262174949077)
                ·
                  refine ⟨460060352285162394725369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19629241697500262174949077 460060352285162394725369)
                  ·
                    rfl

theorem cell23_8063679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 3, 7].length) (baseStart_8063679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063679 prefixEnd_8063679 := by exact prefixLift 8063679
  have htrace : WordTrace (prefixWord ++ tailWord_8063679) baseStart_8063679 baseEnd_8063679 := by
    simpa [prefixWord, tailWord_8063679, baseEnd_8063679] using wordTrace_append hprefix tailTrace_8063679
  have hstable : (prefixWord ++ tailWord_8063679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063679).length < 2 ^ (prefixWord ++ tailWord_8063679).sum := by decide
  have hdescent : baseEnd_8063679 < baseStart_8063679 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063690 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2]
def baseStart_8063690 : Nat := 118140960795 + 8063690 * 2 ^ 59
def prefixEnd_8063690 : Nat := 4983230072969 + 3 ^ 40 * 8063690 * 2
def baseEnd_8063690 : Nat := 4140548818853661009490771

theorem tailTrace_8063690 : CollatzResearch.WordTrace tailWord_8063690 prefixEnd_8063690 4140548818853661009490771 := by
  unfold tailWord_8063690
  simp only [CollatzResearch.WordTrace]
  refine ⟨73526734039158943363779131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196071290771090515636744349 73526734039158943363779131)
  ·
    refine ⟨110290101058738415045668697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73526734039158943363779131 110290101058738415045668697)
    ·
      refine ⟨82717575794053811284251523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110290101058738415045668697 82717575794053811284251523)
      ·
        refine ⟨124076363691080716926377285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82717575794053811284251523 124076363691080716926377285)
        ·
          refine ⟨23264318192077634423695741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124076363691080716926377285 23264318192077634423695741)
          ·
            refine ⟨8724119322029112908885903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23264318192077634423695741 8724119322029112908885903)
            ·
              refine ⟨13086178983043669363328855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8724119322029112908885903 13086178983043669363328855)
              ·
                refine ⟨19629268474565504044993283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13086178983043669363328855 19629268474565504044993283)
                ·
                  refine ⟨29443902711848256067489925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19629268474565504044993283 29443902711848256067489925)
                  ·
                    refine ⟨5520731758471548012654361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29443902711848256067489925 5520731758471548012654361)
                    ·
                      refine ⟨4140548818853661009490771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520731758471548012654361 4140548818853661009490771)
                      ·
                        rfl

theorem cell23_8063690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2].length) (baseStart_8063690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063690 prefixEnd_8063690 := by exact prefixLift 8063690
  have htrace : WordTrace (prefixWord ++ tailWord_8063690) baseStart_8063690 baseEnd_8063690 := by
    simpa [prefixWord, tailWord_8063690, baseEnd_8063690] using wordTrace_append hprefix tailTrace_8063690
  have hstable : (prefixWord ++ tailWord_8063690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063690).length < 2 ^ (prefixWord ++ tailWord_8063690).sum := by decide
  have hdescent : baseEnd_8063690 < baseStart_8063690 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063713 : List Nat := [1, 2, 3, 1, 4, 1, 3, 3, 5]
def baseStart_8063713 : Nat := 118140960795 + 8063713 * 2 ^ 59
def prefixEnd_8063713 : Nat := 4983230072969 + 3 ^ 40 * 8063713 * 2
def baseEnd_8063713 : Nat := 460062292100968268833685

theorem tailTrace_8063713 : CollatzResearch.WordTrace tailWord_8063713 prefixEnd_8063713 460062292100968268833685 := by
  unfold tailWord_8063713
  simp only [CollatzResearch.WordTrace]
  refine ⟨294107775035552448383203793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196071850023701632255469195 294107775035552448383203793)
  ·
    refine ⟨220580831276664336287402845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294107775035552448383203793 220580831276664336287402845)
    ·
      refine ⟨82717811728749126107776067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220580831276664336287402845 82717811728749126107776067)
      ·
        refine ⟨124076717593123689161664101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82717811728749126107776067 124076717593123689161664101)
        ·
          refine ⟨23264384548710691717812019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124076717593123689161664101 23264384548710691717812019)
          ·
            refine ⟨34896576823066037576718029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23264384548710691717812019 34896576823066037576718029)
            ·
              refine ⟨13086216308649764091269261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34896576823066037576718029 13086216308649764091269261)
              ·
                refine ⟨4907331115743661534225973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13086216308649764091269261 4907331115743661534225973)
                ·
                  refine ⟨460062292100968268833685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4907331115743661534225973 460062292100968268833685)
                  ·
                    rfl

theorem cell23_8063713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 3, 3, 5].length) (baseStart_8063713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063713 prefixEnd_8063713 := by exact prefixLift 8063713
  have htrace : WordTrace (prefixWord ++ tailWord_8063713) baseStart_8063713 baseEnd_8063713 := by
    simpa [prefixWord, tailWord_8063713, baseEnd_8063713] using wordTrace_append hprefix tailTrace_8063713
  have hstable : (prefixWord ++ tailWord_8063713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063713).length < 2 ^ (prefixWord ++ tailWord_8063713).sum := by decide
  have hdescent : baseEnd_8063713 < baseStart_8063713 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063726 : List Nat := [4, 1, 2, 1, 1, 3, 1, 1, 4, 5]
def baseStart_8063726 : Nat := 118140960795 + 8063726 * 2 ^ 59
def prefixEnd_8063726 : Nat := 4983230072969 + 3 ^ 40 * 8063726 * 2
def baseEnd_8063726 : Nat := 1380189101385740956213535

theorem tailTrace_8063726 : CollatzResearch.WordTrace tailWord_8063726 prefixEnd_8063726 1380189101385740956213535 := by
  unfold tailWord_8063726
  simp only [CollatzResearch.WordTrace]
  refine ⟨36763531148063168950428379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196072166123003567735618021 36763531148063168950428379)
  ·
    refine ⟨55145296722094753425642569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36763531148063168950428379 55145296722094753425642569)
    ·
      refine ⟨41358972541571065069231927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55145296722094753425642569 41358972541571065069231927)
      ·
        refine ⟨62038458812356597603847891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41358972541571065069231927 62038458812356597603847891)
        ·
          refine ⟨93057688218534896405771837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62038458812356597603847891 93057688218534896405771837)
          ·
            refine ⟨34896633081950586152164439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 93057688218534896405771837 34896633081950586152164439)
            ·
              refine ⟨52344949622925879228246659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34896633081950586152164439 52344949622925879228246659)
              ·
                refine ⟨78517424434388818842369989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52344949622925879228246659 78517424434388818842369989)
                ·
                  refine ⟨14722017081447903532944373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78517424434388818842369989 14722017081447903532944373)
                  ·
                    refine ⟨1380189101385740956213535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14722017081447903532944373 1380189101385740956213535)
                    ·
                      rfl

theorem cell23_8063726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 1, 4, 5].length) (baseStart_8063726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063726 prefixEnd_8063726 := by exact prefixLift 8063726
  have htrace : WordTrace (prefixWord ++ tailWord_8063726) baseStart_8063726 baseEnd_8063726 := by
    simpa [prefixWord, tailWord_8063726, baseEnd_8063726] using wordTrace_append hprefix tailTrace_8063726
  have hstable : (prefixWord ++ tailWord_8063726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063726).length < 2 ^ (prefixWord ++ tailWord_8063726).sum := by decide
  have hdescent : baseEnd_8063726 < baseStart_8063726 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063730 : List Nat := [3, 2, 1, 3, 1, 3, 3, 2, 5]
def baseStart_8063730 : Nat := 118140960795 + 8063730 * 2 ^ 59
def prefixEnd_8063730 : Nat := 4983230072969 + 3 ^ 40 * 8063730 * 2
def baseEnd_8063730 : Nat := 460063262008871205887843

theorem tailTrace_8063730 : CollatzResearch.WordTrace tailWord_8063730 prefixEnd_8063730 460063262008871205887843 := by
  unfold tailWord_8063730
  simp only [CollatzResearch.WordTrace]
  refine ⟨73527098769122715071643161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196072263384327240191048429 73527098769122715071643161)
  ·
    refine ⟨55145324076842036303732371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73527098769122715071643161 55145324076842036303732371)
    ·
      refine ⟨82717986115263054455598557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55145324076842036303732371 82717986115263054455598557)
      ·
        refine ⟨31019244793223645420849459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82717986115263054455598557 31019244793223645420849459)
        ·
          refine ⟨46528867189835468131274189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31019244793223645420849459 46528867189835468131274189)
          ·
            refine ⟨17448325196188300549227821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46528867189835468131274189 17448325196188300549227821)
            ·
              refine ⟨6543121948570612705960433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17448325196188300549227821 6543121948570612705960433)
              ·
                refine ⟨4907341461427959529470325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6543121948570612705960433 4907341461427959529470325)
                ·
                  refine ⟨460063262008871205887843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4907341461427959529470325 460063262008871205887843)
                  ·
                    rfl

theorem cell23_8063730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 3, 2, 5].length) (baseStart_8063730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063730 prefixEnd_8063730 := by exact prefixLift 8063730
  have htrace : WordTrace (prefixWord ++ tailWord_8063730) baseStart_8063730 baseEnd_8063730 := by
    simpa [prefixWord, tailWord_8063730, baseEnd_8063730] using wordTrace_append hprefix tailTrace_8063730
  have hstable : (prefixWord ++ tailWord_8063730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063730).length < 2 ^ (prefixWord ++ tailWord_8063730).sum := by decide
  have hdescent : baseEnd_8063730 < baseStart_8063730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063749 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 5]
def baseStart_8063749 : Nat := 118140960795 + 8063749 * 2 ^ 59
def prefixEnd_8063749 : Nat := 4983230072969 + 3 ^ 40 * 8063749 * 2
def baseEnd_8063749 : Nat := 4140579114212276278652999

theorem tailTrace_8063749 : CollatzResearch.WordTrace tailWord_8063749 prefixEnd_8063749 4140579114212276278652999 := by
  unfold tailWord_8063749
  simp only [CollatzResearch.WordTrace]
  refine ⟨294109088063422026531514301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196072725375614684354342867 294109088063422026531514301)
  ·
    refine ⟨110290908023783259949317863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294109088063422026531514301 110290908023783259949317863)
    ·
      refine ⟨165436362035674889923976795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110290908023783259949317863 165436362035674889923976795)
      ·
        refine ⟨248154543053512334885965193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165436362035674889923976795 248154543053512334885965193)
        ·
          refine ⟨186115907290134251164473895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248154543053512334885965193 186115907290134251164473895)
          ·
            refine ⟨279173860935201376746710843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186115907290134251164473895 279173860935201376746710843)
            ·
              refine ⟨418760791402802065120066265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279173860935201376746710843 418760791402802065120066265)
              ·
                refine ⟨314070593552101548840049699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418760791402802065120066265 314070593552101548840049699)
                ·
                  refine ⟨471105890328152323260074549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314070593552101548840049699 471105890328152323260074549)
                  ·
                    refine ⟨44166177218264280305631989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 471105890328152323260074549 44166177218264280305631989)
                    ·
                      refine ⟨4140579114212276278652999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44166177218264280305631989 4140579114212276278652999)
                      ·
                        rfl

theorem cell23_8063749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 5, 5].length) (baseStart_8063749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063749 prefixEnd_8063749 := by exact prefixLift 8063749
  have htrace : WordTrace (prefixWord ++ tailWord_8063749) baseStart_8063749 baseEnd_8063749 := by
    simpa [prefixWord, tailWord_8063749, baseEnd_8063749] using wordTrace_append hprefix tailTrace_8063749
  have hstable : (prefixWord ++ tailWord_8063749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063749).length < 2 ^ (prefixWord ++ tailWord_8063749).sum := by decide
  have hdescent : baseEnd_8063749 < baseStart_8063749 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063756 : List Nat := [2, 2, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_8063756 : Nat := 118140960795 + 8063756 * 2 ^ 59
def prefixEnd_8063756 : Nat := 4983230072969 + 3 ^ 40 * 8063756 * 2
def baseEnd_8063756 : Nat := 1380194236192285917088489

theorem tailTrace_8063756 : CollatzResearch.WordTrace tailWord_8063756 prefixEnd_8063756 1380194236192285917088489 := by
  unfold tailWord_8063756
  simp only [CollatzResearch.WordTrace]
  refine ⟨147054671687198333363509561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196072895582931111151346081 147054671687198333363509561)
  ·
    refine ⟨110291003765398750022632171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147054671687198333363509561 110291003765398750022632171)
    ·
      refine ⟨165436505648098125033948257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110291003765398750022632171 165436505648098125033948257)
      ·
        refine ⟨124077379236073593775461193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165436505648098125033948257 124077379236073593775461193)
        ·
          refine ⟨93058034427055195331595895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124077379236073593775461193 93058034427055195331595895)
          ·
            refine ⟨139587051640582792997393843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93058034427055195331595895 139587051640582792997393843)
            ·
              refine ⟨209380577460874189496090765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139587051640582792997393843 209380577460874189496090765)
              ·
                refine ⟨78517716547827821061034037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 209380577460874189496090765 78517716547827821061034037)
                ·
                  refine ⟨7361035926358858224471941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78517716547827821061034037 7361035926358858224471941)
                  ·
                    refine ⟨1380194236192285917088489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7361035926358858224471941 1380194236192285917088489)
                    ·
                      rfl

theorem cell23_8063756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_8063756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063756 prefixEnd_8063756 := by exact prefixLift 8063756
  have htrace : WordTrace (prefixWord ++ tailWord_8063756) baseStart_8063756 baseEnd_8063756 := by
    simpa [prefixWord, tailWord_8063756, baseEnd_8063756] using wordTrace_append hprefix tailTrace_8063756
  have hstable : (prefixWord ++ tailWord_8063756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063756).length < 2 ^ (prefixWord ++ tailWord_8063756).sum := by decide
  have hdescent : baseEnd_8063756 < baseStart_8063756 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063769 : List Nat := [1, 2, 1, 2, 1, 1, 1, 6, 8]
def baseStart_8063769 : Nat := 118140960795 + 8063769 * 2 ^ 59
def prefixEnd_8063769 : Nat := 4983230072969 + 3 ^ 40 * 8063769 * 2
def baseEnd_8063769 : Nat := 460065487091707355600323

theorem tailTrace_8063769 : CollatzResearch.WordTrace tailWord_8063769 prefixEnd_8063769 460065487091707355600323 := by
  unfold tailWord_8063769
  simp only [CollatzResearch.WordTrace]
  refine ⟨294109817523349569947242361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196073211682233046631494907 294109817523349569947242361)
  ·
    refine ⟨220582363142512177460431771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294109817523349569947242361 220582363142512177460431771)
    ·
      refine ⟨330873544713768266190647657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220582363142512177460431771 330873544713768266190647657)
      ·
        refine ⟨248155158535326199642985743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330873544713768266190647657 248155158535326199642985743)
        ·
          refine ⟨372232737802989299464478615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248155158535326199642985743 372232737802989299464478615)
          ·
            refine ⟨558349106704483949196717923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372232737802989299464478615 558349106704483949196717923)
            ·
              refine ⟨837523660056725923795076885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558349106704483949196717923 837523660056725923795076885)
              ·
                refine ⟨39258921565159027677894229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 837523660056725923795076885 39258921565159027677894229)
                ·
                  refine ⟨460065487091707355600323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39258921565159027677894229 460065487091707355600323)
                  ·
                    rfl

theorem cell23_8063769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 6, 8].length) (baseStart_8063769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063769 prefixEnd_8063769 := by exact prefixLift 8063769
  have htrace : WordTrace (prefixWord ++ tailWord_8063769) baseStart_8063769 baseEnd_8063769 := by
    simpa [prefixWord, tailWord_8063769, baseEnd_8063769] using wordTrace_append hprefix tailTrace_8063769
  have hstable : (prefixWord ++ tailWord_8063769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063769).length < 2 ^ (prefixWord ++ tailWord_8063769).sum := by decide
  have hdescent : baseEnd_8063769 < baseStart_8063769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063814 : List Nat := [6, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4]
def baseStart_8063814 : Nat := 118140960795 + 8063814 * 2 ^ 59
def prefixEnd_8063814 : Nat := 4983230072969 + 3 ^ 40 * 8063814 * 2
def baseEnd_8063814 : Nat := 4140612490454818524340201

theorem tailTrace_8063814 : CollatzResearch.WordTrace tailWord_8063814 prefixEnd_8063814 4140612490454818524340201 := by
  unfold tailWord_8063814
  simp only [CollatzResearch.WordTrace]
  refine ⟨9190983087755829457269703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 196074305872124361755086997 9190983087755829457269703)
  ·
    refine ⟨13786474631633744185904555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9190983087755829457269703 13786474631633744185904555)
    ·
      refine ⟨20679711947450616278856833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13786474631633744185904555 20679711947450616278856833)
      ·
        refine ⟨15509783960587962209142625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20679711947450616278856833 15509783960587962209142625)
        ·
          refine ⟨11632337970440971656856969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15509783960587962209142625 11632337970440971656856969)
          ·
            refine ⟨8724253477830728742642727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11632337970440971656856969 8724253477830728742642727)
            ·
              refine ⟨13086380216746093113964091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8724253477830728742642727 13086380216746093113964091)
              ·
                refine ⟨19629570325119139670946137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13086380216746093113964091 19629570325119139670946137)
                ·
                  refine ⟨14722177743839354753209603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19629570325119139670946137 14722177743839354753209603)
                  ·
                    refine ⟨22083266615759032129814405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14722177743839354753209603 22083266615759032129814405)
                    ·
                      refine ⟨4140612490454818524340201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22083266615759032129814405 4140612490454818524340201)
                      ·
                        rfl

theorem cell23_8063814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_8063814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063814 prefixEnd_8063814 := by exact prefixLift 8063814
  have htrace : WordTrace (prefixWord ++ tailWord_8063814) baseStart_8063814 baseEnd_8063814 := by
    simpa [prefixWord, tailWord_8063814, baseEnd_8063814] using wordTrace_append hprefix tailTrace_8063814
  have hstable : (prefixWord ++ tailWord_8063814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063814).length < 2 ^ (prefixWord ++ tailWord_8063814).sum := by decide
  have hdescent : baseEnd_8063814 < baseStart_8063814 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063816 : List Nat := [2, 1, 3, 1, 1, 3, 1, 3, 3, 5]
def baseStart_8063816 : Nat := 118140960795 + 8063816 * 2 ^ 59
def prefixEnd_8063816 : Nat := 4983230072969 + 3 ^ 40 * 8063816 * 2
def baseEnd_8063816 : Nat := 1380204505805375838838397

theorem tailTrace_8063816 : CollatzResearch.WordTrace tailWord_8063816 prefixEnd_8063816 1380204505805375838838397 := by
  unfold tailWord_8063816
  simp only [CollatzResearch.WordTrace]
  refine ⟨147055765877089648487101651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196074354502786197982802201 147055765877089648487101651)
  ·
    refine ⟨220583648815634472730652477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147055765877089648487101651 220583648815634472730652477)
    ·
      refine ⟨82718868305862927273994679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220583648815634472730652477 82718868305862927273994679)
      ·
        refine ⟨124078302458794390910992019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82718868305862927273994679 124078302458794390910992019)
        ·
          refine ⟨186117453688191586366488029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124078302458794390910992019 186117453688191586366488029)
          ·
            refine ⟨69794045133071844887433011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186117453688191586366488029 69794045133071844887433011)
            ·
              refine ⟨104691067699607767331149517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69794045133071844887433011 104691067699607767331149517)
              ·
                refine ⟨39259150387352912749181069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104691067699607767331149517 39259150387352912749181069)
                ·
                  refine ⟨14722181395257342280942901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39259150387352912749181069 14722181395257342280942901)
                  ·
                    refine ⟨1380204505805375838838397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14722181395257342280942901 1380204505805375838838397)
                    ·
                      rfl

theorem cell23_8063816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_8063816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063816 prefixEnd_8063816 := by exact prefixLift 8063816
  have htrace : WordTrace (prefixWord ++ tailWord_8063816) baseStart_8063816 baseEnd_8063816 := by
    simpa [prefixWord, tailWord_8063816, baseEnd_8063816] using wordTrace_append hprefix tailTrace_8063816
  have hstable : (prefixWord ++ tailWord_8063816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063816).length < 2 ^ (prefixWord ++ tailWord_8063816).sum := by decide
  have hdescent : baseEnd_8063816 < baseStart_8063816 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063833 : List Nat := [1, 2, 1, 2, 2, 5, 1, 3, 1, 5]
def baseStart_8063833 : Nat := 118140960795 + 8063833 * 2 ^ 59
def prefixEnd_8063833 : Nat := 4983230072969 + 3 ^ 40 * 8063833 * 2
def baseEnd_8063833 : Nat := 1380207415529084650000871

theorem tailTrace_8063833 : CollatzResearch.WordTrace tailWord_8063833 prefixEnd_8063833 1380207415529084650000871 := by
  unfold tailWord_8063833
  simp only [CollatzResearch.WordTrace]
  refine ⟨294112151795117708877572153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196074767863411805918381435 294112151795117708877572153)
  ·
    refine ⟨220584113846338281658179115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294112151795117708877572153 220584113846338281658179115)
    ·
      refine ⟨330876170769507422487268673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220584113846338281658179115 330876170769507422487268673)
      ·
        refine ⟨248157128077130566865451505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330876170769507422487268673 248157128077130566865451505)
        ·
          refine ⟨186117846057847925149088629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248157128077130566865451505 186117846057847925149088629)
          ·
            refine ⟨17448548067923242982727059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 186117846057847925149088629 17448548067923242982727059)
            ·
              refine ⟨26172822101884864474090589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17448548067923242982727059 26172822101884864474090589)
              ·
                refine ⟨9814808288206824177783971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26172822101884864474090589 9814808288206824177783971)
                ·
                  refine ⟨14722212432310236266675957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9814808288206824177783971 14722212432310236266675957)
                  ·
                    refine ⟨1380207415529084650000871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14722212432310236266675957 1380207415529084650000871)
                    ·
                      rfl

theorem cell23_8063833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 5].length) (baseStart_8063833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063833 prefixEnd_8063833 := by exact prefixLift 8063833
  have htrace : WordTrace (prefixWord ++ tailWord_8063833) baseStart_8063833 baseEnd_8063833 := by
    simpa [prefixWord, tailWord_8063833, baseEnd_8063833] using wordTrace_append hprefix tailTrace_8063833
  have hstable : (prefixWord ++ tailWord_8063833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063833).length < 2 ^ (prefixWord ++ tailWord_8063833).sum := by decide
  have hdescent : baseEnd_8063833 < baseStart_8063833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063847 : List Nat := [1, 1, 5, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_8063847 : Nat := 118140960795 + 8063847 * 2 ^ 59
def prefixEnd_8063847 : Nat := 4983230072969 + 3 ^ 40 * 8063847 * 2
def baseEnd_8063847 : Nat := 4140629435316416895227549

theorem tailTrace_8063847 : CollatzResearch.WordTrace tailWord_8063847 prefixEnd_8063847 4140629435316416895227549 := by
  unfold tailWord_8063847
  simp only [CollatzResearch.WordTrace]
  refine ⟨294112662417066989268581795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196075108278044659512387863 294112662417066989268581795)
  ·
    refine ⟨441168993625600483902872693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294112662417066989268581795 441168993625600483902872693)
    ·
      refine ⟨41359593152400045365894315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441168993625600483902872693 41359593152400045365894315)
      ·
        refine ⟨62039389728600068048841473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41359593152400045365894315 62039389728600068048841473)
        ·
          refine ⟨46529542296450051036631105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62039389728600068048841473 46529542296450051036631105)
          ·
            refine ⟨34897156722337538277473329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46529542296450051036631105 34897156722337538277473329)
            ·
              refine ⟨26172867541753153708104997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34897156722337538277473329 26172867541753153708104997)
              ·
                refine ⟨4907412664078716320269687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26172867541753153708104997 4907412664078716320269687)
                ·
                  refine ⟨7361118996118074480404531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907412664078716320269687 7361118996118074480404531)
                  ·
                    refine ⟨11041678494177111720606797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7361118996118074480404531 11041678494177111720606797)
                    ·
                      refine ⟨4140629435316416895227549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11041678494177111720606797 4140629435316416895227549)
                      ·
                        rfl

theorem cell23_8063847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_8063847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063847 prefixEnd_8063847 := by exact prefixLift 8063847
  have htrace : WordTrace (prefixWord ++ tailWord_8063847) baseStart_8063847 baseEnd_8063847 := by
    simpa [prefixWord, tailWord_8063847, baseEnd_8063847] using wordTrace_append hprefix tailTrace_8063847
  have hstable : (prefixWord ++ tailWord_8063847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063847).length < 2 ^ (prefixWord ++ tailWord_8063847).sum := by decide
  have hdescent : baseEnd_8063847 < baseStart_8063847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063856 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 5]
def baseStart_8063856 : Nat := 118140960795 + 8063856 * 2 ^ 59
def prefixEnd_8063856 : Nat := 4983230072969 + 3 ^ 40 * 8063856 * 2
def baseEnd_8063856 : Nat := 4140634056642307360015007

theorem tailTrace_8063856 : CollatzResearch.WordTrace tailWord_8063856 prefixEnd_8063856 4140634056642307360015007 := by
  unfold tailWord_8063856
  simp only [CollatzResearch.WordTrace]
  refine ⟨147056495337017191902829711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196075327116022922537106281 147056495337017191902829711)
  ·
    refine ⟨220584743005525787854244567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147056495337017191902829711 220584743005525787854244567)
    ·
      refine ⟨330877114508288681781366851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220584743005525787854244567 330877114508288681781366851)
      ·
        refine ⟨496315671762433022672050277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330877114508288681781366851 496315671762433022672050277)
        ·
          refine ⟨93059188455456191751009427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 496315671762433022672050277 93059188455456191751009427)
          ·
            refine ⟨139588782683184287626514141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93059188455456191751009427 139588782683184287626514141)
            ·
              refine ⟨52345793506194107859942803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139588782683184287626514141 52345793506194107859942803)
              ·
                refine ⟨78518690259291161789914205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52345793506194107859942803 78518690259291161789914205)
                ·
                  refine ⟨29444508847234185671217827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78518690259291161789914205 29444508847234185671217827)
                  ·
                    refine ⟨44166763270851278506826741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29444508847234185671217827 44166763270851278506826741)
                    ·
                      refine ⟨4140634056642307360015007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44166763270851278506826741 4140634056642307360015007)
                      ·
                        rfl

theorem cell23_8063856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 5].length) (baseStart_8063856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063856 prefixEnd_8063856 := by exact prefixLift 8063856
  have htrace : WordTrace (prefixWord ++ tailWord_8063856) baseStart_8063856 baseEnd_8063856 := by
    simpa [prefixWord, tailWord_8063856, baseEnd_8063856] using wordTrace_append hprefix tailTrace_8063856
  have hstable : (prefixWord ++ tailWord_8063856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063856).length < 2 ^ (prefixWord ++ tailWord_8063856).sum := by decide
  have hdescent : baseEnd_8063856 < baseStart_8063856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063863 : List Nat := [1, 1, 3, 1, 1, 2, 1, 7, 2, 4]
def baseStart_8063863 : Nat := 118140960795 + 8063863 * 2 ^ 59
def prefixEnd_8063863 : Nat := 4983230072969 + 3 ^ 40 * 8063863 * 2
def baseEnd_8063863 : Nat := 1380212550335629610875825

theorem tailTrace_8063863 : CollatzResearch.WordTrace tailWord_8063863 prefixEnd_8063863 1380212550335629610875825 := by
  unfold tailWord_8063863
  simp only [CollatzResearch.WordTrace]
  refine ⟨294113245985009024001164243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196075497323339349334109495 294113245985009024001164243)
  ·
    refine ⟨441169868977513536001746365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294113245985009024001164243 441169868977513536001746365)
    ·
      refine ⟨165438700866567576000654887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441169868977513536001746365 165438700866567576000654887)
      ·
        refine ⟨248158051299851364000982331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165438700866567576000654887 248158051299851364000982331)
        ·
          refine ⟨372237076949777046001473497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248158051299851364000982331 372237076949777046001473497)
          ·
            refine ⟨279177807712332784501105123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372237076949777046001473497 279177807712332784501105123)
            ·
              refine ⟨418766711568499176751657685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279177807712332784501105123 418766711568499176751657685)
              ·
                refine ⟨9814844802386699455116977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 418766711568499176751657685 9814844802386699455116977)
                ·
                  refine ⟨7361133601790024591337733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9814844802386699455116977 7361133601790024591337733)
                  ·
                    refine ⟨1380212550335629610875825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7361133601790024591337733 1380212550335629610875825)
                    ·
                      rfl

theorem cell23_8063863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_8063863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063863 prefixEnd_8063863 := by exact prefixLift 8063863
  have htrace : WordTrace (prefixWord ++ tailWord_8063863) baseStart_8063863 baseEnd_8063863 := by
    simpa [prefixWord, tailWord_8063863, baseEnd_8063863] using wordTrace_append hprefix tailTrace_8063863
  have hstable : (prefixWord ++ tailWord_8063863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063863).length < 2 ^ (prefixWord ++ tailWord_8063863).sum := by decide
  have hdescent : baseEnd_8063863 < baseStart_8063863 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063916 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_8063916 : Nat := 118140960795 + 8063916 * 2 ^ 59
def prefixEnd_8063916 : Nat := 4983230072969 + 3 ^ 40 * 8063916 * 2
def baseEnd_8063916 : Nat := 4140664865481577125264731

theorem tailTrace_8063916 : CollatzResearch.WordTrace tailWord_8063916 prefixEnd_8063916 4140664865481577125264731 := by
  unfold tailWord_8063916
  simp only [CollatzResearch.WordTrace]
  refine ⟨147057589526908507026421801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196076786035878009368562401 147057589526908507026421801)
  ·
    refine ⟨110293192145181380269816351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147057589526908507026421801 110293192145181380269816351)
    ·
      refine ⟨165439788217772070404724527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110293192145181380269816351 165439788217772070404724527)
      ·
        refine ⟨248159682326658105607086791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165439788217772070404724527 248159682326658105607086791)
        ·
          refine ⟨372239523489987158410630187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248159682326658105607086791 372239523489987158410630187)
          ·
            refine ⟨558359285234980737615945281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372239523489987158410630187 558359285234980737615945281)
            ·
              refine ⟨418769463926235553211958961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558359285234980737615945281 418769463926235553211958961)
              ·
                refine ⟨314077097944676664908969221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418769463926235553211958961 314077097944676664908969221)
                ·
                  refine ⟨58889455864626874670431729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 314077097944676664908969221 58889455864626874670431729)
                  ·
                    refine ⟨44167091898470156002823797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58889455864626874670431729 44167091898470156002823797)
                    ·
                      refine ⟨4140664865481577125264731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44167091898470156002823797 4140664865481577125264731)
                      ·
                        rfl

theorem cell23_8063916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_8063916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063916 prefixEnd_8063916 := by exact prefixLift 8063916
  have htrace : WordTrace (prefixWord ++ tailWord_8063916) baseStart_8063916 baseEnd_8063916 := by
    simpa [prefixWord, tailWord_8063916, baseEnd_8063916] using wordTrace_append hprefix tailTrace_8063916
  have hstable : (prefixWord ++ tailWord_8063916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063916).length < 2 ^ (prefixWord ++ tailWord_8063916).sum := by decide
  have hdescent : baseEnd_8063916 < baseStart_8063916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063924 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_8063924 : Nat := 118140960795 + 8063924 * 2 ^ 59
def prefixEnd_8063924 : Nat := 4983230072969 + 3 ^ 40 * 8063924 * 2
def baseEnd_8063924 : Nat := 4140668973326813093964695

theorem tailTrace_8063924 : CollatzResearch.WordTrace tailWord_8063924 prefixEnd_8063924 4140668973326813093964695 := by
  unfold tailWord_8063924
  simp only [CollatzResearch.WordTrace]
  refine ⟨147057735418894015709567413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196076980558525354279423217 147057735418894015709567413)
  ·
    refine ⟨13786662695521313972771945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147057735418894015709567413 13786662695521313972771945)
    ·
      refine ⟨10339997021640985479578959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13786662695521313972771945 10339997021640985479578959)
      ·
        refine ⟨15509995532461478219368439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10339997021640985479578959 15509995532461478219368439)
        ·
          refine ⟨23264993298692217329052659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15509995532461478219368439 23264993298692217329052659)
          ·
            refine ⟨34897489948038325993578989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23264993298692217329052659 34897489948038325993578989)
            ·
              refine ⟨13086558730514372247592121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34897489948038325993578989 13086558730514372247592121)
              ·
                refine ⟨9814919047885779185694091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13086558730514372247592121 9814919047885779185694091)
                ·
                  refine ⟨14722378571828668778541137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9814919047885779185694091 14722378571828668778541137)
                  ·
                    refine ⟨11041783928871501583905853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14722378571828668778541137 11041783928871501583905853)
                    ·
                      refine ⟨4140668973326813093964695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11041783928871501583905853 4140668973326813093964695)
                      ·
                        rfl

theorem cell23_8063924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_8063924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063924 prefixEnd_8063924 := by exact prefixLift 8063924
  have htrace : WordTrace (prefixWord ++ tailWord_8063924) baseStart_8063924 baseEnd_8063924 := by
    simpa [prefixWord, tailWord_8063924, baseEnd_8063924] using wordTrace_append hprefix tailTrace_8063924
  have hstable : (prefixWord ++ tailWord_8063924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063924).length < 2 ^ (prefixWord ++ tailWord_8063924).sum := by decide
  have hdescent : baseEnd_8063924 < baseStart_8063924 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063930 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2]
def baseStart_8063930 : Nat := 118140960795 + 8063930 * 2 ^ 59
def prefixEnd_8063930 : Nat := 4983230072969 + 3 ^ 40 * 8063930 * 2
def baseEnd_8063930 : Nat := 4140672054210740070489667

theorem tailTrace_8063930 : CollatzResearch.WordTrace tailWord_8063930 prefixEnd_8063930 4140672054210740070489667 := by
  unfold tailWord_8063930
  simp only [CollatzResearch.WordTrace]
  refine ⟨73528922418941573610963311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196077126450510862962568829 73528922418941573610963311)
  ·
    refine ⟨110293383628412360416444967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73528922418941573610963311 110293383628412360416444967)
    ·
      refine ⟨165440075442618540624667451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110293383628412360416444967 165440075442618540624667451)
      ·
        refine ⟨248160113163927810937001177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165440075442618540624667451 248160113163927810937001177)
        ·
          refine ⟨186120084872945858202750883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248160113163927810937001177 186120084872945858202750883)
          ·
            refine ⟨279180127309418787304126325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186120084872945858202750883 279180127309418787304126325)
            ·
              refine ⟨26173136935258011309761843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 279180127309418787304126325 26173136935258011309761843)
              ·
                refine ⟨39259705402887016964642765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26173136935258011309761843 39259705402887016964642765)
                ·
                  refine ⟨14722389526082631361741037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39259705402887016964642765 14722389526082631361741037)
                  ·
                    refine ⟨5520896072280986760652889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14722389526082631361741037 5520896072280986760652889)
                    ·
                      refine ⟨4140672054210740070489667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520896072280986760652889 4140672054210740070489667)
                      ·
                        rfl

theorem cell23_8063930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2].length) (baseStart_8063930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063930 prefixEnd_8063930 := by exact prefixLift 8063930
  have htrace : WordTrace (prefixWord ++ tailWord_8063930) baseStart_8063930 baseEnd_8063930 := by
    simpa [prefixWord, tailWord_8063930, baseEnd_8063930] using wordTrace_append hprefix tailTrace_8063930
  have hstable : (prefixWord ++ tailWord_8063930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063930).length < 2 ^ (prefixWord ++ tailWord_8063930).sum := by decide
  have hdescent : baseEnd_8063930 < baseStart_8063930 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063954 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_8063954 : Nat := 118140960795 + 8063954 * 2 ^ 59
def prefixEnd_8063954 : Nat := 4983230072969 + 3 ^ 40 * 8063954 * 2
def baseEnd_8063954 : Nat := 4140684377746447976589557

theorem tailTrace_8063954 : CollatzResearch.WordTrace tailWord_8063954 prefixEnd_8063954 4140684377746447976589557 := by
  unfold tailWord_8063954
  simp only [CollatzResearch.WordTrace]
  refine ⟨73529141256919836635681729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196077710018452897695151277 73529141256919836635681729)
  ·
    refine ⟨55146855942689877476761297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73529141256919836635681729 55146855942689877476761297)
    ·
      refine ⟨41360141957017408107570973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55146855942689877476761297 41360141957017408107570973)
      ·
        refine ⟨15510053233881528040339115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41360141957017408107570973 15510053233881528040339115)
        ·
          refine ⟨23265079850822292060508673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15510053233881528040339115 23265079850822292060508673)
          ·
            refine ⟨17448809888116719045381505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23265079850822292060508673 17448809888116719045381505)
            ·
              refine ⟨13086607416087539284036129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17448809888116719045381505 13086607416087539284036129)
              ·
                refine ⟨9814955562065654463027097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13086607416087539284036129 9814955562065654463027097)
                ·
                  refine ⟨7361216671549240847270323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9814955562065654463027097 7361216671549240847270323)
                  ·
                    refine ⟨11041825007323861270905485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7361216671549240847270323 11041825007323861270905485)
                    ·
                      refine ⟨4140684377746447976589557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11041825007323861270905485 4140684377746447976589557)
                      ·
                        rfl

theorem cell23_8063954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_8063954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063954 prefixEnd_8063954 := by exact prefixLift 8063954
  have htrace : WordTrace (prefixWord ++ tailWord_8063954) baseStart_8063954 baseEnd_8063954 := by
    simpa [prefixWord, tailWord_8063954, baseEnd_8063954] using wordTrace_append hprefix tailTrace_8063954
  have hstable : (prefixWord ++ tailWord_8063954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063954).length < 2 ^ (prefixWord ++ tailWord_8063954).sum := by decide
  have hdescent : baseEnd_8063954 < baseStart_8063954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063970 : List Nat := [3, 3, 3, 1, 1, 1, 1, 1, 1, 8]
def baseStart_8063970 : Nat := 118140960795 + 8063970 * 2 ^ 59
def prefixEnd_8063970 : Nat := 4983230072969 + 3 ^ 40 * 8063970 * 2
def baseEnd_8063970 : Nat := 1380230864478973304663161

theorem tailTrace_8063970 : CollatzResearch.WordTrace tailWord_8063970 prefixEnd_8063970 1380230864478973304663161 := by
  unfold tailWord_8063970
  simp only [CollatzResearch.WordTrace]
  refine ⟨73529287148905345318827341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196078099063747587516872909 73529287148905345318827341)
  ·
    refine ⟨27573482680839504494560253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73529287148905345318827341 27573482680839504494560253)
    ·
      refine ⟨10340056005314814185460095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27573482680839504494560253 10340056005314814185460095)
      ·
        refine ⟨15510084007972221278190143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10340056005314814185460095 15510084007972221278190143)
        ·
          refine ⟨23265126011958331917285215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15510084007972221278190143 23265126011958331917285215)
          ·
            refine ⟨34897689017937497875927823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23265126011958331917285215 34897689017937497875927823)
            ·
              refine ⟨52346533526906246813891735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34897689017937497875927823 52346533526906246813891735)
              ·
                refine ⟨78519800290359370220837603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52346533526906246813891735 78519800290359370220837603)
                ·
                  refine ⟨117779700435539055331256405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78519800290359370220837603 117779700435539055331256405)
                  ·
                    refine ⟨1380230864478973304663161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117779700435539055331256405 1380230864478973304663161)
                    ·
                      rfl

theorem cell23_8063970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_8063970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063970 prefixEnd_8063970 := by exact prefixLift 8063970
  have htrace : WordTrace (prefixWord ++ tailWord_8063970) baseStart_8063970 baseEnd_8063970 := by
    simpa [prefixWord, tailWord_8063970, baseEnd_8063970] using wordTrace_append hprefix tailTrace_8063970
  have hstable : (prefixWord ++ tailWord_8063970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063970).length < 2 ^ (prefixWord ++ tailWord_8063970).sum := by decide
  have hdescent : baseEnd_8063970 < baseStart_8063970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063983 : List Nat := [1, 1, 2, 1, 4, 4, 1, 2, 7]
def baseStart_8063983 : Nat := 118140960795 + 8063983 * 2 ^ 59
def prefixEnd_8063983 : Nat := 4983230072969 + 3 ^ 40 * 8063983 * 2
def baseEnd_8063983 : Nat := 460077696520603151458547

theorem tailTrace_8063983 : CollatzResearch.WordTrace tailWord_8063983 prefixEnd_8063983 460077696520603151458547 := by
  unfold tailWord_8063983
  simp only [CollatzResearch.WordTrace]
  refine ⟨294117622744574284495532603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196078415163049522997021735 294117622744574284495532603)
  ·
    refine ⟨441176434116861426743298905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294117622744574284495532603 441176434116861426743298905)
    ·
      refine ⟨330882325587646070057474179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441176434116861426743298905 330882325587646070057474179)
      ·
        refine ⟨496323488381469105086211269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330882325587646070057474179 496323488381469105086211269)
        ·
          refine ⟨93060654071525457203664613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 496323488381469105086211269 93060654071525457203664613)
          ·
            refine ⟨17448872638411023225687115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 93060654071525457203664613 17448872638411023225687115)
            ·
              refine ⟨26173308957616534838530673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17448872638411023225687115 26173308957616534838530673)
              ·
                refine ⟨19629981718212401128898005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26173308957616534838530673 19629981718212401128898005)
                ·
                  refine ⟨460077696520603151458547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19629981718212401128898005 460077696520603151458547)
                  ·
                    rfl

theorem cell23_8063983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 2, 7].length) (baseStart_8063983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063983 prefixEnd_8063983 := by exact prefixLift 8063983
  have htrace : WordTrace (prefixWord ++ tailWord_8063983) baseStart_8063983 baseEnd_8063983 := by
    simpa [prefixWord, tailWord_8063983, baseEnd_8063983] using wordTrace_append hprefix tailTrace_8063983
  have hstable : (prefixWord ++ tailWord_8063983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063983).length < 2 ^ (prefixWord ++ tailWord_8063983).sum := by decide
  have hdescent : baseEnd_8063983 < baseStart_8063983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063993 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 3]
def baseStart_8063993 : Nat := 118140960795 + 8063993 * 2 ^ 59
def prefixEnd_8063993 : Nat := 4983230072969 + 3 ^ 40 * 8063993 * 2
def baseEnd_8063993 : Nat := 4140704403491973324001877

theorem tailTrace_8063993 : CollatzResearch.WordTrace tailWord_8063993 prefixEnd_8063993 4140704403491973324001877 := by
  unfold tailWord_8063993
  simp only [CollatzResearch.WordTrace]
  refine ⟨294117987474538056203396633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196078658316358704135597755 294117987474538056203396633)
  ·
    refine ⟨220588490605903542152547475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294117987474538056203396633 220588490605903542152547475)
    ·
      refine ⟨330882735908855313228821213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220588490605903542152547475 330882735908855313228821213)
      ·
        refine ⟨124081025965820742460807955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330882735908855313228821213 124081025965820742460807955)
        ·
          refine ⟨186121538948731113691211933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124081025965820742460807955 186121538948731113691211933)
          ·
            refine ⟨69795577105774167634204475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 186121538948731113691211933 69795577105774167634204475)
            ·
              refine ⟨104693365658661251451306713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69795577105774167634204475 104693365658661251451306713)
              ·
                refine ⟨78520024243995938588480035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104693365658661251451306713 78520024243995938588480035)
                ·
                  refine ⟨117780036365993907882720053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78520024243995938588480035 117780036365993907882720053)
                  ·
                    refine ⟨11041878409311928864005005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117780036365993907882720053 11041878409311928864005005)
                    ·
                      refine ⟨4140704403491973324001877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11041878409311928864005005 4140704403491973324001877)
                      ·
                        rfl

theorem cell23_8063993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_8063993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063993 prefixEnd_8063993 := by exact prefixLift 8063993
  have htrace : WordTrace (prefixWord ++ tailWord_8063993) baseStart_8063993 baseEnd_8063993 := by
    simpa [prefixWord, tailWord_8063993, baseEnd_8063993] using wordTrace_append hprefix tailTrace_8063993
  have hstable : (prefixWord ++ tailWord_8063993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063993).length < 2 ^ (prefixWord ++ tailWord_8063993).sum := by decide
  have hdescent : baseEnd_8063993 < baseStart_8063993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8063998 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 1, 3, 2]
def baseStart_8063998 : Nat := 118140960795 + 8063998 * 2 ^ 59
def prefixEnd_8063998 : Nat := 4983230072969 + 3 ^ 40 * 8063998 * 2
def baseEnd_8063998 : Nat := 4140706970895245804439355

theorem tailTrace_8063998 : CollatzResearch.WordTrace tailWord_8063998 prefixEnd_8063998 4140706970895245804439355 := by
  unfold tailWord_8063998
  simp only [CollatzResearch.WordTrace]
  refine ⟨36764771229939992757166081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196078779893013294704885765 36764771229939992757166081)
  ·
    refine ⟨27573578422454994567874561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36764771229939992757166081 27573578422454994567874561)
    ·
      refine ⟨20680183816841245925905921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27573578422454994567874561 20680183816841245925905921)
      ·
        refine ⟨15510137862630934444429441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20680183816841245925905921 15510137862630934444429441)
        ·
          refine ⟨11632603396973200833322081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15510137862630934444429441 11632603396973200833322081)
          ·
            refine ⟨8724452547729900624991561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11632603396973200833322081 8724452547729900624991561)
            ·
              refine ⟨6543339410797425468743671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8724452547729900624991561 6543339410797425468743671)
              ·
                refine ⟨9815009116196138203115507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543339410797425468743671 9815009116196138203115507)
                ·
                  refine ⟨14722513674294207304673261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9815009116196138203115507 14722513674294207304673261)
                  ·
                    refine ⟨5520942627860327739252473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14722513674294207304673261 5520942627860327739252473)
                    ·
                      refine ⟨4140706970895245804439355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5520942627860327739252473 4140706970895245804439355)
                      ·
                        rfl

theorem cell23_8063998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_8063998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8063998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8063998 prefixEnd_8063998 := by exact prefixLift 8063998
  have htrace : WordTrace (prefixWord ++ tailWord_8063998) baseStart_8063998 baseEnd_8063998 := by
    simpa [prefixWord, tailWord_8063998, baseEnd_8063998] using wordTrace_append hprefix tailTrace_8063998
  have hstable : (prefixWord ++ tailWord_8063998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8063998).length < 2 ^ (prefixWord ++ tailWord_8063998).sum := by decide
  have hdescent : baseEnd_8063998 < baseStart_8063998 := by decide
  rcases family_descends (prefixWord ++ tailWord_8063998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064010 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3]
def baseStart_8064010 : Nat := 118140960795 + 8064010 * 2 ^ 59
def prefixEnd_8064010 : Nat := 4983230072969 + 3 ^ 40 * 8064010 * 2
def baseEnd_8064010 : Nat := 4140713132663099757489299

theorem tailTrace_8064010 : CollatzResearch.WordTrace tailWord_8064010 prefixEnd_8064010 4140713132663099757489299 := by
  unfold tailWord_8064010
  simp only [CollatzResearch.WordTrace]
  refine ⟨73529651878869117026691371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196079071676984312071176989 73529651878869117026691371)
  ·
    refine ⟨110294477818303675540037057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73529651878869117026691371 110294477818303675540037057)
    ·
      refine ⟨82720858363727756655027793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110294477818303675540037057 82720858363727756655027793)
      ·
        refine ⟨62040643772795817491270845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82720858363727756655027793 62040643772795817491270845)
        ·
          refine ⟨23265241414798431559226567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62040643772795817491270845 23265241414798431559226567)
          ·
            refine ⟨34897862122197647338839851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23265241414798431559226567 34897862122197647338839851)
            ·
              refine ⟨52346793183296471008259777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34897862122197647338839851 52346793183296471008259777)
              ·
                refine ⟨39260094887472353256194833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52346793183296471008259777 39260094887472353256194833)
                ·
                  refine ⟨29445071165604264942146125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39260094887472353256194833 29445071165604264942146125)
                  ·
                    refine ⟨11041901687101599353304797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29445071165604264942146125 11041901687101599353304797)
                    ·
                      refine ⟨4140713132663099757489299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11041901687101599353304797 4140713132663099757489299)
                      ·
                        rfl

theorem cell23_8064010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3].length) (baseStart_8064010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064010 prefixEnd_8064010 := by exact prefixLift 8064010
  have htrace : WordTrace (prefixWord ++ tailWord_8064010) baseStart_8064010 baseEnd_8064010 := by
    simpa [prefixWord, tailWord_8064010, baseEnd_8064010] using wordTrace_append hprefix tailTrace_8064010
  have hstable : (prefixWord ++ tailWord_8064010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064010).length < 2 ^ (prefixWord ++ tailWord_8064010).sum := by decide
  have hdescent : baseEnd_8064010 < baseStart_8064010 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064050 : List Nat := [3, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4]
def baseStart_8064050 : Nat := 118140960795 + 8064050 * 2 ^ 59
def prefixEnd_8064050 : Nat := 4983230072969 + 3 ^ 40 * 8064050 * 2
def baseEnd_8064050 : Nat := 4140733671889279600989115

theorem tailTrace_8064050 : CollatzResearch.WordTrace tailWord_8064050 prefixEnd_8064050 4140733671889279600989115 := by
  unfold tailWord_8064050
  simp only [CollatzResearch.WordTrace]
  refine ⟨73530016608832888734555401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196080044290221036625481069 73530016608832888734555401)
  ·
    refine ⟨55147512456624666550916551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73530016608832888734555401 55147512456624666550916551)
    ·
      refine ⟨82721268684936999826374827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55147512456624666550916551 82721268684936999826374827)
      ·
        refine ⟨124081903027405499739562241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82721268684936999826374827 124081903027405499739562241)
        ·
          refine ⟨93061427270554124804671681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124081903027405499739562241 93061427270554124804671681)
          ·
            refine ⟨69796070452915593603503761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93061427270554124804671681 69796070452915593603503761)
            ·
              refine ⟨52347052839686695202627821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69796070452915593603503761 52347052839686695202627821)
              ·
                refine ⟨19630144814882510700985433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52347052839686695202627821 19630144814882510700985433)
                ·
                  refine ⟨14722608611161883025739075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19630144814882510700985433 14722608611161883025739075)
                  ·
                    refine ⟨22083912916742824538608613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14722608611161883025739075 22083912916742824538608613)
                    ·
                      refine ⟨4140733671889279600989115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22083912916742824538608613 4140733671889279600989115)
                      ·
                        rfl

theorem cell23_8064050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 3, 2, 1, 4].length) (baseStart_8064050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064050 prefixEnd_8064050 := by exact prefixLift 8064050
  have htrace : WordTrace (prefixWord ++ tailWord_8064050) baseStart_8064050 baseEnd_8064050 := by
    simpa [prefixWord, tailWord_8064050, baseEnd_8064050] using wordTrace_append hprefix tailTrace_8064050
  have hstable : (prefixWord ++ tailWord_8064050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064050).length < 2 ^ (prefixWord ++ tailWord_8064050).sum := by decide
  have hdescent : baseEnd_8064050 < baseStart_8064050 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064053 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 5]
def baseStart_8064053 : Nat := 118140960795 + 8064053 * 2 ^ 59
def prefixEnd_8064053 : Nat := 4983230072969 + 3 ^ 40 * 8064053 * 2
def baseEnd_8064053 : Nat := 4140735212331243089251601

theorem tailTrace_8064053 : CollatzResearch.WordTrace tailWord_8064053 prefixEnd_8064053 4140735212331243089251601 := by
  unfold tailWord_8064053
  simp only [CollatzResearch.WordTrace]
  refine ⟨294120175854320686450580813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196080117236213790967053875 294120175854320686450580813)
  ·
    refine ⟨110295065945370257418967805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294120175854320686450580813 110295065945370257418967805)
    ·
      refine ⟨41360649729513846532112927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110295065945370257418967805 41360649729513846532112927)
      ·
        refine ⟨62040974594270769798169391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41360649729513846532112927 62040974594270769798169391)
        ·
          refine ⟨93061461891406154697254087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62040974594270769798169391 93061461891406154697254087)
          ·
            refine ⟨139592192837109232045881131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93061461891406154697254087 139592192837109232045881131)
            ·
              refine ⟨209388289255663848068821697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139592192837109232045881131 209388289255663848068821697)
              ·
                refine ⟨157041216941747886051616273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209388289255663848068821697 157041216941747886051616273)
                ·
                  refine ⟨117780912706310914538712205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 157041216941747886051616273 117780912706310914538712205)
                  ·
                    refine ⟨44167842264866592952017077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117780912706310914538712205 44167842264866592952017077)
                    ·
                      refine ⟨4140735212331243089251601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44167842264866592952017077 4140735212331243089251601)
                      ·
                        rfl

theorem cell23_8064053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 2, 3, 5].length) (baseStart_8064053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064053 prefixEnd_8064053 := by exact prefixLift 8064053
  have htrace : WordTrace (prefixWord ++ tailWord_8064053) baseStart_8064053 baseEnd_8064053 := by
    simpa [prefixWord, tailWord_8064053, baseEnd_8064053] using wordTrace_append hprefix tailTrace_8064053
  have hstable : (prefixWord ++ tailWord_8064053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064053).length < 2 ^ (prefixWord ++ tailWord_8064053).sum := by decide
  have hdescent : baseEnd_8064053 < baseStart_8064053 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064113 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 5]
def baseStart_8064113 : Nat := 118140960795 + 8064113 * 2 ^ 59
def prefixEnd_8064113 : Nat := 4983230072969 + 3 ^ 40 * 8064113 * 2
def baseEnd_8064113 : Nat := 4140766021170512854501325

theorem tailTrace_8064113 : CollatzResearch.WordTrace tailWord_8064113 prefixEnd_8064113 4140766021170512854501325 := by
  unfold tailWord_8064113
  simp only [CollatzResearch.WordTrace]
  refine ⟨294122364234103316697764993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196081576156068877798509995 294122364234103316697764993)
  ·
    refine ⟨220591773175577487523323745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294122364234103316697764993 220591773175577487523323745)
    ·
      refine ⟨165443829881683115642492809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220591773175577487523323745 165443829881683115642492809)
      ·
        refine ⟨124082872411262336731869607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165443829881683115642492809 124082872411262336731869607)
        ·
          refine ⟨186124308616893505097804411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124082872411262336731869607 186124308616893505097804411)
          ·
            refine ⟨279186462925340257646706617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186124308616893505097804411 279186462925340257646706617)
            ·
              refine ⟨209389847194005193235029963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279186462925340257646706617 209389847194005193235029963)
              ·
                refine ⟨314084770791007789852544945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209389847194005193235029963 314084770791007789852544945)
                ·
                  refine ⟨235563578093255842389408709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314084770791007789852544945 235563578093255842389408709)
                  ·
                    refine ⟨44168170892485470448014133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235563578093255842389408709 44168170892485470448014133)
                    ·
                      refine ⟨4140766021170512854501325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44168170892485470448014133 4140766021170512854501325)
                      ·
                        rfl

theorem cell23_8064113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_8064113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064113 prefixEnd_8064113 := by exact prefixLift 8064113
  have htrace : WordTrace (prefixWord ++ tailWord_8064113) baseStart_8064113 baseEnd_8064113 := by
    simpa [prefixWord, tailWord_8064113, baseEnd_8064113] using wordTrace_append hprefix tailTrace_8064113
  have hstable : (prefixWord ++ tailWord_8064113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064113).length < 2 ^ (prefixWord ++ tailWord_8064113).sum := by decide
  have hdescent : baseEnd_8064113 < baseStart_8064113 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064120 : List Nat := [2, 1, 2, 1, 1, 1, 4, 5, 1, 5]
def baseStart_8064120 : Nat := 118140960795 + 8064120 * 2 ^ 59
def prefixEnd_8064120 : Nat := 4983230072969 + 3 ^ 40 * 8064120 * 2
def baseEnd_8064120 : Nat := 1380256538511698109037931

theorem tailTrace_8064120 : CollatzResearch.WordTrace tailWord_8064120 prefixEnd_8064120 1380256538511698109037931 := by
  unfold tailWord_8064120
  simp only [CollatzResearch.WordTrace]
  refine ⟨147061309772538978446634907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196081746363385304595513209 147061309772538978446634907)
  ·
    refine ⟨220591964658808467669952361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147061309772538978446634907 220591964658808467669952361)
    ·
      refine ⟨165443973494106350752464271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220591964658808467669952361 165443973494106350752464271)
      ·
        refine ⟨248165960241159526128696407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165443973494106350752464271 248165960241159526128696407)
        ·
          refine ⟨372248940361739289193044611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248165960241159526128696407 372248940361739289193044611)
          ·
            refine ⟨558373410542608933789566917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372248940361739289193044611 558373410542608933789566917)
            ·
              refine ⟨104695014476739175085543797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 558373410542608933789566917 104695014476739175085543797)
              ·
                refine ⟨9815157607194297664269731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104695014476739175085543797 9815157607194297664269731)
                ·
                  refine ⟨14722736410791446496404597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9815157607194297664269731 14722736410791446496404597)
                  ·
                    refine ⟨1380256538511698109037931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14722736410791446496404597 1380256538511698109037931)
                    ·
                      rfl

theorem cell23_8064120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_8064120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064120 prefixEnd_8064120 := by exact prefixLift 8064120
  have htrace : WordTrace (prefixWord ++ tailWord_8064120) baseStart_8064120 baseEnd_8064120 := by
    simpa [prefixWord, tailWord_8064120, baseEnd_8064120] using wordTrace_append hprefix tailTrace_8064120
  have hstable : (prefixWord ++ tailWord_8064120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064120).length < 2 ^ (prefixWord ++ tailWord_8064120).sum := by decide
  have hdescent : baseEnd_8064120 < baseStart_8064120 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064157 : List Nat := [1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 4]
def baseStart_8064157 : Nat := 118140960795 + 8064157 * 2 ^ 59
def prefixEnd_8064157 : Nat := 4983230072969 + 3 ^ 40 * 8064157 * 2
def baseEnd_8064157 : Nat := 4140788614319310682351123

theorem tailTrace_8064157 : CollatzResearch.WordTrace tailWord_8064157 prefixEnd_8064157 4140788614319310682351123 := by
  unfold tailWord_8064157
  simp only [CollatzResearch.WordTrace]
  refine ⟨294123969045943912212366725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196082646030629274808244483 294123969045943912212366725)
  ·
    refine ⟨55148244196114483539818761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294123969045943912212366725 55148244196114483539818761)
    ·
      refine ⟨41361183147085862654864071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55148244196114483539818761 41361183147085862654864071)
      ·
        refine ⟨62041774720628793982296107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41361183147085862654864071 62041774720628793982296107)
        ·
          refine ⟨93062662080943190973444161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62041774720628793982296107 93062662080943190973444161)
          ·
            refine ⟨69796996560707393230083121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93062662080943190973444161 69796996560707393230083121)
            ·
              refine ⟨52347747420530544922562341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69796996560707393230083121 52347747420530544922562341)
              ·
                refine ⟨9815202641349477172980439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52347747420530544922562341 9815202641349477172980439)
                ·
                  refine ⟨14722803962024215759470659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9815202641349477172980439 14722803962024215759470659)
                  ·
                    refine ⟨22084205943036323639205989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14722803962024215759470659 22084205943036323639205989)
                    ·
                      refine ⟨4140788614319310682351123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22084205943036323639205989 4140788614319310682351123)
                      ·
                        rfl

theorem cell23_8064157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_8064157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064157 prefixEnd_8064157 := by exact prefixLift 8064157
  have htrace : WordTrace (prefixWord ++ tailWord_8064157) baseStart_8064157 baseEnd_8064157 := by
    simpa [prefixWord, tailWord_8064157, baseEnd_8064157] using wordTrace_append hprefix tailTrace_8064157
  have hstable : (prefixWord ++ tailWord_8064157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064157).length < 2 ^ (prefixWord ++ tailWord_8064157).sum := by decide
  have hdescent : baseEnd_8064157 < baseStart_8064157 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064163 : List Nat := [1, 1, 1, 4, 1, 1, 1, 13]
def baseStart_8064163 : Nat := 118140960795 + 8064163 * 2 ^ 59
def prefixEnd_8064163 : Nat := 4983230072969 + 3 ^ 40 * 8064163 * 2
def baseEnd_8064163 : Nat := 153362655377897691069485

theorem tailTrace_8064163 : CollatzResearch.WordTrace tailWord_8064163 prefixEnd_8064163 153362655377897691069485 := by
  unfold tailWord_8064163
  simp only [CollatzResearch.WordTrace]
  refine ⟨294124187883922175237085143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196082791922614783491390095 294124187883922175237085143)
  ·
    refine ⟨441186281825883262855627715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294124187883922175237085143 441186281825883262855627715)
    ·
      refine ⟨661779422738824894283441573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441186281825883262855627715 661779422738824894283441573)
      ·
        refine ⟨124083641763529667678145295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 661779422738824894283441573 124083641763529667678145295)
        ·
          refine ⟨186125462645294501517217943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124083641763529667678145295 186125462645294501517217943)
          ·
            refine ⟨279188193967941752275826915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186125462645294501517217943 279188193967941752275826915)
            ·
              refine ⟨418782290951912628413740373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279188193967941752275826915 418782290951912628413740373)
              ·
                refine ⟨153362655377897691069485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 418782290951912628413740373 153362655377897691069485)
                ·
                  rfl

theorem cell23_8064163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 13].length) (baseStart_8064163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064163 prefixEnd_8064163 := by exact prefixLift 8064163
  have htrace : WordTrace (prefixWord ++ tailWord_8064163) baseStart_8064163 baseEnd_8064163 := by
    simpa [prefixWord, tailWord_8064163, baseEnd_8064163] using wordTrace_append hprefix tailTrace_8064163
  have hstable : (prefixWord ++ tailWord_8064163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064163).length < 2 ^ (prefixWord ++ tailWord_8064163).sum := by decide
  have hdescent : baseEnd_8064163 < baseStart_8064163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064167 : List Nat := [1, 1, 6, 2, 1, 1, 2, 2, 1, 6]
def baseStart_8064167 : Nat := 118140960795 + 8064167 * 2 ^ 59
def prefixEnd_8064167 : Nat := 4983230072969 + 3 ^ 40 * 8064167 * 2
def baseEnd_8064167 : Nat := 1380264583041951881075359

theorem tailTrace_8064167 : CollatzResearch.WordTrace tailWord_8064167 prefixEnd_8064167 1380264583041951881075359 := by
  unfold tailWord_8064167
  simp only [CollatzResearch.WordTrace]
  refine ⟨294124333775907683920230755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196082889183938455946820503 294124333775907683920230755)
  ·
    refine ⟨441186500663861525880346133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294124333775907683920230755 441186500663861525880346133)
    ·
      refine ⟨20680617218618509025641225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 441186500663861525880346133 20680617218618509025641225)
      ·
        refine ⟨15510462913963881769230919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20680617218618509025641225 15510462913963881769230919)
        ·
          refine ⟨23265694370945822653846379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15510462913963881769230919 23265694370945822653846379)
          ·
            refine ⟨34898541556418733980769569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23265694370945822653846379 34898541556418733980769569)
            ·
              refine ⟨26173906167314050485577177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34898541556418733980769569 26173906167314050485577177)
              ·
                refine ⟨19630429625485537864182883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26173906167314050485577177 19630429625485537864182883)
                ·
                  refine ⟨29445644438228306796274325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19630429625485537864182883 29445644438228306796274325)
                  ·
                    refine ⟨1380264583041951881075359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29445644438228306796274325 1380264583041951881075359)
                    ·
                      rfl

theorem cell23_8064167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_8064167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064167 prefixEnd_8064167 := by exact prefixLift 8064167
  have htrace : WordTrace (prefixWord ++ tailWord_8064167) baseStart_8064167 baseEnd_8064167 := by
    simpa [prefixWord, tailWord_8064167, baseEnd_8064167] using wordTrace_append hprefix tailTrace_8064167
  have hstable : (prefixWord ++ tailWord_8064167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064167).length < 2 ^ (prefixWord ++ tailWord_8064167).sum := by decide
  have hdescent : baseEnd_8064167 < baseStart_8064167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064191 : List Nat := [1, 1, 2, 2, 2, 2, 4, 4, 1, 2, 2]
def baseStart_8064191 : Nat := 118140960795 + 8064191 * 2 ^ 59
def prefixEnd_8064191 : Nat := 4983230072969 + 3 ^ 40 * 8064191 * 2
def baseEnd_8064191 : Nat := 4140806072661563549325967

theorem tailTrace_8064191 : CollatzResearch.WordTrace tailWord_8064191 prefixEnd_8064191 4140806072661563549325967 := by
  unfold tailWord_8064191
  simp only [CollatzResearch.WordTrace]
  refine ⟨294125209127820736019104427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196083472751880490679402951 294125209127820736019104427)
  ·
    refine ⟨441187813691731104028656641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294125209127820736019104427 441187813691731104028656641)
    ·
      refine ⟨330890860268798328021492481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441187813691731104028656641 330890860268798328021492481)
      ·
        refine ⟨248168145201598746016119361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330890860268798328021492481 248168145201598746016119361)
        ·
          refine ⟨186126108901199059512089521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248168145201598746016119361 186126108901199059512089521)
          ·
            refine ⟨139594581675899294634067141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186126108901199059512089521 139594581675899294634067141)
            ·
              refine ⟨26173984064231117743887589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139594581675899294634067141 26173984064231117743887589)
              ·
                refine ⟨4907622012043334576978923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26173984064231117743887589 4907622012043334576978923)
                ·
                  refine ⟨7361433018065001865468385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4907622012043334576978923 7361433018065001865468385)
                  ·
                    refine ⟨5521074763548751399101289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7361433018065001865468385 5521074763548751399101289)
                    ·
                      refine ⟨4140806072661563549325967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521074763548751399101289 4140806072661563549325967)
                      ·
                        rfl

theorem cell23_8064191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 2, 2].length) (baseStart_8064191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064191 prefixEnd_8064191 := by exact prefixLift 8064191
  have htrace : WordTrace (prefixWord ++ tailWord_8064191) baseStart_8064191 baseEnd_8064191 := by
    simpa [prefixWord, tailWord_8064191, baseEnd_8064191] using wordTrace_append hprefix tailTrace_8064191
  have hstable : (prefixWord ++ tailWord_8064191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064191).length < 2 ^ (prefixWord ++ tailWord_8064191).sum := by decide
  have hdescent : baseEnd_8064191 < baseStart_8064191 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064214 : List Nat := [5, 2, 1, 2, 2, 1, 1, 9]
def baseStart_8064214 : Nat := 118140960795 + 8064214 * 2 ^ 59
def prefixEnd_8064214 : Nat := 4983230072969 + 3 ^ 40 * 8064214 * 2
def baseEnd_8064214 : Nat := 153363625285800628123643

theorem tailTrace_8064214 : CollatzResearch.WordTrace tailWord_8064214 prefixEnd_8064214 153363625285800628123643 := by
  unfold tailWord_8064214
  simp only [CollatzResearch.WordTrace]
  refine ⟨18382878000421088184199481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 196084032004491607298127797 18382878000421088184199481)
  ·
    refine ⟨13787158500315816138149611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18382878000421088184199481 13787158500315816138149611)
    ·
      refine ⟨20680737750473724207224417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13787158500315816138149611 20680737750473724207224417)
      ·
        refine ⟨15510553312855293155418313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20680737750473724207224417 15510553312855293155418313)
        ·
          refine ⟨11632914984641469866563735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15510553312855293155418313 11632914984641469866563735)
          ·
            refine ⟨17449372476962204799845603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11632914984641469866563735 17449372476962204799845603)
            ·
              refine ⟨26174058715443307199768405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17449372476962204799845603 26174058715443307199768405)
              ·
                refine ⟨153363625285800628123643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 26174058715443307199768405 153363625285800628123643)
                ·
                  rfl

theorem cell23_8064214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 9].length) (baseStart_8064214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064214 prefixEnd_8064214 := by exact prefixLift 8064214
  have htrace : WordTrace (prefixWord ++ tailWord_8064214) baseStart_8064214 baseEnd_8064214 := by
    simpa [prefixWord, tailWord_8064214, baseEnd_8064214] using wordTrace_append hprefix tailTrace_8064214
  have hstable : (prefixWord ++ tailWord_8064214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064214).length < 2 ^ (prefixWord ++ tailWord_8064214).sum := by decide
  have hdescent : baseEnd_8064214 < baseStart_8064214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064247 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 3, 4, 2]
def baseStart_8064247 : Nat := 118140960795 + 8064247 * 2 ^ 59
def prefixEnd_8064247 : Nat := 4983230072969 + 3 ^ 40 * 8064247 * 2
def baseEnd_8064247 : Nat := 4140834827578215330225709

theorem tailTrace_8064247 : CollatzResearch.WordTrace tailWord_8064247 prefixEnd_8064247 4140834827578215330225709 := by
  unfold tailWord_8064247
  simp only [CollatzResearch.WordTrace]
  refine ⟨294127251615617857583142995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196084834410411905055428663 294127251615617857583142995)
  ·
    refine ⟨441190877423426786374714493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294127251615617857583142995 441190877423426786374714493)
    ·
      refine ⟨165446579033785044890517935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441190877423426786374714493 165446579033785044890517935)
      ·
        refine ⟨248169868550677567335776903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165446579033785044890517935 248169868550677567335776903)
        ·
          refine ⟨372254802826016351003665355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248169868550677567335776903 372254802826016351003665355)
          ·
            refine ⟨558382204239024526505498033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372254802826016351003665355 558382204239024526505498033)
            ·
              refine ⟨418786653179268394879123525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558382204239024526505498033 418786653179268394879123525)
              ·
                refine ⟨78522497471112824039835661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418786653179268394879123525 78522497471112824039835661)
                ·
                  refine ⟨29445936551667309014938373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78522497471112824039835661 29445936551667309014938373)
                  ·
                    refine ⟨5521113103437620440300945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29445936551667309014938373 5521113103437620440300945)
                    ·
                      refine ⟨4140834827578215330225709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521113103437620440300945 4140834827578215330225709)
                      ·
                        rfl

theorem cell23_8064247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_8064247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064247 prefixEnd_8064247 := by exact prefixLift 8064247
  have htrace : WordTrace (prefixWord ++ tailWord_8064247) baseStart_8064247 baseEnd_8064247 := by
    simpa [prefixWord, tailWord_8064247, baseEnd_8064247] using wordTrace_append hprefix tailTrace_8064247
  have hstable : (prefixWord ++ tailWord_8064247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064247).length < 2 ^ (prefixWord ++ tailWord_8064247).sum := by decide
  have hdescent : baseEnd_8064247 < baseStart_8064247 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064250 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5]
def baseStart_8064250 : Nat := 118140960795 + 8064250 * 2 ^ 59
def prefixEnd_8064250 : Nat := 4983230072969 + 3 ^ 40 * 8064250 * 2
def baseEnd_8064250 : Nat := 4140836368020178818488195

theorem tailTrace_8064250 : CollatzResearch.WordTrace tailWord_8064250 prefixEnd_8064250 4140836368020178818488195 := by
  unfold tailWord_8064250
  simp only [CollatzResearch.WordTrace]
  refine ⟨73531840258651747273875551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196084907356404659397001469 73531840258651747273875551)
  ·
    refine ⟨110297760387977620910813327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73531840258651747273875551 110297760387977620910813327)
    ·
      refine ⟨165446640581966431366219991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110297760387977620910813327 165446640581966431366219991)
      ·
        refine ⟨248169960872949647049329987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165446640581966431366219991 248169960872949647049329987)
        ·
          refine ⟨372254941309424470573994981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248169960872949647049329987 372254941309424470573994981)
          ·
            refine ⟨69797801495517088232624059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 372254941309424470573994981 69797801495517088232624059)
            ·
              refine ⟨104696702243275632348936089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69797801495517088232624059 104696702243275632348936089)
              ·
                refine ⟨78522526682456724261702067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104696702243275632348936089 78522526682456724261702067)
                ·
                  refine ⟨117783790023685086392553101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78522526682456724261702067 117783790023685086392553101)
                  ·
                    refine ⟨44168921258881907397207413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117783790023685086392553101 44168921258881907397207413)
                    ·
                      refine ⟨4140836368020178818488195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44168921258881907397207413 4140836368020178818488195)
                      ·
                        rfl

theorem cell23_8064250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_8064250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064250 prefixEnd_8064250 := by exact prefixLift 8064250
  have htrace : WordTrace (prefixWord ++ tailWord_8064250) baseStart_8064250 baseEnd_8064250 := by
    simpa [prefixWord, tailWord_8064250, baseEnd_8064250] using wordTrace_append hprefix tailTrace_8064250
  have hstable : (prefixWord ++ tailWord_8064250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064250).length < 2 ^ (prefixWord ++ tailWord_8064250).sum := by decide
  have hdescent : baseEnd_8064250 < baseStart_8064250 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064258 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_8064258 : Nat := 118140960795 + 8064258 * 2 ^ 59
def prefixEnd_8064258 : Nat := 4983230072969 + 3 ^ 40 * 8064258 * 2
def baseEnd_8064258 : Nat := 4140840475865414787188159

theorem tailTrace_8064258 : CollatzResearch.WordTrace tailWord_8064258 prefixEnd_8064258 4140840475865414787188159 := by
  unfold tailWord_8064258
  simp only [CollatzResearch.WordTrace]
  refine ⟨73531913204644501615448357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196085101879052004307862285 73531913204644501615448357)
  ·
    refine ⟨13787233725870844052896567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73531913204644501615448357 13787233725870844052896567)
    ·
      refine ⟨20680850588806266079344851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13787233725870844052896567 20680850588806266079344851)
      ·
        refine ⟨31021275883209399119017277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20680850588806266079344851 31021275883209399119017277)
        ·
          refine ⟨11632978456203524669631479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31021275883209399119017277 11632978456203524669631479)
          ·
            refine ⟨17449467684305287004447219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11632978456203524669631479 17449467684305287004447219)
            ·
              refine ⟨26174201526457930506670829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17449467684305287004447219 26174201526457930506670829)
              ·
                refine ⟨9815325572421723940001561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26174201526457930506670829 9815325572421723940001561)
                ·
                  refine ⟨7361494179316292955001171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9815325572421723940001561 7361494179316292955001171)
                  ·
                    refine ⟨11042241268974439432501757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7361494179316292955001171 11042241268974439432501757)
                    ·
                      refine ⟨4140840475865414787188159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11042241268974439432501757 4140840475865414787188159)
                      ·
                        rfl

theorem cell23_8064258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_8064258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064258 prefixEnd_8064258 := by exact prefixLift 8064258
  have htrace : WordTrace (prefixWord ++ tailWord_8064258) baseStart_8064258 baseEnd_8064258 := by
    simpa [prefixWord, tailWord_8064258, baseEnd_8064258] using wordTrace_append hprefix tailTrace_8064258
  have hstable : (prefixWord ++ tailWord_8064258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064258).length < 2 ^ (prefixWord ++ tailWord_8064258).sum := by decide
  have hdescent : baseEnd_8064258 < baseStart_8064258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064298 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2]
def baseStart_8064298 : Nat := 118140960795 + 8064298 * 2 ^ 59
def prefixEnd_8064298 : Nat := 4983230072969 + 3 ^ 40 * 8064298 * 2
def baseEnd_8064298 : Nat := 4140861015091594630687975

theorem tailTrace_8064298 : CollatzResearch.WordTrace tailWord_8064298 prefixEnd_8064298 4140861015091594630687975 := by
  unfold tailWord_8064298
  simp only [CollatzResearch.WordTrace]
  refine ⟨73532277934608273323312387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196086074492288728862166365 73532277934608273323312387)
  ·
    refine ⟨110298416901912409984968581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73532277934608273323312387 110298416901912409984968581)
    ·
      refine ⟨20680953169108576872181609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110298416901912409984968581 20680953169108576872181609)
      ·
        refine ⟨15510714876831432654136207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20680953169108576872181609 15510714876831432654136207)
        ·
          refine ⟨23266072315247148981204311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15510714876831432654136207 23266072315247148981204311)
          ·
            refine ⟨34899108472870723471806467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23266072315247148981204311 34899108472870723471806467)
            ·
              refine ⟨52348662709306085207709701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34899108472870723471806467 52348662709306085207709701)
              ·
                refine ⟨9815374257994890976445569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52348662709306085207709701 9815374257994890976445569)
                ·
                  refine ⟨7361530693496168232334177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9815374257994890976445569 7361530693496168232334177)
                  ·
                    refine ⟨5521148020122126174250633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7361530693496168232334177 5521148020122126174250633)
                    ·
                      refine ⟨4140861015091594630687975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521148020122126174250633 4140861015091594630687975)
                      ·
                        rfl

theorem cell23_8064298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 2, 2].length) (baseStart_8064298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064298 prefixEnd_8064298 := by exact prefixLift 8064298
  have htrace : WordTrace (prefixWord ++ tailWord_8064298) baseStart_8064298 baseEnd_8064298 := by
    simpa [prefixWord, tailWord_8064298, baseEnd_8064298] using wordTrace_append hprefix tailTrace_8064298
  have hstable : (prefixWord ++ tailWord_8064298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064298).length < 2 ^ (prefixWord ++ tailWord_8064298).sum := by decide
  have hdescent : baseEnd_8064298 < baseStart_8064298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064300 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_8064300 : Nat := 118140960795 + 8064300 * 2 ^ 59
def prefixEnd_8064300 : Nat := 4983230072969 + 3 ^ 40 * 8064300 * 2
def baseEnd_8064300 : Nat := 1380287347350967874287655

theorem tailTrace_8064300 : CollatzResearch.WordTrace tailWord_8064300 prefixEnd_8064300 1380287347350967874287655 := by
  unfold tailWord_8064300
  simp only [CollatzResearch.WordTrace]
  refine ⟨147064592342212923817411177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196086123122950565089881569 147064592342212923817411177)
  ·
    refine ⟨110298444256659692863058383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147064592342212923817411177 110298444256659692863058383)
    ·
      refine ⟨165447666384989539294587575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110298444256659692863058383 165447666384989539294587575)
      ·
        refine ⟨248171499577484308941881363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165447666384989539294587575 248171499577484308941881363)
        ·
          refine ⟨372257249366226463412822045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248171499577484308941881363 372257249366226463412822045)
          ·
            refine ⟨139596468512334923779808267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 372257249366226463412822045 139596468512334923779808267)
            ·
              refine ⟨209394702768502385669712401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139596468512334923779808267 209394702768502385669712401)
              ·
                refine ⟨157046027076376789252284301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209394702768502385669712401 157046027076376789252284301)
                ·
                  refine ⟨58892260153641295969606613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157046027076376789252284301 58892260153641295969606613)
                  ·
                    refine ⟨1380287347350967874287655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58892260153641295969606613 1380287347350967874287655)
                    ·
                      rfl

theorem cell23_8064300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_8064300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064300 prefixEnd_8064300 := by exact prefixLift 8064300
  have htrace : WordTrace (prefixWord ++ tailWord_8064300) baseStart_8064300 baseEnd_8064300 := by
    simpa [prefixWord, tailWord_8064300, baseEnd_8064300] using wordTrace_append hprefix tailTrace_8064300
  have hstable : (prefixWord ++ tailWord_8064300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064300).length < 2 ^ (prefixWord ++ tailWord_8064300).sum := by decide
  have hdescent : baseEnd_8064300 < baseStart_8064300 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064337 : List Nat := [1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 4]
def baseStart_8064337 : Nat := 118140960795 + 8064337 * 2 ^ 59
def prefixEnd_8064337 : Nat := 4983230072969 + 3 ^ 40 * 8064337 * 2
def baseEnd_8064337 : Nat := 4140881040837119978100295

theorem tailTrace_8064337 : CollatzResearch.WordTrace tailWord_8064337 prefixEnd_8064337 4140881040837119978100295 := by
  unfold tailWord_8064337
  simp only [CollatzResearch.WordTrace]
  refine ⟨294130534185291802953919265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196087022790194535302612843 294130534185291802953919265)
  ·
    refine ⟨220597900638968852215439449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294130534185291802953919265 220597900638968852215439449)
    ·
      refine ⟨165448425479226639161579587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220597900638968852215439449 165448425479226639161579587)
      ·
        refine ⟨248172638218839958742369381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165448425479226639161579587 248172638218839958742369381)
        ·
          refine ⟨46532369666032492264194259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248172638218839958742369381 46532369666032492264194259)
          ·
            refine ⟨69798554499048738396291389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46532369666032492264194259 69798554499048738396291389)
            ·
              refine ⟨26174457937143276898609271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69798554499048738396291389 26174457937143276898609271)
              ·
                refine ⟨39261686905714915347913907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26174457937143276898609271 39261686905714915347913907)
                ·
                  refine ⟨58892530358572373021870861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39261686905714915347913907 58892530358572373021870861)
                  ·
                    refine ⟨22084698884464639883201573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58892530358572373021870861 22084698884464639883201573)
                    ·
                      refine ⟨4140881040837119978100295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22084698884464639883201573 4140881040837119978100295)
                      ·
                        rfl

theorem cell23_8064337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 3, 4].length) (baseStart_8064337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064337 prefixEnd_8064337 := by exact prefixLift 8064337
  have htrace : WordTrace (prefixWord ++ tailWord_8064337) baseStart_8064337 baseEnd_8064337 := by
    simpa [prefixWord, tailWord_8064337, baseEnd_8064337] using wordTrace_append hprefix tailTrace_8064337
  have hstable : (prefixWord ++ tailWord_8064337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064337).length < 2 ^ (prefixWord ++ tailWord_8064337).sum := by decide
  have hdescent : baseEnd_8064337 < baseStart_8064337 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064349 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 2, 2, 2]
def baseStart_8064349 : Nat := 118140960795 + 8064349 * 2 ^ 59
def prefixEnd_8064349 : Nat := 4983230072969 + 3 ^ 40 * 8064349 * 2
def baseEnd_8064349 : Nat := 4140887202604973931150241

theorem tailTrace_8064349 : CollatzResearch.WordTrace tailWord_8064349 prefixEnd_8064349 4140887202604973931150241 := by
  unfold tailWord_8064349
  simp only [CollatzResearch.WordTrace]
  refine ⟨294130971861248329003356101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196087314574165552668904067 294130971861248329003356101)
  ·
    refine ⟨55149557223984061688129269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294130971861248329003356101 55149557223984061688129269)
    ·
      refine ⟨5170270989748505783262119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55149557223984061688129269 5170270989748505783262119)
      ·
        refine ⟨7755406484622758674893179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170270989748505783262119 7755406484622758674893179)
        ·
          refine ⟨11633109726934138012339769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7755406484622758674893179 11633109726934138012339769)
          ·
            refine ⟨8724832295200603509254827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11633109726934138012339769 8724832295200603509254827)
            ·
              refine ⟨13087248442800905263882241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8724832295200603509254827 13087248442800905263882241)
              ·
                refine ⟨9815436332100678947911681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13087248442800905263882241 9815436332100678947911681)
                ·
                  refine ⟨7361577249075509210933761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9815436332100678947911681 7361577249075509210933761)
                  ·
                    refine ⟨5521182936806631908200321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7361577249075509210933761 5521182936806631908200321)
                    ·
                      refine ⟨4140887202604973931150241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521182936806631908200321 4140887202604973931150241)
                      ·
                        rfl

theorem cell23_8064349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 2, 2].length) (baseStart_8064349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064349 prefixEnd_8064349 := by exact prefixLift 8064349
  have htrace : WordTrace (prefixWord ++ tailWord_8064349) baseStart_8064349 baseEnd_8064349 := by
    simpa [prefixWord, tailWord_8064349, baseEnd_8064349] using wordTrace_append hprefix tailTrace_8064349
  have hstable : (prefixWord ++ tailWord_8064349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064349).length < 2 ^ (prefixWord ++ tailWord_8064349).sum := by decide
  have hdescent : baseEnd_8064349 < baseStart_8064349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064354 : List Nat := [3, 3, 2, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_8064354 : Nat := 118140960795 + 8064354 * 2 ^ 59
def prefixEnd_8064354 : Nat := 4983230072969 + 3 ^ 40 * 8064354 * 2
def baseEnd_8064354 : Nat := 4140889770008246411587717

theorem tailTrace_8064354 : CollatzResearch.WordTrace tailWord_8064354 prefixEnd_8064354 4140889770008246411587717 := by
  unfold tailWord_8064354
  simp only [CollatzResearch.WordTrace]
  refine ⟨73532788556557553714322029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196087436150820143238192077 73532788556557553714322029)
  ·
    refine ⟨27574795708709082642870761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73532788556557553714322029 27574795708709082642870761)
    ·
      refine ⟨20681096781531811982153071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27574795708709082642870761 20681096781531811982153071)
      ·
        refine ⟨31021645172297717973229607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20681096781531811982153071 31021645172297717973229607)
        ·
          refine ⟨46532467758446576959844411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31021645172297717973229607 46532467758446576959844411)
          ·
            refine ⟨69798701637669865439766617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46532467758446576959844411 69798701637669865439766617)
            ·
              refine ⟨52349026228252399079824963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69798701637669865439766617 52349026228252399079824963)
              ·
                refine ⟨78523539342378598619737445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52349026228252399079824963 78523539342378598619737445)
                ·
                  refine ⟨14723163626695987241200771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78523539342378598619737445 14723163626695987241200771)
                  ·
                    refine ⟨22084745440043980861801157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14723163626695987241200771 22084745440043980861801157)
                    ·
                      refine ⟨4140889770008246411587717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22084745440043980861801157 4140889770008246411587717)
                      ·
                        rfl

theorem cell23_8064354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_8064354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064354 prefixEnd_8064354 := by exact prefixLift 8064354
  have htrace : WordTrace (prefixWord ++ tailWord_8064354) baseStart_8064354 baseEnd_8064354 := by
    simpa [prefixWord, tailWord_8064354, baseEnd_8064354] using wordTrace_append hprefix tailTrace_8064354
  have hstable : (prefixWord ++ tailWord_8064354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064354).length < 2 ^ (prefixWord ++ tailWord_8064354).sum := by decide
  have hdescent : baseEnd_8064354 < baseStart_8064354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064364 : List Nat := [2, 2, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_8064364 : Nat := 118140960795 + 8064364 * 2 ^ 59
def prefixEnd_8064364 : Nat := 4983230072969 + 3 ^ 40 * 8064364 * 2
def baseEnd_8064364 : Nat := 1380298301604930457487557

theorem tailTrace_8064364 : CollatzResearch.WordTrace tailWord_8064364 prefixEnd_8064364 1380298301604930457487557 := by
  unfold tailWord_8064364
  simp only [CollatzResearch.WordTrace]
  refine ⟨147065759478096993282576073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196087679304129324376768097 147065759478096993282576073)
  ·
    refine ⟨110299319608572744961932055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147065759478096993282576073 110299319608572744961932055)
    ·
      refine ⟨165448979412859117442898083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110299319608572744961932055 165448979412859117442898083)
      ·
        refine ⟨248173469119288676164347125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165448979412859117442898083 248173469119288676164347125)
        ·
          refine ⟨23266262729933313390407543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 248173469119288676164347125 23266262729933313390407543)
          ·
            refine ⟨34899394094899970085611315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23266262729933313390407543 34899394094899970085611315)
            ·
              refine ⟨52349091142349955128416973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34899394094899970085611315 52349091142349955128416973)
              ·
                refine ⟨19630909178381233173156365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52349091142349955128416973 19630909178381233173156365)
                ·
                  refine ⟨7361590941892962439933637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19630909178381233173156365 7361590941892962439933637)
                  ·
                    refine ⟨1380298301604930457487557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7361590941892962439933637 1380298301604930457487557)
                    ·
                      rfl

theorem cell23_8064364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_8064364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064364 prefixEnd_8064364 := by exact prefixLift 8064364
  have htrace : WordTrace (prefixWord ++ tailWord_8064364) baseStart_8064364 baseEnd_8064364 := by
    simpa [prefixWord, tailWord_8064364, baseEnd_8064364] using wordTrace_append hprefix tailTrace_8064364
  have hstable : (prefixWord ++ tailWord_8064364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064364).length < 2 ^ (prefixWord ++ tailWord_8064364).sum := by decide
  have hdescent : baseEnd_8064364 < baseStart_8064364 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064377 : List Nat := [1, 2, 1, 3, 2, 1, 2, 5, 6]
def baseStart_8064377 : Nat := 118140960795 + 8064377 * 2 ^ 59
def prefixEnd_8064377 : Nat := 4983230072969 + 3 ^ 40 * 8064377 * 2
def baseEnd_8064377 : Nat := 460100175562588869066679

theorem tailTrace_8064377 : CollatzResearch.WordTrace tailWord_8064377 prefixEnd_8064377 460100175562588869066679 := by
  unfold tailWord_8064377
  simp only [CollatzResearch.WordTrace]
  refine ⟨294131993105146889785375385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196087995403431259856916923 294131993105146889785375385)
  ·
    refine ⟨220598994828860167339031539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294131993105146889785375385 220598994828860167339031539)
    ·
      refine ⟨330898492243290251008547309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220598994828860167339031539 330898492243290251008547309)
      ·
        refine ⟨124086934591233844128205241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330898492243290251008547309 124086934591233844128205241)
        ·
          refine ⟨93065200943425383096153931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124086934591233844128205241 93065200943425383096153931)
          ·
            refine ⟨139597801415138074644230897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93065200943425383096153931 139597801415138074644230897)
            ·
              refine ⟨104698351061353555983173173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139597801415138074644230897 104698351061353555983173173)
              ·
                refine ⟨9815470412001895873422485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104698351061353555983173173 9815470412001895873422485)
                ·
                  refine ⟨460100175562588869066679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9815470412001895873422485 460100175562588869066679)
                  ·
                    rfl

theorem cell23_8064377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 5, 6].length) (baseStart_8064377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064377 prefixEnd_8064377 := by exact prefixLift 8064377
  have htrace : WordTrace (prefixWord ++ tailWord_8064377) baseStart_8064377 baseEnd_8064377 := by
    simpa [prefixWord, tailWord_8064377, baseEnd_8064377] using wordTrace_append hprefix tailTrace_8064377
  have hstable : (prefixWord ++ tailWord_8064377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064377).length < 2 ^ (prefixWord ++ tailWord_8064377).sum := by decide
  have hdescent : baseEnd_8064377 < baseStart_8064377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064407 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 5, 5]
def baseStart_8064407 : Nat := 118140960795 + 8064407 * 2 ^ 59
def prefixEnd_8064407 : Nat := 4983230072969 + 3 ^ 40 * 8064407 * 2
def baseEnd_8064407 : Nat := 1380305661494311568074991

theorem tailTrace_8064407 : CollatzResearch.WordTrace tailWord_8064407 prefixEnd_8064407 1380305661494311568074991 := by
  unfold tailWord_8064407
  simp only [CollatzResearch.WordTrace]
  refine ⟨294133087295038204908967475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196088724863358803272644983 294133087295038204908967475)
  ·
    refine ⟨441199630942557307363451213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294133087295038204908967475 441199630942557307363451213)
    ·
      refine ⟨165449861603458990261294205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441199630942557307363451213 165449861603458990261294205)
      ·
        refine ⟨62043698101297121347985327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165449861603458990261294205 62043698101297121347985327)
        ·
          refine ⟨93065547151945682021977991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62043698101297121347985327 93065547151945682021977991)
          ·
            refine ⟨139598320727918523032966987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93065547151945682021977991 139598320727918523032966987)
            ·
              refine ⟨209397481091877784549450481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139598320727918523032966987 209397481091877784549450481)
              ·
                refine ⟨157048110818908338412087861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209397481091877784549450481 157048110818908338412087861)
                ·
                  refine ⟨14723260389272656726133237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 157048110818908338412087861 14723260389272656726133237)
                  ·
                    refine ⟨1380305661494311568074991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14723260389272656726133237 1380305661494311568074991)
                    ·
                      rfl

theorem cell23_8064407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_8064407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064407 prefixEnd_8064407 := by exact prefixLift 8064407
  have htrace : WordTrace (prefixWord ++ tailWord_8064407) baseStart_8064407 baseEnd_8064407 := by
    simpa [prefixWord, tailWord_8064407, baseEnd_8064407] using wordTrace_append hprefix tailTrace_8064407
  have hstable : (prefixWord ++ tailWord_8064407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064407).length < 2 ^ (prefixWord ++ tailWord_8064407).sum := by decide
  have hdescent : baseEnd_8064407 < baseStart_8064407 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064447 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_8064447 : Nat := 118140960795 + 8064447 * 2 ^ 59
def prefixEnd_8064447 : Nat := 4983230072969 + 3 ^ 40 * 8064447 * 2
def baseEnd_8064447 : Nat := 4140937523709114547724789

theorem tailTrace_8064447 : CollatzResearch.WordTrace tailWord_8064447 prefixEnd_8064447 4140937523709114547724789 := by
  unfold tailWord_8064447
  simp only [CollatzResearch.WordTrace]
  refine ⟨294134546214893291740423595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196089697476595527826949063 294134546214893291740423595)
  ·
    refine ⟨441201819322339937610635393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294134546214893291740423595 441201819322339937610635393)
    ·
      refine ⟨330901364491754953207976545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441201819322339937610635393 330901364491754953207976545)
      ·
        refine ⟨248176023368816214905982409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330901364491754953207976545 248176023368816214905982409)
        ·
          refine ⟨186132017526612161179486807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248176023368816214905982409 186132017526612161179486807)
          ·
            refine ⟨279198026289918241769230211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186132017526612161179486807 279198026289918241769230211)
            ·
              refine ⟨418797039434877362653845317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279198026289918241769230211 418797039434877362653845317)
              ·
                refine ⟨78524444894039505497595997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418797039434877362653845317 78524444894039505497595997)
                ·
                  refine ⟨29446666835264814561598499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78524444894039505497595997 29446666835264814561598499)
                  ·
                    refine ⟨44170000252897221842397749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29446666835264814561598499 44170000252897221842397749)
                    ·
                      refine ⟨4140937523709114547724789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44170000252897221842397749 4140937523709114547724789)
                      ·
                        rfl

theorem cell23_8064447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_8064447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064447 prefixEnd_8064447 := by exact prefixLift 8064447
  have htrace : WordTrace (prefixWord ++ tailWord_8064447) baseStart_8064447 baseEnd_8064447 := by
    simpa [prefixWord, tailWord_8064447, baseEnd_8064447] using wordTrace_append hprefix tailTrace_8064447
  have hstable : (prefixWord ++ tailWord_8064447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064447).length < 2 ^ (prefixWord ++ tailWord_8064447).sum := by decide
  have hdescent : baseEnd_8064447 < baseStart_8064447 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064507 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 5]
def baseStart_8064507 : Nat := 118140960795 + 8064507 * 2 ^ 59
def prefixEnd_8064507 : Nat := 4983230072969 + 3 ^ 40 * 8064507 * 2
def baseEnd_8064507 : Nat := 4140968332548384312974513

theorem tailTrace_8064507 : CollatzResearch.WordTrace tailWord_8064507 prefixEnd_8064507 4140968332548384312974513 := by
  unfold tailWord_8064507
  simp only [CollatzResearch.WordTrace]
  refine ⟨294136734594675921987607775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196091156396450614658405183 294136734594675921987607775)
  ·
    refine ⟨441205101892013882981411663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294136734594675921987607775 441205101892013882981411663)
    ·
      refine ⟨661807652838020824472117495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441205101892013882981411663 661807652838020824472117495)
      ·
        refine ⟨992711479257031236708176243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661807652838020824472117495 992711479257031236708176243)
        ·
          refine ⟨1489067218885546855062264365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 992711479257031236708176243 1489067218885546855062264365)
          ·
            refine ⟨558400207082080070648349137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1489067218885546855062264365 558400207082080070648349137)
            ·
              refine ⟨418800155311560052986261853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558400207082080070648349137 418800155311560052986261853)
              ·
                refine ⟨157050058241835019869848195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 418800155311560052986261853 157050058241835019869848195)
                ·
                  refine ⟨235575087362752529804772293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157050058241835019869848195 235575087362752529804772293)
                  ·
                    refine ⟨44170328880516099338394805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235575087362752529804772293 44170328880516099338394805)
                    ·
                      refine ⟨4140968332548384312974513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44170328880516099338394805 4140968332548384312974513)
                      ·
                        rfl

theorem cell23_8064507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_8064507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064507 prefixEnd_8064507 := by exact prefixLift 8064507
  have htrace : WordTrace (prefixWord ++ tailWord_8064507) baseStart_8064507 baseEnd_8064507 := by
    simpa [prefixWord, tailWord_8064507, baseEnd_8064507] using wordTrace_append hprefix tailTrace_8064507
  have hstable : (prefixWord ++ tailWord_8064507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064507).length < 2 ^ (prefixWord ++ tailWord_8064507).sum := by decide
  have hdescent : baseEnd_8064507 < baseStart_8064507 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064545 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 2, 1, 3]
def baseStart_8064545 : Nat := 118140960795 + 8064545 * 2 ^ 59
def prefixEnd_8064545 : Nat := 4983230072969 + 3 ^ 40 * 8064545 * 2
def baseEnd_8064545 : Nat := 4140987844813255164299339

theorem tailTrace_8064545 : CollatzResearch.WordTrace tailWord_8064545 prefixEnd_8064545 4140987844813255164299339 := by
  unfold tailWord_8064545
  simp only [CollatzResearch.WordTrace]
  refine ⟨294138120568538254477491089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196092080379025502984994059 294138120568538254477491089)
  ·
    refine ⟨220603590426403690858118317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294138120568538254477491089 220603590426403690858118317)
    ·
      refine ⟨82726346409901384071794369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220603590426403690858118317 82726346409901384071794369)
      ·
        refine ⟨62044759807426038053845777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82726346409901384071794369 62044759807426038053845777)
        ·
          refine ⟨46533569855569528540384333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62044759807426038053845777 46533569855569528540384333)
          ·
            refine ⟨17450088695838573202644125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46533569855569528540384333 17450088695838573202644125)
            ·
              refine ⟨6543783260939464950991547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17450088695838573202644125 6543783260939464950991547)
              ·
                refine ⟨9815674891409197426487321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543783260939464950991547 9815674891409197426487321)
                ·
                  refine ⟨7361756168556898069865491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9815674891409197426487321 7361756168556898069865491)
                  ·
                    refine ⟨11042634252835347104798237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7361756168556898069865491 11042634252835347104798237)
                    ·
                      refine ⟨4140987844813255164299339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11042634252835347104798237 4140987844813255164299339)
                      ·
                        rfl

theorem cell23_8064545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 1, 3].length) (baseStart_8064545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064545 prefixEnd_8064545 := by exact prefixLift 8064545
  have htrace : WordTrace (prefixWord ++ tailWord_8064545) baseStart_8064545 baseEnd_8064545 := by
    simpa [prefixWord, tailWord_8064545, baseEnd_8064545] using wordTrace_append hprefix tailTrace_8064545
  have hstable : (prefixWord ++ tailWord_8064545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064545).length < 2 ^ (prefixWord ++ tailWord_8064545).sum := by decide
  have hdescent : baseEnd_8064545 < baseStart_8064545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064568 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 4, 2, 2]
def baseStart_8064568 : Nat := 118140960795 + 8064568 * 2 ^ 59
def prefixEnd_8064568 : Nat := 4983230072969 + 3 ^ 40 * 8064568 * 2
def baseEnd_8064568 : Nat := 4140999654868308574311733

theorem tailTrace_8064568 : CollatzResearch.WordTrace tailWord_8064568 prefixEnd_8064568 4140999654868308574311733 := by
  unfold tailWord_8064568
  simp only [CollatzResearch.WordTrace]
  refine ⟨147069479723727464702789179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196092639631636619603718905 147069479723727464702789179)
  ·
    refine ⟨220604219585591197054183769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147069479723727464702789179 220604219585591197054183769)
    ·
      refine ⟨165453164689193397790637827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220604219585591197054183769 165453164689193397790637827)
      ·
        refine ⟨248179747033790096685956741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165453164689193397790637827 248179747033790096685956741)
        ·
          refine ⟨46533702568835643128616889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 248179747033790096685956741 46533702568835643128616889)
          ·
            refine ⟨34900276926626732346462667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46533702568835643128616889 34900276926626732346462667)
            ·
              refine ⟨52350415389940098519694001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34900276926626732346462667 52350415389940098519694001)
              ·
                refine ⟨39262811542455073889770501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52350415389940098519694001 39262811542455073889770501)
                ·
                  refine ⟨7361777164210326354331969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39262811542455073889770501 7361777164210326354331969)
                  ·
                    refine ⟨5521332873157744765748977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7361777164210326354331969 5521332873157744765748977)
                    ·
                      refine ⟨4140999654868308574311733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521332873157744765748977 4140999654868308574311733)
                      ·
                        rfl

theorem cell23_8064568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_8064568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064568 prefixEnd_8064568 := by exact prefixLift 8064568
  have htrace : WordTrace (prefixWord ++ tailWord_8064568) baseStart_8064568 baseEnd_8064568 := by
    simpa [prefixWord, tailWord_8064568, baseEnd_8064568] using wordTrace_append hprefix tailTrace_8064568
  have hstable : (prefixWord ++ tailWord_8064568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064568).length < 2 ^ (prefixWord ++ tailWord_8064568).sum := by decide
  have hdescent : baseEnd_8064568 < baseStart_8064568 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064651 : List Nat := [1, 1, 1, 1, 4, 1, 4, 3, 3, 4]
def baseStart_8064651 : Nat := 118140960795 + 8064651 * 2 ^ 59
def prefixEnd_8064651 : Nat := 4983230072969 + 3 ^ 40 * 8064651 * 2
def baseEnd_8064651 : Nat := 1380347424587543916524617

theorem tailTrace_8064651 : CollatzResearch.WordTrace tailWord_8064651 prefixEnd_8064651 1380347424587543916524617 := by
  unfold tailWord_8064651
  simp only [CollatzResearch.WordTrace]
  refine ⟨294141986706154234580849807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196094657804102823053899871 294141986706154234580849807)
  ·
    refine ⟨441212980059231351871274711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294141986706154234580849807 441212980059231351871274711)
    ·
      refine ⟨661819470088847027806912067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441212980059231351871274711 661819470088847027806912067)
      ·
        refine ⟨992729205133270541710368101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 661819470088847027806912067 992729205133270541710368101)
        ·
          refine ⟨186136725962488226570694019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 992729205133270541710368101 186136725962488226570694019)
          ·
            refine ⟨279205088943732339856041029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186136725962488226570694019 279205088943732339856041029)
            ·
              refine ⟨52350954176949813723007693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 279205088943732339856041029 52350954176949813723007693)
              ·
                refine ⟨19631607816356180146127885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52350954176949813723007693 19631607816356180146127885)
                ·
                  refine ⟨7361852931133567554797957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19631607816356180146127885 7361852931133567554797957)
                  ·
                    refine ⟨1380347424587543916524617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7361852931133567554797957 1380347424587543916524617)
                    ·
                      rfl

theorem cell23_8064651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 3, 3, 4].length) (baseStart_8064651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064651 prefixEnd_8064651 := by exact prefixLift 8064651
  have htrace : WordTrace (prefixWord ++ tailWord_8064651) baseStart_8064651 baseEnd_8064651 := by
    simpa [prefixWord, tailWord_8064651, baseEnd_8064651] using wordTrace_append hprefix tailTrace_8064651
  have hstable : (prefixWord ++ tailWord_8064651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064651).length < 2 ^ (prefixWord ++ tailWord_8064651).sum := by decide
  have hdescent : baseEnd_8064651 < baseStart_8064651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064661 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 3]
def baseStart_8064661 : Nat := 118140960795 + 8064661 * 2 ^ 59
def prefixEnd_8064661 : Nat := 4983230072969 + 3 ^ 40 * 8064661 * 2
def baseEnd_8064661 : Nat := 4141047408569176710448805

theorem tailTrace_8064661 : CollatzResearch.WordTrace tailWord_8064661 prefixEnd_8064661 4141047408569176710448805 := by
  unfold tailWord_8064661
  simp only [CollatzResearch.WordTrace]
  refine ⟨294142351436118006288713837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196094900957412004192475891 294142351436118006288713837)
  ·
    refine ⟨110303381788544252358267689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294142351436118006288713837 110303381788544252358267689)
    ·
      refine ⟨82727536341408189268700767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110303381788544252358267689 82727536341408189268700767)
      ·
        refine ⟨124091304512112283903051151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82727536341408189268700767 124091304512112283903051151)
        ·
          refine ⟨186136956768168425854576727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124091304512112283903051151 186136956768168425854576727)
          ·
            refine ⟨279205435152252638781865091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186136956768168425854576727 279205435152252638781865091)
            ·
              refine ⟨418808152728378958172797637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279205435152252638781865091 418808152728378958172797637)
              ·
                refine ⟨78526528636571054657399557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 418808152728378958172797637 78526528636571054657399557)
                ·
                  refine ⟨14723724119357072748262417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78526528636571054657399557 14723724119357072748262417)
                  ·
                    refine ⟨11042793089517804561196813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14723724119357072748262417 11042793089517804561196813)
                    ·
                      refine ⟨4141047408569176710448805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11042793089517804561196813 4141047408569176710448805)
                      ·
                        rfl

theorem cell23_8064661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_8064661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064661 prefixEnd_8064661 := by exact prefixLift 8064661
  have htrace : WordTrace (prefixWord ++ tailWord_8064661) baseStart_8064661 baseEnd_8064661 := by
    simpa [prefixWord, tailWord_8064661, baseEnd_8064661] using wordTrace_append hprefix tailTrace_8064661
  have hstable : (prefixWord ++ tailWord_8064661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064661).length < 2 ^ (prefixWord ++ tailWord_8064661).sum := by decide
  have hdescent : baseEnd_8064661 < baseStart_8064661 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064684 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_8064684 : Nat := 118140960795 + 8064684 * 2 ^ 59
def prefixEnd_8064684 : Nat := 4983230072969 + 3 ^ 40 * 8064684 * 2
def baseEnd_8064684 : Nat := 4141059218624230120461199

theorem tailTrace_8064684 : CollatzResearch.WordTrace tailWord_8064684 prefixEnd_8064684 4141059218624230120461199 := by
  unfold tailWord_8064684
  simp only [CollatzResearch.WordTrace]
  refine ⟨147071595157517340608400553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196095460210023120811200737 147071595157517340608400553)
  ·
    refine ⟨110303696368138005456300415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147071595157517340608400553 110303696368138005456300415)
    ·
      refine ⟨165455544552207008184450623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110303696368138005456300415 165455544552207008184450623)
      ·
        refine ⟨248183316828310512276675935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165455544552207008184450623 248183316828310512276675935)
        ·
          refine ⟨372274975242465768415013903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248183316828310512276675935 372274975242465768415013903)
          ·
            refine ⟨558412462863698652622520855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372274975242465768415013903 558412462863698652622520855)
            ·
              refine ⟨837618694295547978933781283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 558412462863698652622520855 837618694295547978933781283)
              ·
                refine ⟨1256428041443321968400671925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 837618694295547978933781283 1256428041443321968400671925)
                ·
                  refine ⟨117790128885311434537562993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1256428041443321968400671925 117790128885311434537562993)
                  ·
                    refine ⟨88342596663983575903172245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 117790128885311434537562993 88342596663983575903172245)
                    ·
                      refine ⟨4141059218624230120461199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88342596663983575903172245 4141059218624230120461199)
                      ·
                        rfl

theorem cell23_8064684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_8064684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064684 prefixEnd_8064684 := by exact prefixLift 8064684
  have htrace : WordTrace (prefixWord ++ tailWord_8064684) baseStart_8064684 baseEnd_8064684 := by
    simpa [prefixWord, tailWord_8064684, baseEnd_8064684] using wordTrace_append hprefix tailTrace_8064684
  have hstable : (prefixWord ++ tailWord_8064684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064684).length < 2 ^ (prefixWord ++ tailWord_8064684).sum := by decide
  have hdescent : baseEnd_8064684 < baseStart_8064684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064698 : List Nat := [3, 1, 1, 1, 2, 6, 1, 2, 6]
def baseStart_8064698 : Nat := 118140960795 + 8064698 * 2 ^ 59
def prefixEnd_8064698 : Nat := 4983230072969 + 3 ^ 40 * 8064698 * 2
def baseEnd_8064698 : Nat := 460118489705932562854015

theorem tailTrace_8064698 : CollatzResearch.WordTrace tailWord_8064698 prefixEnd_8064698 460118489705932562854015 := by
  unfold tailWord_8064698
  simp only [CollatzResearch.WordTrace]
  refine ⟨73535925234245990401952687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196095800624655974405207165 73535925234245990401952687)
  ·
    refine ⟨110303887851368985602929031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73535925234245990401952687 110303887851368985602929031)
    ·
      refine ⟨165455831777053478404393547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110303887851368985602929031 165455831777053478404393547)
      ·
        refine ⟨248183747665580217606590321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165455831777053478404393547 248183747665580217606590321)
        ·
          refine ⟨186137810749185163204942741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248183747665580217606590321 186137810749185163204942741)
          ·
            refine ⟨8725209878868054525231691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 186137810749185163204942741 8725209878868054525231691)
            ·
              refine ⟨13087814818302081787847537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8725209878868054525231691 13087814818302081787847537)
              ·
                refine ⟨9815861113726561340885653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13087814818302081787847537 9815861113726561340885653)
                ·
                  refine ⟨460118489705932562854015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9815861113726561340885653 460118489705932562854015)
                  ·
                    rfl

theorem cell23_8064698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 2, 6].length) (baseStart_8064698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064698 prefixEnd_8064698 := by exact prefixLift 8064698
  have htrace : WordTrace (prefixWord ++ tailWord_8064698) baseStart_8064698 baseEnd_8064698 := by
    simpa [prefixWord, tailWord_8064698, baseEnd_8064698] using wordTrace_append hprefix tailTrace_8064698
  have hstable : (prefixWord ++ tailWord_8064698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064698).length < 2 ^ (prefixWord ++ tailWord_8064698).sum := by decide
  have hdescent : baseEnd_8064698 < baseStart_8064698 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064718 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2]
def baseStart_8064718 : Nat := 118140960795 + 8064718 * 2 ^ 59
def prefixEnd_8064718 : Nat := 4983230072969 + 3 ^ 40 * 8064718 * 2
def baseEnd_8064718 : Nat := 4141076676966482987436043

theorem tailTrace_8064718 : CollatzResearch.WordTrace tailWord_8064718 prefixEnd_8064718 4141076676966482987436043 := by
  unfold tailWord_8064718
  simp only [CollatzResearch.WordTrace]
  refine ⟨36768053799613938127942351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196096286931274336682359205 36768053799613938127942351)
  ·
    refine ⟨55152080699420907191913527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36768053799613938127942351 55152080699420907191913527)
    ·
      refine ⟨82728121049131360787870291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55152080699420907191913527 82728121049131360787870291)
      ·
        refine ⟨124092181573697041181805437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82728121049131360787870291 124092181573697041181805437)
        ·
          refine ⟨46534568090136390443177039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124092181573697041181805437 46534568090136390443177039)
          ·
            refine ⟨69801852135204585664765559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46534568090136390443177039 69801852135204585664765559)
            ·
              refine ⟨104702778202806878497148339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69801852135204585664765559 104702778202806878497148339)
              ·
                refine ⟨157054167304210317745722509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104702778202806878497148339 157054167304210317745722509)
                ·
                  refine ⟨58895312739078869154645941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 157054167304210317745722509 58895312739078869154645941)
                  ·
                    refine ⟨5521435569288643983248057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58895312739078869154645941 5521435569288643983248057)
                    ·
                      refine ⟨4141076676966482987436043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521435569288643983248057 4141076676966482987436043)
                      ·
                        rfl

theorem cell23_8064718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 5, 2].length) (baseStart_8064718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064718 prefixEnd_8064718 := by exact prefixLift 8064718
  have htrace : WordTrace (prefixWord ++ tailWord_8064718) baseStart_8064718 baseEnd_8064718 := by
    simpa [prefixWord, tailWord_8064718, baseEnd_8064718] using wordTrace_append hprefix tailTrace_8064718
  have hstable : (prefixWord ++ tailWord_8064718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064718).length < 2 ^ (prefixWord ++ tailWord_8064718).sum := by decide
  have hdescent : baseEnd_8064718 < baseStart_8064718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064728 : List Nat := [2, 1, 2, 2, 3, 1, 4, 2, 1, 5]
def baseStart_8064728 : Nat := 118140960795 + 8064728 * 2 ^ 59
def prefixEnd_8064728 : Nat := 4983230072969 + 3 ^ 40 * 8064728 * 2
def baseEnd_8064728 : Nat := 1380360603924342649436999

theorem tailTrace_8064728 : CollatzResearch.WordTrace tailWord_8064728 prefixEnd_8064728 1380360603924342649436999 := by
  unfold tailWord_8064728
  simp only [CollatzResearch.WordTrace]
  refine ⟨147072397563437638365701419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196096530084583517820935225 147072397563437638365701419)
  ·
    refine ⟨220608596345156457548552129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147072397563437638365701419 220608596345156457548552129)
    ·
      refine ⟨165456447258867343161414097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220608596345156457548552129 165456447258867343161414097)
      ·
        refine ⟨124092335444150507371060573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165456447258867343161414097 124092335444150507371060573)
        ·
          refine ⟨46534625791556440264147715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 124092335444150507371060573 46534625791556440264147715)
          ·
            refine ⟨69801938687334660396221573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46534625791556440264147715 69801938687334660396221573)
            ·
              refine ⟨13087863503875248824291545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69801938687334660396221573 13087863503875248824291545)
              ·
                refine ⟨9815897627906436618218659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13087863503875248824291545 9815897627906436618218659)
                ·
                  refine ⟨14723846441859654927327989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9815897627906436618218659 14723846441859654927327989)
                  ·
                    refine ⟨1380360603924342649436999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14723846441859654927327989 1380360603924342649436999)
                    ·
                      rfl

theorem cell23_8064728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_8064728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064728 prefixEnd_8064728 := by exact prefixLift 8064728
  have htrace : WordTrace (prefixWord ++ tailWord_8064728) baseStart_8064728 baseEnd_8064728 := by
    simpa [prefixWord, tailWord_8064728, baseEnd_8064728] using wordTrace_append hprefix tailTrace_8064728
  have hstable : (prefixWord ++ tailWord_8064728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064728).length < 2 ^ (prefixWord ++ tailWord_8064728).sum := by decide
  have hdescent : baseEnd_8064728 < baseStart_8064728 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064741 : List Nat := [1, 3, 1, 4, 1, 1, 2, 1, 3, 6]
def baseStart_8064741 : Nat := 118140960795 + 8064741 * 2 ^ 59
def prefixEnd_8064741 : Nat := 4983230072969 + 3 ^ 40 * 8064741 * 2
def baseEnd_8064741 : Nat := 1380362829007178799149479

theorem tailTrace_8064741 : CollatzResearch.WordTrace tailWord_8064741 prefixEnd_8064741 1380362829007178799149479 := by
  unfold tailWord_8064741
  simp only [CollatzResearch.WordTrace]
  refine ⟨294145269275828179951626077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196096846183885453301084051 294145269275828179951626077)
  ·
    refine ⟨110304475978435567481859779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294145269275828179951626077 110304475978435567481859779)
    ·
      refine ⟨165456713967653351222789669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110304475978435567481859779 165456713967653351222789669)
      ·
        refine ⟨31023133868935003354273063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165456713967653351222789669 31023133868935003354273063)
        ·
          refine ⟨46534700803402505031409595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31023133868935003354273063 46534700803402505031409595)
          ·
            refine ⟨69802051205103757547114393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46534700803402505031409595 69802051205103757547114393)
            ·
              refine ⟨52351538403827818160335795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69802051205103757547114393 52351538403827818160335795)
              ·
                refine ⟨78527307605741727240503693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52351538403827818160335795 78527307605741727240503693)
                ·
                  refine ⟨29447740352153147715188885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78527307605741727240503693 29447740352153147715188885)
                  ·
                    refine ⟨1380362829007178799149479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29447740352153147715188885 1380362829007178799149479)
                    ·
                      rfl

theorem cell23_8064741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_8064741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064741 prefixEnd_8064741 := by exact prefixLift 8064741
  have htrace : WordTrace (prefixWord ++ tailWord_8064741) baseStart_8064741 baseEnd_8064741 := by
    simpa [prefixWord, tailWord_8064741, baseEnd_8064741] using wordTrace_append hprefix tailTrace_8064741
  have hstable : (prefixWord ++ tailWord_8064741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064741).length < 2 ^ (prefixWord ++ tailWord_8064741).sum := by decide
  have hdescent : baseEnd_8064741 < baseStart_8064741 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064748 : List Nat := [2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 4]
def baseStart_8064748 : Nat := 118140960795 + 8064748 * 2 ^ 59
def prefixEnd_8064748 : Nat := 4983230072969 + 3 ^ 40 * 8064748 * 2
def baseEnd_8064748 : Nat := 4141092081386117870060905

theorem tailTrace_8064748 : CollatzResearch.WordTrace tailWord_8064748 prefixEnd_8064748 4141092081386117870060905 := by
  unfold tailWord_8064748
  simp only [CollatzResearch.WordTrace]
  refine ⟨147072762293401410073565449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196097016391201880098087265 147072762293401410073565449)
  ·
    refine ⟨110304571720051057555174087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147072762293401410073565449 110304571720051057555174087)
    ·
      refine ⟨165456857580076586332761131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110304571720051057555174087 165456857580076586332761131)
      ·
        refine ⟨248185286370114879499141697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165456857580076586332761131 248185286370114879499141697)
        ·
          refine ⟨186138964777586159624356273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248185286370114879499141697 186138964777586159624356273)
          ·
            refine ⟨139604223583189619718267205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186138964777586159624356273 139604223583189619718267205)
            ·
              refine ⟨26175791921848053697175101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139604223583189619718267205 26175791921848053697175101)
              ·
                refine ⟨9815921970693020136440663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26175791921848053697175101 9815921970693020136440663)
                ·
                  refine ⟨14723882956039530204660995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9815921970693020136440663 14723882956039530204660995)
                  ·
                    refine ⟨22085824434059295306991493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14723882956039530204660995 22085824434059295306991493)
                    ·
                      refine ⟨4141092081386117870060905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22085824434059295306991493 4141092081386117870060905)
                      ·
                        rfl

theorem cell23_8064748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_8064748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064748 prefixEnd_8064748 := by exact prefixLift 8064748
  have htrace : WordTrace (prefixWord ++ tailWord_8064748) baseStart_8064748 baseEnd_8064748 := by
    simpa [prefixWord, tailWord_8064748, baseEnd_8064748] using wordTrace_append hprefix tailTrace_8064748
  have hstable : (prefixWord ++ tailWord_8064748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064748).length < 2 ^ (prefixWord ++ tailWord_8064748).sum := by decide
  have hdescent : baseEnd_8064748 < baseStart_8064748 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064765 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 3, 2, 2]
def baseStart_8064765 : Nat := 118140960795 + 8064765 * 2 ^ 59
def prefixEnd_8064765 : Nat := 4983230072969 + 3 ^ 40 * 8064765 * 2
def baseEnd_8064765 : Nat := 4141100810557244303548327

theorem tailTrace_8064765 : CollatzResearch.WordTrace tailWord_8064765 prefixEnd_8064765 4141100810557244303548327 := by
  unfold tailWord_8064765
  simp only [CollatzResearch.WordTrace]
  refine ⟨294146144627741232050499749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196097429751827488033666499 294146144627741232050499749)
  ·
    refine ⟨55152402117701481009468703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294146144627741232050499749 55152402117701481009468703)
    ·
      refine ⟨82728603176552221514203055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55152402117701481009468703 82728603176552221514203055)
      ·
        refine ⟨124092904764828332271304583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82728603176552221514203055 124092904764828332271304583)
        ·
          refine ⟨186139357147242498406956875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124092904764828332271304583 186139357147242498406956875)
          ·
            refine ⟨279209035720863747610435313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186139357147242498406956875 279209035720863747610435313)
            ·
              refine ⟨209406776790647810707826485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279209035720863747610435313 209406776790647810707826485)
              ·
                refine ⟨19631885324123232253858733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209406776790647810707826485 19631885324123232253858733)
                ·
                  refine ⟨7361956996546212095197025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19631885324123232253858733 7361956996546212095197025)
                  ·
                    refine ⟨5521467747409659071397769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7361956996546212095197025 5521467747409659071397769)
                    ·
                      refine ⟨4141100810557244303548327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521467747409659071397769 4141100810557244303548327)
                      ·
                        rfl

theorem cell23_8064765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 2, 2].length) (baseStart_8064765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064765 prefixEnd_8064765 := by exact prefixLift 8064765
  have htrace : WordTrace (prefixWord ++ tailWord_8064765) baseStart_8064765 baseEnd_8064765 := by
    simpa [prefixWord, tailWord_8064765, baseEnd_8064765] using wordTrace_append hprefix tailTrace_8064765
  have hstable : (prefixWord ++ tailWord_8064765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064765).length < 2 ^ (prefixWord ++ tailWord_8064765).sum := by decide
  have hdescent : baseEnd_8064765 < baseStart_8064765 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064802 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 1, 2, 3]
def baseStart_8064802 : Nat := 118140960795 + 8064802 * 2 ^ 59
def prefixEnd_8064802 : Nat := 4983230072969 + 3 ^ 40 * 8064802 * 2
def baseEnd_8064802 : Nat := 4141119809341460658785657

theorem tailTrace_8064802 : CollatzResearch.WordTrace tailWord_8064802 prefixEnd_8064802 4141119809341460658785657 := by
  unfold tailWord_8064802
  simp only [CollatzResearch.WordTrace]
  refine ⟨73536873532151796842399165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196098329419071458246397773 73536873532151796842399165)
  ·
    refine ⟨27576327574556923815899687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73536873532151796842399165 27576327574556923815899687)
    ·
      refine ⟨41364491361835385723849531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27576327574556923815899687 41364491361835385723849531)
      ·
        refine ⟨62046737042753078585774297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41364491361835385723849531 62046737042753078585774297)
        ·
          refine ⟨46535052782064808939330723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62046737042753078585774297 46535052782064808939330723)
          ·
            refine ⟨69802579173097213408996085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46535052782064808939330723 69802579173097213408996085)
            ·
              refine ⟨6543991797477863757093383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69802579173097213408996085 6543991797477863757093383)
              ·
                refine ⟨9815987696216795635640075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6543991797477863757093383 9815987696216795635640075)
                ·
                  refine ⟨14723981544325193453460113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9815987696216795635640075 14723981544325193453460113)
                  ·
                    refine ⟨11042986158243895090095085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14723981544325193453460113 11042986158243895090095085)
                    ·
                      refine ⟨4141119809341460658785657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11042986158243895090095085 4141119809341460658785657)
                      ·
                        rfl

theorem cell23_8064802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 2, 3].length) (baseStart_8064802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064802 prefixEnd_8064802 := by exact prefixLift 8064802
  have htrace : WordTrace (prefixWord ++ tailWord_8064802) baseStart_8064802 baseEnd_8064802 := by
    simpa [prefixWord, tailWord_8064802, baseEnd_8064802] using wordTrace_append hprefix tailTrace_8064802
  have hstable : (prefixWord ++ tailWord_8064802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064802).length < 2 ^ (prefixWord ++ tailWord_8064802).sum := by decide
  have hdescent : baseEnd_8064802 < baseStart_8064802 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064872 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_8064872 : Nat := 118140960795 + 8064872 * 2 ^ 59
def prefixEnd_8064872 : Nat := 4983230072969 + 3 ^ 40 * 8064872 * 2
def baseEnd_8064872 : Nat := 4141155752987275384910335

theorem tailTrace_8064872 : CollatzResearch.WordTrace tailWord_8064872 prefixEnd_8064872 4141155752987275384910335 := by
  unfold tailWord_8064872
  simp only [CollatzResearch.WordTrace]
  refine ⟨147075023619176794662322435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196100031492235726216429913 147075023619176794662322435)
  ·
    refine ⟨220612535428765191993483653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147075023619176794662322435 220612535428765191993483653)
    ·
      refine ⟨41364850392893473498778185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220612535428765191993483653 41364850392893473498778185)
      ·
        refine ⟨31023637794670105124083639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41364850392893473498778185 31023637794670105124083639)
        ·
          refine ⟨46535456692005157686125459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31023637794670105124083639 46535456692005157686125459)
          ·
            refine ⟨69803185038007736529188189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46535456692005157686125459 69803185038007736529188189)
            ·
              refine ⟨26176194389252901198445571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69803185038007736529188189 26176194389252901198445571)
              ·
                refine ⟨39264291583879351797668357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26176194389252901198445571 39264291583879351797668357)
                ·
                  refine ⟨7362054671977378462062817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39264291583879351797668357 7362054671977378462062817)
                  ·
                    refine ⟨5521541003983033846547113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7362054671977378462062817 5521541003983033846547113)
                    ·
                      refine ⟨4141155752987275384910335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521541003983033846547113 4141155752987275384910335)
                      ·
                        rfl

theorem cell23_8064872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_8064872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064872 prefixEnd_8064872 := by exact prefixLift 8064872
  have htrace : WordTrace (prefixWord ++ tailWord_8064872) baseStart_8064872 baseEnd_8064872 := by
    simpa [prefixWord, tailWord_8064872, baseEnd_8064872] using wordTrace_append hprefix tailTrace_8064872
  have hstable : (prefixWord ++ tailWord_8064872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064872).length < 2 ^ (prefixWord ++ tailWord_8064872).sum := by decide
  have hdescent : baseEnd_8064872 < baseStart_8064872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064889 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 2, 2, 2]
def baseStart_8064889 : Nat := 118140960795 + 8064889 * 2 ^ 59
def prefixEnd_8064889 : Nat := 4983230072969 + 3 ^ 40 * 8064889 * 2
def baseEnd_8064889 : Nat := 4141164482158401818397757

theorem tailTrace_8064889 : CollatzResearch.WordTrace tailWord_8064889 prefixEnd_8064889 4141164482158401818397757 := by
  unfold tailWord_8064889
  simp only [CollatzResearch.WordTrace]
  refine ⟨294150667279292001228013721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196100444852861334152009147 294150667279292001228013721)
  ·
    refine ⟨220613000459469000921010291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294150667279292001228013721 220613000459469000921010291)
    ·
      refine ⟨330919500689203501381515437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220613000459469000921010291 330919500689203501381515437)
      ·
        refine ⟨124094812758451313018068289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330919500689203501381515437 124094812758451313018068289)
        ·
          refine ⟨93071109568838484763551217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 124094812758451313018068289 93071109568838484763551217)
          ·
            refine ⟨69803332176628863572663413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93071109568838484763551217 69803332176628863572663413)
            ·
              refine ⟨6544062391558955959937195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69803332176628863572663413 6544062391558955959937195)
              ·
                refine ⟨9816093587338433939905793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6544062391558955959937195 9816093587338433939905793)
                ·
                  refine ⟨7362070190503825454929345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9816093587338433939905793 7362070190503825454929345)
                  ·
                    refine ⟨5521552642877869091197009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7362070190503825454929345 5521552642877869091197009)
                    ·
                      refine ⟨4141164482158401818397757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521552642877869091197009 4141164482158401818397757)
                      ·
                        rfl

theorem cell23_8064889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_8064889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064889 prefixEnd_8064889 := by exact prefixLift 8064889
  have htrace : WordTrace (prefixWord ++ tailWord_8064889) baseStart_8064889 baseEnd_8064889 := by
    simpa [prefixWord, tailWord_8064889, baseEnd_8064889] using wordTrace_append hprefix tailTrace_8064889
  have hstable : (prefixWord ++ tailWord_8064889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064889).length < 2 ^ (prefixWord ++ tailWord_8064889).sum := by decide
  have hdescent : baseEnd_8064889 < baseStart_8064889 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064908 : List Nat := [2, 2, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_8064908 : Nat := 118140960795 + 8064908 * 2 ^ 59
def prefixEnd_8064908 : Nat := 4983230072969 + 3 ^ 40 * 8064908 * 2
def baseEnd_8064908 : Nat := 1380391412763612414686723

theorem tailTrace_8064908 : CollatzResearch.WordTrace tailWord_8064908 prefixEnd_8064908 1380391412763612414686723 := by
  unfold tailWord_8064908
  simp only [CollatzResearch.WordTrace]
  refine ⟨147075680133111583736477689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196100906844148778315303585 147075680133111583736477689)
  ·
    refine ⟨110306760099833687802358267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147075680133111583736477689 110306760099833687802358267)
    ·
      refine ⟨165460140149750531703537401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110306760099833687802358267 165460140149750531703537401)
      ·
        refine ⟨124095105112312898777653051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165460140149750531703537401 124095105112312898777653051)
        ·
          refine ⟨186142657668469348166479577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124095105112312898777653051 186142657668469348166479577)
          ·
            refine ⟨139606993251352011124859683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186142657668469348166479577 139606993251352011124859683)
            ·
              refine ⟨209410489877028016687289525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139606993251352011124859683 209410489877028016687289525)
              ·
                refine ⟨19632233425971376564433393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 209410489877028016687289525 19632233425971376564433393)
                ·
                  refine ⟨14724175069478532423325045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19632233425971376564433393 14724175069478532423325045)
                  ·
                    refine ⟨1380391412763612414686723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14724175069478532423325045 1380391412763612414686723)
                    ·
                      rfl

theorem cell23_8064908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_8064908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064908 prefixEnd_8064908 := by exact prefixLift 8064908
  have htrace : WordTrace (prefixWord ++ tailWord_8064908) baseStart_8064908 baseEnd_8064908 := by
    simpa [prefixWord, tailWord_8064908, baseEnd_8064908] using wordTrace_append hprefix tailTrace_8064908
  have hstable : (prefixWord ++ tailWord_8064908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064908).length < 2 ^ (prefixWord ++ tailWord_8064908).sum := by decide
  have hdescent : baseEnd_8064908 < baseStart_8064908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064911 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 8]
def baseStart_8064911 : Nat := 118140960795 + 8064911 * 2 ^ 59
def prefixEnd_8064911 : Nat := 4983230072969 + 3 ^ 40 * 8064911 * 2
def baseEnd_8064911 : Nat := 4141175778732800732322655

theorem tailTrace_8064911 : CollatzResearch.WordTrace tailWord_8064911 prefixEnd_8064911 4141175778732800732322655 := by
  unfold tailWord_8064911
  simp only [CollatzResearch.WordTrace]
  refine ⟨294151469685212298985314587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196100979790141532656876391 294151469685212298985314587)
  ·
    refine ⟨441227204527818448477971881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294151469685212298985314587 441227204527818448477971881)
    ·
      refine ⟨330920403395863836358478911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441227204527818448477971881 330920403395863836358478911)
      ·
        refine ⟨496380605093795754537718367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330920403395863836358478911 496380605093795754537718367)
        ·
          refine ⟨744570907640693631806577551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496380605093795754537718367 744570907640693631806577551)
          ·
            refine ⟨1116856361461040447709866327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 744570907640693631806577551 1116856361461040447709866327)
            ·
              refine ⟨1675284542191560671564799491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1116856361461040447709866327 1675284542191560671564799491)
              ·
                refine ⟨2512926813287341007347199237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1675284542191560671564799491 2512926813287341007347199237)
                ·
                  refine ⟨471173777491376438877599857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2512926813287341007347199237 471173777491376438877599857)
                  ·
                    refine ⟨353380333118532329158199893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 471173777491376438877599857 353380333118532329158199893)
                    ·
                      refine ⟨4141175778732800732322655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 353380333118532329158199893 4141175778732800732322655)
                      ·
                        rfl

theorem cell23_8064911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_8064911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064911 prefixEnd_8064911 := by exact prefixLift 8064911
  have htrace : WordTrace (prefixWord ++ tailWord_8064911) baseStart_8064911 baseEnd_8064911 := by
    simpa [prefixWord, tailWord_8064911, baseEnd_8064911] using wordTrace_append hprefix tailTrace_8064911
  have hstable : (prefixWord ++ tailWord_8064911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064911).length < 2 ^ (prefixWord ++ tailWord_8064911).sum := by decide
  have hdescent : baseEnd_8064911 < baseStart_8064911 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064925 : List Nat := [1, 4, 2, 1, 2, 3, 1, 2, 2, 5]
def baseStart_8064925 : Nat := 118140960795 + 8064925 * 2 ^ 59
def prefixEnd_8064925 : Nat := 4983230072969 + 3 ^ 40 * 8064925 * 2
def baseEnd_8064925 : Nat := 1380394322487321225849197

theorem tailTrace_8064925 : CollatzResearch.WordTrace tailWord_8064925 prefixEnd_8064925 1380394322487321225849197 := by
  unfold tailWord_8064925
  simp only [CollatzResearch.WordTrace]
  refine ⟨294151980307161579376324229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196101320204774386250882819 294151980307161579376324229)
  ·
    refine ⟨55153496307592796133060793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 294151980307161579376324229 55153496307592796133060793)
    ·
      refine ⟨41365122230694597099795595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55153496307592796133060793 41365122230694597099795595)
      ·
        refine ⟨62047683346041895649693393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41365122230694597099795595 62047683346041895649693393)
        ·
          refine ⟨46535762509531421737270045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62047683346041895649693393 46535762509531421737270045)
          ·
            refine ⟨17450910941074283151476267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46535762509531421737270045 17450910941074283151476267)
            ·
              refine ⟨26176366411611424727214401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17450910941074283151476267 26176366411611424727214401)
              ·
                refine ⟨19632274808708568545410801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26176366411611424727214401 19632274808708568545410801)
                ·
                  refine ⟨14724206106531426409058101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19632274808708568545410801 14724206106531426409058101)
                  ·
                    refine ⟨1380394322487321225849197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14724206106531426409058101 1380394322487321225849197)
                    ·
                      rfl

theorem cell23_8064925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_8064925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064925 prefixEnd_8064925 := by exact prefixLift 8064925
  have htrace : WordTrace (prefixWord ++ tailWord_8064925) baseStart_8064925 baseEnd_8064925 := by
    simpa [prefixWord, tailWord_8064925, baseEnd_8064925] using wordTrace_append hprefix tailTrace_8064925
  have hstable : (prefixWord ++ tailWord_8064925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064925).length < 2 ^ (prefixWord ++ tailWord_8064925).sum := by decide
  have hdescent : baseEnd_8064925 < baseStart_8064925 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064929 : List Nat := [1, 2, 3, 4, 2, 1, 3, 2, 5]
def baseStart_8064929 : Nat := 118140960795 + 8064929 * 2 ^ 59
def prefixEnd_8064929 : Nat := 4983230072969 + 3 ^ 40 * 8064929 * 2
def baseEnd_8064929 : Nat := 460131669042731295766397

theorem tailTrace_8064929 : CollatzResearch.WordTrace tailWord_8064929 prefixEnd_8064929 460131669042731295766397 := by
  unfold tailWord_8064929
  simp only [CollatzResearch.WordTrace]
  refine ⟨294152126199147088059469841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196101417466098058706313227 294152126199147088059469841)
  ·
    refine ⟨220614094649360316044602381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294152126199147088059469841 220614094649360316044602381)
    ·
      refine ⟨82730285493510118516725893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220614094649360316044602381 82730285493510118516725893)
      ·
        refine ⟨15511928530033147221886105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82730285493510118516725893 15511928530033147221886105)
        ·
          refine ⟨11633946397524860416414579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15511928530033147221886105 11633946397524860416414579)
          ·
            refine ⟨17450919596287290624621869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11633946397524860416414579 17450919596287290624621869)
            ·
              refine ⟨6544094848607733984233201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17450919596287290624621869 6544094848607733984233201)
              ·
                refine ⟨4908071136455800488174901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6544094848607733984233201 4908071136455800488174901)
                ·
                  refine ⟨460131669042731295766397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4908071136455800488174901 460131669042731295766397)
                  ·
                    rfl

theorem cell23_8064929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 2, 1, 3, 2, 5].length) (baseStart_8064929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064929 prefixEnd_8064929 := by exact prefixLift 8064929
  have htrace : WordTrace (prefixWord ++ tailWord_8064929) baseStart_8064929 baseEnd_8064929 := by
    simpa [prefixWord, tailWord_8064929, baseEnd_8064929] using wordTrace_append hprefix tailTrace_8064929
  have hstable : (prefixWord ++ tailWord_8064929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064929).length < 2 ^ (prefixWord ++ tailWord_8064929).sum := by decide
  have hdescent : baseEnd_8064929 < baseStart_8064929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8064935 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_8064935 : Nat := 118140960795 + 8064935 * 2 ^ 59
def prefixEnd_8064935 : Nat := 4983230072969 + 3 ^ 40 * 8064935 * 2
def baseEnd_8064935 : Nat := 4141188102268508638422545

theorem tailTrace_8064935 : CollatzResearch.WordTrace tailWord_8064935 prefixEnd_8064935 4141188102268508638422545 := by
  unfold tailWord_8064935
  simp only [CollatzResearch.WordTrace]
  refine ⟨294152345037125351084188259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196101563358083567389458839 294152345037125351084188259)
  ·
    refine ⟨441228517555688026626282389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294152345037125351084188259 441228517555688026626282389)
    ·
      refine ⟨20682586760422876248106987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 441228517555688026626282389 20682586760422876248106987)
      ·
        refine ⟨31023880140634314372160481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20682586760422876248106987 31023880140634314372160481)
        ·
          refine ⟨23267910105475735779120361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31023880140634314372160481 23267910105475735779120361)
          ·
            refine ⟨17450932579106801834340271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23267910105475735779120361 17450932579106801834340271)
            ·
              refine ⟨26176398868660202751510407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17450932579106801834340271 26176398868660202751510407)
              ·
                refine ⟨39264598302990304127265611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26176398868660202751510407 39264598302990304127265611)
                ·
                  refine ⟨58896897454485456190898417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39264598302990304127265611 58896897454485456190898417)
                  ·
                    refine ⟨44172673090864092143173813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58896897454485456190898417 44172673090864092143173813)
                    ·
                      refine ⟨4141188102268508638422545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44172673090864092143173813 4141188102268508638422545)
                      ·
                        rfl

theorem cell23_8064935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_8064935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8064935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8064935 prefixEnd_8064935 := by exact prefixLift 8064935
  have htrace : WordTrace (prefixWord ++ tailWord_8064935) baseStart_8064935 baseEnd_8064935 := by
    simpa [prefixWord, tailWord_8064935, baseEnd_8064935] using wordTrace_append hprefix tailTrace_8064935
  have hstable : (prefixWord ++ tailWord_8064935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8064935).length < 2 ^ (prefixWord ++ tailWord_8064935).sum := by decide
  have hdescent : baseEnd_8064935 < baseStart_8064935 := by decide
  rcases family_descends (prefixWord ++ tailWord_8064935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065029 : List Nat := [1, 3, 1, 1, 2, 4, 1, 5, 1, 1, 3]
def baseStart_8065029 : Nat := 118140960795 + 8065029 * 2 ^ 59
def prefixEnd_8065029 : Nat := 4983230072969 + 3 ^ 40 * 8065029 * 2
def baseEnd_8065029 : Nat := 4141236369450031270647113

theorem tailTrace_8065029 : CollatzResearch.WordTrace tailWord_8065029 prefixEnd_8065029 4141236369450031270647113 := by
  unfold tailWord_8065029
  simp only [CollatzResearch.WordTrace]
  refine ⟨294155773498784805138110141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196103848999189870092073427 294155773498784805138110141)
  ·
    refine ⟨110308415062044301926791303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294155773498784805138110141 110308415062044301926791303)
    ·
      refine ⟨165462622593066452890186955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110308415062044301926791303 165462622593066452890186955)
      ·
        refine ⟨248193933889599679335280433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165462622593066452890186955 248193933889599679335280433)
        ·
          refine ⟨186145450417199759501460325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 248193933889599679335280433 186145450417199759501460325)
          ·
            refine ⟨34902271953224954906523811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186145450417199759501460325 34902271953224954906523811)
            ·
              refine ⟨52353407929837432359785717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34902271953224954906523811 52353407929837432359785717)
              ·
                refine ⟨4908131993422259283729911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 52353407929837432359785717 4908131993422259283729911)
                ·
                  refine ⟨7362197990133388925594867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908131993422259283729911 7362197990133388925594867)
                  ·
                    refine ⟨11043296985200083388392301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7362197990133388925594867 11043296985200083388392301)
                    ·
                      refine ⟨4141236369450031270647113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11043296985200083388392301 4141236369450031270647113)
                      ·
                        rfl

theorem cell23_8065029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 1, 3].length) (baseStart_8065029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065029 prefixEnd_8065029 := by exact prefixLift 8065029
  have htrace : WordTrace (prefixWord ++ tailWord_8065029) baseStart_8065029 baseEnd_8065029 := by
    simpa [prefixWord, tailWord_8065029, baseEnd_8065029] using wordTrace_append hprefix tailTrace_8065029
  have hstable : (prefixWord ++ tailWord_8065029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065029).length < 2 ^ (prefixWord ++ tailWord_8065029).sum := by decide
  have hdescent : baseEnd_8065029 < baseStart_8065029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065055 : List Nat := [1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 5]
def baseStart_8065055 : Nat := 118140960795 + 8065055 * 2 ^ 59
def prefixEnd_8065055 : Nat := 4983230072969 + 3 ^ 40 * 8065055 * 2
def baseEnd_8065055 : Nat := 4141249719947048168921993

theorem tailTrace_8065055 : CollatzResearch.WordTrace tailWord_8065055 prefixEnd_8065055 4141249719947048168921993 := by
  unfold tailWord_8065055
  simp only [CollatzResearch.WordTrace]
  refine ⟨294156721796690611578556619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196104481197793741052371079 294156721796690611578556619)
  ·
    refine ⟨441235082695035917367834929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294156721796690611578556619 441235082695035917367834929)
    ·
      refine ⟨330926312021276938025876197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 441235082695035917367834929 330926312021276938025876197)
      ·
        refine ⟨62048683503989425879851787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330926312021276938025876197 62048683503989425879851787)
        ·
          refine ⟨93073025255984138819777681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62048683503989425879851787 93073025255984138819777681)
          ·
            refine ⟨69804768941988104114833261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 93073025255984138819777681 69804768941988104114833261)
            ·
              refine ⟨26176788353245539043062473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69804768941988104114833261 26176788353245539043062473)
              ·
                refine ⟨19632591264934154282296855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26176788353245539043062473 19632591264934154282296855)
                ·
                  refine ⟨29448886897401231423445283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19632591264934154282296855 29448886897401231423445283)
                  ·
                    refine ⟨44173330346101847135167925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29448886897401231423445283 44173330346101847135167925)
                    ·
                      refine ⟨4141249719947048168921993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44173330346101847135167925 4141249719947048168921993)
                      ·
                        rfl

theorem cell23_8065055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_8065055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065055 prefixEnd_8065055 := by exact prefixLift 8065055
  have htrace : WordTrace (prefixWord ++ tailWord_8065055) baseStart_8065055 baseEnd_8065055 := by
    simpa [prefixWord, tailWord_8065055, baseEnd_8065055] using wordTrace_append hprefix tailTrace_8065055
  have hstable : (prefixWord ++ tailWord_8065055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065055).length < 2 ^ (prefixWord ++ tailWord_8065055).sum := by decide
  have hdescent : baseEnd_8065055 < baseStart_8065055 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065072 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 3]
def baseStart_8065072 : Nat := 118140960795 + 8065072 * 2 ^ 59
def prefixEnd_8065072 : Nat := 4983230072969 + 3 ^ 40 * 8065072 * 2
def baseEnd_8065072 : Nat := 4141258449118174602409415

theorem tailTrace_8065072 : CollatzResearch.WordTrace tailWord_8065072 prefixEnd_8065072 4141258449118174602409415 := by
  unfold tailWord_8065072
  simp only [CollatzResearch.WordTrace]
  refine ⟨147078670918814511740962735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196104894558419348987950313 147078670918814511740962735)
  ·
    refine ⟨220618006378221767611444103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147078670918814511740962735 220618006378221767611444103)
    ·
      refine ⟨330927009567332651417166155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220618006378221767611444103 330927009567332651417166155)
      ·
        refine ⟨496390514350998977125749233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330927009567332651417166155 496390514350998977125749233)
        ·
          refine ⟨372292885763249232844311925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 496390514350998977125749233 372292885763249232844311925)
          ·
            refine ⟨34902458040304615579154243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 372292885763249232844311925 34902458040304615579154243)
            ·
              refine ⟨52353687060456923368731365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34902458040304615579154243 52353687060456923368731365)
              ·
                refine ⟨9816316323835673131637131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52353687060456923368731365 9816316323835673131637131)
                ·
                  refine ⟨14724474485753509697455697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9816316323835673131637131 14724474485753509697455697)
                  ·
                    refine ⟨11043355864315132273091773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14724474485753509697455697 11043355864315132273091773)
                    ·
                      refine ⟨4141258449118174602409415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11043355864315132273091773 4141258449118174602409415)
                      ·
                        rfl

theorem cell23_8065072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 2, 3].length) (baseStart_8065072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065072 prefixEnd_8065072 := by exact prefixLift 8065072
  have htrace : WordTrace (prefixWord ++ tailWord_8065072) baseStart_8065072 baseEnd_8065072 := by
    simpa [prefixWord, tailWord_8065072, baseEnd_8065072] using wordTrace_append hprefix tailTrace_8065072
  have hstable : (prefixWord ++ tailWord_8065072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065072).length < 2 ^ (prefixWord ++ tailWord_8065072).sum := by decide
  have hdescent : baseEnd_8065072 < baseStart_8065072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065075 : List Nat := [1, 1, 1, 2, 4, 1, 6, 7]
def baseStart_8065075 : Nat := 118140960795 + 8065075 * 2 ^ 59
def prefixEnd_8065075 : Nat := 4983230072969 + 3 ^ 40 * 8065075 * 2
def baseEnd_8065075 : Nat := 153379999613338447802663

theorem tailTrace_8065075 : CollatzResearch.WordTrace tailWord_8065075 prefixEnd_8065075 153379999613338447802663 := by
  unfold tailWord_8065075
  simp only [CollatzResearch.WordTrace]
  refine ⟨294157451256618154994284679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196104967504412103329523119 294157451256618154994284679)
  ·
    refine ⟨441236176884927232491427019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294157451256618154994284679 441236176884927232491427019)
    ·
      refine ⟨661854265327390848737140529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441236176884927232491427019 661854265327390848737140529)
      ·
        refine ⟨496390698995543136552855397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661854265327390848737140529 496390698995543136552855397)
        ·
          refine ⟨93073256061664338103660387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 496390698995543136552855397 93073256061664338103660387)
          ·
            refine ⟨139609884092496507155490581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93073256061664338103660387 139609884092496507155490581)
            ·
              refine ⟨6544213316835773772913621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139609884092496507155490581 6544213316835773772913621)
              ·
                refine ⟨153379999613338447802663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6544213316835773772913621 153379999613338447802663)
                ·
                  rfl

theorem cell23_8065075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 7].length) (baseStart_8065075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065075 prefixEnd_8065075 := by exact prefixLift 8065075
  have htrace : WordTrace (prefixWord ++ tailWord_8065075) baseStart_8065075 baseEnd_8065075 := by
    simpa [prefixWord, tailWord_8065075, baseEnd_8065075] using wordTrace_append hprefix tailTrace_8065075
  have hstable : (prefixWord ++ tailWord_8065075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065075).length < 2 ^ (prefixWord ++ tailWord_8065075).sum := by decide
  have hdescent : baseEnd_8065075 < baseStart_8065075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065089 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_8065089 : Nat := 118140960795 + 8065089 * 2 ^ 59
def prefixEnd_8065089 : Nat := 4983230072969 + 3 ^ 40 * 8065089 * 2
def baseEnd_8065089 : Nat := 4141267178289301035896837

theorem tailTrace_8065089 : CollatzResearch.WordTrace tailWord_8065089 prefixEnd_8065089 4141267178289301035896837 := by
  unfold tailWord_8065089
  simp only [CollatzResearch.WordTrace]
  refine ⟨294157961878567435385294321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196105307919044956923529547 294157961878567435385294321)
  ·
    refine ⟨220618471408925576538970741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294157961878567435385294321 220618471408925576538970741)
    ·
      refine ⟨20682981694586772800528507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220618471408925576538970741 20682981694586772800528507)
      ·
        refine ⟨31024472541880159200792761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20682981694586772800528507 31024472541880159200792761)
        ·
          refine ⟨23268354406410119400594571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31024472541880159200792761 23268354406410119400594571)
          ·
            refine ⟨34902531609615179100891857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23268354406410119400594571 34902531609615179100891857)
            ·
              refine ⟨26176898707211384325668893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34902531609615179100891857 26176898707211384325668893)
              ·
                refine ⟨9816337015204269122125835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26176898707211384325668893 9816337015204269122125835)
                ·
                  refine ⟨14724505522806403683188753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9816337015204269122125835 14724505522806403683188753)
                  ·
                    refine ⟨11043379142104802762391565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14724505522806403683188753 11043379142104802762391565)
                    ·
                      refine ⟨4141267178289301035896837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11043379142104802762391565 4141267178289301035896837)
                      ·
                        rfl

theorem cell23_8065089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_8065089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065089 prefixEnd_8065089 := by exact prefixLift 8065089
  have htrace : WordTrace (prefixWord ++ tailWord_8065089) baseStart_8065089 baseEnd_8065089 := by
    simpa [prefixWord, tailWord_8065089, baseEnd_8065089] using wordTrace_append hprefix tailTrace_8065089
  have hstable : (prefixWord ++ tailWord_8065089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065089).length < 2 ^ (prefixWord ++ tailWord_8065089).sum := by decide
  have hdescent : baseEnd_8065089 < baseStart_8065089 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065159 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_8065159 : Nat := 118140960795 + 8065159 * 2 ^ 59
def prefixEnd_8065159 : Nat := 4983230072969 + 3 ^ 40 * 8065159 * 2
def baseEnd_8065159 : Nat := 4141303121935115762021515

theorem tailTrace_8065159 : CollatzResearch.WordTrace tailWord_8065159 prefixEnd_8065159 4141303121935115762021515 := by
  unfold tailWord_8065159
  simp only [CollatzResearch.WordTrace]
  refine ⟨294160514988313837340342531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196107009992209224893561687 294160514988313837340342531)
  ·
    refine ⟨441240772482470756010513797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294160514988313837340342531 441240772482470756010513797)
    ·
      refine ⟨82732644840463266751971337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 441240772482470756010513797 82732644840463266751971337)
      ·
        refine ⟨62049483630347450063978503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82732644840463266751971337 62049483630347450063978503)
        ·
          refine ⟨93074225445521175095967755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62049483630347450063978503 93074225445521175095967755)
          ·
            refine ⟨139611338168281762643951633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93074225445521175095967755 139611338168281762643951633)
            ·
              refine ⟨104708503626211321982963725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139611338168281762643951633 104708503626211321982963725)
              ·
                refine ⟨39265688859829245743611397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104708503626211321982963725 39265688859829245743611397)
                ·
                  refine ⟨7362316661217983576927137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39265688859829245743611397 7362316661217983576927137)
                  ·
                    refine ⟨5521737495913487682695353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7362316661217983576927137 5521737495913487682695353)
                    ·
                      refine ⟨4141303121935115762021515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521737495913487682695353 4141303121935115762021515)
                      ·
                        rfl

theorem cell23_8065159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_8065159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065159 prefixEnd_8065159 := by exact prefixLift 8065159
  have htrace : WordTrace (prefixWord ++ tailWord_8065159) baseStart_8065159 baseEnd_8065159 := by
    simpa [prefixWord, tailWord_8065159, baseEnd_8065159] using wordTrace_append hprefix tailTrace_8065159
  have hstable : (prefixWord ++ tailWord_8065159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065159).length < 2 ^ (prefixWord ++ tailWord_8065159).sum := by decide
  have hdescent : baseEnd_8065159 < baseStart_8065159 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065162 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3]
def baseStart_8065162 : Nat := 118140960795 + 8065162 * 2 ^ 59
def prefixEnd_8065162 : Nat := 4983230072969 + 3 ^ 40 * 8065162 * 2
def baseEnd_8065162 : Nat := 4141304662377079250284001

theorem tailTrace_8065162 : CollatzResearch.WordTrace tailWord_8065162 prefixEnd_8065162 4141304662377079250284001 := by
  unfold tailWord_8065162
  simp only [CollatzResearch.WordTrace]
  refine ⟨73540156101825742213175435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196107082938201979235134493 73540156101825742213175435)
  ·
    refine ⟨110310234152738613319763153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73540156101825742213175435 110310234152738613319763153)
    ·
      refine ⟨82732675614553959989822365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110310234152738613319763153 82732675614553959989822365)
      ·
        refine ⟨31024753355457734996183387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82732675614553959989822365 31024753355457734996183387)
        ·
          refine ⟨46537130033186602494275081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31024753355457734996183387 46537130033186602494275081)
          ·
            refine ⟨34902847524889951870706311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46537130033186602494275081 34902847524889951870706311)
            ·
              refine ⟨52354271287334927806059467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34902847524889951870706311 52354271287334927806059467)
              ·
                refine ⟨78531406931002391709089201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52354271287334927806059467 78531406931002391709089201)
                ·
                  refine ⟨58898555198251793781816901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78531406931002391709089201 58898555198251793781816901)
                  ·
                    refine ⟨11043479099672211334090669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58898555198251793781816901 11043479099672211334090669)
                    ·
                      refine ⟨4141304662377079250284001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11043479099672211334090669 4141304662377079250284001)
                      ·
                        rfl

theorem cell23_8065162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 4, 3].length) (baseStart_8065162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065162 prefixEnd_8065162 := by exact prefixLift 8065162
  have htrace : WordTrace (prefixWord ++ tailWord_8065162) baseStart_8065162 baseEnd_8065162 := by
    simpa [prefixWord, tailWord_8065162, baseEnd_8065162] using wordTrace_append hprefix tailTrace_8065162
  have hstable : (prefixWord ++ tailWord_8065162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065162).length < 2 ^ (prefixWord ++ tailWord_8065162).sum := by decide
  have hdescent : baseEnd_8065162 < baseStart_8065162 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065176 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 1, 4, 2]
def baseStart_8065176 : Nat := 118140960795 + 8065176 * 2 ^ 59
def prefixEnd_8065176 : Nat := 4983230072969 + 3 ^ 40 * 8065176 * 2
def baseEnd_8065176 : Nat := 4141311851106242195508937

theorem tailTrace_8065176 : CollatzResearch.WordTrace tailWord_8065176 prefixEnd_8065176 4141311851106242195508937 := by
  unfold tailWord_8065176
  simp only [CollatzResearch.WordTrace]
  refine ⟨147080567514626124621855691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196107423352834832829140921 147080567514626124621855691)
  ·
    refine ⟨220620851271939186932783537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147080567514626124621855691 220620851271939186932783537)
    ·
      refine ⟨165465638453954390199587653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220620851271939186932783537 165465638453954390199587653)
      ·
        refine ⟨31024807210116448162422685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165465638453954390199587653 31024807210116448162422685)
        ·
          refine ⟨11634302703793668060908507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31024807210116448162422685 11634302703793668060908507)
          ·
            refine ⟨17451454055690502091362761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11634302703793668060908507 17451454055690502091362761)
            ·
              refine ⟨13088590541767876568522071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17451454055690502091362761 13088590541767876568522071)
              ·
                refine ⟨19632885812651814852783107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13088590541767876568522071 19632885812651814852783107)
                ·
                  refine ⟨29449328718977722279174661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19632885812651814852783107 29449328718977722279174661)
                  ·
                    refine ⟨5521749134808322927345249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29449328718977722279174661 5521749134808322927345249)
                    ·
                      refine ⟨4141311851106242195508937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521749134808322927345249 4141311851106242195508937)
                      ·
                        rfl

theorem cell23_8065176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_8065176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065176 prefixEnd_8065176 := by exact prefixLift 8065176
  have htrace : WordTrace (prefixWord ++ tailWord_8065176) baseStart_8065176 baseEnd_8065176 := by
    simpa [prefixWord, tailWord_8065176, baseEnd_8065176] using wordTrace_append hprefix tailTrace_8065176
  have hstable : (prefixWord ++ tailWord_8065176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065176).length < 2 ^ (prefixWord ++ tailWord_8065176).sum := by decide
  have hdescent : baseEnd_8065176 < baseStart_8065176 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065204 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_8065204 : Nat := 118140960795 + 8065204 * 2 ^ 59
def prefixEnd_8065204 : Nat := 4983230072969 + 3 ^ 40 * 8065204 * 2
def baseEnd_8065204 : Nat := 4141326228564568085958809

theorem tailTrace_8065204 : CollatzResearch.WordTrace tailWord_8065204 prefixEnd_8065204 4141326228564568085958809 := by
  unfold tailWord_8065204
  simp only [CollatzResearch.WordTrace]
  refine ⟨147081078136575405012865333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196108104182100540017153777 147081078136575405012865333)
  ·
    refine ⟨13788851075303944219956125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 147081078136575405012865333 13788851075303944219956125)
    ·
      refine ⟨5170819153238979082483547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13788851075303944219956125 5170819153238979082483547)
      ·
        refine ⟨7756228729858468623725321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170819153238979082483547 7756228729858468623725321)
        ·
          refine ⟨5817171547393851467793991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7756228729858468623725321 5817171547393851467793991)
          ·
            refine ⟨8725757321090777201690987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817171547393851467793991 8725757321090777201690987)
            ·
              refine ⟨13088635981636165802536481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8725757321090777201690987 13088635981636165802536481)
              ·
                refine ⟨9816476986227124351902361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13088635981636165802536481 9816476986227124351902361)
                ·
                  refine ⟨7362357739670343263926771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9816476986227124351902361 7362357739670343263926771)
                  ·
                    refine ⟨11043536609505514895890157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7362357739670343263926771 11043536609505514895890157)
                    ·
                      refine ⟨4141326228564568085958809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11043536609505514895890157 4141326228564568085958809)
                      ·
                        rfl

theorem cell23_8065204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_8065204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065204 prefixEnd_8065204 := by exact prefixLift 8065204
  have htrace : WordTrace (prefixWord ++ tailWord_8065204) baseStart_8065204 baseEnd_8065204 := by
    simpa [prefixWord, tailWord_8065204, baseEnd_8065204] using wordTrace_append hprefix tailTrace_8065204
  have hstable : (prefixWord ++ tailWord_8065204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065204).length < 2 ^ (prefixWord ++ tailWord_8065204).sum := by decide
  have hdescent : baseEnd_8065204 < baseStart_8065204 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065276 : List Nat := [2, 2, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_8065276 : Nat := 118140960795 + 8065276 * 2 ^ 59
def prefixEnd_8065276 : Nat := 4983230072969 + 3 ^ 40 * 8065276 * 2
def baseEnd_8065276 : Nat := 1380454399723897268086159

theorem tailTrace_8065276 : CollatzResearch.WordTrace tailWord_8065276 prefixEnd_8065276 1380454399723897268086159 := by
  unfold tailWord_8065276
  simp only [CollatzResearch.WordTrace]
  refine ⟨147082391164444983161175841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196109854885926644214901121 147082391164444983161175841)
  ·
    refine ⟨110311793373333737370881881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 147082391164444983161175841 110311793373333737370881881)
    ·
      refine ⟨82733845030000303028161411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110311793373333737370881881 82733845030000303028161411)
      ·
        refine ⟨124100767545000454542242117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82733845030000303028161411 124100767545000454542242117)
        ·
          refine ⟨23268893914687585226670397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 124100767545000454542242117 23268893914687585226670397)
          ·
            refine ⟨8725835218007844460001399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23268893914687585226670397 8725835218007844460001399)
            ·
              refine ⟨13088752827011766690002099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8725835218007844460001399 13088752827011766690002099)
              ·
                refine ⟨19633129240517650035003149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13088752827011766690002099 19633129240517650035003149)
                ·
                  refine ⟨7362423465194118763126181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19633129240517650035003149 7362423465194118763126181)
                  ·
                    refine ⟨1380454399723897268086159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362423465194118763126181 1380454399723897268086159)
                    ·
                      rfl

theorem cell23_8065276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_8065276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065276 prefixEnd_8065276 := by exact prefixLift 8065276
  have htrace : WordTrace (prefixWord ++ tailWord_8065276) baseStart_8065276 baseEnd_8065276 := by
    simpa [prefixWord, tailWord_8065276, baseEnd_8065276] using wordTrace_append hprefix tailTrace_8065276
  have hstable : (prefixWord ++ tailWord_8065276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065276).length < 2 ^ (prefixWord ++ tailWord_8065276).sum := by decide
  have hdescent : baseEnd_8065276 < baseStart_8065276 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065289 : List Nat := [1, 2, 1, 1, 3, 4, 4, 1, 6]
def baseStart_8065289 : Nat := 118140960795 + 8065289 * 2 ^ 59
def prefixEnd_8065289 : Nat := 4983230072969 + 3 ^ 40 * 8065289 * 2
def baseEnd_8065289 : Nat := 460152208268911139266213

theorem tailTrace_8065289 : CollatzResearch.WordTrace tailWord_8065289 prefixEnd_8065289 460152208268911139266213 := by
  unfold tailWord_8065289
  simp only [CollatzResearch.WordTrace]
  refine ⟨294165256477842869542574921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196110170985228579695049947 294165256477842869542574921)
  ·
    refine ⟨220623942358382152156931191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 294165256477842869542574921 220623942358382152156931191)
    ·
      refine ⟨330935913537573228235396787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220623942358382152156931191 330935913537573228235396787)
      ·
        refine ⟨496403870306359842353095181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330935913537573228235396787 496403870306359842353095181)
        ·
          refine ⟨186151451364884940882410693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 496403870306359842353095181 186151451364884940882410693)
          ·
            refine ⟨34903397130915926415452005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 186151451364884940882410693 34903397130915926415452005)
            ·
              refine ⟨6544386962046736202897251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34903397130915926415452005 6544386962046736202897251)
              ·
                refine ⟨9816580443070104304345877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6544386962046736202897251 9816580443070104304345877)
                ·
                  refine ⟨460152208268911139266213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9816580443070104304345877 460152208268911139266213)
                  ·
                    rfl

theorem cell23_8065289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 1, 6].length) (baseStart_8065289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065289 prefixEnd_8065289 := by exact prefixLift 8065289
  have htrace : WordTrace (prefixWord ++ tailWord_8065289) baseStart_8065289 baseEnd_8065289 := by
    simpa [prefixWord, tailWord_8065289, baseEnd_8065289] using wordTrace_append hprefix tailTrace_8065289
  have hstable : (prefixWord ++ tailWord_8065289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065289).length < 2 ^ (prefixWord ++ tailWord_8065289).sum := by decide
  have hdescent : baseEnd_8065289 < baseStart_8065289 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065299 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 3]
def baseStart_8065299 : Nat := 118140960795 + 8065299 * 2 ^ 59
def prefixEnd_8065299 : Nat := 4983230072969 + 3 ^ 40 * 8065299 * 2
def baseEnd_8065299 : Nat := 4141375009226745214270871

theorem tailTrace_8065299 : CollatzResearch.WordTrace tailWord_8065299 prefixEnd_8065299 4141375009226745214270871 := by
  unfold tailWord_8065299
  simp only [CollatzResearch.WordTrace]
  refine ⟨294165621207806641250438951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196110414138537760833625967 294165621207806641250438951)
  ·
    refine ⟨441248431811709961875658427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294165621207806641250438951 441248431811709961875658427)
    ·
      refine ⟨661872647717564942813487641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441248431811709961875658427 661872647717564942813487641)
      ·
        refine ⟨496404485788173707110115731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 661872647717564942813487641 496404485788173707110115731)
        ·
          refine ⟨744606728682260560665173597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 496404485788173707110115731 744606728682260560665173597)
          ·
            refine ⟨279227523255847710249440099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 744606728682260560665173597 279227523255847710249440099)
            ·
              refine ⟨418841284883771565374160149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279227523255847710249440099 418841284883771565374160149)
              ·
                refine ⟨19633185228926792126913757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 418841284883771565374160149 19633185228926792126913757)
                ·
                  refine ⟨7362444460847547047592659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19633185228926792126913757 7362444460847547047592659)
                  ·
                    refine ⟨11043666691271320571388989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7362444460847547047592659 11043666691271320571388989)
                    ·
                      refine ⟨4141375009226745214270871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11043666691271320571388989 4141375009226745214270871)
                      ·
                        rfl

theorem cell23_8065299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 1, 3].length) (baseStart_8065299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065299 prefixEnd_8065299 := by exact prefixLift 8065299
  have htrace : WordTrace (prefixWord ++ tailWord_8065299) baseStart_8065299 baseEnd_8065299 := by
    simpa [prefixWord, tailWord_8065299, baseEnd_8065299] using wordTrace_append hprefix tailTrace_8065299
  have hstable : (prefixWord ++ tailWord_8065299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065299).length < 2 ^ (prefixWord ++ tailWord_8065299).sum := by decide
  have hdescent : baseEnd_8065299 < baseStart_8065299 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065333 : List Nat := [1, 3, 3, 1, 2, 1, 3, 4, 1, 1, 3]
def baseStart_8065333 : Nat := 118140960795 + 8065333 * 2 ^ 59
def prefixEnd_8065333 : Nat := 4983230072969 + 3 ^ 40 * 8065333 * 2
def baseEnd_8065333 : Nat := 4141392467568998081245715

theorem tailTrace_8065333 : CollatzResearch.WordTrace tailWord_8065333 prefixEnd_8065333 4141392467568998081245715 := by
  unfold tailWord_8065333
  simp only [CollatzResearch.WordTrace]
  refine ⟨294166861289683465057176653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196111240859788976704784435 294166861289683465057176653)
  ·
    refine ⟨110312572983631299396441245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 294166861289683465057176653 110312572983631299396441245)
    ·
      refine ⟨41367214868861737273665467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110312572983631299396441245 41367214868861737273665467)
      ·
        refine ⟨62050822303292605910498201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41367214868861737273665467 62050822303292605910498201)
        ·
          refine ⟨46538116727469454432873651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 62050822303292605910498201 46538116727469454432873651)
          ·
            refine ⟨69807175091204181649310477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46538116727469454432873651 69807175091204181649310477)
            ·
              refine ⟨26177690659201568118491429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69807175091204181649310477 26177690659201568118491429)
              ·
                refine ⟨4908316998600294022217143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26177690659201568118491429 4908316998600294022217143)
                ·
                  refine ⟨7362475497900441033325715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4908316998600294022217143 7362475497900441033325715)
                  ·
                    refine ⟨11043713246850661549988573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7362475497900441033325715 11043713246850661549988573)
                    ·
                      refine ⟨4141392467568998081245715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11043713246850661549988573 4141392467568998081245715)
                      ·
                        rfl

theorem cell23_8065333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 1, 3].length) (baseStart_8065333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065333 prefixEnd_8065333 := by exact prefixLift 8065333
  have htrace : WordTrace (prefixWord ++ tailWord_8065333) baseStart_8065333 baseEnd_8065333 := by
    simpa [prefixWord, tailWord_8065333, baseEnd_8065333] using wordTrace_append hprefix tailTrace_8065333
  have hstable : (prefixWord ++ tailWord_8065333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065333).length < 2 ^ (prefixWord ++ tailWord_8065333).sum := by decide
  have hdescent : baseEnd_8065333 < baseStart_8065333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065352 : List Nat := [2, 1, 3, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_8065352 : Nat := 118140960795 + 8065352 * 2 ^ 59
def prefixEnd_8065352 : Nat := 4983230072969 + 3 ^ 40 * 8065352 * 2
def baseEnd_8065352 : Nat := 4141402223701433506908127

theorem tailTrace_8065352 : CollatzResearch.WordTrace tailWord_8065352 prefixEnd_8065352 4141402223701433506908127 := by
  unfold tailWord_8065352
  simp only [CollatzResearch.WordTrace]
  refine ⟨147083777138307315651059155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 196111702851076420868078873 147083777138307315651059155)
  ·
    refine ⟨220625665707460973476588733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 147083777138307315651059155 220625665707460973476588733)
    ·
      refine ⟨82734624640297865053720775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220625665707460973476588733 82734624640297865053720775)
      ·
        refine ⟨124101936960446797580581163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82734624640297865053720775 124101936960446797580581163)
        ·
          refine ⟨186152905440670196370871745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 124101936960446797580581163 186152905440670196370871745)
          ·
            refine ⟨139614679080502647278153809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 186152905440670196370871745 139614679080502647278153809)
            ·
              refine ⟨104711009310376985458615357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139614679080502647278153809 104711009310376985458615357)
              ·
                refine ⟨39266628491391369546980759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104711009310376985458615357 39266628491391369546980759)
                ·
                  refine ⟨58899942737087054320471139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39266628491391369546980759 58899942737087054320471139)
                  ·
                    refine ⟨88349914105630581480706709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58899942737087054320471139 88349914105630581480706709)
                    ·
                      refine ⟨4141402223701433506908127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88349914105630581480706709 4141402223701433506908127)
                      ·
                        rfl

theorem cell23_8065352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_8065352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065352 prefixEnd_8065352 := by exact prefixLift 8065352
  have htrace : WordTrace (prefixWord ++ tailWord_8065352) baseStart_8065352 baseEnd_8065352 := by
    simpa [prefixWord, tailWord_8065352, baseEnd_8065352] using wordTrace_append hprefix tailTrace_8065352
  have hstable : (prefixWord ++ tailWord_8065352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065352).length < 2 ^ (prefixWord ++ tailWord_8065352).sum := by decide
  have hdescent : baseEnd_8065352 < baseStart_8065352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065362 : List Nat := [3, 2, 2, 1, 1, 1, 2, 11]
def baseStart_8065362 : Nat := 118140960795 + 8065362 * 2 ^ 59
def prefixEnd_8065362 : Nat := 4983230072969 + 3 ^ 40 * 8065362 * 2
def baseEnd_8065362 : Nat := 153385457722517721029003

theorem tailTrace_8065362 : CollatzResearch.WordTrace tailWord_8065362 prefixEnd_8065362 153385457722517721029003 := by
  unfold tailWord_8065362
  simp only [CollatzResearch.WordTrace]
  refine ⟨73541979751644600752495585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196111946004385602006654893 73541979751644600752495585)
  ·
    refine ⟨55156484813733450564371689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73541979751644600752495585 55156484813733450564371689)
    ·
      refine ⟨41367363610300087923278767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55156484813733450564371689 41367363610300087923278767)
      ·
        refine ⟨62051045415450131884918151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41367363610300087923278767 62051045415450131884918151)
        ·
          refine ⟨93076568123175197827377227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 62051045415450131884918151 93076568123175197827377227)
          ·
            refine ⟨139614852184762796741065841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 93076568123175197827377227 139614852184762796741065841)
            ·
              refine ⟨104711139138572097555799381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139614852184762796741065841 104711139138572097555799381)
              ·
                refine ⟨153385457722517721029003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 104711139138572097555799381 153385457722517721029003)
                ·
                  rfl

theorem cell23_8065362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 11].length) (baseStart_8065362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065362 prefixEnd_8065362 := by exact prefixLift 8065362
  have htrace : WordTrace (prefixWord ++ tailWord_8065362) baseStart_8065362 baseEnd_8065362 := by
    simpa [prefixWord, tailWord_8065362, baseEnd_8065362] using wordTrace_append hprefix tailTrace_8065362
  have hstable : (prefixWord ++ tailWord_8065362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065362).length < 2 ^ (prefixWord ++ tailWord_8065362).sum := by decide
  have hdescent : baseEnd_8065362 < baseStart_8065362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065374 : List Nat := [4, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_8065374 : Nat := 118140960795 + 8065374 * 2 ^ 59
def prefixEnd_8065374 : Nat := 4983230072969 + 3 ^ 40 * 8065374 * 2
def baseEnd_8065374 : Nat := 460157057808425824537003

theorem tailTrace_8065374 : CollatzResearch.WordTrace tailWord_8065374 prefixEnd_8065374 460157057808425824537003 := by
  unfold tailWord_8065374
  simp only [CollatzResearch.WordTrace]
  refine ⟨36771044585316866132427397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 196112237788356619372946117 36771044585316866132427397)
  ·
    refine ⟨6894570859746912399830137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36771044585316866132427397 6894570859746912399830137)
    ·
      refine ⟨5170928144810184299872603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6894570859746912399830137 5170928144810184299872603)
      ·
        refine ⟨7756392217215276449808905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5170928144810184299872603 7756392217215276449808905)
        ·
          refine ⟨5817294162911457337356679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7756392217215276449808905 5817294162911457337356679)
          ·
            refine ⟨8725941244367186006035019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5817294162911457337356679 8725941244367186006035019)
            ·
              refine ⟨13088911866550779009052529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8725941244367186006035019 13088911866550779009052529)
              ·
                refine ⟨9816683899913084256789397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13088911866550779009052529 9816683899913084256789397)
                ·
                  refine ⟨460157057808425824537003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9816683899913084256789397 460157057808425824537003)
                  ·
                    rfl

theorem cell23_8065374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_8065374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065374 prefixEnd_8065374 := by exact prefixLift 8065374
  have htrace : WordTrace (prefixWord ++ tailWord_8065374) baseStart_8065374 baseEnd_8065374 := by
    simpa [prefixWord, tailWord_8065374, baseEnd_8065374] using wordTrace_append hprefix tailTrace_8065374
  have hstable : (prefixWord ++ tailWord_8065374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065374).length < 2 ^ (prefixWord ++ tailWord_8065374).sum := by decide
  have hdescent : baseEnd_8065374 < baseStart_8065374 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065383 : List Nat := [1, 1, 5, 1, 3, 3, 1, 2, 2, 4]
def baseStart_8065383 : Nat := 118140960795 + 8065383 * 2 ^ 59
def prefixEnd_8065383 : Nat := 4983230072969 + 3 ^ 40 * 8065383 * 2
def baseEnd_8065383 : Nat := 1380472713867240961873495

theorem tailTrace_8065383 : CollatzResearch.WordTrace tailWord_8065383 prefixEnd_8065383 1380472713867240961873495 := by
  unfold tailWord_8065383
  simp only [CollatzResearch.WordTrace]
  refine ⟨294168684939502323596496803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196112456626334882397664535 294168684939502323596496803)
  ·
    refine ⟨441253027409253485394745205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294168684939502323596496803 441253027409253485394745205)
    ·
      refine ⟨41367471319617514255757363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 441253027409253485394745205 41367471319617514255757363)
      ·
        refine ⟨62051206979426271383636045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41367471319617514255757363 62051206979426271383636045)
        ·
          refine ⟨23269202617284851768863517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 62051206979426271383636045 23269202617284851768863517)
          ·
            refine ⟨8725950981481819413323819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23269202617284851768863517 8725950981481819413323819)
            ·
              refine ⟨13088926472222729119985729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8725950981481819413323819 13088926472222729119985729)
              ·
                refine ⟨9816694854167046839989297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13088926472222729119985729 9816694854167046839989297)
                ·
                  refine ⟨7362521140625285129991973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9816694854167046839989297 7362521140625285129991973)
                  ·
                    refine ⟨1380472713867240961873495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7362521140625285129991973 1380472713867240961873495)
                    ·
                      rfl

theorem cell23_8065383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_8065383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065383 prefixEnd_8065383 := by exact prefixLift 8065383
  have htrace : WordTrace (prefixWord ++ tailWord_8065383) baseStart_8065383 baseEnd_8065383 := by
    simpa [prefixWord, tailWord_8065383, baseEnd_8065383] using wordTrace_append hprefix tailTrace_8065383
  have hstable : (prefixWord ++ tailWord_8065383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065383).length < 2 ^ (prefixWord ++ tailWord_8065383).sum := by decide
  have hdescent : baseEnd_8065383 < baseStart_8065383 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065399 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 2, 7, 2]
def baseStart_8065399 : Nat := 118140960795 + 8065399 * 2 ^ 59
def prefixEnd_8065399 : Nat := 4983230072969 + 3 ^ 40 * 8065399 * 2
def baseEnd_8065399 : Nat := 4141426357292194823020411

theorem tailTrace_8065399 : CollatzResearch.WordTrace tailWord_8065399 prefixEnd_8065399 4141426357292194823020411 := by
  unfold tailWord_8065399
  simp only [CollatzResearch.WordTrace]
  refine ⟨294169268507444358329079251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 196112845671629572219386167 294169268507444358329079251)
  ·
    refine ⟨441253902761166537493618877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294169268507444358329079251 441253902761166537493618877)
    ·
      refine ⟨165470213535437451560107079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 441253902761166537493618877 165470213535437451560107079)
      ·
        refine ⟨248205320303156177340160619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165470213535437451560107079 248205320303156177340160619)
        ·
          refine ⟨372307980454734266010240929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248205320303156177340160619 372307980454734266010240929)
          ·
            refine ⟨279230985341050699507680697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372307980454734266010240929 279230985341050699507680697)
            ·
              refine ⟨209423239005788024630760523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 279230985341050699507680697 209423239005788024630760523)
              ·
                refine ⟨314134858508682036946140785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209423239005788024630760523 314134858508682036946140785)
                ·
                  refine ⟨235601143881511527709605589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 314134858508682036946140785 235601143881511527709605589)
                  ·
                    refine ⟨5521901809722926430693881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 235601143881511527709605589 5521901809722926430693881)
                    ·
                      refine ⟨4141426357292194823020411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5521901809722926430693881 4141426357292194823020411)
                      ·
                        rfl

theorem cell23_8065399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 7, 2].length) (baseStart_8065399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065399 prefixEnd_8065399 := by exact prefixLift 8065399
  have htrace : WordTrace (prefixWord ++ tailWord_8065399) baseStart_8065399 baseEnd_8065399 := by
    simpa [prefixWord, tailWord_8065399, baseEnd_8065399] using wordTrace_append hprefix tailTrace_8065399
  have hstable : (prefixWord ++ tailWord_8065399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065399).length < 2 ^ (prefixWord ++ tailWord_8065399).sum := by decide
  have hdescent : baseEnd_8065399 < baseStart_8065399 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8065402 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5]
def baseStart_8065402 : Nat := 118140960795 + 8065402 * 2 ^ 59
def prefixEnd_8065402 : Nat := 4983230072969 + 3 ^ 40 * 8065402 * 2
def baseEnd_8065402 : Nat := 4141427897734158311282897

theorem tailTrace_8065402 : CollatzResearch.WordTrace tailWord_8065402 prefixEnd_8065402 4141427897734158311282897 := by
  unfold tailWord_8065402
  simp only [CollatzResearch.WordTrace]
  refine ⟨73542344481608372460359615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 196112918617622326560958973 73542344481608372460359615)
  ·
    refine ⟨110313516722412558690539423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73542344481608372460359615 110313516722412558690539423)
    ·
      refine ⟨165470275083618838035809135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110313516722412558690539423 165470275083618838035809135)
      ·
        refine ⟨248205412625428257053713703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165470275083618838035809135 248205412625428257053713703)
        ·
          refine ⟨372308118938142385580570555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 248205412625428257053713703 372308118938142385580570555)
          ·
            refine ⟨558462178407213578370855833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 372308118938142385580570555 558462178407213578370855833)
            ·
              refine ⟨418846633805410183778141875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558462178407213578370855833 418846633805410183778141875)
              ·
                refine ⟨628269950708115275667212813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418846633805410183778141875 628269950708115275667212813)
                ·
                  refine ⟨235601231515543228375204805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628269950708115275667212813 235601231515543228375204805)
                  ·
                    refine ⟨44175230909164355320350901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235601231515543228375204805 44175230909164355320350901)
                    ·
                      refine ⟨4141427897734158311282897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44175230909164355320350901 4141427897734158311282897)
                      ·
                        rfl

theorem cell23_8065402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 3, 4, 5].length) (baseStart_8065402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8065402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8065402 prefixEnd_8065402 := by exact prefixLift 8065402
  have htrace : WordTrace (prefixWord ++ tailWord_8065402) baseStart_8065402 baseEnd_8065402 := by
    simpa [prefixWord, tailWord_8065402, baseEnd_8065402] using wordTrace_append hprefix tailTrace_8065402
  have hstable : (prefixWord ++ tailWord_8065402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8065402).length < 2 ^ (prefixWord ++ tailWord_8065402).sum := by decide
  have hdescent : baseEnd_8065402 < baseStart_8065402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8065402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
