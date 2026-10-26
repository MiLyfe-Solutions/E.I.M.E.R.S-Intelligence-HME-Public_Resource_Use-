import V185TrunkScan23Chunk0782

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4631093 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_4631093 : Nat := 118140960795 + 4631093 * 2 ^ 59
def prefixEnd_4631093 : Nat := 4983230072969 + 3 ^ 40 * 4631093 * 2
def baseEnd_4631093 : Nat := 2377976664672354561039497

theorem tailTrace_4631093 : CollatzResearch.WordTrace tailWord_4631093 prefixEnd_4631093 2377976664672354561039497 := by
  unfold tailWord_4631093
  simp only [CollatzResearch.WordTrace]
  refine ⟨168909838211348463560537933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112606558807565642373691955 168909838211348463560537933)
  ·
    refine ⟨63341189329255673835201725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168909838211348463560537933 63341189329255673835201725)
    ·
      refine ⟨23752945998470877688200647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63341189329255673835201725 23752945998470877688200647)
      ·
        refine ⟨35629418997706316532300971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23752945998470877688200647 35629418997706316532300971)
        ·
          refine ⟨53444128496559474798451457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35629418997706316532300971 53444128496559474798451457)
          ·
            refine ⟨40083096372419606098838593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53444128496559474798451457 40083096372419606098838593)
            ·
              refine ⟨30062322279314704574128945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40083096372419606098838593 30062322279314704574128945)
              ·
                refine ⟨22546741709486028430596709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30062322279314704574128945 22546741709486028430596709)
                ·
                  refine ⟨4227514070528630330736883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22546741709486028430596709 4227514070528630330736883)
                  ·
                    refine ⟨6341271105792945496105325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4227514070528630330736883 6341271105792945496105325)
                    ·
                      refine ⟨2377976664672354561039497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6341271105792945496105325 2377976664672354561039497)
                      ·
                        rfl

theorem cell23_4631093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_4631093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631093 prefixEnd_4631093 := by exact prefixLift 4631093
  have htrace : WordTrace (prefixWord ++ tailWord_4631093) baseStart_4631093 baseEnd_4631093 := by
    simpa [prefixWord, tailWord_4631093, baseEnd_4631093] using wordTrace_append hprefix tailTrace_4631093
  have hstable : (prefixWord ++ tailWord_4631093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631093).length < 2 ^ (prefixWord ++ tailWord_4631093).sum := by decide
  have hdescent : baseEnd_4631093 < baseStart_4631093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631094 : List Nat := [5, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_4631094 : Nat := 118140960795 + 4631094 * 2 ^ 59
def prefixEnd_4631094 : Nat := 4983230072969 + 3 ^ 40 * 4631094 * 2
def baseEnd_4631094 : Nat := 2377977178153009057126993

theorem tailTrace_4631094 : CollatzResearch.WordTrace tailWord_4631094 prefixEnd_4631094 2377977178153009057126993 := by
  unfold tailWord_4631094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10556867167771552545707771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112606583122896560487549557 10556867167771552545707771)
  ·
    refine ⟨15835300751657328818561657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10556867167771552545707771 15835300751657328818561657)
    ·
      refine ⟨11876475563742996613921243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15835300751657328818561657 11876475563742996613921243)
      ·
        refine ⟨17814713345614494920881865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11876475563742996613921243 17814713345614494920881865)
        ·
          refine ⟨13361035009210871190661399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17814713345614494920881865 13361035009210871190661399)
          ·
            refine ⟨20041552513816306785992099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13361035009210871190661399 20041552513816306785992099)
            ·
              refine ⟨30062328770724460178988149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20041552513816306785992099 30062328770724460178988149)
              ·
                refine ⟨2818343322255418141780139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30062328770724460178988149 2818343322255418141780139)
                ·
                  refine ⟨4227514983383127212670209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818343322255418141780139 4227514983383127212670209)
                  ·
                    refine ⟨3170636237537345409502657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4227514983383127212670209 3170636237537345409502657)
                    ·
                      refine ⟨2377977178153009057126993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170636237537345409502657 2377977178153009057126993)
                      ·
                        rfl

theorem cell23_4631094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_4631094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631094 prefixEnd_4631094 := by exact prefixLift 4631094
  have htrace : WordTrace (prefixWord ++ tailWord_4631094) baseStart_4631094 baseEnd_4631094 := by
    simpa [prefixWord, tailWord_4631094, baseEnd_4631094] using wordTrace_append hprefix tailTrace_4631094
  have hstable : (prefixWord ++ tailWord_4631094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631094).length < 2 ^ (prefixWord ++ tailWord_4631094).sum := by decide
  have hdescent : baseEnd_4631094 < baseStart_4631094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631134 : List Nat := [4, 4, 1, 2, 1, 2, 2, 7]
def baseStart_4631134 : Nat := 118140960795 + 4631134 * 2 ^ 59
def prefixEnd_4631134 : Nat := 4983230072969 + 3 ^ 40 * 4631134 * 2
def baseEnd_4631134 : Nat := 88073989532562551875067

theorem tailTrace_4631134 : CollatzResearch.WordTrace tailWord_4631134 prefixEnd_4631134 88073989532562551875067 := by
  unfold tailWord_4631134
  simp only [CollatzResearch.WordTrace]
  refine ⟨21113916700524990945347557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112607555736133285041853637 21113916700524990945347557)
  ·
    refine ⟨3958859381348435802252667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21113916700524990945347557 3958859381348435802252667)
    ·
      refine ⟨5938289072022653703379001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3958859381348435802252667 5938289072022653703379001)
      ·
        refine ⟨4453716804016990277534251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5938289072022653703379001 4453716804016990277534251)
        ·
          refine ⟨6680575206025485416301377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453716804016990277534251 6680575206025485416301377)
          ·
            refine ⟨5010431404519114062226033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6680575206025485416301377 5010431404519114062226033)
            ·
              refine ⟨3757823553389335546669525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5010431404519114062226033 3757823553389335546669525)
              ·
                refine ⟨88073989532562551875067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3757823553389335546669525 88073989532562551875067)
                ·
                  rfl

theorem cell23_4631134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_4631134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631134 prefixEnd_4631134 := by exact prefixLift 4631134
  have htrace : WordTrace (prefixWord ++ tailWord_4631134) baseStart_4631134 baseEnd_4631134 := by
    simpa [prefixWord, tailWord_4631134, baseEnd_4631134] using wordTrace_append hprefix tailTrace_4631134
  have hstable : (prefixWord ++ tailWord_4631134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631134).length < 2 ^ (prefixWord ++ tailWord_4631134).sum := by decide
  have hdescent : baseEnd_4631134 < baseStart_4631134 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631136 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 3]
def baseStart_4631136 : Nat := 118140960795 + 4631136 * 2 ^ 59
def prefixEnd_4631136 : Nat := 4983230072969 + 3 ^ 40 * 4631136 * 2
def baseEnd_4631136 : Nat := 2377998744340497892801799

theorem tailTrace_4631136 : CollatzResearch.WordTrace tailWord_4631136 prefixEnd_4631136 2377998744340497892801799 := by
  unfold tailWord_4631136
  simp only [CollatzResearch.WordTrace]
  refine ⟨84455703275096340952176631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112607604366795121269568841 84455703275096340952176631)
  ·
    refine ⟨126683554912644511428264947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84455703275096340952176631 126683554912644511428264947)
    ·
      refine ⟨190025332368966767142397421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126683554912644511428264947 190025332368966767142397421)
      ·
        refine ⟨71259499638362537678399033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190025332368966767142397421 71259499638362537678399033)
        ·
          refine ⟨53444624728771903258799275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71259499638362537678399033 53444624728771903258799275)
          ·
            refine ⟨80166937093157854888198913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53444624728771903258799275 80166937093157854888198913)
            ·
              refine ⟨60125202819868391166149185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80166937093157854888198913 60125202819868391166149185)
              ·
                refine ⟨45093902114901293374611889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60125202819868391166149185 45093902114901293374611889)
                ·
                  refine ⟨33820426586175970030958917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45093902114901293374611889 33820426586175970030958917)
                  ·
                    refine ⟨6341329984907994380804797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33820426586175970030958917 6341329984907994380804797)
                    ·
                      refine ⟨2377998744340497892801799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6341329984907994380804797 2377998744340497892801799)
                      ·
                        rfl

theorem cell23_4631136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 3].length) (baseStart_4631136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631136 prefixEnd_4631136 := by exact prefixLift 4631136
  have htrace : WordTrace (prefixWord ++ tailWord_4631136) baseStart_4631136 baseEnd_4631136 := by
    simpa [prefixWord, tailWord_4631136, baseEnd_4631136] using wordTrace_append hprefix tailTrace_4631136
  have hstable : (prefixWord ++ tailWord_4631136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631136).length < 2 ^ (prefixWord ++ tailWord_4631136).sum := by decide
  have hdescent : baseEnd_4631136 < baseStart_4631136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631173 : List Nat := [1, 3, 1, 1, 4, 4, 1, 1, 7]
def baseStart_4631173 : Nat := 118140960795 + 4631173 * 2 ^ 59
def prefixEnd_4631173 : Nat := 4983230072969 + 3 ^ 40 * 4631173 * 2
def baseEnd_4631173 : Nat := 264224193680523805337681

theorem tailTrace_4631173 : CollatzResearch.WordTrace tailWord_4631173 prefixEnd_4631173 264224193680523805337681 := by
  unfold tailWord_4631173
  simp only [CollatzResearch.WordTrace]
  refine ⟨168912756051058637223450173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112608504034039091482300115 168912756051058637223450173)
  ·
    refine ⟨63342283519146988958793815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168912756051058637223450173 63342283519146988958793815)
    ·
      refine ⟨95013425278720483438190723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63342283519146988958793815 95013425278720483438190723)
      ·
        refine ⟨142520137918080725157286085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95013425278720483438190723 142520137918080725157286085)
        ·
          refine ⟨26722525859640135966991141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142520137918080725157286085 26722525859640135966991141)
          ·
            refine ⟨5010473598682525493810839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26722525859640135966991141 5010473598682525493810839)
            ·
              refine ⟨7515710398023788240716259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010473598682525493810839 7515710398023788240716259)
              ·
                refine ⟨11273565597035682361074389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7515710398023788240716259 11273565597035682361074389)
                ·
                  refine ⟨264224193680523805337681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11273565597035682361074389 264224193680523805337681)
                  ·
                    rfl

theorem cell23_4631173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_4631173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631173 prefixEnd_4631173 := by exact prefixLift 4631173
  have htrace : WordTrace (prefixWord ++ tailWord_4631173) baseStart_4631173 baseEnd_4631173 := by
    simpa [prefixWord, tailWord_4631173, baseEnd_4631173] using wordTrace_append hprefix tailTrace_4631173
  have hstable : (prefixWord ++ tailWord_4631173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631173).length < 2 ^ (prefixWord ++ tailWord_4631173).sum := by decide
  have hdescent : baseEnd_4631173 < baseStart_4631173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631213 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 5]
def baseStart_4631213 : Nat := 118140960795 + 4631213 * 2 ^ 59
def prefixEnd_4631213 : Nat := 4983230072969 + 3 ^ 40 * 4631213 * 2
def baseEnd_4631213 : Nat := 2378038282350894091538945

theorem tailTrace_4631213 : CollatzResearch.WordTrace tailWord_4631213 prefixEnd_4631213 2378038282350894091538945 := by
  unfold tailWord_4631213
  simp only [CollatzResearch.WordTrace]
  refine ⟨168914214970913724054906293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112609476647275816036604195 168914214970913724054906293)
  ·
    refine ⟨15835707653523161630147465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168914214970913724054906293 15835707653523161630147465)
    ·
      refine ⟨11876780740142371222610599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15835707653523161630147465 11876780740142371222610599)
      ·
        refine ⟨17815171110213556833915899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11876780740142371222610599 17815171110213556833915899)
        ·
          refine ⟨26722756665320335250873849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17815171110213556833915899 26722756665320335250873849)
          ·
            refine ⟨20042067498990251438155387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26722756665320335250873849 20042067498990251438155387)
            ·
              refine ⟨30063101248485377157233081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20042067498990251438155387 30063101248485377157233081)
              ·
                refine ⟨22547325936364032867924811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30063101248485377157233081 22547325936364032867924811)
                ·
                  refine ⟨33820988904546049301887217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22547325936364032867924811 33820988904546049301887217)
                  ·
                    refine ⟨25365741678409536976415413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33820988904546049301887217 25365741678409536976415413)
                    ·
                      refine ⟨2378038282350894091538945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25365741678409536976415413 2378038282350894091538945)
                      ·
                        rfl

theorem cell23_4631213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_4631213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631213 prefixEnd_4631213 := by exact prefixLift 4631213
  have htrace : WordTrace (prefixWord ++ tailWord_4631213) baseStart_4631213 baseEnd_4631213 := by
    simpa [prefixWord, tailWord_4631213, baseEnd_4631213] using wordTrace_append hprefix tailTrace_4631213
  have hstable : (prefixWord ++ tailWord_4631213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631213).length < 2 ^ (prefixWord ++ tailWord_4631213).sum := by decide
  have hdescent : baseEnd_4631213 < baseStart_4631213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631226 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5]
def baseStart_4631226 : Nat := 118140960795 + 4631226 * 2 ^ 59
def prefixEnd_4631226 : Nat := 4983230072969 + 3 ^ 40 * 4631226 * 2
def baseEnd_4631226 : Nat := 2378044957599402540676385

theorem tailTrace_4631226 : CollatzResearch.WordTrace tailWord_4631226 prefixEnd_4631226 2378044957599402540676385 := by
  unfold tailWord_4631226
  simp only [CollatzResearch.WordTrace]
  refine ⟨42228672279966656818782383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112609792746577751516753021 42228672279966656818782383)
  ·
    refine ⟨63343008419949985228173575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42228672279966656818782383 63343008419949985228173575)
    ·
      refine ⟨95014512629924977842260363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63343008419949985228173575 95014512629924977842260363)
      ·
        refine ⟨142521768944887466763390545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95014512629924977842260363 142521768944887466763390545)
        ·
          refine ⟨106891326708665600072542909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142521768944887466763390545 106891326708665600072542909)
          ·
            refine ⟨40084247515749600027203591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106891326708665600072542909 40084247515749600027203591)
            ·
              refine ⟨60126371273624400040805387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40084247515749600027203591 60126371273624400040805387)
              ·
                refine ⟨90189556910436600061208081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60126371273624400040805387 90189556910436600061208081)
                ·
                  refine ⟨67642167682827450045906061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90189556910436600061208081 67642167682827450045906061)
                  ·
                    refine ⟨25365812881060293767214773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67642167682827450045906061 25365812881060293767214773)
                    ·
                      refine ⟨2378044957599402540676385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25365812881060293767214773 2378044957599402540676385)
                      ·
                        rfl

theorem cell23_4631226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_4631226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631226 prefixEnd_4631226 := by exact prefixLift 4631226
  have htrace : WordTrace (prefixWord ++ tailWord_4631226) baseStart_4631226 baseEnd_4631226 := by
    simpa [prefixWord, tailWord_4631226, baseEnd_4631226] using wordTrace_append hprefix tailTrace_4631226
  have hstable : (prefixWord ++ tailWord_4631226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631226).length < 2 ^ (prefixWord ++ tailWord_4631226).sum := by decide
  have hdescent : baseEnd_4631226 < baseStart_4631226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631240 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 2, 4, 2]
def baseStart_4631240 : Nat := 118140960795 + 4631240 * 2 ^ 59
def prefixEnd_4631240 : Nat := 4983230072969 + 3 ^ 40 * 4631240 * 2
def baseEnd_4631240 : Nat := 2378052146328565485901321

theorem tailTrace_4631240 : CollatzResearch.WordTrace tailWord_4631240 prefixEnd_4631240 2378052146328565485901321 := by
  unfold tailWord_4631240
  simp only [CollatzResearch.WordTrace]
  refine ⟨84457599870907953833069587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112610133161210605110759449 84457599870907953833069587)
  ·
    refine ⟨126686399806361930749604381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84457599870907953833069587 126686399806361930749604381)
    ·
      refine ⟨47507399927385724031101643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126686399806361930749604381 47507399927385724031101643)
      ·
        refine ⟨71261099891078586046652465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47507399927385724031101643 71261099891078586046652465)
        ·
          refine ⟨53445824918308939534989349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71261099891078586046652465 53445824918308939534989349)
          ·
            refine ⟨10021092172182926162810503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53445824918308939534989349 10021092172182926162810503)
            ·
              refine ⟨15031638258274389244215755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10021092172182926162810503 15031638258274389244215755)
              ·
                refine ⟨22547457387411583866323633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15031638258274389244215755 22547457387411583866323633)
                ·
                  refine ⟨16910593040558687899742725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22547457387411583866323633 16910593040558687899742725)
                  ·
                    refine ⟨3170736195104753981201761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16910593040558687899742725 3170736195104753981201761)
                    ·
                      refine ⟨2378052146328565485901321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170736195104753981201761 2378052146328565485901321)
                      ·
                        rfl

theorem cell23_4631240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_4631240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631240 prefixEnd_4631240 := by exact prefixLift 4631240
  have htrace : WordTrace (prefixWord ++ tailWord_4631240) baseStart_4631240 baseEnd_4631240 := by
    simpa [prefixWord, tailWord_4631240, baseEnd_4631240] using wordTrace_append hprefix tailTrace_4631240
  have hstable : (prefixWord ++ tailWord_4631240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631240).length < 2 ^ (prefixWord ++ tailWord_4631240).sum := by decide
  have hdescent : baseEnd_4631240 < baseStart_4631240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631267 : List Nat := [1, 1, 1, 7, 1, 1, 1, 5, 1, 4]
def baseStart_4631267 : Nat := 118140960795 + 4631267 * 2 ^ 59
def prefixEnd_4631267 : Nat := 4983230072969 + 3 ^ 40 * 4631267 * 2
def baseEnd_4631267 : Nat := 792688670102078960087899

theorem tailTrace_4631267 : CollatzResearch.WordTrace tailWord_4631267 prefixEnd_4631267 792688670102078960087899 := by
  unfold tailWord_4631267
  simp only [CollatzResearch.WordTrace]
  refine ⟨168916184512718091277372055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112610789675145394184914703 168916184512718091277372055)
  ·
    refine ⟨253374276769077136916058083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168916184512718091277372055 253374276769077136916058083)
    ·
      refine ⟨380061415153615705374087125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253374276769077136916058083 380061415153615705374087125)
      ·
        refine ⟨8907689417662868094705167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 380061415153615705374087125 8907689417662868094705167)
        ·
          refine ⟨13361534126494302142057751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8907689417662868094705167 13361534126494302142057751)
          ·
            refine ⟨20042301189741453213086627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13361534126494302142057751 20042301189741453213086627)
            ·
              refine ⟨30063451784612179819629941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20042301189741453213086627 30063451784612179819629941)
              ·
                refine ⟨2818448604807391858090307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30063451784612179819629941 2818448604807391858090307)
                ·
                  refine ⟨4227672907211087787135461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818448604807391858090307 4227672907211087787135461)
                  ·
                    refine ⟨792688670102078960087899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4227672907211087787135461 792688670102078960087899)
                    ·
                      rfl

theorem cell23_4631267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 5, 1, 4].length) (baseStart_4631267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631267 prefixEnd_4631267 := by exact prefixLift 4631267
  have htrace : WordTrace (prefixWord ++ tailWord_4631267) baseStart_4631267 baseEnd_4631267 := by
    simpa [prefixWord, tailWord_4631267, baseEnd_4631267] using wordTrace_append hprefix tailTrace_4631267
  have hstable : (prefixWord ++ tailWord_4631267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631267).length < 2 ^ (prefixWord ++ tailWord_4631267).sum := by decide
  have hdescent : baseEnd_4631267 < baseStart_4631267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631290 : List Nat := [3, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3]
def baseStart_4631290 : Nat := 118140960795 + 4631290 * 2 ^ 59
def prefixEnd_4631290 : Nat := 4983230072969 + 3 ^ 40 * 4631290 * 2
def baseEnd_4631290 : Nat := 2378077820361290290276091

theorem tailTrace_4631290 : CollatzResearch.WordTrace tailWord_4631290 prefixEnd_4631290 2378077820361290290276091 := by
  unfold tailWord_4631290
  simp only [CollatzResearch.WordTrace]
  refine ⟨42229255847908691551364831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112611348927756510803639549 42229255847908691551364831)
  ·
    refine ⟨63343883771863037327047247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42229255847908691551364831 63343883771863037327047247)
    ·
      refine ⟨95015825657794555990570871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63343883771863037327047247 95015825657794555990570871)
      ·
        refine ⟨142523738486691833985856307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95015825657794555990570871 142523738486691833985856307)
        ·
          refine ⟨213785607730037750978784461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142523738486691833985856307 213785607730037750978784461)
          ·
            refine ⟨80169602898764156617044173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213785607730037750978784461 80169602898764156617044173)
            ·
              refine ⟨30063601087036558731391565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80169602898764156617044173 30063601087036558731391565)
              ·
                refine ⟨11273850407638709524271837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30063601087036558731391565 11273850407638709524271837)
                ·
                  refine ⟨4227693902864516071601939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11273850407638709524271837 4227693902864516071601939)
                  ·
                    refine ⟨6341540854296774107402909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4227693902864516071601939 6341540854296774107402909)
                    ·
                      refine ⟨2378077820361290290276091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6341540854296774107402909 2378077820361290290276091)
                      ·
                        rfl

theorem cell23_4631290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_4631290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631290 prefixEnd_4631290 := by exact prefixLift 4631290
  have htrace : WordTrace (prefixWord ++ tailWord_4631290) baseStart_4631290 baseEnd_4631290 := by
    simpa [prefixWord, tailWord_4631290, baseEnd_4631290] using wordTrace_append hprefix tailTrace_4631290
  have hstable : (prefixWord ++ tailWord_4631290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631290).length < 2 ^ (prefixWord ++ tailWord_4631290).sum := by decide
  have hdescent : baseEnd_4631290 < baseStart_4631290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631300 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_4631300 : Nat := 118140960795 + 4631300 * 2 ^ 59
def prefixEnd_4631300 : Nat := 4983230072969 + 3 ^ 40 * 4631300 * 2
def baseEnd_4631300 : Nat := 2378082955167835251151045

theorem tailTrace_4631300 : CollatzResearch.WordTrace tailWord_4631300 prefixEnd_4631300 2378082955167835251151045 := by
  unfold tailWord_4631300
  simp only [CollatzResearch.WordTrace]
  refine ⟨84458694060799268956661677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112611592081065691942215569 84458694060799268956661677)
  ·
    refine ⟨31672010272799725858748129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84458694060799268956661677 31672010272799725858748129)
    ·
      refine ⟨23754007704599794394061097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31672010272799725858748129 23754007704599794394061097)
      ·
        refine ⟨17815505778449845795545823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23754007704599794394061097 17815505778449845795545823)
        ·
          refine ⟨26723258667674768693318735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17815505778449845795545823 26723258667674768693318735)
          ·
            refine ⟨40084888001512153039978103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26723258667674768693318735 40084888001512153039978103)
            ·
              refine ⟨60127332002268229559967155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40084888001512153039978103 60127332002268229559967155)
              ·
                refine ⟨90190998003402344339950733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60127332002268229559967155 90190998003402344339950733)
                ·
                  refine ⟨33821624251275879127481525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90190998003402344339950733 33821624251275879127481525)
                  ·
                    refine ⟨3170777273557113668201393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33821624251275879127481525 3170777273557113668201393)
                    ·
                      refine ⟨2378082955167835251151045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3170777273557113668201393 2378082955167835251151045)
                      ·
                        rfl

theorem cell23_4631300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_4631300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631300 prefixEnd_4631300 := by exact prefixLift 4631300
  have htrace : WordTrace (prefixWord ++ tailWord_4631300) baseStart_4631300 baseEnd_4631300 := by
    simpa [prefixWord, tailWord_4631300, baseEnd_4631300] using wordTrace_append hprefix tailTrace_4631300
  have hstable : (prefixWord ++ tailWord_4631300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631300).length < 2 ^ (prefixWord ++ tailWord_4631300).sum := by decide
  have hdescent : baseEnd_4631300 < baseStart_4631300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631313 : List Nat := [1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 4]
def baseStart_4631313 : Nat := 118140960795 + 4631313 * 2 ^ 59
def prefixEnd_4631313 : Nat := 4983230072969 + 3 ^ 40 * 4631313 * 2
def baseEnd_4631313 : Nat := 2378089630416343700288485

theorem tailTrace_4631313 : CollatzResearch.WordTrace tailWord_4631313 prefixEnd_4631313 2378089630416343700288485 := by
  unfold tailWord_4631313
  simp only [CollatzResearch.WordTrace]
  refine ⟨168917862270551441133546593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112611908180367627422364395 168917862270551441133546593)
  ·
    refine ⟨126688396702913580850159945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168917862270551441133546593 126688396702913580850159945)
    ·
      refine ⟨95016297527185185637619959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126688396702913580850159945 95016297527185185637619959)
      ·
        refine ⟨142524446290777778456429939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95016297527185185637619959 142524446290777778456429939)
        ·
          refine ⟨213786669436166667684644909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142524446290777778456429939 213786669436166667684644909)
          ·
            refine ⟨80170001038562500381741841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213786669436166667684644909 80170001038562500381741841)
            ·
              refine ⟨60127500778921875286306381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80170001038562500381741841 60127500778921875286306381)
              ·
                refine ⟨22547812792095703232364893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60127500778921875286306381 22547812792095703232364893)
                ·
                  refine ⟨8455429797035888712136835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22547812792095703232364893 8455429797035888712136835)
                  ·
                    refine ⟨12683144695553833068205253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8455429797035888712136835 12683144695553833068205253)
                    ·
                      refine ⟨2378089630416343700288485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12683144695553833068205253 2378089630416343700288485)
                      ·
                        rfl

theorem cell23_4631313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 4].length) (baseStart_4631313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631313 prefixEnd_4631313 := by exact prefixLift 4631313
  have htrace : WordTrace (prefixWord ++ tailWord_4631313) baseStart_4631313 baseEnd_4631313 := by
    simpa [prefixWord, tailWord_4631313, baseEnd_4631313] using wordTrace_append hprefix tailTrace_4631313
  have hstable : (prefixWord ++ tailWord_4631313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631313).length < 2 ^ (prefixWord ++ tailWord_4631313).sum := by decide
  have hdescent : baseEnd_4631313 < baseStart_4631313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631324 : List Nat := [2, 2, 3, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_4631324 : Nat := 118140960795 + 4631324 * 2 ^ 59
def prefixEnd_4631324 : Nat := 4983230072969 + 3 ^ 40 * 4631324 * 2
def baseEnd_4631324 : Nat := 2378095278703543157250935

theorem tailTrace_4631324 : CollatzResearch.WordTrace tailWord_4631324 prefixEnd_4631324 2378095278703543157250935 := by
  unfold tailWord_4631324
  simp only [CollatzResearch.WordTrace]
  refine ⟨84459131736755795006098513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112612175649007726674798017 84459131736755795006098513)
  ·
    refine ⟨63344348802566846254573885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84459131736755795006098513 63344348802566846254573885)
    ·
      refine ⟨23754130800962567345465207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63344348802566846254573885 23754130800962567345465207)
      ·
        refine ⟨35631196201443851018197811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23754130800962567345465207 35631196201443851018197811)
        ·
          refine ⟨53446794302165776527296717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35631196201443851018197811 53446794302165776527296717)
          ·
            refine ⟨20042547863312166197736269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53446794302165776527296717 20042547863312166197736269)
            ·
              refine ⟨7515955448742062324151101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20042547863312166197736269 7515955448742062324151101)
              ·
                refine ⟨2818483293278273371556663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7515955448742062324151101 2818483293278273371556663)
                ·
                  refine ⟨4227724939917410057334995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818483293278273371556663 4227724939917410057334995)
                  ·
                    refine ⟨6341587409876115086002493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4227724939917410057334995 6341587409876115086002493)
                    ·
                      refine ⟨2378095278703543157250935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6341587409876115086002493 2378095278703543157250935)
                      ·
                        rfl

theorem cell23_4631324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_4631324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631324 prefixEnd_4631324 := by exact prefixLift 4631324
  have htrace : WordTrace (prefixWord ++ tailWord_4631324) baseStart_4631324 baseEnd_4631324 := by
    simpa [prefixWord, tailWord_4631324, baseEnd_4631324] using wordTrace_append hprefix tailTrace_4631324
  have hstable : (prefixWord ++ tailWord_4631324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631324).length < 2 ^ (prefixWord ++ tailWord_4631324).sum := by decide
  have hdescent : baseEnd_4631324 < baseStart_4631324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631340 : List Nat := [2, 2, 1, 1, 1, 4, 2, 4, 2, 4]
def baseStart_4631340 : Nat := 118140960795 + 4631340 * 2 ^ 59
def prefixEnd_4631340 : Nat := 4983230072969 + 3 ^ 40 * 4631340 * 2
def baseEnd_4631340 : Nat := 792701164798005031550287

theorem tailTrace_4631340 : CollatzResearch.WordTrace tailWord_4631340 prefixEnd_4631340 792701164798005031550287 := by
  unfold tailWord_4631340
  simp only [CollatzResearch.WordTrace]
  refine ⟨84459423520726812372389737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112612564694302416496519649 84459423520726812372389737)
  ·
    refine ⟨63344567640545109279292303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84459423520726812372389737 63344567640545109279292303)
    ·
      refine ⟨95016851460817663918938455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63344567640545109279292303 95016851460817663918938455)
      ·
        refine ⟨142525277191226495878407683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95016851460817663918938455 142525277191226495878407683)
        ·
          refine ⟨213787915786839743817611525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142525277191226495878407683 213787915786839743817611525)
          ·
            refine ⟨40085234210032451965802161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213787915786839743817611525 40085234210032451965802161)
            ·
              refine ⟨30063925657524338974351621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40085234210032451965802161 30063925657524338974351621)
              ·
                refine ⟨5636986060785813557690929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30063925657524338974351621 5636986060785813557690929)
                ·
                  refine ⟨4227739545589360168268197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5636986060785813557690929 4227739545589360168268197)
                  ·
                    refine ⟨792701164798005031550287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4227739545589360168268197 792701164798005031550287)
                    ·
                      rfl

theorem cell23_4631340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_4631340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631340 prefixEnd_4631340 := by exact prefixLift 4631340
  have htrace : WordTrace (prefixWord ++ tailWord_4631340) baseStart_4631340 baseEnd_4631340 := by
    simpa [prefixWord, tailWord_4631340, baseEnd_4631340] using wordTrace_append hprefix tailTrace_4631340
  have hstable : (prefixWord ++ tailWord_4631340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631340).length < 2 ^ (prefixWord ++ tailWord_4631340).sum := by decide
  have hdescent : baseEnd_4631340 < baseStart_4631340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631361 : List Nat := [1, 2, 5, 3, 2, 1, 1, 2, 1, 5]
def baseStart_4631361 : Nat := 118140960795 + 4631361 * 2 ^ 59
def prefixEnd_4631361 : Nat := 4983230072969 + 3 ^ 40 * 4631361 * 2
def baseEnd_4631361 : Nat := 792704759162586504162755

theorem tailTrace_4631361 : CollatzResearch.WordTrace tailWord_4631361 prefixEnd_4631361 792704759162586504162755 := by
  unfold tailWord_4631361
  simp only [CollatzResearch.WordTrace]
  refine ⟨168919612974377545331293937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112613075316251696887529291 168919612974377545331293937)
  ·
    refine ⟨126689709730783158998470453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168919612974377545331293937 126689709730783158998470453)
    ·
      refine ⟨11877160287260921156106605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126689709730783158998470453 11877160287260921156106605)
      ·
        refine ⟨4453935107722845433539977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11877160287260921156106605 4453935107722845433539977)
        ·
          refine ⟨3340451330792134075154983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4453935107722845433539977 3340451330792134075154983)
          ·
            refine ⟨5010676996188201112732475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340451330792134075154983 5010676996188201112732475)
            ·
              refine ⟨7516015494282301669098713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5010676996188201112732475 7516015494282301669098713)
              ·
                refine ⟨5637011620711726251824035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7516015494282301669098713 5637011620711726251824035)
                ·
                  refine ⟨8455517431067589377736053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5637011620711726251824035 8455517431067589377736053)
                  ·
                    refine ⟨792704759162586504162755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8455517431067589377736053 792704759162586504162755)
                    ·
                      rfl

theorem cell23_4631361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_4631361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631361 prefixEnd_4631361 := by exact prefixLift 4631361
  have htrace : WordTrace (prefixWord ++ tailWord_4631361) baseStart_4631361 baseEnd_4631361 := by
    simpa [prefixWord, tailWord_4631361, baseEnd_4631361] using wordTrace_append hprefix tailTrace_4631361
  have hstable : (prefixWord ++ tailWord_4631361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631361).length < 2 ^ (prefixWord ++ tailWord_4631361).sum := by decide
  have hdescent : baseEnd_4631361 < baseStart_4631361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631364 : List Nat := [2, 3, 4, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4631364 : Nat := 118140960795 + 4631364 * 2 ^ 59
def prefixEnd_4631364 : Nat := 4983230072969 + 3 ^ 40 * 4631364 * 2
def baseEnd_4631364 : Nat := 2378115817929723000750751

theorem tailTrace_4631364 : CollatzResearch.WordTrace tailWord_4631364 prefixEnd_4631364 2378115817929723000750751 := by
  unfold tailWord_4631364
  simp only [CollatzResearch.WordTrace]
  refine ⟨84459861196683338421826573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112613148262244451229102097 84459861196683338421826573)
  ·
    refine ⟨31672447948756251908184965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84459861196683338421826573 31672447948756251908184965)
    ·
      refine ⟨5938583990391797232784681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31672447948756251908184965 5938583990391797232784681)
      ·
        refine ⟨4453937992793847924588511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5938583990391797232784681 4453937992793847924588511)
        ·
          refine ⟨6680906989190771886882767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4453937992793847924588511 6680906989190771886882767)
          ·
            refine ⟨10021360483786157830324151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6680906989190771886882767 10021360483786157830324151)
            ·
              refine ⟨15032040725679236745486227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10021360483786157830324151 15032040725679236745486227)
              ·
                refine ⟨22548061088518855118229341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15032040725679236745486227 22548061088518855118229341)
                ·
                  refine ⟨8455522908194570669336003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22548061088518855118229341 8455522908194570669336003)
                  ·
                    refine ⟨12683284362291856004004005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8455522908194570669336003 12683284362291856004004005)
                    ·
                      refine ⟨2378115817929723000750751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12683284362291856004004005 2378115817929723000750751)
                      ·
                        rfl

theorem cell23_4631364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4631364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631364 prefixEnd_4631364 := by exact prefixLift 4631364
  have htrace : WordTrace (prefixWord ++ tailWord_4631364) baseStart_4631364 baseEnd_4631364 := by
    simpa [prefixWord, tailWord_4631364, baseEnd_4631364] using wordTrace_append hprefix tailTrace_4631364
  have hstable : (prefixWord ++ tailWord_4631364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631364).length < 2 ^ (prefixWord ++ tailWord_4631364).sum := by decide
  have hdescent : baseEnd_4631364 < baseStart_4631364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631397 : List Nat := [1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 3]
def baseStart_4631397 : Nat := 118140960795 + 4631397 * 2 ^ 59
def prefixEnd_4631397 : Nat := 4983230072969 + 3 ^ 40 * 4631397 * 2
def baseEnd_4631397 : Nat := 2378132762791321371638099

theorem tailTrace_4631397 : CollatzResearch.WordTrace tailWord_4631397 prefixEnd_4631397 2378132762791321371638099 := by
  unfold tailWord_4631397
  simp only [CollatzResearch.WordTrace]
  refine ⟨168920926002247123479604445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112613950668164748986402963 168920926002247123479604445)
  ·
    refine ⟨63345347250842671304851667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168920926002247123479604445 63345347250842671304851667)
    ·
      refine ⟨95018020876264006957277501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63345347250842671304851667 95018020876264006957277501)
      ·
        refine ⟨35631757828599002608979063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95018020876264006957277501 35631757828599002608979063)
        ·
          refine ⟨53447636742898503913468595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35631757828599002608979063 53447636742898503913468595)
          ·
            refine ⟨80171455114347755870202893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53447636742898503913468595 80171455114347755870202893)
            ·
              refine ⟨30064295667880408451326085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80171455114347755870202893 30064295667880408451326085)
              ·
                refine ⟨5637055437727576584623641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30064295667880408451326085 5637055437727576584623641)
                ·
                  refine ⟨4227791578295682438467731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5637055437727576584623641 4227791578295682438467731)
                  ·
                    refine ⟨6341687367443523657701597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4227791578295682438467731 6341687367443523657701597)
                    ·
                      refine ⟨2378132762791321371638099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6341687367443523657701597 2378132762791321371638099)
                      ·
                        rfl

theorem cell23_4631397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_4631397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631397 prefixEnd_4631397 := by exact prefixLift 4631397
  have htrace : WordTrace (prefixWord ++ tailWord_4631397) baseStart_4631397 baseEnd_4631397 := by
    simpa [prefixWord, tailWord_4631397, baseEnd_4631397] using wordTrace_append hprefix tailTrace_4631397
  have hstable : (prefixWord ++ tailWord_4631397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631397).length < 2 ^ (prefixWord ++ tailWord_4631397).sum := by decide
  have hdescent : baseEnd_4631397 < baseStart_4631397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631403 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 4]
def baseStart_4631403 : Nat := 118140960795 + 4631403 * 2 ^ 59
def prefixEnd_4631403 : Nat := 4983230072969 + 3 ^ 40 * 4631403 * 2
def baseEnd_4631403 : Nat := 2378135843675248348163071

theorem tailTrace_4631403 : CollatzResearch.WordTrace tailWord_4631403 prefixEnd_4631403 2378135843675248348163071 := by
  unfold tailWord_4631403
  simp only [CollatzResearch.WordTrace]
  refine ⟨168921144840225386504322863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112614096560150257669548575 168921144840225386504322863)
  ·
    refine ⟨253381717260338079756484295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168921144840225386504322863 253381717260338079756484295)
    ·
      refine ⟨380072575890507119634726443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253381717260338079756484295 380072575890507119634726443)
      ·
        refine ⟨570108863835760679452089665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380072575890507119634726443 570108863835760679452089665)
        ·
          refine ⟨427581647876820509589067249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570108863835760679452089665 427581647876820509589067249)
          ·
            refine ⟨320686235907615382191800437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427581647876820509589067249 320686235907615382191800437)
            ·
              refine ⟨30064334616338942080481291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 320686235907615382191800437 30064334616338942080481291)
              ·
                refine ⟨45096501924508413120721937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30064334616338942080481291 45096501924508413120721937)
                ·
                  refine ⟨33822376443381309840541453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45096501924508413120721937 33822376443381309840541453)
                  ·
                    refine ⟨12683391166267991190203045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33822376443381309840541453 12683391166267991190203045)
                    ·
                      refine ⟨2378135843675248348163071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12683391166267991190203045 2378135843675248348163071)
                      ·
                        rfl

theorem cell23_4631403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 4].length) (baseStart_4631403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631403 prefixEnd_4631403 := by exact prefixLift 4631403
  have htrace : WordTrace (prefixWord ++ tailWord_4631403) baseStart_4631403 baseEnd_4631403 := by
    simpa [prefixWord, tailWord_4631403, baseEnd_4631403] using wordTrace_append hprefix tailTrace_4631403
  have hstable : (prefixWord ++ tailWord_4631403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631403).length < 2 ^ (prefixWord ++ tailWord_4631403).sum := by decide
  have hdescent : baseEnd_4631403 < baseStart_4631403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631414 : List Nat := [5, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_4631414 : Nat := 118140960795 + 4631414 * 2 ^ 59
def prefixEnd_4631414 : Nat := 4983230072969 + 3 ^ 40 * 4631414 * 2
def baseEnd_4631414 : Nat := 2378141491962447805125521

theorem tailTrace_4631414 : CollatzResearch.WordTrace tailWord_4631414 prefixEnd_4631414 2378141491962447805125521 := by
  unfold tailWord_4631414
  simp only [CollatzResearch.WordTrace]
  refine ⟨10557596627699095961435831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112614364028790356921982197 10557596627699095961435831)
  ·
    refine ⟨15836394941548643942153747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10557596627699095961435831 15836394941548643942153747)
    ·
      refine ⟨23754592412322965913230621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15836394941548643942153747 23754592412322965913230621)
      ·
        refine ⟨8907972154621112217461483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23754592412322965913230621 8907972154621112217461483)
        ·
          refine ⟨13361958231931668326192225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8907972154621112217461483 13361958231931668326192225)
          ·
            refine ⟨10021468673948751244644169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13361958231931668326192225 10021468673948751244644169)
            ·
              refine ⟨7516101505461563433483127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10021468673948751244644169 7516101505461563433483127)
              ·
                refine ⟨11274152258192345150224691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7516101505461563433483127 11274152258192345150224691)
                ·
                  refine ⟨16911228387288517725337037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11274152258192345150224691 16911228387288517725337037)
                  ·
                    refine ⟨6341710645233194147001389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16911228387288517725337037 6341710645233194147001389)
                    ·
                      refine ⟨2378141491962447805125521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6341710645233194147001389 2378141491962447805125521)
                      ·
                        rfl

theorem cell23_4631414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_4631414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631414 prefixEnd_4631414 := by exact prefixLift 4631414
  have htrace : WordTrace (prefixWord ++ tailWord_4631414) baseStart_4631414 baseEnd_4631414 := by
    simpa [prefixWord, tailWord_4631414, baseEnd_4631414] using wordTrace_append hprefix tailTrace_4631414
  have hstable : (prefixWord ++ tailWord_4631414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631414).length < 2 ^ (prefixWord ++ tailWord_4631414).sum := by decide
  have hdescent : baseEnd_4631414 < baseStart_4631414 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631423 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 5]
def baseStart_4631423 : Nat := 118140960795 + 4631423 * 2 ^ 59
def prefixEnd_4631423 : Nat := 4983230072969 + 3 ^ 40 * 4631423 * 2
def baseEnd_4631423 : Nat := 2378146113288338269912979

theorem tailTrace_4631423 : CollatzResearch.WordTrace tailWord_4631423 prefixEnd_4631423 2378146113288338269912979 := by
  unfold tailWord_4631423
  simp only [CollatzResearch.WordTrace]
  refine ⟨168921874300152929920050923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112614582866768619946700615 168921874300152929920050923)
  ·
    refine ⟨253382811450229394880076385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168921874300152929920050923 253382811450229394880076385)
    ·
      refine ⟨190037108587672046160057289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253382811450229394880076385 190037108587672046160057289)
      ·
        refine ⟨142527831440754034620042967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190037108587672046160057289 142527831440754034620042967)
        ·
          refine ⟨213791747161131051930064451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142527831440754034620042967 213791747161131051930064451)
          ·
            refine ⟨320687620741696577895096677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213791747161131051930064451 320687620741696577895096677)
            ·
              refine ⟨60128928889068108355330627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 320687620741696577895096677 60128928889068108355330627)
              ·
                refine ⟨90193393333602162532995941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60128928889068108355330627 90193393333602162532995941)
                ·
                  refine ⟨16911261250050405474936739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90193393333602162532995941 16911261250050405474936739)
                  ·
                    refine ⟨25366891875075608212405109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16911261250050405474936739 25366891875075608212405109)
                    ·
                      refine ⟨2378146113288338269912979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25366891875075608212405109 2378146113288338269912979)
                      ·
                        rfl

theorem cell23_4631423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_4631423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631423 prefixEnd_4631423 := by exact prefixLift 4631423
  have htrace : WordTrace (prefixWord ++ tailWord_4631423) baseStart_4631423 baseEnd_4631423 := by
    simpa [prefixWord, tailWord_4631423, baseEnd_4631423] using wordTrace_append hprefix tailTrace_4631423
  have hstable : (prefixWord ++ tailWord_4631423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631423).length < 2 ^ (prefixWord ++ tailWord_4631423).sum := by decide
  have hdescent : baseEnd_4631423 < baseStart_4631423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631460 : List Nat := [2, 3, 1, 2, 1, 2, 4, 1, 7]
def baseStart_4631460 : Nat := 118140960795 + 4631460 * 2 ^ 59
def prefixEnd_4631460 : Nat := 4983230072969 + 3 ^ 40 * 4631460 * 2
def baseEnd_4631460 : Nat := 264240568008061625016701

theorem tailTrace_4631460 : CollatzResearch.WordTrace tailWord_4631460 prefixEnd_4631460 264240568008061625016701 := by
  unfold tailWord_4631460
  simp only [CollatzResearch.WordTrace]
  refine ⟨84461611900509442619573917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112615482534012590159431889 84461611900509442619573917)
  ·
    refine ⟨31673104462691040982340219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84461611900509442619573917 31673104462691040982340219)
    ·
      refine ⟨47509656694036561473510329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31673104462691040982340219 47509656694036561473510329)
      ·
        refine ⟨35632242520527421105132747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47509656694036561473510329 35632242520527421105132747)
        ·
          refine ⟨53448363780791131657699121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35632242520527421105132747 53448363780791131657699121)
          ·
            refine ⟨40086272835593348743274341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53448363780791131657699121 40086272835593348743274341)
            ·
              refine ⟨7516176156673752889363939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40086272835593348743274341 7516176156673752889363939)
              ·
                refine ⟨11274264235010629334045909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7516176156673752889363939 11274264235010629334045909)
                ·
                  refine ⟨264240568008061625016701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11274264235010629334045909 264240568008061625016701)
                  ·
                    rfl

theorem cell23_4631460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 4, 1, 7].length) (baseStart_4631460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631460 prefixEnd_4631460 := by exact prefixLift 4631460
  have htrace : WordTrace (prefixWord ++ tailWord_4631460) baseStart_4631460 baseEnd_4631460 := by
    simpa [prefixWord, tailWord_4631460, baseEnd_4631460] using wordTrace_append hprefix tailTrace_4631460
  have hstable : (prefixWord ++ tailWord_4631460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631460).length < 2 ^ (prefixWord ++ tailWord_4631460).sum := by decide
  have hdescent : baseEnd_4631460 < baseStart_4631460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631493 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_4631493 : Nat := 118140960795 + 4631493 * 2 ^ 59
def prefixEnd_4631493 : Nat := 4983230072969 + 3 ^ 40 * 4631493 * 2
def baseEnd_4631493 : Nat := 2378182056934152996037657

theorem tailTrace_4631493 : CollatzResearch.WordTrace tailWord_4631493 prefixEnd_4631493 2378182056934152996037657 := by
  unfold tailWord_4631493
  simp only [CollatzResearch.WordTrace]
  refine ⟨168924427409899331875099133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112616284939932887916732755 168924427409899331875099133)
  ·
    refine ⟨63346660278712249453162175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168924427409899331875099133 63346660278712249453162175)
    ·
      refine ⟨95019990418068374179743263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63346660278712249453162175 95019990418068374179743263)
      ·
        refine ⟨142529985627102561269614895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95019990418068374179743263 142529985627102561269614895)
        ·
          refine ⟨213794978440653841904422343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142529985627102561269614895 213794978440653841904422343)
          ·
            refine ⟨320692467660980762856633515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213794978440653841904422343 320692467660980762856633515)
            ·
              refine ⟨481038701491471144284950273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320692467660980762856633515 481038701491471144284950273)
              ·
                refine ⟨360779026118603358213712705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481038701491471144284950273 360779026118603358213712705)
                ·
                  refine ⟨270584269588952518660284529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 360779026118603358213712705 270584269588952518660284529)
                  ·
                    refine ⟨202938202191714388995213397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 270584269588952518660284529 202938202191714388995213397)
                    ·
                      refine ⟨2378182056934152996037657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 202938202191714388995213397 2378182056934152996037657)
                      ·
                        rfl

theorem cell23_4631493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_4631493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631493 prefixEnd_4631493 := by exact prefixLift 4631493
  have htrace : WordTrace (prefixWord ++ tailWord_4631493) baseStart_4631493 baseEnd_4631493 := by
    simpa [prefixWord, tailWord_4631493, baseEnd_4631493] using wordTrace_append hprefix tailTrace_4631493
  have hstable : (prefixWord ++ tailWord_4631493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631493).length < 2 ^ (prefixWord ++ tailWord_4631493).sum := by decide
  have hdescent : baseEnd_4631493 < baseStart_4631493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631500 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_4631500 : Nat := 118140960795 + 4631500 * 2 ^ 59
def prefixEnd_4631500 : Nat := 4983230072969 + 3 ^ 40 * 4631500 * 2
def baseEnd_4631500 : Nat := 2378185651298734468650125

theorem tailTrace_4631500 : CollatzResearch.WordTrace tailWord_4631500 prefixEnd_4631500 2378185651298734468650125 := by
  unfold tailWord_4631500
  simp only [CollatzResearch.WordTrace]
  refine ⟨84462341360436986035301977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112616455147249314713735969 84462341360436986035301977)
  ·
    refine ⟨63346756020327739526476483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84462341360436986035301977 63346756020327739526476483)
    ·
      refine ⟨95020134030491609289714725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63346756020327739526476483 95020134030491609289714725)
      ·
        refine ⟨17816275130717176741821511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95020134030491609289714725 17816275130717176741821511)
        ·
          refine ⟨26724412696075765112732267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17816275130717176741821511 26724412696075765112732267)
          ·
            refine ⟨40086619044113647669098401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26724412696075765112732267 40086619044113647669098401)
            ·
              refine ⟨30064964283085235751823801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40086619044113647669098401 30064964283085235751823801)
              ·
                refine ⟨22548723212313926813867851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30064964283085235751823801 22548723212313926813867851)
                ·
                  refine ⟨33823084818470890220801777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22548723212313926813867851 33823084818470890220801777)
                  ·
                    refine ⟨25367313613853167665601333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33823084818470890220801777 25367313613853167665601333)
                    ·
                      refine ⟨2378185651298734468650125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25367313613853167665601333 2378185651298734468650125)
                      ·
                        rfl

theorem cell23_4631500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_4631500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631500 prefixEnd_4631500 := by exact prefixLift 4631500
  have htrace : WordTrace (prefixWord ++ tailWord_4631500) baseStart_4631500 baseEnd_4631500 := by
    simpa [prefixWord, tailWord_4631500, baseEnd_4631500] using wordTrace_append hprefix tailTrace_4631500
  have hstable : (prefixWord ++ tailWord_4631500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631500).length < 2 ^ (prefixWord ++ tailWord_4631500).sum := by decide
  have hdescent : baseEnd_4631500 < baseStart_4631500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631517 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 5]
def baseStart_4631517 : Nat := 118140960795 + 4631517 * 2 ^ 59
def prefixEnd_4631517 : Nat := 4983230072969 + 3 ^ 40 * 4631517 * 2
def baseEnd_4631517 : Nat := 2378194380469860902137547

theorem tailTrace_4631517 : CollatzResearch.WordTrace tailWord_4631517 prefixEnd_4631517 2378194380469860902137547 := by
  unfold tailWord_4631517
  simp only [CollatzResearch.WordTrace]
  refine ⟨168925302761812383973972805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112616868507874922649315203 168925302761812383973972805)
  ·
    refine ⟨31673494267839821995119901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168925302761812383973972805 31673494267839821995119901)
    ·
      refine ⟨11877560350439933248169963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31673494267839821995119901 11877560350439933248169963)
      ·
        refine ⟨17816340525659899872254945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11877560350439933248169963 17816340525659899872254945)
        ·
          refine ⟨13362255394244924904191209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17816340525659899872254945 13362255394244924904191209)
          ·
            refine ⟨10021691545683693678143407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13362255394244924904191209 10021691545683693678143407)
            ·
              refine ⟨15032537318525540517215111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10021691545683693678143407 15032537318525540517215111)
              ·
                refine ⟨22548805977788310775822667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15032537318525540517215111 22548805977788310775822667)
                ·
                  refine ⟨33823208966682466163734001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22548805977788310775822667 33823208966682466163734001)
                  ·
                    refine ⟨25367406725011849622800501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33823208966682466163734001 25367406725011849622800501)
                    ·
                      refine ⟨2378194380469860902137547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25367406725011849622800501 2378194380469860902137547)
                      ·
                        rfl

theorem cell23_4631517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_4631517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631517 prefixEnd_4631517 := by exact prefixLift 4631517
  have htrace : WordTrace (prefixWord ++ tailWord_4631517) baseStart_4631517 baseEnd_4631517 := by
    simpa [prefixWord, tailWord_4631517, baseEnd_4631517] using wordTrace_append hprefix tailTrace_4631517
  have hstable : (prefixWord ++ tailWord_4631517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631517).length < 2 ^ (prefixWord ++ tailWord_4631517).sum := by decide
  have hdescent : baseEnd_4631517 < baseStart_4631517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631541 : List Nat := [1, 3, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4631541 : Nat := 118140960795 + 4631541 * 2 ^ 59
def prefixEnd_4631541 : Nat := 4983230072969 + 3 ^ 40 * 4631541 * 2
def baseEnd_4631541 : Nat := 792735568001856269412479

theorem tailTrace_4631541 : CollatzResearch.WordTrace tailWord_4631541 prefixEnd_4631541 792735568001856269412479 := by
  unfold tailWord_4631541
  simp only [CollatzResearch.WordTrace]
  refine ⟨168926178113725436072846477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112617452075816957381897651 168926178113725436072846477)
  ·
    refine ⟨63347316792647038527317429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168926178113725436072846477 63347316792647038527317429)
    ·
      refine ⟨5938810949310659861936009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 63347316792647038527317429 5938810949310659861936009)
      ·
        refine ⟨4454108211982994896452007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5938810949310659861936009 4454108211982994896452007)
        ·
          refine ⟨6681162317974492344678011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454108211982994896452007 6681162317974492344678011)
          ·
            refine ⟨10021743476961738517017017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6681162317974492344678011 10021743476961738517017017)
            ·
              refine ⟨7516307607721303887762763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10021743476961738517017017 7516307607721303887762763)
              ·
                refine ⟨11274461411581955831644145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7516307607721303887762763 11274461411581955831644145)
                ·
                  refine ⟨8455846058686466873733109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11274461411581955831644145 8455846058686466873733109)
                  ·
                    refine ⟨792735568001856269412479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8455846058686466873733109 792735568001856269412479)
                    ·
                      rfl

theorem cell23_4631541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4631541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631541 prefixEnd_4631541 := by exact prefixLift 4631541
  have htrace : WordTrace (prefixWord ++ tailWord_4631541) baseStart_4631541 baseEnd_4631541 := by
    simpa [prefixWord, tailWord_4631541, baseEnd_4631541] using wordTrace_append hprefix tailTrace_4631541
  have hstable : (prefixWord ++ tailWord_4631541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631541).length < 2 ^ (prefixWord ++ tailWord_4631541).sum := by decide
  have hdescent : baseEnd_4631541 < baseStart_4631541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631637 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_4631637 : Nat := 118140960795 + 4631637 * 2 ^ 59
def prefixEnd_4631637 : Nat := 4983230072969 + 3 ^ 40 * 4631637 * 2
def baseEnd_4631637 : Nat := 2378255998148400432636995

theorem tailTrace_4631637 : CollatzResearch.WordTrace tailWord_4631637 prefixEnd_4631637 2378255998148400432636995 := by
  unfold tailWord_4631637
  simp only [CollatzResearch.WordTrace]
  refine ⟨168929679521377644468341165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112619786347585096312227443 168929679521377644468341165)
  ·
    refine ⟨63348629820516616675627937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168929679521377644468341165 63348629820516616675627937)
    ·
      refine ⟨47511472365387462506720953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63348629820516616675627937 47511472365387462506720953)
      ·
        refine ⟨35633604274040596880040715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47511472365387462506720953 35633604274040596880040715)
        ·
          refine ⟨53450406411060895320061073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35633604274040596880040715 53450406411060895320061073)
          ·
            refine ⟨40087804808295671490045805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53450406411060895320061073 40087804808295671490045805)
            ·
              refine ⟨15032926803110876808767177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40087804808295671490045805 15032926803110876808767177)
              ·
                refine ⟨11274695102333157606575383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15032926803110876808767177 11274695102333157606575383)
                ·
                  refine ⟨16912042653499736409863075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11274695102333157606575383 16912042653499736409863075)
                  ·
                    refine ⟨25368063980249604614794613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16912042653499736409863075 25368063980249604614794613)
                    ·
                      refine ⟨2378255998148400432636995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25368063980249604614794613 2378255998148400432636995)
                      ·
                        rfl

theorem cell23_4631637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_4631637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631637 prefixEnd_4631637 := by exact prefixLift 4631637
  have htrace : WordTrace (prefixWord ++ tailWord_4631637) baseStart_4631637 baseEnd_4631637 := by
    simpa [prefixWord, tailWord_4631637, baseEnd_4631637] using wordTrace_append hprefix tailTrace_4631637
  have hstable : (prefixWord ++ tailWord_4631637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631637).length < 2 ^ (prefixWord ++ tailWord_4631637).sum := by decide
  have hdescent : baseEnd_4631637 < baseStart_4631637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631640 : List Nat := [2, 1, 2, 2, 1, 3, 2, 10]
def baseStart_4631640 : Nat := 118140960795 + 4631640 * 2 ^ 59
def prefixEnd_4631640 : Nat := 4983230072969 + 3 ^ 40 * 4631640 * 2
def baseEnd_4631640 : Nat := 88083612540383848922203

theorem tailTrace_4631640 : CollatzResearch.WordTrace tailWord_4631640 prefixEnd_4631640 88083612540383848922203 := by
  unfold tailWord_4631640
  simp only [CollatzResearch.WordTrace]
  refine ⟨84464894470183387990350187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112619859293577850653800249 84464894470183387990350187)
  ·
    refine ⟨126697341705275081985525281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84464894470183387990350187 126697341705275081985525281)
    ·
      refine ⟨95023006278956311489143961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126697341705275081985525281 95023006278956311489143961)
      ·
        refine ⟨71267254709217233616857971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95023006278956311489143961 71267254709217233616857971)
        ·
          refine ⟨106900882063825850425286957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71267254709217233616857971 106900882063825850425286957)
          ·
            refine ⟨40087830773934693909482609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106900882063825850425286957 40087830773934693909482609)
            ·
              refine ⟨30065873080451020432111957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40087830773934693909482609 30065873080451020432111957)
              ·
                refine ⟨88083612540383848922203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 30065873080451020432111957 88083612540383848922203)
                ·
                  rfl

theorem cell23_4631640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 10].length) (baseStart_4631640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631640 prefixEnd_4631640 := by exact prefixLift 4631640
  have htrace : WordTrace (prefixWord ++ tailWord_4631640) baseStart_4631640 baseEnd_4631640 := by
    simpa [prefixWord, tailWord_4631640, baseEnd_4631640] using wordTrace_append hprefix tailTrace_4631640
  have hstable : (prefixWord ++ tailWord_4631640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631640).length < 2 ^ (prefixWord ++ tailWord_4631640).sum := by decide
  have hdescent : baseEnd_4631640 < baseStart_4631640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631657 : List Nat := [1, 2, 1, 1, 1, 6, 4, 7]
def baseStart_4631657 : Nat := 118140960795 + 4631657 * 2 ^ 59
def prefixEnd_4631657 : Nat := 4983230072969 + 3 ^ 40 * 4631657 * 2
def baseEnd_4631657 : Nat := 88083935843018161273589

theorem tailTrace_4631657 : CollatzResearch.WordTrace tailWord_4631657 prefixEnd_4631657 88083935843018161273589 := by
  unfold tailWord_4631657
  simp only [CollatzResearch.WordTrace]
  refine ⟨168930408981305187884069225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112620272654203458589379483 168930408981305187884069225)
  ·
    refine ⟨126697806735978890913051919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168930408981305187884069225 126697806735978890913051919)
    ·
      refine ⟨190046710103968336369577879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126697806735978890913051919 190046710103968336369577879)
      ·
        refine ⟨285070065155952504554366819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190046710103968336369577879 285070065155952504554366819)
        ·
          refine ⟨427605097733928756831550229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285070065155952504554366819 427605097733928756831550229)
          ·
            refine ⟨20043988956277910476478917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 427605097733928756831550229 20043988956277910476478917)
            ·
              refine ⟨3758247929302108214339797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20043988956277910476478917 3758247929302108214339797)
              ·
                refine ⟨88083935843018161273589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3758247929302108214339797 88083935843018161273589)
                ·
                  rfl

theorem cell23_4631657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 4, 7].length) (baseStart_4631657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631657 prefixEnd_4631657 := by exact prefixLift 4631657
  have htrace : WordTrace (prefixWord ++ tailWord_4631657) baseStart_4631657 baseEnd_4631657 := by
    simpa [prefixWord, tailWord_4631657, baseEnd_4631657] using wordTrace_append hprefix tailTrace_4631657
  have hstable : (prefixWord ++ tailWord_4631657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631657).length < 2 ^ (prefixWord ++ tailWord_4631657).sum := by decide
  have hdescent : baseEnd_4631657 < baseStart_4631657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631685 : List Nat := [1, 3, 1, 1, 7, 1, 1, 1, 3, 2, 2]
def baseStart_4631685 : Nat := 118140960795 + 4631685 * 2 ^ 59
def prefixEnd_4631685 : Nat := 4983230072969 + 3 ^ 40 * 4631685 * 2
def baseEnd_4631685 : Nat := 2378280645219816244836775

theorem tailTrace_4631685 : CollatzResearch.WordTrace tailWord_4631685 prefixEnd_4631685 2378280645219816244836775 := by
  unfold tailWord_4631685
  simp only [CollatzResearch.WordTrace]
  refine ⟨168931430225203748666088509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112620953483469165777392339 168931430225203748666088509)
  ·
    refine ⟨63349286334451405749783191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168931430225203748666088509 63349286334451405749783191)
    ·
      refine ⟨95023929501677108624674787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63349286334451405749783191 95023929501677108624674787)
      ·
        refine ⟨142535894252515662937012181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95023929501677108624674787 142535894252515662937012181)
        ·
          refine ⟨3340685021543335850086223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 142535894252515662937012181 3340685021543335850086223)
          ·
            refine ⟨5011027532315003775129335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3340685021543335850086223 5011027532315003775129335)
            ·
              refine ⟨7516541298472505662694003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5011027532315003775129335 7516541298472505662694003)
              ·
                refine ⟨11274811947708758494041005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7516541298472505662694003 11274811947708758494041005)
                ·
                  refine ⟨4228054480390784435265377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11274811947708758494041005 4228054480390784435265377)
                  ·
                    refine ⟨3171040860293088326449033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4228054480390784435265377 3171040860293088326449033)
                    ·
                      refine ⟨2378280645219816244836775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3171040860293088326449033 2378280645219816244836775)
                      ·
                        rfl

theorem cell23_4631685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_4631685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631685 prefixEnd_4631685 := by exact prefixLift 4631685
  have htrace : WordTrace (prefixWord ++ tailWord_4631685) baseStart_4631685 baseEnd_4631685 := by
    simpa [prefixWord, tailWord_4631685, baseEnd_4631685] using wordTrace_append hprefix tailTrace_4631685
  have hstable : (prefixWord ++ tailWord_4631685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631685).length < 2 ^ (prefixWord ++ tailWord_4631685).sum := by decide
  have hdescent : baseEnd_4631685 < baseStart_4631685 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631727 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 5]
def baseStart_4631727 : Nat := 118140960795 + 4631727 * 2 ^ 59
def prefixEnd_4631727 : Nat := 4983230072969 + 3 ^ 40 * 4631727 * 2
def baseEnd_4631727 : Nat := 2378302211407305080511581

theorem tailTrace_4631727 : CollatzResearch.WordTrace tailWord_4631727 prefixEnd_4631727 2378302211407305080511581 := by
  unfold tailWord_4631727
  simp only [CollatzResearch.WordTrace]
  refine ⟨168932962091051589839117435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112621974727367726559411623 168932962091051589839117435)
  ·
    refine ⟨253399443136577384758676153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168932962091051589839117435 253399443136577384758676153)
    ·
      refine ⟨190049582352433038569007115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253399443136577384758676153 190049582352433038569007115)
      ·
        refine ⟨285074373528649557853510673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190049582352433038569007115 285074373528649557853510673)
        ·
          refine ⟨213805780146487168390133005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285074373528649557853510673 213805780146487168390133005)
          ·
            refine ⟨80177167554932688146299877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213805780146487168390133005 80177167554932688146299877)
            ·
              refine ⟨15033218916549879027431227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80177167554932688146299877 15033218916549879027431227)
              ·
                refine ⟨22549828374824818541146841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15033218916549879027431227 22549828374824818541146841)
                ·
                  refine ⟨16912371281118613905860131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22549828374824818541146841 16912371281118613905860131)
                  ·
                    refine ⟨25368556921677920858790197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16912371281118613905860131 25368556921677920858790197)
                    ·
                      refine ⟨2378302211407305080511581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25368556921677920858790197 2378302211407305080511581)
                      ·
                        rfl

theorem cell23_4631727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 1, 5].length) (baseStart_4631727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631727 prefixEnd_4631727 := by exact prefixLift 4631727
  have htrace : WordTrace (prefixWord ++ tailWord_4631727) baseStart_4631727 baseEnd_4631727 := by
    simpa [prefixWord, tailWord_4631727, baseEnd_4631727] using wordTrace_append hprefix tailTrace_4631727
  have hstable : (prefixWord ++ tailWord_4631727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631727).length < 2 ^ (prefixWord ++ tailWord_4631727).sum := by decide
  have hdescent : baseEnd_4631727 < baseStart_4631727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631741 : List Nat := [1, 4, 1, 2, 1, 1, 2, 3, 4, 2, 2]
def baseStart_4631741 : Nat := 118140960795 + 4631741 * 2 ^ 59
def prefixEnd_4631741 : Nat := 4983230072969 + 3 ^ 40 * 4631741 * 2
def baseEnd_4631741 : Nat := 2378309400136468025736517

theorem tailTrace_4631741 : CollatzResearch.WordTrace tailWord_4631741 prefixEnd_4631741 2378309400136468025736517 := by
  unfold tailWord_4631741
  simp only [CollatzResearch.WordTrace]
  refine ⟨168933472713000870230127077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112622315142000580153418051 168933472713000870230127077)
  ·
    refine ⟨31675026133687663168148827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168933472713000870230127077 31675026133687663168148827)
    ·
      refine ⟨47512539200531494752223241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31675026133687663168148827 47512539200531494752223241)
      ·
        refine ⟨35634404400398621064167431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47512539200531494752223241 35634404400398621064167431)
        ·
          refine ⟨53451606600597931596251147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35634404400398621064167431 53451606600597931596251147)
          ·
            refine ⟨80177409900896897394376721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53451606600597931596251147 80177409900896897394376721)
            ·
              refine ⟨60133057425672673045782541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80177409900896897394376721 60133057425672673045782541)
              ·
                refine ⟨22549896534627252392168453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60133057425672673045782541 22549896534627252392168453)
                ·
                  refine ⟨4228105600242609823531585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22549896534627252392168453 4228105600242609823531585)
                  ·
                    refine ⟨3171079200181957367648689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4228105600242609823531585 3171079200181957367648689)
                    ·
                      refine ⟨2378309400136468025736517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3171079200181957367648689 2378309400136468025736517)
                      ·
                        rfl

theorem cell23_4631741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_4631741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631741 prefixEnd_4631741 := by exact prefixLift 4631741
  have htrace : WordTrace (prefixWord ++ tailWord_4631741) baseStart_4631741 baseEnd_4631741 := by
    simpa [prefixWord, tailWord_4631741, baseEnd_4631741] using wordTrace_append hprefix tailTrace_4631741
  have hstable : (prefixWord ++ tailWord_4631741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631741).length < 2 ^ (prefixWord ++ tailWord_4631741).sum := by decide
  have hdescent : baseEnd_4631741 < baseStart_4631741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631754 : List Nat := [3, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4]
def baseStart_4631754 : Nat := 118140960795 + 4631754 * 2 ^ 59
def prefixEnd_4631754 : Nat := 4983230072969 + 3 ^ 40 * 4631754 * 2
def baseEnd_4631754 : Nat := 2378316075384976474873957

theorem tailTrace_4631754 : CollatzResearch.WordTrace tailWord_4631754 prefixEnd_4631754 2378316075384976474873957 := by
  unfold tailWord_4631754
  simp only [CollatzResearch.WordTrace]
  refine ⟨42233486715488443362587579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112622631241302515633566877 42233486715488443362587579)
  ·
    refine ⟨63350230073232665043881369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42233486715488443362587579 63350230073232665043881369)
    ·
      refine ⟨47512672554924498782911027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63350230073232665043881369 47512672554924498782911027)
      ·
        refine ⟨71269008832386748174366541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47512672554924498782911027 71269008832386748174366541)
        ·
          refine ⟨26725878312145030565387453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71269008832386748174366541 26725878312145030565387453)
          ·
            refine ⟨10022204367054386462020295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26725878312145030565387453 10022204367054386462020295)
            ·
              refine ⟨15033306550581579693030443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10022204367054386462020295 15033306550581579693030443)
              ·
                refine ⟨22549959825872369539545665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15033306550581579693030443 22549959825872369539545665)
                ·
                  refine ⟨16912469869404277154659249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22549959825872369539545665 16912469869404277154659249)
                  ·
                    refine ⟨12684352402053207865994437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16912469869404277154659249 12684352402053207865994437)
                    ·
                      refine ⟨2378316075384976474873957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12684352402053207865994437 2378316075384976474873957)
                      ·
                        rfl

theorem cell23_4631754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 1, 2, 2, 4].length) (baseStart_4631754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631754 prefixEnd_4631754 := by exact prefixLift 4631754
  have htrace : WordTrace (prefixWord ++ tailWord_4631754) baseStart_4631754 baseEnd_4631754 := by
    simpa [prefixWord, tailWord_4631754, baseEnd_4631754] using wordTrace_append hprefix tailTrace_4631754
  have hstable : (prefixWord ++ tailWord_4631754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631754).length < 2 ^ (prefixWord ++ tailWord_4631754).sum := by decide
  have hdescent : baseEnd_4631754 < baseStart_4631754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631758 : List Nat := [4, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2]
def baseStart_4631758 : Nat := 118140960795 + 4631758 * 2 ^ 59
def prefixEnd_4631758 : Nat := 4983230072969 + 3 ^ 40 * 4631758 * 2
def baseEnd_4631758 : Nat := 2378318129307594459223939

theorem tailTrace_4631758 : CollatzResearch.WordTrace tailWord_4631758 prefixEnd_4631758 2378318129307594459223939 := by
  unfold tailWord_4631758
  simp only [CollatzResearch.WordTrace]
  refine ⟨21116761594242410266686991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112622728502626188088997285 21116761594242410266686991)
  ·
    refine ⟨31675142391363615400030487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21116761594242410266686991 31675142391363615400030487)
    ·
      refine ⟨47512713587045423100045731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31675142391363615400030487 47512713587045423100045731)
      ·
        refine ⟨71269070380568134650068597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47512713587045423100045731 71269070380568134650068597)
        ·
          refine ⟨6681475348178262623443931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71269070380568134650068597 6681475348178262623443931)
          ·
            refine ⟨10022213022267393935165897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6681475348178262623443931 10022213022267393935165897)
            ·
              refine ⟨7516659766700545451374423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10022213022267393935165897 7516659766700545451374423)
              ·
                refine ⟨11274989650050818177061635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7516659766700545451374423 11274989650050818177061635)
                ·
                  refine ⟨16912484475076227265592453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11274989650050818177061635 16912484475076227265592453)
                  ·
                    refine ⟨3171090839076792612298585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16912484475076227265592453 3171090839076792612298585)
                    ·
                      refine ⟨2378318129307594459223939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3171090839076792612298585 2378318129307594459223939)
                      ·
                        rfl

theorem cell23_4631758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2].length) (baseStart_4631758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631758 prefixEnd_4631758 := by exact prefixLift 4631758
  have htrace : WordTrace (prefixWord ++ tailWord_4631758) baseStart_4631758 baseEnd_4631758 := by
    simpa [prefixWord, tailWord_4631758, baseEnd_4631758] using wordTrace_append hprefix tailTrace_4631758
  have hstable : (prefixWord ++ tailWord_4631758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631758).length < 2 ^ (prefixWord ++ tailWord_4631758).sum := by decide
  have hdescent : baseEnd_4631758 < baseStart_4631758 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631858 : List Nat := [3, 2, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_4631858 : Nat := 118140960795 + 4631858 * 2 ^ 59
def prefixEnd_4631858 : Nat := 4983230072969 + 3 ^ 40 * 4631858 * 2
def baseEnd_4631858 : Nat := 792789825791014689324493

theorem tailTrace_4631858 : CollatzResearch.WordTrace tailWord_4631858 prefixEnd_4631858 792789825791014689324493 := by
  unfold tailWord_4631858
  simp only [CollatzResearch.WordTrace]
  refine ⟨42234435013394249803034057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112625160035717999474757485 42234435013394249803034057)
  ·
    refine ⟨31675826260045687352275543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42234435013394249803034057 31675826260045687352275543)
    ·
      refine ⟨47513739390068531028413315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31675826260045687352275543 47513739390068531028413315)
      ·
        refine ⟨71270609085102796542619973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47513739390068531028413315 71270609085102796542619973)
        ·
          refine ⟨13363239203456774351741245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71270609085102796542619973 13363239203456774351741245)
          ·
            refine ⟨5011214701296290381902967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13363239203456774351741245 5011214701296290381902967)
            ·
              refine ⟨7516822051944435572854451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5011214701296290381902967 7516822051944435572854451)
              ·
                refine ⟨11275233077916653359281677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7516822051944435572854451 11275233077916653359281677)
                ·
                  refine ⟨4228212404218745009730629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11275233077916653359281677 4228212404218745009730629)
                  ·
                    refine ⟨792789825791014689324493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228212404218745009730629 792789825791014689324493)
                    ·
                      rfl

theorem cell23_4631858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_4631858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631858 prefixEnd_4631858 := by exact prefixLift 4631858
  have htrace : WordTrace (prefixWord ++ tailWord_4631858) baseStart_4631858 baseEnd_4631858 := by
    simpa [prefixWord, tailWord_4631858, baseEnd_4631858] using wordTrace_append hprefix tailTrace_4631858
  have hstable : (prefixWord ++ tailWord_4631858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631858).length < 2 ^ (prefixWord ++ tailWord_4631858).sum := by decide
  have hdescent : baseEnd_4631858 < baseStart_4631858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631871 : List Nat := [1, 1, 2, 2, 4, 2, 4, 1, 6]
def baseStart_4631871 : Nat := 118140960795 + 4631871 * 2 ^ 59
def prefixEnd_4631871 : Nat := 4983230072969 + 3 ^ 40 * 4631871 * 2
def baseEnd_4631871 : Nat := 264264016957950279678991

theorem tailTrace_4631871 : CollatzResearch.WordTrace tailWord_4631871 prefixEnd_4631871 264264016957950279678991 := by
  unfold tailWord_4631871
  simp only [CollatzResearch.WordTrace]
  refine ⟨168938214202529902432359467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112625476135019934954906311 168938214202529902432359467)
  ·
    refine ⟨253407321303794853648539201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168938214202529902432359467 253407321303794853648539201)
    ·
      refine ⟨190055490977846140236404401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253407321303794853648539201 190055490977846140236404401)
      ·
        refine ⟨142541618233384605177303301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190055490977846140236404401 142541618233384605177303301)
        ·
          refine ⟨26726553418759613470744369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142541618233384605177303301 26726553418759613470744369)
          ·
            refine ⟨20044915064069710103058277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26726553418759613470744369 20044915064069710103058277)
            ·
              refine ⟨3758421574513070644323427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20044915064069710103058277 3758421574513070644323427)
              ·
                refine ⟨5637632361769605966485141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3758421574513070644323427 5637632361769605966485141)
                ·
                  refine ⟨264264016957950279678991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5637632361769605966485141 264264016957950279678991)
                  ·
                    rfl

theorem cell23_4631871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 4, 1, 6].length) (baseStart_4631871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631871 prefixEnd_4631871 := by exact prefixLift 4631871
  have htrace : WordTrace (prefixWord ++ tailWord_4631871) baseStart_4631871 baseEnd_4631871 := by
    simpa [prefixWord, tailWord_4631871, baseEnd_4631871] using wordTrace_append hprefix tailTrace_4631871
  have hstable : (prefixWord ++ tailWord_4631871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631871).length < 2 ^ (prefixWord ++ tailWord_4631871).sum := by decide
  have hdescent : baseEnd_4631871 < baseStart_4631871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631881 : List Nat := [1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 3]
def baseStart_4631881 : Nat := 118140960795 + 4631881 * 2 ^ 59
def prefixEnd_4631881 : Nat := 4983230072969 + 3 ^ 40 * 4631881 * 2
def baseEnd_4631881 : Nat := 2378381287428097477985873

theorem tailTrace_4631881 : CollatzResearch.WordTrace tailWord_4631881 prefixEnd_4631881 2378381287428097477985873 := by
  unfold tailWord_4631881
  simp only [CollatzResearch.WordTrace]
  refine ⟨168938578932493674140223497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112625719288329116093482331 168938578932493674140223497)
  ·
    refine ⟨126703934199370255605167623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168938578932493674140223497 126703934199370255605167623)
    ·
      refine ⟨190055901299055383407751435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126703934199370255605167623 190055901299055383407751435)
      ·
        refine ⟨285083851948583075111627153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190055901299055383407751435 285083851948583075111627153)
        ·
          refine ⟨213812888961437306333720365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285083851948583075111627153 213812888961437306333720365)
          ·
            refine ⟨80179833360538989875145137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213812888961437306333720365 80179833360538989875145137)
            ·
              refine ⟨60134875020404242406358853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80179833360538989875145137 60134875020404242406358853)
              ·
                refine ⟨11275289066325795451192285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60134875020404242406358853 11275289066325795451192285)
                ·
                  refine ⟨4228233399872173294197107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11275289066325795451192285 4228233399872173294197107)
                  ·
                    refine ⟨6342350099808259941295661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4228233399872173294197107 6342350099808259941295661)
                    ·
                      refine ⟨2378381287428097477985873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6342350099808259941295661 2378381287428097477985873)
                      ·
                        rfl

theorem cell23_4631881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 4, 3, 1, 3].length) (baseStart_4631881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631881 prefixEnd_4631881 := by exact prefixLift 4631881
  have htrace : WordTrace (prefixWord ++ tailWord_4631881) baseStart_4631881 baseEnd_4631881 := by
    simpa [prefixWord, tailWord_4631881, baseEnd_4631881] using wordTrace_append hprefix tailTrace_4631881
  have hstable : (prefixWord ++ tailWord_4631881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631881).length < 2 ^ (prefixWord ++ tailWord_4631881).sum := by decide
  have hdescent : baseEnd_4631881 < baseStart_4631881 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631908 : List Nat := [2, 3, 1, 1, 3, 2, 2, 2, 2, 3, 2]
def baseStart_4631908 : Nat := 118140960795 + 4631908 * 2 ^ 59
def prefixEnd_4631908 : Nat := 4983230072969 + 3 ^ 40 * 4631908 * 2
def baseEnd_4631908 : Nat := 2378395151405768872348249

theorem tailTrace_4631908 : CollatzResearch.WordTrace tailWord_4631908 prefixEnd_4631908 2378395151405768872348249 := by
  unfold tailWord_4631908
  simp only [CollatzResearch.WordTrace]
  refine ⟨84469781851697928875728189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112626375802263905167637585 84469781851697928875728189)
  ·
    refine ⟨31676168194386723328398071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84469781851697928875728189 31676168194386723328398071)
    ·
      refine ⟨47514252291580084992597107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31676168194386723328398071 47514252291580084992597107)
      ·
        refine ⟨71271378437370127488895661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47514252291580084992597107 71271378437370127488895661)
        ·
          refine ⟨26726766914013797808335873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71271378437370127488895661 26726766914013797808335873)
          ·
            refine ⟨20045075185510348356251905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26726766914013797808335873 20045075185510348356251905)
            ·
              refine ⟨15033806389132761267188929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20045075185510348356251905 15033806389132761267188929)
              ·
                refine ⟨11275354791849570950391697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15033806389132761267188929 11275354791849570950391697)
                ·
                  refine ⟨8456516093887178212793773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11275354791849570950391697 8456516093887178212793773)
                  ·
                    refine ⟨3171193535207691829797665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8456516093887178212793773 3171193535207691829797665)
                    ·
                      refine ⟨2378395151405768872348249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3171193535207691829797665 2378395151405768872348249)
                      ·
                        rfl

theorem cell23_4631908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 2, 3, 2].length) (baseStart_4631908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631908 prefixEnd_4631908 := by exact prefixLift 4631908
  have htrace : WordTrace (prefixWord ++ tailWord_4631908) baseStart_4631908 baseEnd_4631908 := by
    simpa [prefixWord, tailWord_4631908, baseEnd_4631908] using wordTrace_append hprefix tailTrace_4631908
  have hstable : (prefixWord ++ tailWord_4631908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631908).length < 2 ^ (prefixWord ++ tailWord_4631908).sum := by decide
  have hdescent : baseEnd_4631908 < baseStart_4631908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631931 : List Nat := [1, 1, 1, 1, 1, 6, 1, 5, 2, 4]
def baseStart_4631931 : Nat := 118140960795 + 4631931 * 2 ^ 59
def prefixEnd_4631931 : Nat := 4983230072969 + 3 ^ 40 * 4631931 * 2
def baseEnd_4631931 : Nat := 792802320486940760786881

theorem tailTrace_4631931 : CollatzResearch.WordTrace tailWord_4631931 prefixEnd_4631931 792802320486940760786881 := by
  unfold tailWord_4631931
  simp only [CollatzResearch.WordTrace]
  refine ⟨168940402582312532679543647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112626935054875021786362431 168940402582312532679543647)
  ·
    refine ⟨253410603873468799019315471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168940402582312532679543647 253410603873468799019315471)
    ·
      refine ⟨380115905810203198528973207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253410603873468799019315471 380115905810203198528973207)
      ·
        refine ⟨570173858715304797793459811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380115905810203198528973207 570173858715304797793459811)
        ·
          refine ⟨855260788072957196690189717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570173858715304797793459811 855260788072957196690189717)
          ·
            refine ⟨40090349440919868594852643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 855260788072957196690189717 40090349440919868594852643)
            ·
              refine ⟨60135524161379802892278965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40090349440919868594852643 60135524161379802892278965)
              ·
                refine ⟨5637705390129356521151153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60135524161379802892278965 5637705390129356521151153)
                ·
                  refine ⟨4228279042597017390863365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5637705390129356521151153 4228279042597017390863365)
                  ·
                    refine ⟨792802320486940760786881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228279042597017390863365 792802320486940760786881)
                    ·
                      rfl

theorem cell23_4631931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 5, 2, 4].length) (baseStart_4631931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631931 prefixEnd_4631931 := by exact prefixLift 4631931
  have htrace : WordTrace (prefixWord ++ tailWord_4631931) baseStart_4631931 baseEnd_4631931 := by
    simpa [prefixWord, tailWord_4631931, baseEnd_4631931] using wordTrace_append hprefix tailTrace_4631931
  have hstable : (prefixWord ++ tailWord_4631931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631931).length < 2 ^ (prefixWord ++ tailWord_4631931).sum := by decide
  have hdescent : baseEnd_4631931 < baseStart_4631931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631941 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_4631941 : Nat := 118140960795 + 4631941 * 2 ^ 59
def prefixEnd_4631941 : Nat := 4983230072969 + 3 ^ 40 * 4631941 * 2
def baseEnd_4631941 : Nat := 2378412096267367243235597

theorem tailTrace_4631941 : CollatzResearch.WordTrace tailWord_4631941 prefixEnd_4631941 2378412096267367243235597 := by
  unfold tailWord_4631941
  simp only [CollatzResearch.WordTrace]
  refine ⟨168940767312276304387407677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112627178208184202924938451 168940767312276304387407677)
  ·
    refine ⟨63352787742103614145277879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168940767312276304387407677 63352787742103614145277879)
    ·
      refine ⟨95029181613155421217916819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63352787742103614145277879 95029181613155421217916819)
      ·
        refine ⟨142543772419733131826875229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95029181613155421217916819 142543772419733131826875229)
        ·
          refine ⟨53453914657399924435078211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142543772419733131826875229 53453914657399924435078211)
          ·
            refine ⟨80180871986099886652617317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53453914657399924435078211 80180871986099886652617317)
            ·
              refine ⟨15033913497393728747365747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80180871986099886652617317 15033913497393728747365747)
              ·
                refine ⟨22550870246090593121048621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15033913497393728747365747 22550870246090593121048621)
                ·
                  refine ⟨8456576342283972420393233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22550870246090593121048621 8456576342283972420393233)
                  ·
                    refine ⟨6342432256712979315294925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8456576342283972420393233 6342432256712979315294925)
                    ·
                      refine ⟨2378412096267367243235597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6342432256712979315294925 2378412096267367243235597)
                      ·
                        rfl

theorem cell23_4631941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_4631941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631941 prefixEnd_4631941 := by exact prefixLift 4631941
  have htrace : WordTrace (prefixWord ++ tailWord_4631941) baseStart_4631941 baseEnd_4631941 := by
    simpa [prefixWord, tailWord_4631941, baseEnd_4631941] using wordTrace_append hprefix tailTrace_4631941
  have hstable : (prefixWord ++ tailWord_4631941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631941).length < 2 ^ (prefixWord ++ tailWord_4631941).sum := by decide
  have hdescent : baseEnd_4631941 < baseStart_4631941 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4631965 : List Nat := [1, 4, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_4631965 : Nat := 118140960795 + 4631965 * 2 ^ 59
def prefixEnd_4631965 : Nat := 4983230072969 + 3 ^ 40 * 4631965 * 2
def baseEnd_4631965 : Nat := 792808139934358383111829

theorem tailTrace_4631965 : CollatzResearch.WordTrace tailWord_4631965 prefixEnd_4631965 792808139934358383111829 := by
  unfold tailWord_4631965
  simp only [CollatzResearch.WordTrace]
  refine ⟨168941642664189356486281349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112627761776126237657520899 168941642664189356486281349)
  ·
    refine ⟨31676557999535504341177753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168941642664189356486281349 31676557999535504341177753)
    ·
      refine ⟨23757418499651628255883315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31676557999535504341177753 23757418499651628255883315)
      ·
        refine ⟨35636127749477442383824973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23757418499651628255883315 35636127749477442383824973)
        ·
          refine ⟨13363547906054040893934365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35636127749477442383824973 13363547906054040893934365)
          ·
            refine ⟨5011330464770265335225387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13363547906054040893934365 5011330464770265335225387)
            ·
              refine ⟨7516995697155398002838081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5011330464770265335225387 7516995697155398002838081)
              ·
                refine ⟨5637746772866548502128561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7516995697155398002838081 5637746772866548502128561)
                ·
                  refine ⟨4228310079649911376596421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5637746772866548502128561 4228310079649911376596421)
                  ·
                    refine ⟨792808139934358383111829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228310079649911376596421 792808139934358383111829)
                    ·
                      rfl

theorem cell23_4631965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_4631965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4631965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4631965 prefixEnd_4631965 := by exact prefixLift 4631965
  have htrace : WordTrace (prefixWord ++ tailWord_4631965) baseStart_4631965 baseEnd_4631965 := by
    simpa [prefixWord, tailWord_4631965, baseEnd_4631965] using wordTrace_append hprefix tailTrace_4631965
  have hstable : (prefixWord ++ tailWord_4631965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4631965).length < 2 ^ (prefixWord ++ tailWord_4631965).sum := by decide
  have hdescent : baseEnd_4631965 < baseStart_4631965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4631965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632031 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 3]
def baseStart_4632031 : Nat := 118140960795 + 4632031 * 2 ^ 59
def prefixEnd_4632031 : Nat := 4983230072969 + 3 ^ 40 * 4632031 * 2
def baseEnd_4632031 : Nat := 2378458309526271891110183

theorem tailTrace_4632031 : CollatzResearch.WordTrace tailWord_4632031 prefixEnd_4632031 2378458309526271891110183 := by
  unfold tailWord_4632031
  simp only [CollatzResearch.WordTrace]
  refine ⟨168944049881950249758183947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112629366587966833172122631 168944049881950249758183947)
  ·
    refine ⟨253416074822925374637275921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168944049881950249758183947 253416074822925374637275921)
    ·
      refine ⟨190062056117194030977956941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253416074822925374637275921 190062056117194030977956941)
      ·
        refine ⟨71273271043947761616733853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190062056117194030977956941 71273271043947761616733853)
        ·
          refine ⟨26727476641480410606275195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71273271043947761616733853 26727476641480410606275195)
          ·
            refine ⟨40091214962220615909412793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26727476641480410606275195 40091214962220615909412793)
            ·
              refine ⟨30068411221665461932059595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40091214962220615909412793 30068411221665461932059595)
              ·
                refine ⟨45102616832498192898089393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30068411221665461932059595 45102616832498192898089393)
                ·
                  refine ⟨33826962624373644673567045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45102616832498192898089393 33826962624373644673567045)
                  ·
                    refine ⟨6342555492070058376293821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33826962624373644673567045 6342555492070058376293821)
                    ·
                      refine ⟨2378458309526271891110183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6342555492070058376293821 2378458309526271891110183)
                      ·
                        rfl

theorem cell23_4632031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 3].length) (baseStart_4632031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632031 prefixEnd_4632031 := by exact prefixLift 4632031
  have htrace : WordTrace (prefixWord ++ tailWord_4632031) baseStart_4632031 baseEnd_4632031 := by
    simpa [prefixWord, tailWord_4632031, baseEnd_4632031] using wordTrace_append hprefix tailTrace_4632031
  have hstable : (prefixWord ++ tailWord_4632031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632031).length < 2 ^ (prefixWord ++ tailWord_4632031).sum := by decide
  have hdescent : baseEnd_4632031 < baseStart_4632031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632081 : List Nat := [1, 2, 2, 1, 1, 2, 3, 4, 2, 5]
def baseStart_4632081 : Nat := 118140960795 + 4632081 * 2 ^ 59
def prefixEnd_4632081 : Nat := 4983230072969 + 3 ^ 40 * 4632081 * 2
def baseEnd_4632081 : Nat := 792827994519665565161651

theorem tailTrace_4632081 : CollatzResearch.WordTrace tailWord_4632081 prefixEnd_4632081 792827994519665565161651 := by
  unfold tailWord_4632081
  simp only [CollatzResearch.WordTrace]
  refine ⟨168945873531769108297504097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112630582354512738865002731 168945873531769108297504097)
  ·
    refine ⟨126709405148826831223128073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168945873531769108297504097 126709405148826831223128073)
    ·
      refine ⟨95032053861620123417346055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126709405148826831223128073 95032053861620123417346055)
      ·
        refine ⟨142548080792430185126019083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95032053861620123417346055 142548080792430185126019083)
        ·
          refine ⟨213822121188645277689028625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142548080792430185126019083 213822121188645277689028625)
          ·
            refine ⟨160366590891483958266771469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213822121188645277689028625 160366590891483958266771469)
            ·
              refine ⟨60137471584306484350039301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160366590891483958266771469 60137471584306484350039301)
              ·
                refine ⟨11275775922057465815632369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60137471584306484350039301 11275775922057465815632369)
                ·
                  refine ⟨8456831941543099361724277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11275775922057465815632369 8456831941543099361724277)
                  ·
                    refine ⟨792827994519665565161651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8456831941543099361724277 792827994519665565161651)
                    ·
                      rfl

theorem cell23_4632081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_4632081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632081 prefixEnd_4632081 := by exact prefixLift 4632081
  have htrace : WordTrace (prefixWord ++ tailWord_4632081) baseStart_4632081 baseEnd_4632081 := by
    simpa [prefixWord, tailWord_4632081, baseEnd_4632081] using wordTrace_append hprefix tailTrace_4632081
  have hstable : (prefixWord ++ tailWord_4632081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632081).length < 2 ^ (prefixWord ++ tailWord_4632081).sum := by decide
  have hdescent : baseEnd_4632081 < baseStart_4632081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632085 : List Nat := [1, 3, 2, 1, 3, 2, 4, 2, 5]
def baseStart_4632085 : Nat := 118140960795 + 4632085 * 2 ^ 59
def prefixEnd_4632085 : Nat := 4983230072969 + 3 ^ 40 * 4632085 * 2
def baseEnd_4632085 : Nat := 264276226386846075537215

theorem tailTrace_4632085 : CollatzResearch.WordTrace tailWord_4632085 prefixEnd_4632085 264276226386846075537215 := by
  unfold tailWord_4632085
  simp only [CollatzResearch.WordTrace]
  refine ⟨168946019423754616980649709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112630679615836411320433139 168946019423754616980649709)
  ·
    refine ⟨63354757283907981367743641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168946019423754616980649709 63354757283907981367743641)
    ·
      refine ⟨47516067962930986025807731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63354757283907981367743641 47516067962930986025807731)
      ·
        refine ⟨71274101944396479038711597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47516067962930986025807731 71274101944396479038711597)
        ·
          refine ⟨26727788229148679639516849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71274101944396479038711597 26727788229148679639516849)
          ·
            refine ⟨20045841171861509729637637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26727788229148679639516849 20045841171861509729637637)
            ·
              refine ⟨3758595219724033074307057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20045841171861509729637637 3758595219724033074307057)
              ·
                refine ⟨2818946414793024805730293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3758595219724033074307057 2818946414793024805730293)
                ·
                  refine ⟨264276226386846075537215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2818946414793024805730293 264276226386846075537215)
                  ·
                    rfl

theorem cell23_4632085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_4632085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632085 prefixEnd_4632085 := by exact prefixLift 4632085
  have htrace : WordTrace (prefixWord ++ tailWord_4632085) baseStart_4632085 baseEnd_4632085 := by
    simpa [prefixWord, tailWord_4632085, baseEnd_4632085] using wordTrace_append hprefix tailTrace_4632085
  have hstable : (prefixWord ++ tailWord_4632085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632085).length < 2 ^ (prefixWord ++ tailWord_4632085).sum := by decide
  have hdescent : baseEnd_4632085 < baseStart_4632085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632101 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_4632101 : Nat := 118140960795 + 4632101 * 2 ^ 59
def prefixEnd_4632101 : Nat := 4983230072969 + 3 ^ 40 * 4632101 * 2
def baseEnd_4632101 : Nat := 2378494253172086617234861

theorem tailTrace_4632101 : CollatzResearch.WordTrace tailWord_4632101 prefixEnd_4632101 2378494253172086617234861 := by
  unfold tailWord_4632101
  simp only [CollatzResearch.WordTrace]
  refine ⟨168946602991696651713232157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112631068661131101142154771 168946602991696651713232157)
  ·
    refine ⟨63354976121886244392462059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168946602991696651713232157 63354976121886244392462059)
    ·
      refine ⟨95032464182829366588693089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63354976121886244392462059 95032464182829366588693089)
      ·
        refine ⟨71274348137122024941519817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95032464182829366588693089 71274348137122024941519817)
        ·
          refine ⟨53455761102841518706139863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71274348137122024941519817 53455761102841518706139863)
          ·
            refine ⟨80183641654262278059209795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53455761102841518706139863 80183641654262278059209795)
            ·
              refine ⟨120275462481393417088814693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80183641654262278059209795 120275462481393417088814693)
              ·
                refine ⟨22551649215261265704152755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120275462481393417088814693 22551649215261265704152755)
                ·
                  refine ⟨33827473822891898556229133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22551649215261265704152755 33827473822891898556229133)
                  ·
                    refine ⟨12685302683584461958585925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33827473822891898556229133 12685302683584461958585925)
                    ·
                      refine ⟨2378494253172086617234861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12685302683584461958585925 2378494253172086617234861)
                      ·
                        rfl

theorem cell23_4632101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_4632101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632101 prefixEnd_4632101 := by exact prefixLift 4632101
  have htrace : WordTrace (prefixWord ++ tailWord_4632101) baseStart_4632101 baseEnd_4632101 := by
    simpa [prefixWord, tailWord_4632101, baseEnd_4632101] using wordTrace_append hprefix tailTrace_4632101
  have hstable : (prefixWord ++ tailWord_4632101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632101).length < 2 ^ (prefixWord ++ tailWord_4632101).sum := by decide
  have hdescent : baseEnd_4632101 < baseStart_4632101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632138 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3]
def baseStart_4632138 : Nat := 118140960795 + 4632138 * 2 ^ 59
def prefixEnd_4632138 : Nat := 4983230072969 + 3 ^ 40 * 4632138 * 2
def baseEnd_4632138 : Nat := 2378513251956302972472191

theorem tailTrace_4632138 : CollatzResearch.WordTrace tailWord_4632138 prefixEnd_4632138 2378513251956302972472191 := by
  unfold tailWord_4632138
  simp only [CollatzResearch.WordTrace]
  refine ⟨42236988123140651758082267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112631968328375071354886045 42236988123140651758082267)
  ·
    refine ⟨63355482184710977637123401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42236988123140651758082267 63355482184710977637123401)
    ·
      refine ⟨47516611638533233227842551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63355482184710977637123401 47516611638533233227842551)
      ·
        refine ⟨71274917457799849841763827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47516611638533233227842551 71274917457799849841763827)
        ·
          refine ⟨106912376186699774762645741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71274917457799849841763827 106912376186699774762645741)
          ·
            refine ⟨40092141070012415535992153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106912376186699774762645741 40092141070012415535992153)
            ·
              refine ⟨30069105802509311651994115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40092141070012415535992153 30069105802509311651994115)
              ·
                refine ⟨45103658703763967477991173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30069105802509311651994115 45103658703763967477991173)
                ·
                  refine ⟨8456936006955743902123345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45103658703763967477991173 8456936006955743902123345)
                  ·
                    refine ⟨6342702005216807926592509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8456936006955743902123345 6342702005216807926592509)
                    ·
                      refine ⟨2378513251956302972472191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6342702005216807926592509 2378513251956302972472191)
                      ·
                        rfl

theorem cell23_4632138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_4632138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632138 prefixEnd_4632138 := by exact prefixLift 4632138
  have htrace : WordTrace (prefixWord ++ tailWord_4632138) baseStart_4632138 baseEnd_4632138 := by
    simpa [prefixWord, tailWord_4632138, baseEnd_4632138] using wordTrace_append hprefix tailTrace_4632138
  have hstable : (prefixWord ++ tailWord_4632138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632138).length < 2 ^ (prefixWord ++ tailWord_4632138).sum := by decide
  have hdescent : baseEnd_4632138 < baseStart_4632138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632145 : List Nat := [1, 2, 2, 1, 3, 2, 1, 6, 1, 4]
def baseStart_4632145 : Nat := 118140960795 + 4632145 * 2 ^ 59
def prefixEnd_4632145 : Nat := 4983230072969 + 3 ^ 40 * 4632145 * 2
def baseEnd_4632145 : Nat := 792838948773628148361553

theorem tailTrace_4632145 : CollatzResearch.WordTrace tailWord_4632145 prefixEnd_4632145 792838948773628148361553 := by
  unfold tailWord_4632145
  simp only [CollatzResearch.WordTrace]
  refine ⟨168948207803537247227833889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112632138535691498151889259 168948207803537247227833889)
  ·
    refine ⟨126711155852652935420875417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168948207803537247227833889 126711155852652935420875417)
    ·
      refine ⟨95033366889489701565656563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126711155852652935420875417 95033366889489701565656563)
      ·
        refine ⟨142550050334234552348484845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95033366889489701565656563 142550050334234552348484845)
        ·
          refine ⟨53456268875337957130681817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142550050334234552348484845 53456268875337957130681817)
          ·
            refine ⟨40092201656503467848011363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53456268875337957130681817 40092201656503467848011363)
            ·
              refine ⟨60138302484755201772017045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40092201656503467848011363 60138302484755201772017045)
              ·
                refine ⟨2818982928972900083063299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60138302484755201772017045 2818982928972900083063299)
                ·
                  refine ⟨4228474393459350124594949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2818982928972900083063299 4228474393459350124594949)
                  ·
                    refine ⟨792838948773628148361553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228474393459350124594949 792838948773628148361553)
                    ·
                      rfl

theorem cell23_4632145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_4632145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632145 prefixEnd_4632145 := by exact prefixLift 4632145
  have htrace : WordTrace (prefixWord ++ tailWord_4632145) baseStart_4632145 baseEnd_4632145 := by
    simpa [prefixWord, tailWord_4632145, baseEnd_4632145] using wordTrace_append hprefix tailTrace_4632145
  have hstable : (prefixWord ++ tailWord_4632145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632145).length < 2 ^ (prefixWord ++ tailWord_4632145).sum := by decide
  have hdescent : baseEnd_4632145 < baseStart_4632145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632161 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 6]
def baseStart_4632161 : Nat := 118140960795 + 4632161 * 2 ^ 59
def prefixEnd_4632161 : Nat := 4983230072969 + 3 ^ 40 * 4632161 * 2
def baseEnd_4632161 : Nat := 2378525062011356382484585

theorem tailTrace_4632161 : CollatzResearch.WordTrace tailWord_4632161 prefixEnd_4632161 2378525062011356382484585 := by
  unfold tailWord_4632161
  simp only [CollatzResearch.WordTrace]
  refine ⟨168948791371479281960416337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112632527580986187973610891 168948791371479281960416337)
  ·
    refine ⟨126711593528609461470312253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168948791371479281960416337 126711593528609461470312253)
    ·
      refine ⟨47516847573228548051367095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126711593528609461470312253 47516847573228548051367095)
      ·
        refine ⟨71275271359842822077050643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47516847573228548051367095 71275271359842822077050643)
        ·
          refine ⟨106912907039764233115575965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71275271359842822077050643 106912907039764233115575965)
          ·
            refine ⟨40092340139911587418340987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106912907039764233115575965 40092340139911587418340987)
            ·
              refine ⟨60138510209867381127511481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40092340139911587418340987 60138510209867381127511481)
              ·
                refine ⟨45103882657400535845633611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60138510209867381127511481 45103882657400535845633611)
                ·
                  refine ⟨67655823986100803768450417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45103882657400535845633611 67655823986100803768450417)
                  ·
                    refine ⟨50741867989575602826337813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67655823986100803768450417 50741867989575602826337813)
                    ·
                      refine ⟨2378525062011356382484585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50741867989575602826337813 2378525062011356382484585)
                      ·
                        rfl

theorem cell23_4632161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 2, 6].length) (baseStart_4632161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632161 prefixEnd_4632161 := by exact prefixLift 4632161
  have htrace : WordTrace (prefixWord ++ tailWord_4632161) baseStart_4632161 baseEnd_4632161 := by
    simpa [prefixWord, tailWord_4632161, baseEnd_4632161] using wordTrace_append hprefix tailTrace_4632161
  have hstable : (prefixWord ++ tailWord_4632161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632161).length < 2 ^ (prefixWord ++ tailWord_4632161).sum := by decide
  have hdescent : baseEnd_4632161 < baseStart_4632161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632171 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 7, 5]
def baseStart_4632171 : Nat := 118140960795 + 4632171 * 2 ^ 59
def prefixEnd_4632171 : Nat := 4983230072969 + 3 ^ 40 * 4632171 * 2
def baseEnd_4632171 : Nat := 792843398939300447786513

theorem tailTrace_4632171 : CollatzResearch.WordTrace tailWord_4632171 prefixEnd_4632171 792843398939300447786513 := by
  unfold tailWord_4632171
  simp only [CollatzResearch.WordTrace]
  refine ⟨168949156101443053668280367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112632770734295369112186911 168949156101443053668280367)
  ·
    refine ⟨253423734152164580502420551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168949156101443053668280367 253423734152164580502420551)
    ·
      refine ⟨380135601228246870753630827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253423734152164580502420551 380135601228246870753630827)
      ·
        refine ⟨570203401842370306130446241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380135601228246870753630827 570203401842370306130446241)
        ·
          refine ⟨427652551381777729597834681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570203401842370306130446241 427652551381777729597834681)
          ·
            refine ⟨320739413536333297198376011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427652551381777729597834681 320739413536333297198376011)
            ·
              refine ⟨481109120304499945797564017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320739413536333297198376011 481109120304499945797564017)
              ·
                refine ⟨360831840228374959348173013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481109120304499945797564017 360831840228374959348173013)
                ·
                  refine ⟨8456996255352538109722805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 360831840228374959348173013 8456996255352538109722805)
                  ·
                    refine ⟨792843398939300447786513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8456996255352538109722805 792843398939300447786513)
                    ·
                      rfl

theorem cell23_4632171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 7, 5].length) (baseStart_4632171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632171 prefixEnd_4632171 := by exact prefixLift 4632171
  have htrace : WordTrace (prefixWord ++ tailWord_4632171) baseStart_4632171 baseEnd_4632171 := by
    simpa [prefixWord, tailWord_4632171, baseEnd_4632171] using wordTrace_append hprefix tailTrace_4632171
  have hstable : (prefixWord ++ tailWord_4632171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632171).length < 2 ^ (prefixWord ++ tailWord_4632171).sum := by decide
  have hdescent : baseEnd_4632171 < baseStart_4632171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632191 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 4]
def baseStart_4632191 : Nat := 118140960795 + 4632191 * 2 ^ 59
def prefixEnd_4632191 : Nat := 4983230072969 + 3 ^ 40 * 4632191 * 2
def baseEnd_4632191 : Nat := 2378540466430991265109447

theorem tailTrace_4632191 : CollatzResearch.WordTrace tailWord_4632191 prefixEnd_4632191 2378540466430991265109447 := by
  unfold tailWord_4632191
  simp only [CollatzResearch.WordTrace]
  refine ⟨168949885561370597084008427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112633257040913731389338951 168949885561370597084008427)
  ·
    refine ⟨253424828342055895626012641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168949885561370597084008427 253424828342055895626012641)
    ·
      refine ⟨190068621256541921719509481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253424828342055895626012641 190068621256541921719509481)
      ·
        refine ⟨142551465942406441289632111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190068621256541921719509481 142551465942406441289632111)
        ·
          refine ⟨213827198913609661934448167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142551465942406441289632111 213827198913609661934448167)
          ·
            refine ⟨320740798370414492901672251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213827198913609661934448167 320740798370414492901672251)
            ·
              refine ⟨481111197555621739352508377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320740798370414492901672251 481111197555621739352508377)
              ·
                refine ⟨360833398166716304514381283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481111197555621739352508377 360833398166716304514381283)
                ·
                  refine ⟨541250097250074456771571925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360833398166716304514381283 541250097250074456771571925)
                  ·
                    refine ⟨12685549154298620080583717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 541250097250074456771571925 12685549154298620080583717)
                    ·
                      refine ⟨2378540466430991265109447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12685549154298620080583717 2378540466430991265109447)
                      ·
                        rfl

theorem cell23_4632191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_4632191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632191 prefixEnd_4632191 := by exact prefixLift 4632191
  have htrace : WordTrace (prefixWord ++ tailWord_4632191) baseStart_4632191 baseEnd_4632191 := by
    simpa [prefixWord, tailWord_4632191, baseEnd_4632191] using wordTrace_append hprefix tailTrace_4632191
  have hstable : (prefixWord ++ tailWord_4632191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632191).length < 2 ^ (prefixWord ++ tailWord_4632191).sum := by decide
  have hdescent : baseEnd_4632191 < baseStart_4632191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632202 : List Nat := [3, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3]
def baseStart_4632202 : Nat := 118140960795 + 4632202 * 2 ^ 59
def prefixEnd_4632202 : Nat := 4983230072969 + 3 ^ 40 * 4632202 * 2
def baseEnd_4632202 : Nat := 2378546114718190722071897

theorem tailTrace_4632202 : CollatzResearch.WordTrace tailWord_4632202 prefixEnd_4632202 2378546114718190722071897 := by
  unfold tailWord_4632202
  simp only [CollatzResearch.WordTrace]
  refine ⟨42237571691082686490664715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112633524509553830641772573 42237571691082686490664715)
  ·
    refine ⟨63356357536624029735997073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42237571691082686490664715 63356357536624029735997073)
    ·
      refine ⟨47517268152468022301997805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63356357536624029735997073 47517268152468022301997805)
      ·
        refine ⟨17818975557175508363249177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47517268152468022301997805 17818975557175508363249177)
        ·
          refine ⟨13364231667881631272436883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17818975557175508363249177 13364231667881631272436883)
          ·
            refine ⟨20046347501822446908655325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13364231667881631272436883 20046347501822446908655325)
            ·
              refine ⟨7517380313183417590745747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20046347501822446908655325 7517380313183417590745747)
              ·
                refine ⟨11276070469775126386118621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7517380313183417590745747 11276070469775126386118621)
                ·
                  refine ⟨4228526426165672394794483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11276070469775126386118621 4228526426165672394794483)
                  ·
                    refine ⟨6342789639248508592191725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4228526426165672394794483 6342789639248508592191725)
                    ·
                      refine ⟨2378546114718190722071897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6342789639248508592191725 2378546114718190722071897)
                      ·
                        rfl

theorem cell23_4632202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_4632202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632202 prefixEnd_4632202 := by exact prefixLift 4632202
  have htrace : WordTrace (prefixWord ++ tailWord_4632202) baseStart_4632202 baseEnd_4632202 := by
    simpa [prefixWord, tailWord_4632202, baseEnd_4632202] using wordTrace_append hprefix tailTrace_4632202
  have hstable : (prefixWord ++ tailWord_4632202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632202).length < 2 ^ (prefixWord ++ tailWord_4632202).sum := by decide
  have hdescent : baseEnd_4632202 < baseStart_4632202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632222 : List Nat := [4, 3, 1, 1, 1, 2, 3, 2, 1, 5]
def baseStart_4632222 : Nat := 118140960795 + 4632222 * 2 ^ 59
def prefixEnd_4632222 : Nat := 4983230072969 + 3 ^ 40 * 4632222 * 2
def baseEnd_4632222 : Nat := 792852128110426881273935

theorem tailTrace_4632222 : CollatzResearch.WordTrace tailWord_4632222 prefixEnd_4632222 792852128110426881273935 := by
  unfold tailWord_4632222
  simp only [CollatzResearch.WordTrace]
  refine ⟨21118877028032286172298365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112634010816172192918924613 21118877028032286172298365)
  ·
    refine ⟨7919578885512107314611887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21118877028032286172298365 7919578885512107314611887)
    ·
      refine ⟨11879368328268160971917831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7919578885512107314611887 11879368328268160971917831)
      ·
        refine ⟨17819052492402241457876747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11879368328268160971917831 17819052492402241457876747)
        ·
          refine ⟨26728578738603362186815121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17819052492402241457876747 26728578738603362186815121)
          ·
            refine ⟨20046434053952521640111341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26728578738603362186815121 20046434053952521640111341)
            ·
              refine ⟨7517412770232195615041753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20046434053952521640111341 7517412770232195615041753)
              ·
                refine ⟨5638059577674146711281315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7517412770232195615041753 5638059577674146711281315)
                ·
                  refine ⟨8457089366511220066921973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5638059577674146711281315 8457089366511220066921973)
                  ·
                    refine ⟨792852128110426881273935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8457089366511220066921973 792852128110426881273935)
                    ·
                      rfl

theorem cell23_4632222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_4632222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632222 prefixEnd_4632222 := by exact prefixLift 4632222
  have htrace : WordTrace (prefixWord ++ tailWord_4632222) baseStart_4632222 baseEnd_4632222 := by
    simpa [prefixWord, tailWord_4632222, baseEnd_4632222] using wordTrace_append hprefix tailTrace_4632222
  have hstable : (prefixWord ++ tailWord_4632222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632222).length < 2 ^ (prefixWord ++ tailWord_4632222).sum := by decide
  have hdescent : baseEnd_4632222 < baseStart_4632222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632225 : List Nat := [1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 4]
def baseStart_4632225 : Nat := 118140960795 + 4632225 * 2 ^ 59
def prefixEnd_4632225 : Nat := 4983230072969 + 3 ^ 40 * 4632225 * 2
def baseEnd_4632225 : Nat := 2378557924773244132084291

theorem tailTrace_4632225 : CollatzResearch.WordTrace tailWord_4632225 prefixEnd_4632225 2378557924773244132084291 := by
  unfold tailWord_4632225
  simp only [CollatzResearch.WordTrace]
  refine ⟨168951125643247420890746129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112634083762164947260497419 168951125643247420890746129)
  ·
    refine ⟨126713344232435565668059597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168951125643247420890746129 126713344232435565668059597)
    ·
      refine ⟨47517504087163337125522349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126713344232435565668059597 47517504087163337125522349)
      ·
        refine ⟨17819064032686251422070881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47517504087163337125522349 17819064032686251422070881)
        ·
          refine ⟨13364298024514688566553161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17819064032686251422070881 13364298024514688566553161)
          ·
            refine ⟨10023223518386016424914871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13364298024514688566553161 10023223518386016424914871)
            ·
              refine ⟨15034835277579024637372307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10023223518386016424914871 15034835277579024637372307)
              ·
                refine ⟨22552252916368536956058461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15034835277579024637372307 22552252916368536956058461)
                ·
                  refine ⟨8457094843638201358521923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22552252916368536956058461 8457094843638201358521923)
                  ·
                    refine ⟨12685642265457302037782885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8457094843638201358521923 12685642265457302037782885)
                    ·
                      refine ⟨2378557924773244132084291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12685642265457302037782885 2378557924773244132084291)
                      ·
                        rfl

theorem cell23_4632225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_4632225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632225 prefixEnd_4632225 := by exact prefixLift 4632225
  have htrace : WordTrace (prefixWord ++ tailWord_4632225) baseStart_4632225 baseEnd_4632225 := by
    simpa [prefixWord, tailWord_4632225, baseEnd_4632225] using wordTrace_append hprefix tailTrace_4632225
  have hstable : (prefixWord ++ tailWord_4632225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632225).length < 2 ^ (prefixWord ++ tailWord_4632225).sum := by decide
  have hdescent : baseEnd_4632225 < baseStart_4632225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632252 : List Nat := [2, 2, 2, 3, 1, 3, 2, 2, 2, 4]
def baseStart_4632252 : Nat := 118140960795 + 4632252 * 2 ^ 59
def prefixEnd_4632252 : Nat := 4983230072969 + 3 ^ 40 * 4632252 * 2
def baseEnd_4632252 : Nat := 792857262916971842148889

theorem tailTrace_4632252 : CollatzResearch.WordTrace tailWord_4632252 prefixEnd_4632252 792857262916971842148889 := by
  unfold tailWord_4632252
  simp only [CollatzResearch.WordTrace]
  refine ⟨84476055207074802250989505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112634740276099736334652673 84476055207074802250989505)
  ·
    refine ⟨63357041405306101688242129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84476055207074802250989505 63357041405306101688242129)
    ·
      refine ⟨47517781053979576266181597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63357041405306101688242129 47517781053979576266181597)
      ·
        refine ⟨17819167895242341099818099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47517781053979576266181597 17819167895242341099818099)
        ·
          refine ⟨26728751842863511649727149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17819167895242341099818099 26728751842863511649727149)
          ·
            refine ⟨10023281941073816868647681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26728751842863511649727149 10023281941073816868647681)
            ·
              refine ⟨7517461455805362651485761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10023281941073816868647681 7517461455805362651485761)
              ·
                refine ⟨5638096091854021988614321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7517461455805362651485761 5638096091854021988614321)
                ·
                  refine ⟨4228572068890516491460741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5638096091854021988614321 4228572068890516491460741)
                  ·
                    refine ⟨792857262916971842148889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228572068890516491460741 792857262916971842148889)
                    ·
                      rfl

theorem cell23_4632252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_4632252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632252 prefixEnd_4632252 := by exact prefixLift 4632252
  have htrace : WordTrace (prefixWord ++ tailWord_4632252) baseStart_4632252 baseEnd_4632252 := by
    simpa [prefixWord, tailWord_4632252, baseEnd_4632252] using wordTrace_append hprefix tailTrace_4632252
  have hstable : (prefixWord ++ tailWord_4632252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632252).length < 2 ^ (prefixWord ++ tailWord_4632252).sum := by decide
  have hdescent : baseEnd_4632252 < baseStart_4632252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632269 : List Nat := [1, 6, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_4632269 : Nat := 118140960795 + 4632269 * 2 ^ 59
def prefixEnd_4632269 : Nat := 4983230072969 + 3 ^ 40 * 4632269 * 2
def baseEnd_4632269 : Nat := 792860172640680653311363

theorem tailTrace_4632269 : CollatzResearch.WordTrace tailWord_4632269 prefixEnd_4632269 792860172640680653311363 := by
  unfold tailWord_4632269
  simp only [CollatzResearch.WordTrace]
  refine ⟨168952730455088016405347861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112635153636725344270231907 168952730455088016405347861)
  ·
    refine ⟨7919659240082250769000681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 168952730455088016405347861 7919659240082250769000681)
    ·
      refine ⟨5939744430061688076750511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7919659240082250769000681 5939744430061688076750511)
      ·
        refine ⟨8909616645092532115125767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5939744430061688076750511 8909616645092532115125767)
        ·
          refine ⟨13364424967638798172688651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8909616645092532115125767 13364424967638798172688651)
          ·
            refine ⟨20046637451458197259032977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13364424967638798172688651 20046637451458197259032977)
            ·
              refine ⟨15034978088593647944274733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20046637451458197259032977 15034978088593647944274733)
              ·
                refine ⟨5638116783222617979103025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15034978088593647944274733 5638116783222617979103025)
                ·
                  refine ⟨4228587587416963484327269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5638116783222617979103025 4228587587416963484327269)
                  ·
                    refine ⟨792860172640680653311363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228587587416963484327269 792860172640680653311363)
                    ·
                      rfl

theorem cell23_4632269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_4632269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632269 prefixEnd_4632269 := by exact prefixLift 4632269
  have htrace : WordTrace (prefixWord ++ tailWord_4632269) baseStart_4632269 baseEnd_4632269 := by
    simpa [prefixWord, tailWord_4632269, baseEnd_4632269] using wordTrace_append hprefix tailTrace_4632269
  have hstable : (prefixWord ++ tailWord_4632269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632269).length < 2 ^ (prefixWord ++ tailWord_4632269).sum := by decide
  have hdescent : baseEnd_4632269 < baseStart_4632269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632332 : List Nat := [2, 2, 1, 2, 2, 1, 5, 1, 1, 4, 2]
def baseStart_4632332 : Nat := 118140960795 + 4632332 * 2 ^ 59
def prefixEnd_4632332 : Nat := 4983230072969 + 3 ^ 40 * 4632332 * 2
def baseEnd_4632332 : Nat := 2378612867203275213446299

theorem tailTrace_4632332 : CollatzResearch.WordTrace tailWord_4632332 prefixEnd_4632332 2378612867203275213446299 := by
  unfold tailWord_4632332
  simp only [CollatzResearch.WordTrace]
  refine ⟨84477514126929889082445625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112636685502573185443260833 84477514126929889082445625)
  ·
    refine ⟨63358135595197416811834219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84477514126929889082445625 63358135595197416811834219)
    ·
      refine ⟨95037203392796125217751329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63358135595197416811834219 95037203392796125217751329)
      ·
        refine ⟨71277902544597093913313497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95037203392796125217751329 71277902544597093913313497)
        ·
          refine ⟨53458426908447820434985123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71277902544597093913313497 53458426908447820434985123)
          ·
            refine ⟨80187640362671730652477685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53458426908447820434985123 80187640362671730652477685)
            ·
              refine ⟨7517591284000474748669783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80187640362671730652477685 7517591284000474748669783)
              ·
                refine ⟨11276386926000712123004675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7517591284000474748669783 11276386926000712123004675)
                ·
                  refine ⟨16914580389001068184507013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11276386926000712123004675 16914580389001068184507013)
                  ·
                    refine ⟨3171483822937700284595065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16914580389001068184507013 3171483822937700284595065)
                    ·
                      refine ⟨2378612867203275213446299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3171483822937700284595065 2378612867203275213446299)
                      ·
                        rfl

theorem cell23_4632332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_4632332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632332 prefixEnd_4632332 := by exact prefixLift 4632332
  have htrace : WordTrace (prefixWord ++ tailWord_4632332) baseStart_4632332 baseEnd_4632332 := by
    simpa [prefixWord, tailWord_4632332, baseEnd_4632332] using wordTrace_append hprefix tailTrace_4632332
  have hstable : (prefixWord ++ tailWord_4632332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632332).length < 2 ^ (prefixWord ++ tailWord_4632332).sum := by decide
  have hdescent : baseEnd_4632332 < baseStart_4632332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632333 : List Nat := [1, 7, 2, 1, 1, 2, 2, 7]
def baseStart_4632333 : Nat := 118140960795 + 4632333 * 2 ^ 59
def prefixEnd_4632333 : Nat := 4983230072969 + 3 ^ 40 * 4632333 * 2
def baseEnd_4632333 : Nat := 88096791877182581834585

theorem tailTrace_4632333 : CollatzResearch.WordTrace tailWord_4632333 prefixEnd_4632333 88096791877182581834585 := by
  unfold tailWord_4632333
  simp only [CollatzResearch.WordTrace]
  refine ⟨168955064726856155335677653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112636709817904103557118435 168955064726856155335677653)
  ·
    refine ⟨3959884329535691140679945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 168955064726856155335677653 3959884329535691140679945)
    ·
      refine ⟨2969913247151768355509959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3959884329535691140679945 2969913247151768355509959)
      ·
        refine ⟨4454869870727652533264939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2969913247151768355509959 4454869870727652533264939)
        ·
          refine ⟨6682304806091478799897409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4454869870727652533264939 6682304806091478799897409)
          ·
            refine ⟨5011728604568609099923057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6682304806091478799897409 5011728604568609099923057)
            ·
              refine ⟨3758796453426456824942293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5011728604568609099923057 3758796453426456824942293)
              ·
                refine ⟨88096791877182581834585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3758796453426456824942293 88096791877182581834585)
                ·
                  rfl

theorem cell23_4632333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 2, 7].length) (baseStart_4632333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632333 prefixEnd_4632333 := by exact prefixLift 4632333
  have htrace : WordTrace (prefixWord ++ tailWord_4632333) baseStart_4632333 baseEnd_4632333 := by
    simpa [prefixWord, tailWord_4632333, baseEnd_4632333] using wordTrace_append hprefix tailTrace_4632333
  have hstable : (prefixWord ++ tailWord_4632333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632333).length < 2 ^ (prefixWord ++ tailWord_4632333).sum := by decide
  have hdescent : baseEnd_4632333 < baseStart_4632333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632372 : List Nat := [2, 5, 1, 1, 2, 1, 3, 1, 7]
def baseStart_4632372 : Nat := 118140960795 + 4632372 * 2 ^ 59
def prefixEnd_4632372 : Nat := 4983230072969 + 3 ^ 40 * 4632372 * 2
def baseEnd_4632372 : Nat := 264292600714383895216235

theorem tailTrace_4632372 : CollatzResearch.WordTrace tailWord_4632372 prefixEnd_4632372 264292600714383895216235 := by
  unfold tailWord_4632372
  simp only [CollatzResearch.WordTrace]
  refine ⟨84478243586857432498173685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112637658115809909997564913 84478243586857432498173685)
  ·
    refine ⟨7919835336267884296703783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 84478243586857432498173685 7919835336267884296703783)
    ·
      refine ⟨11879753004401826445055675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7919835336267884296703783 11879753004401826445055675)
      ·
        refine ⟨17819629506602739667583513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11879753004401826445055675 17819629506602739667583513)
        ·
          refine ⟨13364722129952054750687635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17819629506602739667583513 13364722129952054750687635)
          ·
            refine ⟨20047083194928082126031453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13364722129952054750687635 20047083194928082126031453)
            ·
              refine ⟨7517656198098030797261795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20047083194928082126031453 7517656198098030797261795)
              ·
                refine ⟨11276484297147046195892693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7517656198098030797261795 11276484297147046195892693)
                ·
                  refine ⟨264292600714383895216235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11276484297147046195892693 264292600714383895216235)
                  ·
                    rfl

theorem cell23_4632372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_4632372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632372 prefixEnd_4632372 := by exact prefixLift 4632372
  have htrace : WordTrace (prefixWord ++ tailWord_4632372) baseStart_4632372 baseEnd_4632372 := by
    simpa [prefixWord, tailWord_4632372, baseEnd_4632372] using wordTrace_append hprefix tailTrace_4632372
  have hstable : (prefixWord ++ tailWord_4632372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632372).length < 2 ^ (prefixWord ++ tailWord_4632372).sum := by decide
  have hdescent : baseEnd_4632372 < baseStart_4632372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632383 : List Nat := [1, 1, 2, 2, 6, 2, 2, 1, 2, 2, 2]
def baseStart_4632383 : Nat := 118140960795 + 4632383 * 2 ^ 59
def prefixEnd_4632383 : Nat := 4983230072969 + 3 ^ 40 * 4632383 * 2
def baseEnd_4632383 : Nat := 2378639054716654513908565

theorem tailTrace_4632383 : CollatzResearch.WordTrace tailWord_4632383 prefixEnd_4632383 2378639054716654513908565 := by
  unfold tailWord_4632383
  simp only [CollatzResearch.WordTrace]
  refine ⟨168956888376675013874997803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112637925584450009249998535 168956888376675013874997803)
  ·
    refine ⟨253435332565012520812496705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168956888376675013874997803 253435332565012520812496705)
    ·
      refine ⟨190076499423759390609372529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253435332565012520812496705 190076499423759390609372529)
      ·
        refine ⟨142557374567819542957029397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190076499423759390609372529 142557374567819542957029397)
        ·
          refine ⟨6682376932866541076110753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 142557374567819542957029397 6682376932866541076110753)
          ·
            refine ⟨5011782699649905807083065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6682376932866541076110753 5011782699649905807083065)
            ·
              refine ⟨3758837024737429355312299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5011782699649905807083065 3758837024737429355312299)
              ·
                refine ⟨5638255537106144032968449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3758837024737429355312299 5638255537106144032968449)
                ·
                  refine ⟨4228691652829608024726337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5638255537106144032968449 4228691652829608024726337)
                  ·
                    refine ⟨3171518739622206018544753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4228691652829608024726337 3171518739622206018544753)
                    ·
                      refine ⟨2378639054716654513908565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3171518739622206018544753 2378639054716654513908565)
                      ·
                        rfl

theorem cell23_4632383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 2, 1, 2, 2, 2].length) (baseStart_4632383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632383 prefixEnd_4632383 := by exact prefixLift 4632383
  have htrace : WordTrace (prefixWord ++ tailWord_4632383) baseStart_4632383 baseEnd_4632383 := by
    simpa [prefixWord, tailWord_4632383, baseEnd_4632383] using wordTrace_append hprefix tailTrace_4632383
  have hstable : (prefixWord ++ tailWord_4632383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632383).length < 2 ^ (prefixWord ++ tailWord_4632383).sum := by decide
  have hdescent : baseEnd_4632383 < baseStart_4632383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632402 : List Nat := [3, 2, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_4632402 : Nat := 118140960795 + 4632402 * 2 ^ 59
def prefixEnd_4632402 : Nat := 4983230072969 + 3 ^ 40 * 4632402 * 2
def baseEnd_4632402 : Nat := 792882936949696646523659

theorem tailTrace_4632402 : CollatzResearch.WordTrace tailWord_4632402 prefixEnd_4632402 792882936949696646523659 := by
  unfold tailWord_4632402
  simp only [CollatzResearch.WordTrace]
  refine ⟨42239395340901545029984865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112638387575737453413292973 42239395340901545029984865)
  ·
    refine ⟨31679546505676158772488649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42239395340901545029984865 31679546505676158772488649)
    ·
      refine ⟨23759659879257119079366487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31679546505676158772488649 23759659879257119079366487)
      ·
        refine ⟨35639489818885678619049731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23759659879257119079366487 35639489818885678619049731)
        ·
          refine ⟨53459234728328517928574597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35639489818885678619049731 53459234728328517928574597)
          ·
            refine ⟨10023606511561597111607737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53459234728328517928574597 10023606511561597111607737)
            ·
              refine ⟨7517704883671197833705803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10023606511561597111607737 7517704883671197833705803)
              ·
                refine ⟨11276557325506796750558705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7517704883671197833705803 11276557325506796750558705)
                ·
                  refine ⟨8457417994130097562919029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11276557325506796750558705 8457417994130097562919029)
                  ·
                    refine ⟨792882936949696646523659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8457417994130097562919029 792882936949696646523659)
                    ·
                      rfl

theorem cell23_4632402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_4632402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632402 prefixEnd_4632402 := by exact prefixLift 4632402
  have htrace : WordTrace (prefixWord ++ tailWord_4632402) baseStart_4632402 baseEnd_4632402 := by
    simpa [prefixWord, tailWord_4632402, baseEnd_4632402] using wordTrace_append hprefix tailTrace_4632402
  have hstable : (prefixWord ++ tailWord_4632402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632402).length < 2 ^ (prefixWord ++ tailWord_4632402).sum := by decide
  have hdescent : baseEnd_4632402 < baseStart_4632402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632408 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 1, 2, 9]
def baseStart_4632408 : Nat := 118140960795 + 4632408 * 2 ^ 59
def prefixEnd_4632408 : Nat := 4983230072969 + 3 ^ 40 * 4632408 * 2
def baseEnd_4632408 : Nat := 2378651891733016916095949

theorem tailTrace_4632408 : CollatzResearch.WordTrace tailWord_4632408 prefixEnd_4632408 2378651891733016916095949 := by
  unfold tailWord_4632408
  simp only [CollatzResearch.WordTrace]
  refine ⟨84478900100792221572328939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112638533467722962096438585 84478900100792221572328939)
  ·
    refine ⟨126718350151188332358493409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84478900100792221572328939 126718350151188332358493409)
    ·
      refine ⟨95038762613391249268870057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126718350151188332358493409 95038762613391249268870057)
      ·
        refine ⟨71279071960043436951652543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95038762613391249268870057 71279071960043436951652543)
        ·
          refine ⟨106918607940065155427478815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71279071960043436951652543 106918607940065155427478815)
          ·
            refine ⟨160377911910097733141218223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106918607940065155427478815 160377911910097733141218223)
            ·
              refine ⟨240566867865146599711827335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160377911910097733141218223 240566867865146599711827335)
              ·
                refine ⟨360850301797719899567741003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240566867865146599711827335 360850301797719899567741003)
                ·
                  refine ⟨541275452696579849351611505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 360850301797719899567741003 541275452696579849351611505)
                  ·
                    refine ⟨405956589522434887013708629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 541275452696579849351611505 405956589522434887013708629)
                    ·
                      refine ⟨2378651891733016916095949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 405956589522434887013708629 2378651891733016916095949)
                      ·
                        rfl

theorem cell23_4632408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_4632408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632408 prefixEnd_4632408 := by exact prefixLift 4632408
  have htrace : WordTrace (prefixWord ++ tailWord_4632408) baseStart_4632408 baseEnd_4632408 := by
    simpa [prefixWord, tailWord_4632408, baseEnd_4632408] using wordTrace_append hprefix tailTrace_4632408
  have hstable : (prefixWord ++ tailWord_4632408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632408).length < 2 ^ (prefixWord ++ tailWord_4632408).sum := by decide
  have hdescent : baseEnd_4632408 < baseStart_4632408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632456 : List Nat := [2, 1, 3, 3, 4, 1, 1, 1, 2, 1, 4]
def baseStart_4632456 : Nat := 118140960795 + 4632456 * 2 ^ 59
def prefixEnd_4632456 : Nat := 4983230072969 + 3 ^ 40 * 4632456 * 2
def baseEnd_4632456 : Nat := 2378676538804432728295729

theorem tailTrace_4632456 : CollatzResearch.WordTrace tailWord_4632456 prefixEnd_4632456 2378676538804432728295729 := by
  unfold tailWord_4632456
  simp only [CollatzResearch.WordTrace]
  refine ⟨84479775452705273671202611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112639700603607031561603481 84479775452705273671202611)
  ·
    refine ⟨126719663179057910506803917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84479775452705273671202611 126719663179057910506803917)
    ·
      refine ⟨47519873692146716440051469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126719663179057910506803917 47519873692146716440051469)
      ·
        refine ⟨17819952634555018665019301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47519873692146716440051469 17819952634555018665019301)
        ·
          refine ⟨3341241118979065999691119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17819952634555018665019301 3341241118979065999691119)
          ·
            refine ⟨5011861678468598999536679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341241118979065999691119 5011861678468598999536679)
            ·
              refine ⟨7517792517702898499305019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5011861678468598999536679 7517792517702898499305019)
              ·
                refine ⟨11276688776554347748957529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7517792517702898499305019 11276688776554347748957529)
                ·
                  refine ⟨8457516582415760811718147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11276688776554347748957529 8457516582415760811718147)
                  ·
                    refine ⟨12686274873623641217577221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8457516582415760811718147 12686274873623641217577221)
                    ·
                      refine ⟨2378676538804432728295729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12686274873623641217577221 2378676538804432728295729)
                      ·
                        rfl

theorem cell23_4632456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_4632456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632456 prefixEnd_4632456 := by exact prefixLift 4632456
  have htrace : WordTrace (prefixWord ++ tailWord_4632456) baseStart_4632456 baseEnd_4632456 := by
    simpa [prefixWord, tailWord_4632456, baseEnd_4632456] using wordTrace_append hprefix tailTrace_4632456
  have hstable : (prefixWord ++ tailWord_4632456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632456).length < 2 ^ (prefixWord ++ tailWord_4632456).sum := by decide
  have hdescent : baseEnd_4632456 < baseStart_4632456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632466 : List Nat := [3, 2, 3, 2, 1, 1, 1, 5, 1, 4]
def baseStart_4632466 : Nat := 118140960795 + 4632466 * 2 ^ 59
def prefixEnd_4632466 : Nat := 4983230072969 + 3 ^ 40 * 4632466 * 2
def baseEnd_4632466 : Nat := 792893891203659229723561

theorem tailTrace_4632466 : CollatzResearch.WordTrace tailWord_4632466 prefixEnd_4632466 792893891203659229723561 := by
  unfold tailWord_4632466
  simp only [CollatzResearch.WordTrace]
  refine ⟨42239978908843579762567313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112639943756916212700179501 42239978908843579762567313)
  ·
    refine ⟨31679984181632684821925485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42239978908843579762567313 31679984181632684821925485)
    ·
      refine ⟨11879994068112256808222057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31679984181632684821925485 11879994068112256808222057)
      ·
        refine ⟨8909995551084192606166543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11879994068112256808222057 8909995551084192606166543)
        ·
          refine ⟨13364993326626288909249815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8909995551084192606166543 13364993326626288909249815)
          ·
            refine ⟨20047489989939433363874723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13364993326626288909249815 20047489989939433363874723)
            ·
              refine ⟨30071234984909150045812085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20047489989939433363874723 30071234984909150045812085)
              ·
                refine ⟨2819178279835232816794883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30071234984909150045812085 2819178279835232816794883)
                ·
                  refine ⟨4228767419752849225192325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819178279835232816794883 4228767419752849225192325)
                  ·
                    refine ⟨792893891203659229723561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228767419752849225192325 792893891203659229723561)
                    ·
                      rfl

theorem cell23_4632466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_4632466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632466 prefixEnd_4632466 := by exact prefixLift 4632466
  have htrace : WordTrace (prefixWord ++ tailWord_4632466) baseStart_4632466 baseEnd_4632466 := by
    simpa [prefixWord, tailWord_4632466, baseEnd_4632466] using wordTrace_append hprefix tailTrace_4632466
  have hstable : (prefixWord ++ tailWord_4632466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632466).length < 2 ^ (prefixWord ++ tailWord_4632466).sum := by decide
  have hdescent : baseEnd_4632466 < baseStart_4632466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632479 : List Nat := [1, 1, 2, 5, 3, 2, 1, 2, 6]
def baseStart_4632479 : Nat := 118140960795 + 4632479 * 2 ^ 59
def prefixEnd_4632479 : Nat := 4983230072969 + 3 ^ 40 * 4632479 * 2
def baseEnd_4632479 : Nat := 264298705428831793145347

theorem tailTrace_4632479 : CollatzResearch.WordTrace tailWord_4632479 prefixEnd_4632479 264298705428831793145347 := by
  unfold tailWord_4632479
  simp only [CollatzResearch.WordTrace]
  refine ⟨168960389784327222270492491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112640259856218148180328327 168960389784327222270492491)
  ·
    refine ⟨253440584676490833405738737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168960389784327222270492491 253440584676490833405738737)
    ·
      refine ⟨190080438507368125054304053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253440584676490833405738737 190080438507368125054304053)
      ·
        refine ⟨17820041110065761723841005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190080438507368125054304053 17820041110065761723841005)
        ·
          refine ⟨6682515416274660646440377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17820041110065761723841005 6682515416274660646440377)
          ·
            refine ⟨5011886562205995484830283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6682515416274660646440377 5011886562205995484830283)
            ·
              refine ⟨7517829843308993227245425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5011886562205995484830283 7517829843308993227245425)
              ·
                refine ⟨5638372382481744920434069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7517829843308993227245425 5638372382481744920434069)
                ·
                  refine ⟨264298705428831793145347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5638372382481744920434069 264298705428831793145347)
                  ·
                    rfl

theorem cell23_4632479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 1, 2, 6].length) (baseStart_4632479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632479 prefixEnd_4632479 := by exact prefixLift 4632479
  have htrace : WordTrace (prefixWord ++ tailWord_4632479) baseStart_4632479 baseEnd_4632479 := by
    simpa [prefixWord, tailWord_4632479, baseEnd_4632479] using wordTrace_append hprefix tailTrace_4632479
  have hstable : (prefixWord ++ tailWord_4632479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632479).length < 2 ^ (prefixWord ++ tailWord_4632479).sum := by decide
  have hdescent : baseEnd_4632479 < baseStart_4632479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632509 : List Nat := [1, 4, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_4632509 : Nat := 118140960795 + 4632509 * 2 ^ 59
def prefixEnd_4632509 : Nat := 4983230072969 + 3 ^ 40 * 4632509 * 2
def baseEnd_4632509 : Nat := 792901251093040340310995

theorem tailTrace_4632509 : CollatzResearch.WordTrace tailWord_4632509 prefixEnd_4632509 792901251093040340310995 := by
  unfold tailWord_4632509
  simp only [CollatzResearch.WordTrace]
  refine ⟨168961483974218537394084581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112640989316145691596056387 168961483974218537394084581)
  ·
    refine ⟨31680278245165975761390859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168961483974218537394084581 31680278245165975761390859)
    ·
      refine ⟨47520417367748963642086289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31680278245165975761390859 47520417367748963642086289)
      ·
        refine ⟨35640313025811722731564717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47520417367748963642086289 35640313025811722731564717)
        ·
          refine ⟨13365117384679396024336769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35640313025811722731564717 13365117384679396024336769)
          ·
            refine ⟨10023838038509547018252577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13365117384679396024336769 10023838038509547018252577)
            ·
              refine ⟨7517878528882160263689433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10023838038509547018252577 7517878528882160263689433)
              ·
                refine ⟨5638408896661620197767075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7517878528882160263689433 5638408896661620197767075)
                ·
                  refine ⟨8457613344992430296650613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5638408896661620197767075 8457613344992430296650613)
                  ·
                    refine ⟨792901251093040340310995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8457613344992430296650613 792901251093040340310995)
                    ·
                      rfl

theorem cell23_4632509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_4632509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632509 prefixEnd_4632509 := by exact prefixLift 4632509
  have htrace : WordTrace (prefixWord ++ tailWord_4632509) baseStart_4632509 baseEnd_4632509 := by
    simpa [prefixWord, tailWord_4632509, baseEnd_4632509] using wordTrace_append hprefix tailTrace_4632509
  have hstable : (prefixWord ++ tailWord_4632509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632509).length < 2 ^ (prefixWord ++ tailWord_4632509).sum := by decide
  have hdescent : baseEnd_4632509 < baseStart_4632509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632512 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 2, 6, 2]
def baseStart_4632512 : Nat := 118140960795 + 4632512 * 2 ^ 59
def prefixEnd_4632512 : Nat := 4983230072969 + 3 ^ 40 * 4632512 * 2
def baseEnd_4632512 : Nat := 2378705293721084509195471

theorem tailTrace_4632512 : CollatzResearch.WordTrace tailWord_4632512 prefixEnd_4632512 2378705293721084509195471 := by
  unfold tailWord_4632512
  simp only [CollatzResearch.WordTrace]
  refine ⟨84480796696603834453221895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112641062262138445937629193 84480796696603834453221895)
  ·
    refine ⟨126721195044905751679832843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84480796696603834453221895 126721195044905751679832843)
    ·
      refine ⟨190081792567358627519749265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126721195044905751679832843 190081792567358627519749265)
      ·
        refine ⟨142561344425518970639811949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190081792567358627519749265 142561344425518970639811949)
        ·
          refine ⟨53460504159569613989929481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142561344425518970639811949 53460504159569613989929481)
          ·
            refine ⟨40095378119677210492447111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53460504159569613989929481 40095378119677210492447111)
            ·
              refine ⟨60143067179515815738670667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40095378119677210492447111 60143067179515815738670667)
              ·
                refine ⟨90214600769273723608006001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60143067179515815738670667 90214600769273723608006001)
                ·
                  refine ⟨67660950576955292706004501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 90214600769273723608006001 67660950576955292706004501)
                  ·
                    refine ⟨3171607058294779345593961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67660950576955292706004501 3171607058294779345593961)
                    ·
                      refine ⟨2378705293721084509195471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3171607058294779345593961 2378705293721084509195471)
                      ·
                        rfl

theorem cell23_4632512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 2, 6, 2].length) (baseStart_4632512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632512 prefixEnd_4632512 := by exact prefixLift 4632512
  have htrace : WordTrace (prefixWord ++ tailWord_4632512) baseStart_4632512 baseEnd_4632512 := by
    simpa [prefixWord, tailWord_4632512, baseEnd_4632512] using wordTrace_append hprefix tailTrace_4632512
  have hstable : (prefixWord ++ tailWord_4632512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632512).length < 2 ^ (prefixWord ++ tailWord_4632512).sum := by decide
  have hdescent : baseEnd_4632512 < baseStart_4632512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632522 : List Nat := [3, 1, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_4632522 : Nat := 118140960795 + 4632522 * 2 ^ 59
def prefixEnd_4632522 : Nat := 4983230072969 + 3 ^ 40 * 4632522 * 2
def baseEnd_4632522 : Nat := 792903476175876490023475

theorem tailTrace_4632522 : CollatzResearch.WordTrace tailWord_4632522 prefixEnd_4632522 792903476175876490023475 := by
  unfold tailWord_4632522
  simp only [CollatzResearch.WordTrace]
  refine ⟨42240489530792860153576955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112641305415447627076205213 42240489530792860153576955)
  ·
    refine ⟨63360734296189290230365433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42240489530792860153576955 63360734296189290230365433)
    ·
      refine ⟨47520550722141967672774075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63360734296189290230365433 47520550722141967672774075)
      ·
        refine ⟨71280826083212951509161113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47520550722141967672774075 71280826083212951509161113)
        ·
          refine ⟨53460619562409713631870835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71280826083212951509161113 53460619562409713631870835)
          ·
            refine ⟨80190929343614570447806253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53460619562409713631870835 80190929343614570447806253)
            ·
              refine ⟨30071598503855463917927345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80190929343614570447806253 30071598503855463917927345)
              ·
                refine ⟨22553698877891597938445509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30071598503855463917927345 22553698877891597938445509)
                ·
                  refine ⟨4228818539604674613458533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22553698877891597938445509 4228818539604674613458533)
                  ·
                    refine ⟨792903476175876490023475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4228818539604674613458533 792903476175876490023475)
                    ·
                      rfl

theorem cell23_4632522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_4632522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632522 prefixEnd_4632522 := by exact prefixLift 4632522
  have htrace : WordTrace (prefixWord ++ tailWord_4632522) baseStart_4632522 baseEnd_4632522 := by
    simpa [prefixWord, tailWord_4632522, baseEnd_4632522] using wordTrace_append hprefix tailTrace_4632522
  have hstable : (prefixWord ++ tailWord_4632522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632522).length < 2 ^ (prefixWord ++ tailWord_4632522).sum := by decide
  have hdescent : baseEnd_4632522 < baseStart_4632522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632566 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_4632566 : Nat := 118140960795 + 4632566 * 2 ^ 59
def prefixEnd_4632566 : Nat := 4983230072969 + 3 ^ 40 * 4632566 * 2
def baseEnd_4632566 : Nat := 2378733021676427297920223

theorem tailTrace_4632566 : CollatzResearch.WordTrace tailWord_4632566 prefixEnd_4632566 2378733021676427297920223 := by
  unfold tailWord_4632566
  simp only [CollatzResearch.WordTrace]
  refine ⟨10560222683438252258056847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112642375290008024085939701 10560222683438252258056847)
  ·
    refine ⟨15840334025157378387085271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10560222683438252258056847 15840334025157378387085271)
    ·
      refine ⟨23760501037736067580627907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15840334025157378387085271 23760501037736067580627907)
      ·
        refine ⟨35640751556604101370941861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23760501037736067580627907 35640751556604101370941861)
        ·
          refine ⟨6682640916863269007051599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35640751556604101370941861 6682640916863269007051599)
          ·
            refine ⟨10023961375294903510577399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6682640916863269007051599 10023961375294903510577399)
            ·
              refine ⟨15035942062942355265866099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10023961375294903510577399 15035942062942355265866099)
              ·
                refine ⟨22553913094413532898799149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15035942062942355265866099 22553913094413532898799149)
                ·
                  refine ⟨8457717410405074837049681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22553913094413532898799149 8457717410405074837049681)
                  ·
                    refine ⟨6343288057803806127787261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8457717410405074837049681 6343288057803806127787261)
                    ·
                      refine ⟨2378733021676427297920223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6343288057803806127787261 2378733021676427297920223)
                      ·
                        rfl

theorem cell23_4632566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_4632566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632566 prefixEnd_4632566 := by exact prefixLift 4632566
  have htrace : WordTrace (prefixWord ++ tailWord_4632566) baseStart_4632566 baseEnd_4632566 := by
    simpa [prefixWord, tailWord_4632566, baseEnd_4632566] using wordTrace_append hprefix tailTrace_4632566
  have hstable : (prefixWord ++ tailWord_4632566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632566).length < 2 ^ (prefixWord ++ tailWord_4632566).sum := by decide
  have hdescent : baseEnd_4632566 < baseStart_4632566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632575 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 5]
def baseStart_4632575 : Nat := 118140960795 + 4632575 * 2 ^ 59
def prefixEnd_4632575 : Nat := 4983230072969 + 3 ^ 40 * 4632575 * 2
def baseEnd_4632575 : Nat := 2378737643002317762707681

theorem tailTrace_4632575 : CollatzResearch.WordTrace tailWord_4632575 prefixEnd_4632575 2378737643002317762707681 := by
  unfold tailWord_4632575
  simp only [CollatzResearch.WordTrace]
  refine ⟨168963891191979430665987179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112642594127986287110658119 168963891191979430665987179)
  ·
    refine ⟨253445836787969145998980769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168963891191979430665987179 253445836787969145998980769)
    ·
      refine ⟨190084377590976859499235577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253445836787969145998980769 190084377590976859499235577)
      ·
        refine ⟨142563283193232644624426683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190084377590976859499235577 142563283193232644624426683)
        ·
          refine ⟨213844924789848966936640025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142563283193232644624426683 213844924789848966936640025)
          ·
            refine ⟨160383693592386725202480019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213844924789848966936640025 160383693592386725202480019)
            ·
              refine ⟨240575540388580087803720029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160383693592386725202480019 240575540388580087803720029)
              ·
                refine ⟨90215827645717532926395011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240575540388580087803720029 90215827645717532926395011)
                ·
                  refine ⟨135323741468576299389592517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90215827645717532926395011 135323741468576299389592517)
                  ·
                    refine ⟨25373201525358056135548597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135323741468576299389592517 25373201525358056135548597)
                    ·
                      refine ⟨2378737643002317762707681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25373201525358056135548597 2378737643002317762707681)
                      ·
                        rfl

theorem cell23_4632575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 4, 5].length) (baseStart_4632575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632575 prefixEnd_4632575 := by exact prefixLift 4632575
  have htrace : WordTrace (prefixWord ++ tailWord_4632575) baseStart_4632575 baseEnd_4632575 := by
    simpa [prefixWord, tailWord_4632575, baseEnd_4632575] using wordTrace_append hprefix tailTrace_4632575
  have hstable : (prefixWord ++ tailWord_4632575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632575).length < 2 ^ (prefixWord ++ tailWord_4632575).sum := by decide
  have hdescent : baseEnd_4632575 < baseStart_4632575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632597 : List Nat := [1, 3, 2, 1, 5, 2, 2, 2, 1, 2, 2]
def baseStart_4632597 : Nat := 118140960795 + 4632597 * 2 ^ 59
def prefixEnd_4632597 : Nat := 4983230072969 + 3 ^ 40 * 4632597 * 2
def baseEnd_4632597 : Nat := 2378748939576716676632581

theorem tailTrace_4632597 : CollatzResearch.WordTrace tailWord_4632597 prefixEnd_4632597 2378748939576716676632581 := by
  unfold tailWord_4632597
  simp only [CollatzResearch.WordTrace]
  refine ⟨168964693597899728423288045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112643129065266485615525363 168964693597899728423288045)
  ·
    refine ⟨63361760099212398158733017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168964693597899728423288045 63361760099212398158733017)
    ·
      refine ⟨47521320074409298619049763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63361760099212398158733017 47521320074409298619049763)
      ·
        refine ⟨71281980111613947928574645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47521320074409298619049763 71281980111613947928574645)
        ·
          refine ⟨6682685635463807618303873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71281980111613947928574645 6682685635463807618303873)
          ·
            refine ⟨5012014226597855713727905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6682685635463807618303873 5012014226597855713727905)
            ·
              refine ⟨3759010669948391785295929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5012014226597855713727905 3759010669948391785295929)
              ·
                refine ⟨2819258002461293838971947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759010669948391785295929 2819258002461293838971947)
                ·
                  refine ⟨4228887003691940758457921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819258002461293838971947 4228887003691940758457921)
                  ·
                    refine ⟨3171665252768955568843441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4228887003691940758457921 3171665252768955568843441)
                    ·
                      refine ⟨2378748939576716676632581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3171665252768955568843441 2378748939576716676632581)
                      ·
                        rfl

theorem cell23_4632597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_4632597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632597 prefixEnd_4632597 := by exact prefixLift 4632597
  have htrace : WordTrace (prefixWord ++ tailWord_4632597) baseStart_4632597 baseEnd_4632597 := by
    simpa [prefixWord, tailWord_4632597, baseEnd_4632597] using wordTrace_append hprefix tailTrace_4632597
  have hstable : (prefixWord ++ tailWord_4632597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632597).length < 2 ^ (prefixWord ++ tailWord_4632597).sum := by decide
  have hdescent : baseEnd_4632597 < baseStart_4632597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632602 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4]
def baseStart_4632602 : Nat := 118140960795 + 4632602 * 2 ^ 59
def prefixEnd_4632602 : Nat := 4983230072969 + 3 ^ 40 * 4632602 * 2
def baseEnd_4632602 : Nat := 2378751506979989157070057

theorem tailTrace_4632602 : CollatzResearch.WordTrace tailWord_4632602 prefixEnd_4632602 2378751506979989157070057 := by
  unfold tailWord_4632602
  simp only [CollatzResearch.WordTrace]
  refine ⟨42241218990720403569305015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112643250641921076184813373 42241218990720403569305015)
  ·
    refine ⟨63361828486080605353957523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42241218990720403569305015 63361828486080605353957523)
    ·
      refine ⟨95042742729120908030936285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63361828486080605353957523 95042742729120908030936285)
      ·
        refine ⟨35641028523420340511601107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95042742729120908030936285 35641028523420340511601107)
        ·
          refine ⟨53461542785130510767401661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35641028523420340511601107 53461542785130510767401661)
          ·
            refine ⟨20048078544423941537775623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53461542785130510767401661 20048078544423941537775623)
            ·
              refine ⟨30072117816635912306663435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20048078544423941537775623 30072117816635912306663435)
              ·
                refine ⟨45108176724953868459995153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30072117816635912306663435 45108176724953868459995153)
                ·
                  refine ⟨33831132543715401344996365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45108176724953868459995153 33831132543715401344996365)
                  ·
                    refine ⟨12686674703893275504373637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33831132543715401344996365 12686674703893275504373637)
                    ·
                      refine ⟨2378751506979989157070057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12686674703893275504373637 2378751506979989157070057)
                      ·
                        rfl

theorem cell23_4632602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_4632602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632602 prefixEnd_4632602 := by exact prefixLift 4632602
  have htrace : WordTrace (prefixWord ++ tailWord_4632602) baseStart_4632602 baseEnd_4632602 := by
    simpa [prefixWord, tailWord_4632602, baseEnd_4632602] using wordTrace_append hprefix tailTrace_4632602
  have hstable : (prefixWord ++ tailWord_4632602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632602).length < 2 ^ (prefixWord ++ tailWord_4632602).sum := by decide
  have hdescent : baseEnd_4632602 < baseStart_4632602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632636 : List Nat := [2, 2, 2, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_4632636 : Nat := 118140960795 + 4632636 * 2 ^ 59
def prefixEnd_4632636 : Nat := 4983230072969 + 3 ^ 40 * 4632636 * 2
def baseEnd_4632636 : Nat := 2378768965322242024044901

theorem tailTrace_4632636 : CollatzResearch.WordTrace tailWord_4632636 prefixEnd_4632636 2378768965322242024044901 := by
  unfold tailWord_4632636
  simp only [CollatzResearch.WordTrace]
  refine ⟨84483058022379219041978881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112644077363172292055971841 84483058022379219041978881)
  ·
    refine ⟨63362293516784414281484161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84483058022379219041978881 63362293516784414281484161)
    ·
      refine ⟨47521720137588310711113121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63362293516784414281484161 47521720137588310711113121)
      ·
        refine ⟨35641290103191233033334841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47521720137588310711113121 35641290103191233033334841)
        ·
          refine ⟨26730967577393424775001131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35641290103191233033334841 26730967577393424775001131)
          ·
            refine ⟨40096451366090137162501697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26730967577393424775001131 40096451366090137162501697)
            ·
              refine ⟨30072338524567602871876273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40096451366090137162501697 30072338524567602871876273)
              ·
                refine ⟨22554253893425702153907205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30072338524567602871876273 22554253893425702153907205)
                ·
                  refine ⟨4228922605017319153857601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22554253893425702153907205 4228922605017319153857601)
                  ·
                    refine ⟨3171691953762989365393201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4228922605017319153857601 3171691953762989365393201)
                    ·
                      refine ⟨2378768965322242024044901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3171691953762989365393201 2378768965322242024044901)
                      ·
                        rfl

theorem cell23_4632636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_4632636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632636 prefixEnd_4632636 := by exact prefixLift 4632636
  have htrace : WordTrace (prefixWord ++ tailWord_4632636) baseStart_4632636 baseEnd_4632636 := by
    simpa [prefixWord, tailWord_4632636, baseEnd_4632636] using wordTrace_append hprefix tailTrace_4632636
  have hstable : (prefixWord ++ tailWord_4632636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632636).length < 2 ^ (prefixWord ++ tailWord_4632636).sum := by decide
  have hdescent : baseEnd_4632636 < baseStart_4632636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632653 : List Nat := [1, 6, 1, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_4632653 : Nat := 118140960795 + 4632653 * 2 ^ 59
def prefixEnd_4632653 : Nat := 4983230072969 + 3 ^ 40 * 4632653 * 2
def baseEnd_4632653 : Nat := 2378777694493368457532323

theorem tailTrace_4632653 : CollatzResearch.WordTrace tailWord_4632653 prefixEnd_4632653 2378777694493368457532323 := by
  unfold tailWord_4632653
  simp only [CollatzResearch.WordTrace]
  refine ⟨168966736085696849987326613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112644490723797899991551075 168966736085696849987326613)
  ·
    refine ⟨7920315754017039843155935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 168966736085696849987326613 7920315754017039843155935)
    ·
      refine ⟨11880473631025559764733903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7920315754017039843155935 11880473631025559764733903)
      ·
        refine ⟨17820710446538339647100855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11880473631025559764733903 17820710446538339647100855)
        ·
          refine ⟨26731065669807509470651283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17820710446538339647100855 26731065669807509470651283)
          ·
            refine ⟨40096598504711264205976925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26731065669807509470651283 40096598504711264205976925)
            ·
              refine ⟨15036224439266724077241347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40096598504711264205976925 15036224439266724077241347)
              ·
                refine ⟨22554336658900086115862021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15036224439266724077241347 22554336658900086115862021)
                ·
                  refine ⟨4228938123543766146724129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22554336658900086115862021 4228938123543766146724129)
                  ·
                    refine ⟨3171703592657824610043097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4228938123543766146724129 3171703592657824610043097)
                    ·
                      refine ⟨2378777694493368457532323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3171703592657824610043097 2378777694493368457532323)
                      ·
                        rfl

theorem cell23_4632653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_4632653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632653 prefixEnd_4632653 := by exact prefixLift 4632653
  have htrace : WordTrace (prefixWord ++ tailWord_4632653) baseStart_4632653 baseEnd_4632653 := by
    simpa [prefixWord, tailWord_4632653, baseEnd_4632653] using wordTrace_append hprefix tailTrace_4632653
  have hstable : (prefixWord ++ tailWord_4632653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632653).length < 2 ^ (prefixWord ++ tailWord_4632653).sum := by decide
  have hdescent : baseEnd_4632653 < baseStart_4632653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632672 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 1, 7]
def baseStart_4632672 : Nat := 118140960795 + 4632672 * 2 ^ 59
def prefixEnd_4632672 : Nat := 4983230072969 + 3 ^ 40 * 4632672 * 2
def baseEnd_4632672 : Nat := 792929150208601294398245

theorem tailTrace_4632672 : CollatzResearch.WordTrace tailWord_4632672 prefixEnd_4632672 792929150208601294398245 := by
  unfold tailWord_4632672
  simp only [CollatzResearch.WordTrace]
  refine ⟨84483714536314008116134135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112644952715085344154845513 84483714536314008116134135)
  ·
    refine ⟨126725571804471012174201203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84483714536314008116134135 126725571804471012174201203)
    ·
      refine ⟨190088357706706518261301805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126725571804471012174201203 190088357706706518261301805)
      ·
        refine ⟨71283134140014944347988177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190088357706706518261301805 71283134140014944347988177)
        ·
          refine ⟨53462350605011208260991133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71283134140014944347988177 53462350605011208260991133)
          ·
            refine ⟨20048381476879203097871675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53462350605011208260991133 20048381476879203097871675)
            ·
              refine ⟨30072572215318804646807513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20048381476879203097871675 30072572215318804646807513)
              ·
                refine ⟨22554429161489103485105635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30072572215318804646807513 22554429161489103485105635)
                ·
                  refine ⟨33831643742233655227658453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22554429161489103485105635 33831643742233655227658453)
                  ·
                    refine ⟨792929150208601294398245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33831643742233655227658453 792929150208601294398245)
                    ·
                      rfl

theorem cell23_4632672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 1, 7].length) (baseStart_4632672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632672 prefixEnd_4632672 := by exact prefixLift 4632672
  have htrace : WordTrace (prefixWord ++ tailWord_4632672) baseStart_4632672 baseEnd_4632672 := by
    simpa [prefixWord, tailWord_4632672, baseEnd_4632672] using wordTrace_append hprefix tailTrace_4632672
  have hstable : (prefixWord ++ tailWord_4632672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632672).length < 2 ^ (prefixWord ++ tailWord_4632672).sum := by decide
  have hdescent : baseEnd_4632672 < baseStart_4632672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632709 : List Nat := [1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_4632709 : Nat := 118140960795 + 4632709 * 2 ^ 59
def prefixEnd_4632709 : Nat := 4983230072969 + 3 ^ 40 * 4632709 * 2
def baseEnd_4632709 : Nat := 2378806449410020238432065

theorem tailTrace_4632709 : CollatzResearch.WordTrace tailWord_4632709 prefixEnd_4632709 2378806449410020238432065 := by
  unfold tailWord_4632709
  simp only [CollatzResearch.WordTrace]
  refine ⟨168968778573493971551365181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112645852382329314367576787 168968778573493971551365181)
  ·
    refine ⟨63363291965060239331761943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168968778573493971551365181 63363291965060239331761943)
    ·
      refine ⟨95044937947590358997642915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63363291965060239331761943 95044937947590358997642915)
      ·
        refine ⟨142567406921385538496464373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95044937947590358997642915 142567406921385538496464373)
        ·
          refine ⟨13365694398879894234043535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142567406921385538496464373 13365694398879894234043535)
          ·
            refine ⟨20048541598319841351065303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13365694398879894234043535 20048541598319841351065303)
            ·
              refine ⟨30072812397479762026597955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20048541598319841351065303 30072812397479762026597955)
              ·
                refine ⟨45109218596219643039896933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30072812397479762026597955 45109218596219643039896933)
                ·
                  refine ⟨8457978486791183069980675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 45109218596219643039896933 8457978486791183069980675)
                  ·
                    refine ⟨12686967730186774604971013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8457978486791183069980675 12686967730186774604971013)
                    ·
                      refine ⟨2378806449410020238432065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12686967730186774604971013 2378806449410020238432065)
                      ·
                        rfl

theorem cell23_4632709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_4632709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632709 prefixEnd_4632709 := by exact prefixLift 4632709
  have htrace : WordTrace (prefixWord ++ tailWord_4632709) baseStart_4632709 baseEnd_4632709 := by
    simpa [prefixWord, tailWord_4632709, baseEnd_4632709] using wordTrace_append hprefix tailTrace_4632709
  have hstable : (prefixWord ++ tailWord_4632709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632709).length < 2 ^ (prefixWord ++ tailWord_4632709).sum := by decide
  have hdescent : baseEnd_4632709 < baseStart_4632709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632743 : List Nat := [1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 4]
def baseStart_4632743 : Nat := 118140960795 + 4632743 * 2 ^ 59
def prefixEnd_4632743 : Nat := 4983230072969 + 3 ^ 40 * 4632743 * 2
def baseEnd_4632743 : Nat := 2378823907752273105406909

theorem tailTrace_4632743 : CollatzResearch.WordTrace tailWord_4632743 prefixEnd_4632743 2378823907752273105406909 := by
  unfold tailWord_4632743
  simp only [CollatzResearch.WordTrace]
  refine ⟨168970018655370795358102883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112646679103580530238735255 168970018655370795358102883)
  ·
    refine ⟨253455027983056193037154325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168970018655370795358102883 253455027983056193037154325)
    ·
      refine ⟨11880704436705759048616609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 253455027983056193037154325 11880704436705759048616609)
      ·
        refine ⟨8910528327529319286462457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11880704436705759048616609 8910528327529319286462457)
        ·
          refine ⟨6682896245646989464846843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8910528327529319286462457 6682896245646989464846843)
          ·
            refine ⟨10024344368470484197270265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6682896245646989464846843 10024344368470484197270265)
            ·
              refine ⟨7518258276352863147952699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10024344368470484197270265 7518258276352863147952699)
              ·
                refine ⟨11277387414529294721929049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7518258276352863147952699 11277387414529294721929049)
                ·
                  refine ⟨8458040560896971041446787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11277387414529294721929049 8458040560896971041446787)
                  ·
                    refine ⟨12687060841345456562170181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8458040560896971041446787 12687060841345456562170181)
                    ·
                      refine ⟨2378823907752273105406909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12687060841345456562170181 2378823907752273105406909)
                      ·
                        rfl

theorem cell23_4632743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_4632743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632743 prefixEnd_4632743 := by exact prefixLift 4632743
  have htrace : WordTrace (prefixWord ++ tailWord_4632743) baseStart_4632743 baseEnd_4632743 := by
    simpa [prefixWord, tailWord_4632743, baseEnd_4632743] using wordTrace_append hprefix tailTrace_4632743
  have hstable : (prefixWord ++ tailWord_4632743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632743).length < 2 ^ (prefixWord ++ tailWord_4632743).sum := by decide
  have hdescent : baseEnd_4632743 < baseStart_4632743 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632776 : List Nat := [2, 1, 3, 1, 2, 1, 1, 5, 3, 1, 3]
def baseStart_4632776 : Nat := 118140960795 + 4632776 * 2 ^ 59
def prefixEnd_4632776 : Nat := 4983230072969 + 3 ^ 40 * 4632776 * 2
def baseEnd_4632776 : Nat := 2378840852613871476294257

theorem tailTrace_4632776 : CollatzResearch.WordTrace tailWord_4632776 prefixEnd_4632776 2378840852613871476294257 := by
  unfold tailWord_4632776
  simp only [CollatzResearch.WordTrace]
  refine ⟨84485611132125620997027091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112647481509500827996036121 84485611132125620997027091)
  ·
    refine ⟨126728416698188431495540637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84485611132125620997027091 126728416698188431495540637)
    ·
      refine ⟨47523156261820661810827739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126728416698188431495540637 47523156261820661810827739)
      ·
        refine ⟨71284734392730992716241609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47523156261820661810827739 71284734392730992716241609)
        ·
          refine ⟨53463550794548244537181207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71284734392730992716241609 53463550794548244537181207)
          ·
            refine ⟨80195326191822366805771811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53463550794548244537181207 80195326191822366805771811)
            ·
              refine ⟨120292989287733550208657717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80195326191822366805771811 120292989287733550208657717)
              ·
                refine ⟨11277467745725020332061661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120292989287733550208657717 11277467745725020332061661)
                ·
                  refine ⟨4229050404646882624523123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11277467745725020332061661 4229050404646882624523123)
                  ·
                    refine ⟨6343575606970323936784685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4229050404646882624523123 6343575606970323936784685)
                    ·
                      refine ⟨2378840852613871476294257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6343575606970323936784685 2378840852613871476294257)
                      ·
                        rfl

theorem cell23_4632776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_4632776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632776 prefixEnd_4632776 := by exact prefixLift 4632776
  have htrace : WordTrace (prefixWord ++ tailWord_4632776) baseStart_4632776 baseEnd_4632776 := by
    simpa [prefixWord, tailWord_4632776, baseEnd_4632776] using wordTrace_append hprefix tailTrace_4632776
  have hstable : (prefixWord ++ tailWord_4632776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632776).length < 2 ^ (prefixWord ++ tailWord_4632776).sum := by decide
  have hdescent : baseEnd_4632776 < baseStart_4632776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632809 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 6, 4]
def baseStart_4632809 : Nat := 118140960795 + 4632809 * 2 ^ 59
def prefixEnd_4632809 : Nat := 4983230072969 + 3 ^ 40 * 4632809 * 2
def baseEnd_4632809 : Nat := 792952599158489949060535

theorem tailTrace_4632809 : CollatzResearch.WordTrace tailWord_4632809 prefixEnd_4632809 792952599158489949060535 := by
  unfold tailWord_4632809
  simp only [CollatzResearch.WordTrace]
  refine ⟨168972425873131688630005481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112648283915421125753336987 168972425873131688630005481)
  ·
    refine ⟨126729319404848766472504111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168972425873131688630005481 126729319404848766472504111)
    ·
      refine ⟨190093979107273149708756167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126729319404848766472504111 190093979107273149708756167)
      ·
        refine ⟨285140968660909724563134251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190093979107273149708756167 285140968660909724563134251)
        ·
          refine ⟨427711452991364586844701377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285140968660909724563134251 427711452991364586844701377)
          ·
            refine ⟨320783589743523440133526033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 427711452991364586844701377 320783589743523440133526033)
            ·
              refine ⟨240587692307642580100144525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320783589743523440133526033 240587692307642580100144525)
              ·
                refine ⟨90220384615365967537554197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240587692307642580100144525 90220384615365967537554197)
                ·
                  refine ⟨4229080528845279728322853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90220384615365967537554197 4229080528845279728322853)
                  ·
                    refine ⟨792952599158489949060535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4229080528845279728322853 792952599158489949060535)
                    ·
                      rfl

theorem cell23_4632809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 6, 4].length) (baseStart_4632809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632809 prefixEnd_4632809 := by exact prefixLift 4632809
  have htrace : WordTrace (prefixWord ++ tailWord_4632809) baseStart_4632809 baseEnd_4632809 := by
    simpa [prefixWord, tailWord_4632809, baseEnd_4632809] using wordTrace_append hprefix tailTrace_4632809
  have hstable : (prefixWord ++ tailWord_4632809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632809).length < 2 ^ (prefixWord ++ tailWord_4632809).sum := by decide
  have hdescent : baseEnd_4632809 < baseStart_4632809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632810 : List Nat := [3, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3]
def baseStart_4632810 : Nat := 118140960795 + 4632810 * 2 ^ 59
def prefixEnd_4632810 : Nat := 4983230072969 + 3 ^ 40 * 4632810 * 2
def baseEnd_4632810 : Nat := 2378858310956124343269101

theorem tailTrace_4632810 : CollatzResearch.WordTrace tailWord_4632810 prefixEnd_4632810 2378858310956124343269101 := by
  unfold tailWord_4632810
  simp only [CollatzResearch.WordTrace]
  refine ⟨42243115586532016450197971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112648308230752043867194589 42243115586532016450197971)
  ·
    refine ⟨63364673379798024675296957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42243115586532016450197971 63364673379798024675296957)
    ·
      refine ⟨23761752517424259253236359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63364673379798024675296957 23761752517424259253236359)
      ·
        refine ⟨35642628776136388879854539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23761752517424259253236359 35642628776136388879854539)
        ·
          refine ⟨53463943164204583319781809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35642628776136388879854539 53463943164204583319781809)
          ·
            refine ⟨40097957373153437489836357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53463943164204583319781809 40097957373153437489836357)
            ·
              refine ⟨7518367007466269529344317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40097957373153437489836357 7518367007466269529344317)
              ·
                refine ⟨2819387627799851073504119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7518367007466269529344317 2819387627799851073504119)
                ·
                  refine ⟨4229081441699776610256179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819387627799851073504119 4229081441699776610256179)
                  ·
                    refine ⟨6343622162549664915384269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4229081441699776610256179 6343622162549664915384269)
                    ·
                      refine ⟨2378858310956124343269101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6343622162549664915384269 2378858310956124343269101)
                      ·
                        rfl

theorem cell23_4632810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 4, 3, 1, 1, 3].length) (baseStart_4632810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632810 prefixEnd_4632810 := by exact prefixLift 4632810
  have htrace : WordTrace (prefixWord ++ tailWord_4632810) baseStart_4632810 baseEnd_4632810 := by
    simpa [prefixWord, tailWord_4632810, baseEnd_4632810] using wordTrace_append hprefix tailTrace_4632810
  have hstable : (prefixWord ++ tailWord_4632810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632810).length < 2 ^ (prefixWord ++ tailWord_4632810).sum := by decide
  have hdescent : baseEnd_4632810 < baseStart_4632810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632813 : List Nat := [1, 5, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_4632813 : Nat := 118140960795 + 4632813 * 2 ^ 59
def prefixEnd_4632813 : Nat := 4983230072969 + 3 ^ 40 * 4632813 * 2
def baseEnd_4632813 : Nat := 792953283799362610510529

theorem tailTrace_4632813 : CollatzResearch.WordTrace tailWord_4632813 prefixEnd_4632813 792953283799362610510529 := by
  unfold tailWord_4632813
  simp only [CollatzResearch.WordTrace]
  refine ⟨168972571765117197313151093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112648381176744798208767395 168972571765117197313151093)
  ·
    refine ⟨15841178602979737248107915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 168972571765117197313151093 15841178602979737248107915)
    ·
      refine ⟨23761767904469605872161873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15841178602979737248107915 23761767904469605872161873)
      ·
        refine ⟨17821325928352204404121405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23761767904469605872161873 17821325928352204404121405)
        ·
          refine ⟨6682997223132076651545527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17821325928352204404121405 6682997223132076651545527)
          ·
            refine ⟨10024495834698114977318291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6682997223132076651545527 10024495834698114977318291)
            ·
              refine ⟨15036743752047172465977437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10024495834698114977318291 15036743752047172465977437)
              ·
                refine ⟨5638778907017689674741539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15036743752047172465977437 5638778907017689674741539)
                ·
                  refine ⟨8458168360526534512112309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5638778907017689674741539 8458168360526534512112309)
                  ·
                    refine ⟨792953283799362610510529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8458168360526534512112309 792953283799362610510529)
                    ·
                      rfl

theorem cell23_4632813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_4632813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632813 prefixEnd_4632813 := by exact prefixLift 4632813
  have htrace : WordTrace (prefixWord ++ tailWord_4632813) baseStart_4632813 baseEnd_4632813 := by
    simpa [prefixWord, tailWord_4632813, baseEnd_4632813] using wordTrace_append hprefix tailTrace_4632813
  have hstable : (prefixWord ++ tailWord_4632813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632813).length < 2 ^ (prefixWord ++ tailWord_4632813).sum := by decide
  have hdescent : baseEnd_4632813 < baseStart_4632813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632819 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 5]
def baseStart_4632819 : Nat := 118140960795 + 4632819 * 2 ^ 59
def prefixEnd_4632819 : Nat := 4983230072969 + 3 ^ 40 * 4632819 * 2
def baseEnd_4632819 : Nat := 2378862932282014808056559

theorem tailTrace_4632819 : CollatzResearch.WordTrace tailWord_4632819 prefixEnd_4632819 2378862932282014808056559 := by
  unfold tailWord_4632819
  simp only [CollatzResearch.WordTrace]
  refine ⟨168972790603095460337869511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112648527068730306891913007 168972790603095460337869511)
  ·
    refine ⟨253459185904643190506804267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168972790603095460337869511 253459185904643190506804267)
    ·
      refine ⟨380188778856964785760206401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253459185904643190506804267 380188778856964785760206401)
      ·
        refine ⟨285141584142723589320154801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380188778856964785760206401 285141584142723589320154801)
        ·
          refine ⟨213856188107042691990116101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285141584142723589320154801 213856188107042691990116101)
          ·
            refine ⟨40098035270070504748146769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213856188107042691990116101 40098035270070504748146769)
            ·
              refine ⟨30073526452552878561110077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40098035270070504748146769 30073526452552878561110077)
              ·
                refine ⟨11277572419707329460416279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30073526452552878561110077 11277572419707329460416279)
                ·
                  refine ⟨16916358629560994190624419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11277572419707329460416279 16916358629560994190624419)
                  ·
                    refine ⟨25374537944341491285936629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16916358629560994190624419 25374537944341491285936629)
                    ·
                      refine ⟨2378862932282014808056559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25374537944341491285936629 2378862932282014808056559)
                      ·
                        rfl

theorem cell23_4632819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 5].length) (baseStart_4632819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632819 prefixEnd_4632819 := by exact prefixLift 4632819
  have htrace : WordTrace (prefixWord ++ tailWord_4632819) baseStart_4632819 baseEnd_4632819 := by
    simpa [prefixWord, tailWord_4632819, baseEnd_4632819] using wordTrace_append hprefix tailTrace_4632819
  have hstable : (prefixWord ++ tailWord_4632819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632819).length < 2 ^ (prefixWord ++ tailWord_4632819).sum := by decide
  have hdescent : baseEnd_4632819 < baseStart_4632819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632826 : List Nat := [3, 1, 1, 1, 1, 6, 1, 1, 4, 4]
def baseStart_4632826 : Nat := 118140960795 + 4632826 * 2 ^ 59
def prefixEnd_4632826 : Nat := 4983230072969 + 3 ^ 40 * 4632826 * 2
def baseEnd_4632826 : Nat := 792955508882198760223009

theorem tailTrace_4632826 : CollatzResearch.WordTrace tailWord_4632826 prefixEnd_4632826 792955508882198760223009 := by
  unfold tailWord_4632826
  simp only [CollatzResearch.WordTrace]
  refine ⟨42243261478517525133343583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112648697276046733688916221 42243261478517525133343583)
  ·
    refine ⟨63364892217776287700015375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42243261478517525133343583 63364892217776287700015375)
    ·
      refine ⟨95047338326664431550023063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63364892217776287700015375 95047338326664431550023063)
      ·
        refine ⟨142571007489996647325034595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95047338326664431550023063 142571007489996647325034595)
        ·
          refine ⟨213856511234994970987551893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142571007489996647325034595 213856511234994970987551893)
          ·
            refine ⟨10024523964140389265041495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 213856511234994970987551893 10024523964140389265041495)
            ·
              refine ⟨15036785946210583897562243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10024523964140389265041495 15036785946210583897562243)
              ·
                refine ⟨22555178919315875846343365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15036785946210583897562243 22555178919315875846343365)
                ·
                  refine ⟨4229096047371726721189381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22555178919315875846343365 4229096047371726721189381)
                  ·
                    refine ⟨792955508882198760223009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4229096047371726721189381 792955508882198760223009)
                    ·
                      rfl

theorem cell23_4632826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 1, 4, 4].length) (baseStart_4632826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632826 prefixEnd_4632826 := by exact prefixLift 4632826
  have htrace : WordTrace (prefixWord ++ tailWord_4632826) baseStart_4632826 baseEnd_4632826 := by
    simpa [prefixWord, tailWord_4632826, baseEnd_4632826] using wordTrace_append hprefix tailTrace_4632826
  have hstable : (prefixWord ++ tailWord_4632826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632826).length < 2 ^ (prefixWord ++ tailWord_4632826).sum := by decide
  have hdescent : baseEnd_4632826 < baseStart_4632826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632829 : List Nat := [1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 4]
def baseStart_4632829 : Nat := 118140960795 + 4632829 * 2 ^ 59
def prefixEnd_4632829 : Nat := 4983230072969 + 3 ^ 40 * 4632829 * 2
def baseEnd_4632829 : Nat := 2378868067088559768931513

theorem tailTrace_4632829 : CollatzResearch.WordTrace tailWord_4632829 prefixEnd_4632829 2378868067088559768931513 := by
  unfold tailWord_4632829
  simp only [CollatzResearch.WordTrace]
  refine ⟨168973155333059232045733541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112648770222039488030489027 168973155333059232045733541)
  ·
    refine ⟨31682466624948606008575039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168973155333059232045733541 31682466624948606008575039)
    ·
      refine ⟨47523699937422909012862559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31682466624948606008575039 47523699937422909012862559)
      ·
        refine ⟨71285549906134363519293839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47523699937422909012862559 71285549906134363519293839)
        ·
          refine ⟨106928324859201545278940759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71285549906134363519293839 106928324859201545278940759)
          ·
            refine ⟨160392487288802317918411139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106928324859201545278940759 160392487288802317918411139)
            ·
              refine ⟨240588730933203476877616709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160392487288802317918411139 240588730933203476877616709)
              ·
                refine ⟨45110387049975651914553133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240588730933203476877616709 45110387049975651914553133)
                ·
                  refine ⟨16916395143740869467957425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45110387049975651914553133 16916395143740869467957425)
                  ·
                    refine ⟨12687296357805652100968069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16916395143740869467957425 12687296357805652100968069)
                    ·
                      refine ⟨2378868067088559768931513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12687296357805652100968069 2378868067088559768931513)
                      ·
                        rfl

theorem cell23_4632829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_4632829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632829 prefixEnd_4632829 := by exact prefixLift 4632829
  have htrace : WordTrace (prefixWord ++ tailWord_4632829) baseStart_4632829 baseEnd_4632829 := by
    simpa [prefixWord, tailWord_4632829, baseEnd_4632829] using wordTrace_append hprefix tailTrace_4632829
  have hstable : (prefixWord ++ tailWord_4632829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632829).length < 2 ^ (prefixWord ++ tailWord_4632829).sum := by decide
  have hdescent : baseEnd_4632829 < baseStart_4632829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632843 : List Nat := [1, 1, 1, 1, 5, 2, 5, 1, 2, 4]
def baseStart_4632843 : Nat := 118140960795 + 4632843 * 2 ^ 59
def prefixEnd_4632843 : Nat := 4983230072969 + 3 ^ 40 * 4632843 * 2
def baseEnd_4632843 : Nat := 792958418605907571385483

theorem tailTrace_4632843 : CollatzResearch.WordTrace tailWord_4632843 prefixEnd_4632843 792958418605907571385483 := by
  unfold tailWord_4632843
  simp only [CollatzResearch.WordTrace]
  refine ⟨168973665955008512436743183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112649110636672341624495455 168973665955008512436743183)
  ·
    refine ⟨253460498932512768655114775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168973665955008512436743183 253460498932512768655114775)
    ·
      refine ⟨380190748398769152982672163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253460498932512768655114775 380190748398769152982672163)
      ·
        refine ⟨570286122598153729474008245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380190748398769152982672163 570286122598153729474008245)
        ·
          refine ⟨53464323993576912138188273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 570286122598153729474008245 53464323993576912138188273)
          ·
            refine ⟨40098242995182684103641205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53464323993576912138188273 40098242995182684103641205)
            ·
              refine ⟨3759210280798376634716363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40098242995182684103641205 3759210280798376634716363)
              ·
                refine ⟨5638815421197564952074545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759210280798376634716363 5638815421197564952074545)
                ·
                  refine ⟨4229111565898173714055909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5638815421197564952074545 4229111565898173714055909)
                  ·
                    refine ⟨792958418605907571385483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4229111565898173714055909 792958418605907571385483)
                    ·
                      rfl

theorem cell23_4632843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 5, 1, 2, 4].length) (baseStart_4632843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632843 prefixEnd_4632843 := by exact prefixLift 4632843
  have htrace : WordTrace (prefixWord ++ tailWord_4632843) baseStart_4632843 baseEnd_4632843 := by
    simpa [prefixWord, tailWord_4632843, baseEnd_4632843] using wordTrace_append hprefix tailTrace_4632843
  have hstable : (prefixWord ++ tailWord_4632843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632843).length < 2 ^ (prefixWord ++ tailWord_4632843).sum := by decide
  have hdescent : baseEnd_4632843 < baseStart_4632843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632883 : List Nat := [1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 3]
def baseStart_4632883 : Nat := 118140960795 + 4632883 * 2 ^ 59
def prefixEnd_4632883 : Nat := 4983230072969 + 3 ^ 40 * 4632883 * 2
def baseEnd_4632883 : Nat := 2378895795043902557656265

theorem tailTrace_4632883 : CollatzResearch.WordTrace tailWord_4632883 prefixEnd_4632883 2378895795043902557656265 := by
  unfold tailWord_4632883
  simp only [CollatzResearch.WordTrace]
  refine ⟨168975124874863599268199303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112650083249909066178799535 168975124874863599268199303)
  ·
    refine ⟨253462687312295398902298955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168975124874863599268199303 253462687312295398902298955)
    ·
      refine ⟨380194030968443098353448433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253462687312295398902298955 380194030968443098353448433)
      ·
        refine ⟨285145523226332323765086325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380194030968443098353448433 285145523226332323765086325)
        ·
          refine ⟨26732392802468655352976843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 285145523226332323765086325 26732392802468655352976843)
          ·
            refine ⟨40098589203702983029465265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26732392802468655352976843 40098589203702983029465265)
            ·
              refine ⟨30073941902777237272098949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40098589203702983029465265 30073941902777237272098949)
              ·
                refine ⟨5638864106770731988518553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30073941902777237272098949 5638864106770731988518553)
                ·
                  refine ⟨4229148080078048991388915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5638864106770731988518553 4229148080078048991388915)
                  ·
                    refine ⟨6343722120117073487083373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4229148080078048991388915 6343722120117073487083373)
                    ·
                      refine ⟨2378895795043902557656265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6343722120117073487083373 2378895795043902557656265)
                      ·
                        rfl

theorem cell23_4632883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 4, 2, 1, 3].length) (baseStart_4632883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632883 prefixEnd_4632883 := by exact prefixLift 4632883
  have htrace : WordTrace (prefixWord ++ tailWord_4632883) baseStart_4632883 baseEnd_4632883 := by
    simpa [prefixWord, tailWord_4632883, baseEnd_4632883] using wordTrace_append hprefix tailTrace_4632883
  have hstable : (prefixWord ++ tailWord_4632883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632883).length < 2 ^ (prefixWord ++ tailWord_4632883).sum := by decide
  have hdescent : baseEnd_4632883 < baseStart_4632883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632899 : List Nat := [1, 1, 1, 3, 1, 3, 2, 3, 2, 6]
def baseStart_4632899 : Nat := 118140960795 + 4632899 * 2 ^ 59
def prefixEnd_4632899 : Nat := 4983230072969 + 3 ^ 40 * 4632899 * 2
def baseEnd_4632899 : Nat := 792968003578124831685397

theorem tailTrace_4632899 : CollatzResearch.WordTrace tailWord_4632899 prefixEnd_4632899 792968003578124831685397 := by
  unfold tailWord_4632899
  simp only [CollatzResearch.WordTrace]
  refine ⟨168975708442805634000781751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112650472295203756000521167 168975708442805634000781751)
  ·
    refine ⟨253463562664208451001172627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168975708442805634000781751 253463562664208451001172627)
    ·
      refine ⟨380195343996312676501758941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253463562664208451001172627 380195343996312676501758941)
      ·
        refine ⟨142573253998617253688159603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380195343996312676501758941 142573253998617253688159603)
        ·
          refine ⟨213859880997925880532239405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142573253998617253688159603 213859880997925880532239405)
          ·
            refine ⟨80197455374222205199589777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213859880997925880532239405 80197455374222205199589777)
            ·
              refine ⟨60148091530666653899692333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80197455374222205199589777 60148091530666653899692333)
              ·
                refine ⟨22555534323999995212384625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60148091530666653899692333 22555534323999995212384625)
                ·
                  refine ⟨16916650742999996409288469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22555534323999995212384625 16916650742999996409288469)
                  ·
                    refine ⟨792968003578124831685397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16916650742999996409288469 792968003578124831685397)
                    ·
                      rfl

theorem cell23_4632899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 2, 6].length) (baseStart_4632899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632899 prefixEnd_4632899 := by exact prefixLift 4632899
  have htrace : WordTrace (prefixWord ++ tailWord_4632899) baseStart_4632899 baseEnd_4632899 := by
    simpa [prefixWord, tailWord_4632899, baseEnd_4632899] using wordTrace_append hprefix tailTrace_4632899
  have hstable : (prefixWord ++ tailWord_4632899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632899).length < 2 ^ (prefixWord ++ tailWord_4632899).sum := by decide
  have hdescent : baseEnd_4632899 < baseStart_4632899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632950 : List Nat := [5, 1, 1, 4, 1, 1, 1, 1, 2, 6]
def baseStart_4632950 : Nat := 118140960795 + 4632950 * 2 ^ 59
def prefixEnd_4632950 : Nat := 4983230072969 + 3 ^ 40 * 4632950 * 2
def baseEnd_4632950 : Nat := 792976732749251265172819

theorem tailTrace_4632950 : CollatzResearch.WordTrace tailWord_4632950 prefixEnd_4632950 792976732749251265172819 := by
  unfold tailWord_4632950
  simp only [CollatzResearch.WordTrace]
  refine ⟨10561098035351304356930519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112651712377080579807258869 10561098035351304356930519)
  ·
    refine ⟨15841647053026956535395779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10561098035351304356930519 15841647053026956535395779)
    ·
      refine ⟨23762470579540434803093669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15841647053026956535395779 23762470579540434803093669)
      ·
        refine ⟨4455463233663831525580063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23762470579540434803093669 4455463233663831525580063)
        ·
          refine ⟨6683194850495747288370095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4455463233663831525580063 6683194850495747288370095)
          ·
            refine ⟨10024792275743620932555143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6683194850495747288370095 10024792275743620932555143)
            ·
              refine ⟨15037188413615431398832715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10024792275743620932555143 15037188413615431398832715)
              ·
                refine ⟨22555782620423147098249073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15037188413615431398832715 22555782620423147098249073)
                ·
                  refine ⟨16916836965317360323686805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22555782620423147098249073 16916836965317360323686805)
                  ·
                    refine ⟨792976732749251265172819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16916836965317360323686805 792976732749251265172819)
                    ·
                      rfl

theorem cell23_4632950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_4632950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632950 prefixEnd_4632950 := by exact prefixLift 4632950
  have htrace : WordTrace (prefixWord ++ tailWord_4632950) baseStart_4632950 baseEnd_4632950 := by
    simpa [prefixWord, tailWord_4632950, baseEnd_4632950] using wordTrace_append hprefix tailTrace_4632950
  have hstable : (prefixWord ++ tailWord_4632950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632950).length < 2 ^ (prefixWord ++ tailWord_4632950).sum := by decide
  have hdescent : baseEnd_4632950 < baseStart_4632950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632959 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 3, 7]
def baseStart_4632959 : Nat := 118140960795 + 4632959 * 2 ^ 59
def prefixEnd_4632959 : Nat := 4983230072969 + 3 ^ 40 * 4632959 * 2
def baseEnd_4632959 : Nat := 792978273191214753435305

theorem tailTrace_4632959 : CollatzResearch.WordTrace tailWord_4632959 prefixEnd_4632959 792978273191214753435305 := by
  unfold tailWord_4632959
  simp only [CollatzResearch.WordTrace]
  refine ⟨168977896822588264247965931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112651931215058842831977287 168977896822588264247965931)
  ·
    refine ⟨253466845233882396371948897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168977896822588264247965931 253466845233882396371948897)
    ·
      refine ⟨190100133925411797278961673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253466845233882396371948897 190100133925411797278961673)
      ·
        refine ⟨142575100444058847959221255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190100133925411797278961673 142575100444058847959221255)
        ·
          refine ⟨213862650666088271938831883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142575100444058847959221255 213862650666088271938831883)
          ·
            refine ⟨320793975999132407908247825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213862650666088271938831883 320793975999132407908247825)
            ·
              refine ⟨240595481999349305931185869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320793975999132407908247825 240595481999349305931185869)
              ·
                refine ⟨90223305749755989724194701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240595481999349305931185869 90223305749755989724194701)
                ·
                  refine ⟨33833739656158496146573013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90223305749755989724194701 33833739656158496146573013)
                  ·
                    refine ⟨792978273191214753435305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33833739656158496146573013 792978273191214753435305)
                    ·
                      rfl

theorem cell23_4632959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 7].length) (baseStart_4632959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632959 prefixEnd_4632959 := by exact prefixLift 4632959
  have htrace : WordTrace (prefixWord ++ tailWord_4632959) baseStart_4632959 baseEnd_4632959 := by
    simpa [prefixWord, tailWord_4632959, baseEnd_4632959] using wordTrace_append hprefix tailTrace_4632959
  have hstable : (prefixWord ++ tailWord_4632959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632959).length < 2 ^ (prefixWord ++ tailWord_4632959).sum := by decide
  have hdescent : baseEnd_4632959 < baseStart_4632959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4632990 : List Nat := [4, 3, 1, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_4632990 : Nat := 118140960795 + 4632990 * 2 ^ 59
def prefixEnd_4632990 : Nat := 4983230072969 + 3 ^ 40 * 4632990 * 2
def baseEnd_4632990 : Nat := 2378950737473933639018273

theorem tailTrace_4632990 : CollatzResearch.WordTrace tailWord_4632990 prefixEnd_4632990 2378950737473933639018273 := by
  unfold tailWord_4632990
  simp only [CollatzResearch.WordTrace]
  refine ⟨21122378435684494567793053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112652684990317304361562949 21122378435684494567793053)
  ·
    refine ⟨7920891913381685462922395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21122378435684494567793053 7920891913381685462922395)
    ·
      refine ⟨11881337870072528194383593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7920891913381685462922395 11881337870072528194383593)
      ·
        refine ⟨8911003402554396145787695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11881337870072528194383593 8911003402554396145787695)
        ·
          refine ⟨13366505103831594218681543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8911003402554396145787695 13366505103831594218681543)
          ·
            refine ⟨20049757655747391328022315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13366505103831594218681543 20049757655747391328022315)
            ·
              refine ⟨30074636483621086992033473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20049757655747391328022315 30074636483621086992033473)
              ·
                refine ⟨22555977362715815244025105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30074636483621086992033473 22555977362715815244025105)
                ·
                  refine ⟨16916983022036861433018829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22555977362715815244025105 16916983022036861433018829)
                  ·
                    refine ⟨6343868633263823037382061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16916983022036861433018829 6343868633263823037382061)
                    ·
                      refine ⟨2378950737473933639018273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6343868633263823037382061 2378950737473933639018273)
                      ·
                        rfl

theorem cell23_4632990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_4632990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4632990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4632990 prefixEnd_4632990 := by exact prefixLift 4632990
  have htrace : WordTrace (prefixWord ++ tailWord_4632990) baseStart_4632990 baseEnd_4632990 := by
    simpa [prefixWord, tailWord_4632990, baseEnd_4632990] using wordTrace_append hprefix tailTrace_4632990
  have hstable : (prefixWord ++ tailWord_4632990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4632990).length < 2 ^ (prefixWord ++ tailWord_4632990).sum := by decide
  have hdescent : baseEnd_4632990 < baseStart_4632990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4632990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633053 : List Nat := [1, 4, 3, 1, 1, 1, 2, 4, 6]
def baseStart_4633053 : Nat := 118140960795 + 4633053 * 2 ^ 59
def prefixEnd_4633053 : Nat := 4983230072969 + 3 ^ 40 * 4633053 * 2
def baseEnd_4633053 : Nat := 264331454083907432503387

theorem tailTrace_4633053 : CollatzResearch.WordTrace tailWord_4633053 prefixEnd_4633053 264331454083907432503387 := by
  unfold tailWord_4633053
  simp only [CollatzResearch.WordTrace]
  refine ⟨168981325284247718301887813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112654216856165145534591875 168981325284247718301887813)
  ·
    refine ⟨31683998490796447181603965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168981325284247718301887813 31683998490796447181603965)
    ·
      refine ⟨11881499434048667693101487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31683998490796447181603965 11881499434048667693101487)
      ·
        refine ⟨17822249151073001539652231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11881499434048667693101487 17822249151073001539652231)
        ·
          refine ⟨26733373726609502309478347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17822249151073001539652231 26733373726609502309478347)
          ·
            refine ⟨40100060589914253464217521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26733373726609502309478347 40100060589914253464217521)
            ·
              refine ⟨30075045442435690098163141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40100060589914253464217521 30075045442435690098163141)
              ·
                refine ⟨5639071020456691893405589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30075045442435690098163141 5639071020456691893405589)
                ·
                  refine ⟨264331454083907432503387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5639071020456691893405589 264331454083907432503387)
                  ·
                    rfl

theorem cell23_4633053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_4633053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633053 prefixEnd_4633053 := by exact prefixLift 4633053
  have htrace : WordTrace (prefixWord ++ tailWord_4633053) baseStart_4633053 baseEnd_4633053 := by
    simpa [prefixWord, tailWord_4633053, baseEnd_4633053] using wordTrace_append hprefix tailTrace_4633053
  have hstable : (prefixWord ++ tailWord_4633053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633053).length < 2 ^ (prefixWord ++ tailWord_4633053).sum := by decide
  have hdescent : baseEnd_4633053 < baseStart_4633053 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633057 : List Nat := [1, 2, 3, 1, 2, 2, 5, 2, 1, 4]
def baseStart_4633057 : Nat := 118140960795 + 4633057 * 2 ^ 59
def prefixEnd_4633057 : Nat := 4983230072969 + 3 ^ 40 * 4633057 * 2
def baseEnd_4633057 : Nat := 792995046892594958960155

theorem tailTrace_4633057 : CollatzResearch.WordTrace tailWord_4633057 prefixEnd_4633057 792995046892594958960155 := by
  unfold tailWord_4633057
  simp only [CollatzResearch.WordTrace]
  refine ⟨168981471176233226985033425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112654314117488817990022283 168981471176233226985033425)
  ·
    refine ⟨126736103382174920238775069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168981471176233226985033425 126736103382174920238775069)
    ·
      refine ⟨47526038768315595089540651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126736103382174920238775069 47526038768315595089540651)
      ·
        refine ⟨71289058152473392634310977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47526038768315595089540651 71289058152473392634310977)
        ·
          refine ⟨53466793614355044475733233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71289058152473392634310977 53466793614355044475733233)
          ·
            refine ⟨40100095210766283356799925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53466793614355044475733233 40100095210766283356799925)
            ·
              refine ⟨3759383926009339064699993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40100095210766283356799925 3759383926009339064699993)
              ·
                refine ⟨2819537944507004298524995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759383926009339064699993 2819537944507004298524995)
                ·
                  refine ⟨4229306916760506447787493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819537944507004298524995 4229306916760506447787493)
                  ·
                    refine ⟨792995046892594958960155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4229306916760506447787493 792995046892594958960155)
                    ·
                      rfl

theorem cell23_4633057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_4633057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633057 prefixEnd_4633057 := by exact prefixLift 4633057
  have htrace : WordTrace (prefixWord ++ tailWord_4633057) baseStart_4633057 baseEnd_4633057 := by
    simpa [prefixWord, tailWord_4633057, baseEnd_4633057] using wordTrace_append hprefix tailTrace_4633057
  have hstable : (prefixWord ++ tailWord_4633057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633057).length < 2 ^ (prefixWord ++ tailWord_4633057).sum := by decide
  have hdescent : baseEnd_4633057 < baseStart_4633057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633070 : List Nat := [4, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_4633070 : Nat := 118140960795 + 4633070 * 2 ^ 59
def prefixEnd_4633070 : Nat := 4983230072969 + 3 ^ 40 * 4633070 * 2
def baseEnd_4633070 : Nat := 264332423991810369557545

theorem tailTrace_4633070 : CollatzResearch.WordTrace tailWord_4633070 prefixEnd_4633070 264332423991810369557545 := by
  unfold tailWord_4633070
  simp only [CollatzResearch.WordTrace]
  refine ⟨21122743165648266275657083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112654630216790753470171109 21122743165648266275657083)
  ·
    refine ⟨31684114748472399413485625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21122743165648266275657083 31684114748472399413485625)
    ·
      refine ⟨23763086061354299560114219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31684114748472399413485625 23763086061354299560114219)
      ·
        refine ⟨35644629092031449340171329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23763086061354299560114219 35644629092031449340171329)
        ·
          refine ⟨26733471819023587005128497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35644629092031449340171329 26733471819023587005128497)
          ·
            refine ⟨20050103864267690253846373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26733471819023587005128497 20050103864267690253846373)
            ·
              refine ⟨3759394474550191922596195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20050103864267690253846373 3759394474550191922596195)
              ·
                refine ⟨5639091711825287883894293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759394474550191922596195 5639091711825287883894293)
                ·
                  refine ⟨264332423991810369557545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5639091711825287883894293 264332423991810369557545)
                  ·
                    rfl

theorem cell23_4633070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_4633070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633070 prefixEnd_4633070 := by exact prefixLift 4633070
  have htrace : WordTrace (prefixWord ++ tailWord_4633070) baseStart_4633070 baseEnd_4633070 := by
    simpa [prefixWord, tailWord_4633070, baseEnd_4633070] using wordTrace_append hprefix tailTrace_4633070
  have hstable : (prefixWord ++ tailWord_4633070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633070).length < 2 ^ (prefixWord ++ tailWord_4633070).sum := by decide
  have hdescent : baseEnd_4633070 < baseStart_4633070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633114 : List Nat := [3, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3]
def baseStart_4633114 : Nat := 118140960795 + 4633114 * 2 ^ 59
def prefixEnd_4633114 : Nat := 4983230072969 + 3 ^ 40 * 4633114 * 2
def baseEnd_4633114 : Nat := 2379014409075091153867703

theorem tailTrace_4633114 : CollatzResearch.WordTrace tailWord_4633114 prefixEnd_4633114 2379014409075091153867703 := by
  unfold tailWord_4633114
  simp only [CollatzResearch.WordTrace]
  refine ⟨42245887534256681429964599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112655700091351150479905597 42245887534256681429964599)
  ·
    refine ⟨63368831301385022144946899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42245887534256681429964599 63368831301385022144946899)
    ·
      refine ⟨95053246952077533217420349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63368831301385022144946899 95053246952077533217420349)
      ·
        refine ⟨35644967607029074956532631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95053246952077533217420349 35644967607029074956532631)
        ·
          refine ⟨53467451410543612434798947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35644967607029074956532631 53467451410543612434798947)
          ·
            refine ⟨80201177115815418652198421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53467451410543612434798947 80201177115815418652198421)
            ·
              refine ⟨3759430177303847749321801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80201177115815418652198421 3759430177303847749321801)
              ·
                refine ⟨2819572632977885811991351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759430177303847749321801 2819572632977885811991351)
                ·
                  refine ⟨4229358949466828717987027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819572632977885811991351 4229358949466828717987027)
                  ·
                    refine ⟨6344038424200243076980541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4229358949466828717987027 6344038424200243076980541)
                    ·
                      refine ⟨2379014409075091153867703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6344038424200243076980541 2379014409075091153867703)
                      ·
                        rfl

theorem cell23_4633114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_4633114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633114 prefixEnd_4633114 := by exact prefixLift 4633114
  have htrace : WordTrace (prefixWord ++ tailWord_4633114) baseStart_4633114 baseEnd_4633114 := by
    simpa [prefixWord, tailWord_4633114, baseEnd_4633114] using wordTrace_append hprefix tailTrace_4633114
  have hstable : (prefixWord ++ tailWord_4633114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633114).length < 2 ^ (prefixWord ++ tailWord_4633114).sum := by decide
  have hdescent : baseEnd_4633114 < baseStart_4633114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633130 : List Nat := [3, 1, 4, 1, 1, 3, 2, 1, 1, 6]
def baseStart_4633130 : Nat := 118140960795 + 4633130 * 2 ^ 59
def prefixEnd_4633130 : Nat := 4983230072969 + 3 ^ 40 * 4633130 * 2
def baseEnd_4633130 : Nat := 793007541588521030422543

theorem tailTrace_4633130 : CollatzResearch.WordTrace tailWord_4633130 prefixEnd_4633130 793007541588521030422543 := by
  unfold tailWord_4633130
  simp only [CollatzResearch.WordTrace]
  refine ⟨42246033426242190113110211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112656089136645840301627229 42246033426242190113110211)
  ·
    refine ⟨63369050139363285169665317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42246033426242190113110211 63369050139363285169665317)
    ·
      refine ⟨11881696901130615969312247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63369050139363285169665317 11881696901130615969312247)
      ·
        refine ⟨17822545351695923953968371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11881696901130615969312247 17822545351695923953968371)
        ·
          refine ⟨26733818027543885930952557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17822545351695923953968371 26733818027543885930952557)
          ·
            refine ⟨10025181760328957224107209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26733818027543885930952557 10025181760328957224107209)
            ·
              refine ⟨7518886320246717918080407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10025181760328957224107209 7518886320246717918080407)
              ·
                refine ⟨11278329480370076877120611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7518886320246717918080407 11278329480370076877120611)
                ·
                  refine ⟨16917494220555115315680917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11278329480370076877120611 16917494220555115315680917)
                  ·
                    refine ⟨793007541588521030422543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16917494220555115315680917 793007541588521030422543)
                    ·
                      rfl

theorem cell23_4633130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_4633130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633130 prefixEnd_4633130 := by exact prefixLift 4633130
  have htrace : WordTrace (prefixWord ++ tailWord_4633130) baseStart_4633130 baseEnd_4633130 := by
    simpa [prefixWord, tailWord_4633130, baseEnd_4633130] using wordTrace_append hprefix tailTrace_4633130
  have hstable : (prefixWord ++ tailWord_4633130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633130).length < 2 ^ (prefixWord ++ tailWord_4633130).sum := by decide
  have hdescent : baseEnd_4633130 < baseStart_4633130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633143 : List Nat := [1, 1, 3, 1, 2, 3, 5, 7]
def baseStart_4633143 : Nat := 118140960795 + 4633143 * 2 ^ 59
def prefixEnd_4633143 : Nat := 4983230072969 + 3 ^ 40 * 4633143 * 2
def baseEnd_4633143 : Nat := 88112196296817464459447

theorem tailTrace_4633143 : CollatzResearch.WordTrace tailWord_4633143 prefixEnd_4633143 88112196296817464459447 := by
  unfold tailWord_4633143
  simp only [CollatzResearch.WordTrace]
  refine ⟨168984607853921663672664083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112656405235947775781776055 168984607853921663672664083)
  ·
    refine ⟨253476911780882495508996125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168984607853921663672664083 253476911780882495508996125)
    ·
      refine ⟨95053841917830935815873547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253476911780882495508996125 95053841917830935815873547)
      ·
        refine ⟨142580762876746403723810321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95053841917830935815873547 142580762876746403723810321)
        ·
          refine ⟨106935572157559802792857741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142580762876746403723810321 106935572157559802792857741)
          ·
            refine ⟨40100839559084926047321653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106935572157559802792857741 40100839559084926047321653)
            ·
              refine ⟨3759453708664211816936405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40100839559084926047321653 3759453708664211816936405)
              ·
                refine ⟨88112196296817464459447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3759453708664211816936405 88112196296817464459447)
                ·
                  rfl

theorem cell23_4633143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 5, 7].length) (baseStart_4633143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633143 prefixEnd_4633143 := by exact prefixLift 4633143
  have htrace : WordTrace (prefixWord ++ tailWord_4633143) baseStart_4633143 baseEnd_4633143 := by
    simpa [prefixWord, tailWord_4633143, baseEnd_4633143] using wordTrace_append hprefix tailTrace_4633143
  have hstable : (prefixWord ++ tailWord_4633143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633143).length < 2 ^ (prefixWord ++ tailWord_4633143).sum := by decide
  have hdescent : baseEnd_4633143 < baseStart_4633143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633157 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 1, 2, 3]
def baseStart_4633157 : Nat := 118140960795 + 4633157 * 2 ^ 59
def prefixEnd_4633157 : Nat := 4983230072969 + 3 ^ 40 * 4633157 * 2
def baseEnd_4633157 : Nat := 2379036488743234485630005

theorem tailTrace_4633157 : CollatzResearch.WordTrace tailWord_4633157 prefixEnd_4633157 2379036488743234485630005 := by
  unfold tailWord_4633157
  simp only [CollatzResearch.WordTrace]
  refine ⟨168985118475870944063673725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112656745650580629375782483 168985118475870944063673725)
  ·
    refine ⟨63369419428451604023877647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168985118475870944063673725 63369419428451604023877647)
    ·
      refine ⟨95054129142677406035816471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63369419428451604023877647 95054129142677406035816471)
      ·
        refine ⟨142581193714016109053724707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95054129142677406035816471 142581193714016109053724707)
        ·
          refine ⟨213871790571024163580587061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142581193714016109053724707 213871790571024163580587061)
          ·
            refine ⟨20050480366033515335680037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 213871790571024163580587061 20050480366033515335680037)
            ·
              refine ⟨3759465068631284125440007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20050480366033515335680037 3759465068631284125440007)
              ·
                refine ⟨5639197602946926188160011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759465068631284125440007 5639197602946926188160011)
                ·
                  refine ⟨8458796404420389282240017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5639197602946926188160011 8458796404420389282240017)
                  ·
                    refine ⟨6344097303315291961680013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8458796404420389282240017 6344097303315291961680013)
                    ·
                      refine ⟨2379036488743234485630005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6344097303315291961680013 2379036488743234485630005)
                      ·
                        rfl

theorem cell23_4633157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_4633157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633157 prefixEnd_4633157 := by exact prefixLift 4633157
  have htrace : WordTrace (prefixWord ++ tailWord_4633157) baseStart_4633157 baseEnd_4633157 := by
    simpa [prefixWord, tailWord_4633157, baseEnd_4633157] using wordTrace_append hprefix tailTrace_4633157
  have hstable : (prefixWord ++ tailWord_4633157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633157).length < 2 ^ (prefixWord ++ tailWord_4633157).sum := by decide
  have hdescent : baseEnd_4633157 < baseStart_4633157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633205 : List Nat := [1, 3, 4, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4633205 : Nat := 118140960795 + 4633205 * 2 ^ 59
def prefixEnd_4633205 : Nat := 4983230072969 + 3 ^ 40 * 4633205 * 2
def baseEnd_4633205 : Nat := 2379061135814650297829785

theorem tailTrace_4633205 : CollatzResearch.WordTrace tailWord_4633205 prefixEnd_4633205 2379061135814650297829785 := by
  unfold tailWord_4633205
  simp only [CollatzResearch.WordTrace]
  refine ⟨168986869179697048261421069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112657912786464698840947379 168986869179697048261421069)
  ·
    refine ⟨63370075942386393098032901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168986869179697048261421069 63370075942386393098032901)
    ·
      refine ⟨11881889239197448705881169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63370075942386393098032901 11881889239197448705881169)
      ·
        refine ⟨8911416929398086529410877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11881889239197448705881169 8911416929398086529410877)
        ·
          refine ⟨3341781348524282448529079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8911416929398086529410877 3341781348524282448529079)
          ·
            refine ⟨5012672022786423672793619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3341781348524282448529079 5012672022786423672793619)
            ·
              refine ⟨7519008034179635509190429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5012672022786423672793619 7519008034179635509190429)
              ·
                refine ⟨2819628012817363315946411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7519008034179635509190429 2819628012817363315946411)
                ·
                  refine ⟨4229442019226044973919617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819628012817363315946411 4229442019226044973919617)
                  ·
                    refine ⟨3172081514419533730439713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4229442019226044973919617 3172081514419533730439713)
                    ·
                      refine ⟨2379061135814650297829785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172081514419533730439713 2379061135814650297829785)
                      ·
                        rfl

theorem cell23_4633205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4633205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633205 prefixEnd_4633205 := by exact prefixLift 4633205
  have htrace : WordTrace (prefixWord ++ tailWord_4633205) baseStart_4633205 baseEnd_4633205 := by
    simpa [prefixWord, tailWord_4633205, baseEnd_4633205] using wordTrace_append hprefix tailTrace_4633205
  have hstable : (prefixWord ++ tailWord_4633205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633205).length < 2 ^ (prefixWord ++ tailWord_4633205).sum := by decide
  have hdescent : baseEnd_4633205 < baseStart_4633205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633230 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3]
def baseStart_4633230 : Nat := 118140960795 + 4633230 * 2 ^ 59
def prefixEnd_4633230 : Nat := 4983230072969 + 3 ^ 40 * 4633230 * 2
def baseEnd_4633230 : Nat := 2379073972831012700017169

theorem tailTrace_4633230 : CollatzResearch.WordTrace tailWord_4633230 prefixEnd_4633230 2379073972831012700017169 := by
  unfold tailWord_4633230
  simp only [CollatzResearch.WordTrace]
  refine ⟨21123472625575809691385143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112658520669737651687387429 21123472625575809691385143)
  ·
    refine ⟨31685208938363714537077715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21123472625575809691385143 31685208938363714537077715)
    ·
      refine ⟨47527813407545571805616573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31685208938363714537077715 47527813407545571805616573)
      ·
        refine ⟨17822930027829589427106215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47527813407545571805616573 17822930027829589427106215)
        ·
          refine ⟨26734395041744384140659323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17822930027829589427106215 26734395041744384140659323)
          ·
            refine ⟨40101592562616576210988985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26734395041744384140659323 40101592562616576210988985)
            ·
              refine ⟨30076194421962432158241739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40101592562616576210988985 30076194421962432158241739)
              ·
                refine ⟨45114291632943648237362609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30076194421962432158241739 45114291632943648237362609)
                ·
                  refine ⟨33835718724707736178021957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45114291632943648237362609 33835718724707736178021957)
                  ·
                    refine ⟨6344197260882700533379117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33835718724707736178021957 6344197260882700533379117)
                    ·
                      refine ⟨2379073972831012700017169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6344197260882700533379117 2379073972831012700017169)
                      ·
                        rfl

theorem cell23_4633230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_4633230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633230 prefixEnd_4633230 := by exact prefixLift 4633230
  have htrace : WordTrace (prefixWord ++ tailWord_4633230) baseStart_4633230 baseEnd_4633230 := by
    simpa [prefixWord, tailWord_4633230, baseEnd_4633230] using wordTrace_append hprefix tailTrace_4633230
  have hstable : (prefixWord ++ tailWord_4633230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633230).length < 2 ^ (prefixWord ++ tailWord_4633230).sum := by decide
  have hdescent : baseEnd_4633230 < baseStart_4633230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633243 : List Nat := [1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 3]
def baseStart_4633243 : Nat := 118140960795 + 4633243 * 2 ^ 59
def prefixEnd_4633243 : Nat := 4983230072969 + 3 ^ 40 * 4633243 * 2
def baseEnd_4633243 : Nat := 2379080648079521149154609

theorem tailTrace_4633243 : CollatzResearch.WordTrace tailWord_4633243 prefixEnd_4633243 2379080648079521149154609 := by
  unfold tailWord_4633243
  simp only [CollatzResearch.WordTrace]
  refine ⟨168988255153559380751304383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112658836769039587167536255 168988255153559380751304383)
  ·
    refine ⟨253482382730339071126956575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168988255153559380751304383 253482382730339071126956575)
    ·
      refine ⟨380223574095508606690434863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253482382730339071126956575 380223574095508606690434863)
      ·
        refine ⟨570335361143262910035652295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380223574095508606690434863 570335361143262910035652295)
        ·
          refine ⟨855503041714894365053478443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570335361143262910035652295 855503041714894365053478443)
          ·
            refine ⟨1283254562572341547580217665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855503041714894365053478443 1283254562572341547580217665)
            ·
              refine ⟨962440921929256160685163249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1283254562572341547580217665 962440921929256160685163249)
              ·
                refine ⟨721830691446942120513872437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 962440921929256160685163249 721830691446942120513872437)
                ·
                  refine ⟨67671627323150823798175541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 721830691446942120513872437 67671627323150823798175541)
                  ·
                    refine ⟨6344215061545389731078957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67671627323150823798175541 6344215061545389731078957)
                    ·
                      refine ⟨2379080648079521149154609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6344215061545389731078957 2379080648079521149154609)
                      ·
                        rfl

theorem cell23_4633243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 5, 5, 3].length) (baseStart_4633243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633243 prefixEnd_4633243 := by exact prefixLift 4633243
  have htrace : WordTrace (prefixWord ++ tailWord_4633243) baseStart_4633243 baseEnd_4633243 := by
    simpa [prefixWord, tailWord_4633243, baseEnd_4633243] using wordTrace_append hprefix tailTrace_4633243
  have hstable : (prefixWord ++ tailWord_4633243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633243).length < 2 ^ (prefixWord ++ tailWord_4633243).sum := by decide
  have hdescent : baseEnd_4633243 < baseStart_4633243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633280 : List Nat := [2, 1, 1, 2, 4, 2, 2, 2, 2, 5]
def baseStart_4633280 : Nat := 118140960795 + 4633280 * 2 ^ 59
def prefixEnd_4633280 : Nat := 4983230072969 + 3 ^ 40 * 4633280 * 2
def baseEnd_4633280 : Nat := 793033215621245834797313

theorem tailTrace_4633280 : CollatzResearch.WordTrace tailWord_4633280 prefixEnd_4633280 793033215621245834797313 := by
  unfold tailWord_4633280
  simp only [CollatzResearch.WordTrace]
  refine ⟨84494802327212668035200647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112659736436283557380267529 84494802327212668035200647)
  ·
    refine ⟨126742203490819002052800971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84494802327212668035200647 126742203490819002052800971)
    ·
      refine ⟨190113305236228503079201457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126742203490819002052800971 190113305236228503079201457)
      ·
        refine ⟨142584978927171377309401093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190113305236228503079201457 142584978927171377309401093)
        ·
          refine ⟨26734683548844633245512705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142584978927171377309401093 26734683548844633245512705)
          ·
            refine ⟨20051012661633474934134529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26734683548844633245512705 20051012661633474934134529)
            ·
              refine ⟨15038259496225106200600897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20051012661633474934134529 15038259496225106200600897)
              ·
                refine ⟨11278694622168829650450673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15038259496225106200600897 11278694622168829650450673)
                ·
                  refine ⟨8459020966626622237838005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11278694622168829650450673 8459020966626622237838005)
                  ·
                    refine ⟨793033215621245834797313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8459020966626622237838005 793033215621245834797313)
                    ·
                      rfl

theorem cell23_4633280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 2, 2, 5].length) (baseStart_4633280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633280 prefixEnd_4633280 := by exact prefixLift 4633280
  have htrace : WordTrace (prefixWord ++ tailWord_4633280) baseStart_4633280 baseEnd_4633280 := by
    simpa [prefixWord, tailWord_4633280, baseEnd_4633280] using wordTrace_append hprefix tailTrace_4633280
  have hstable : (prefixWord ++ tailWord_4633280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633280).length < 2 ^ (prefixWord ++ tailWord_4633280).sum := by decide
  have hdescent : baseEnd_4633280 < baseStart_4633280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633284 : List Nat := [2, 3, 3, 1, 1, 2, 4, 2, 5]
def baseStart_4633284 : Nat := 118140960795 + 4633284 * 2 ^ 59
def prefixEnd_4633284 : Nat := 4983230072969 + 3 ^ 40 * 4633284 * 2
def baseEnd_4633284 : Nat := 264344633420706165415769

theorem tailTrace_4633284 : CollatzResearch.WordTrace tailWord_4633284 prefixEnd_4633284 264344633420706165415769 := by
  unfold tailWord_4633284
  simp only [CollatzResearch.WordTrace]
  refine ⟨84494875273205422376773453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112659833697607229835697937 84494875273205422376773453)
  ·
    refine ⟨31685578227452033391290045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84494875273205422376773453 31685578227452033391290045)
    ·
      refine ⟨11882091835294512521733767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31685578227452033391290045 11882091835294512521733767)
      ·
        refine ⟨17823137752941768782600651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11882091835294512521733767 17823137752941768782600651)
        ·
          refine ⟨26734706629412653173900977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17823137752941768782600651 26734706629412653173900977)
          ·
            refine ⟨20051029972059489880425733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26734706629412653173900977 20051029972059489880425733)
            ·
              refine ⟨3759568119761154352579825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20051029972059489880425733 3759568119761154352579825)
              ·
                refine ⟨2819676089820865764434869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759568119761154352579825 2819676089820865764434869)
                ·
                  refine ⟨264344633420706165415769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819676089820865764434869 264344633420706165415769)
                  ·
                    rfl

theorem cell23_4633284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 4, 2, 5].length) (baseStart_4633284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633284 prefixEnd_4633284 := by exact prefixLift 4633284
  have htrace : WordTrace (prefixWord ++ tailWord_4633284) baseStart_4633284 baseEnd_4633284 := by
    simpa [prefixWord, tailWord_4633284, baseEnd_4633284] using wordTrace_append hprefix tailTrace_4633284
  have hstable : (prefixWord ++ tailWord_4633284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633284).length < 2 ^ (prefixWord ++ tailWord_4633284).sum := by decide
  have hdescent : baseEnd_4633284 < baseStart_4633284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633290 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5]
def baseStart_4633290 : Nat := 118140960795 + 4633290 * 2 ^ 59
def prefixEnd_4633290 : Nat := 4983230072969 + 3 ^ 40 * 4633290 * 2
def baseEnd_4633290 : Nat := 2379104781670282465266893

theorem tailTrace_4633290 : CollatzResearch.WordTrace tailWord_4633290 prefixEnd_4633290 2379104781670282465266893 := by
  unfold tailWord_4633290
  simp only [CollatzResearch.WordTrace]
  refine ⟨42247492346097276944566331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112659979589592738518843549 42247492346097276944566331)
  ·
    refine ⟨63371238519145915416849497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42247492346097276944566331 63371238519145915416849497)
    ·
      refine ⟨47528428889359436562637123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63371238519145915416849497 47528428889359436562637123)
      ·
        refine ⟨71292643334039154843955685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47528428889359436562637123 71292643334039154843955685)
        ·
          refine ⟨13367370625132341533241691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71292643334039154843955685 13367370625132341533241691)
          ·
            refine ⟨20051055937698512299862537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13367370625132341533241691 20051055937698512299862537)
            ·
              refine ⟨15038291953273884224896903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20051055937698512299862537 15038291953273884224896903)
              ·
                refine ⟨22557437929910826337345355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15038291953273884224896903 22557437929910826337345355)
                ·
                  refine ⟨33836156894866239506018033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22557437929910826337345355 33836156894866239506018033)
                  ·
                    refine ⟨25377117671149679629513525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33836156894866239506018033 25377117671149679629513525)
                    ·
                      refine ⟨2379104781670282465266893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25377117671149679629513525 2379104781670282465266893)
                      ·
                        rfl

theorem cell23_4633290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_4633290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633290 prefixEnd_4633290 := by exact prefixLift 4633290
  have htrace : WordTrace (prefixWord ++ tailWord_4633290) baseStart_4633290 baseEnd_4633290 := by
    simpa [prefixWord, tailWord_4633290, baseEnd_4633290] using wordTrace_append hprefix tailTrace_4633290
  have hstable : (prefixWord ++ tailWord_4633290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633290).length < 2 ^ (prefixWord ++ tailWord_4633290).sum := by decide
  have hdescent : baseEnd_4633290 < baseStart_4633290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633317 : List Nat := [1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_4633317 : Nat := 118140960795 + 4633317 * 2 ^ 59
def prefixEnd_4633317 : Nat := 4983230072969 + 3 ^ 40 * 4633317 * 2
def baseEnd_4633317 : Nat := 2379118645647953859629269

theorem tailTrace_4633317 : CollatzResearch.WordTrace tailWord_4633317 prefixEnd_4633317 2379118645647953859629269 := by
  unfold tailWord_4633317
  simp only [CollatzResearch.WordTrace]
  refine ⟨168990954155291291389498205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112660636103527527592998803 168990954155291291389498205)
  ·
    refine ⟨63371607808234234271061827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168990954155291291389498205 63371607808234234271061827)
    ·
      refine ⟨95057411712351351406592741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63371607808234234271061827 95057411712351351406592741)
      ·
        refine ⟨17823264696065878388736139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95057411712351351406592741 17823264696065878388736139)
        ·
          refine ⟨26734897044098817583104209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17823264696065878388736139 26734897044098817583104209)
          ·
            refine ⟨20051172783074113187328157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26734897044098817583104209 20051172783074113187328157)
            ·
              refine ⟨7519189793652792445248059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20051172783074113187328157 7519189793652792445248059)
              ·
                refine ⟨11278784690479188667872089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7519189793652792445248059 11278784690479188667872089)
                ·
                  refine ⟨8459088517859391500904067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11278784690479188667872089 8459088517859391500904067)
                  ·
                    refine ⟨12688632776789087251356101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8459088517859391500904067 12688632776789087251356101)
                    ·
                      refine ⟨2379118645647953859629269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12688632776789087251356101 2379118645647953859629269)
                      ·
                        rfl

theorem cell23_4633317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_4633317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633317 prefixEnd_4633317 := by exact prefixLift 4633317
  have htrace : WordTrace (prefixWord ++ tailWord_4633317) baseStart_4633317 baseEnd_4633317 := by
    simpa [prefixWord, tailWord_4633317, baseEnd_4633317] using wordTrace_append hprefix tailTrace_4633317
  have hstable : (prefixWord ++ tailWord_4633317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633317).length < 2 ^ (prefixWord ++ tailWord_4633317).sum := by decide
  have hdescent : baseEnd_4633317 < baseStart_4633317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633323 : List Nat := [1, 1, 1, 1, 2, 4, 1, 4, 8]
def baseStart_4633323 : Nat := 118140960795 + 4633323 * 2 ^ 59
def prefixEnd_4633323 : Nat := 4983230072969 + 3 ^ 40 * 4633323 * 2
def baseEnd_4633323 : Nat := 264346858503542315128249

theorem tailTrace_4633323 : CollatzResearch.WordTrace tailWord_4633323 prefixEnd_4633323 264346858503542315128249 := by
  unfold tailWord_4633323
  simp only [CollatzResearch.WordTrace]
  refine ⟨168991172993269554414216623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112660781995513036276144415 168991172993269554414216623)
  ·
    refine ⟨253486759489904331621324935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168991172993269554414216623 253486759489904331621324935)
    ·
      refine ⟨380230139234856497431987403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253486759489904331621324935 380230139234856497431987403)
      ·
        refine ⟨570345208852284746147981105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380230139234856497431987403 570345208852284746147981105)
        ·
          refine ⟨427758906639213559610985829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570345208852284746147981105 427758906639213559610985829)
          ·
            refine ⟨80204794994852542427059843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 427758906639213559610985829 80204794994852542427059843)
            ·
              refine ⟨120307192492278813640589765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80204794994852542427059843 120307192492278813640589765)
              ·
                refine ⟨22557598592302277557610581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120307192492278813640589765 22557598592302277557610581)
                ·
                  refine ⟨264346858503542315128249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22557598592302277557610581 264346858503542315128249)
                  ·
                    rfl

theorem cell23_4633323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 4, 8].length) (baseStart_4633323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633323 prefixEnd_4633323 := by exact prefixLift 4633323
  have htrace : WordTrace (prefixWord ++ tailWord_4633323) baseStart_4633323 baseEnd_4633323 := by
    simpa [prefixWord, tailWord_4633323, baseEnd_4633323] using wordTrace_append hprefix tailTrace_4633323
  have hstable : (prefixWord ++ tailWord_4633323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633323).length < 2 ^ (prefixWord ++ tailWord_4633323).sum := by decide
  have hdescent : baseEnd_4633323 < baseStart_4633323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633330 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4633330 : Nat := 118140960795 + 4633330 * 2 ^ 59
def prefixEnd_4633330 : Nat := 4983230072969 + 3 ^ 40 * 4633330 * 2
def baseEnd_4633330 : Nat := 2379125320896462308766709

theorem tailTrace_4633330 : CollatzResearch.WordTrace tailWord_4633330 prefixEnd_4633330 2379125320896462308766709 := by
  unfold tailWord_4633330
  simp only [CollatzResearch.WordTrace]
  refine ⟨42247857076061048652430361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112660952202829463073147629 42247857076061048652430361)
  ·
    refine ⟨31685892807045786489322771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42247857076061048652430361 31685892807045786489322771)
    ·
      refine ⟨47528839210568679733984157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31685892807045786489322771 47528839210568679733984157)
      ·
        refine ⟨17823314703963254900244059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47528839210568679733984157 17823314703963254900244059)
        ·
          refine ⟨26734972055944882350366089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17823314703963254900244059 26734972055944882350366089)
          ·
            refine ⟨20051229041958661762774567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26734972055944882350366089 20051229041958661762774567)
            ·
              refine ⟨30076843562937992644161851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20051229041958661762774567 30076843562937992644161851)
              ·
                refine ⟨45115265344406988966242777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30076843562937992644161851 45115265344406988966242777)
                ·
                  refine ⟨33836449008305241724682083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45115265344406988966242777 33836449008305241724682083)
                  ·
                    refine ⟨50754673512457862587023125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33836449008305241724682083 50754673512457862587023125)
                    ·
                      refine ⟨2379125320896462308766709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50754673512457862587023125 2379125320896462308766709)
                      ·
                        rfl

theorem cell23_4633330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4633330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633330 prefixEnd_4633330 := by exact prefixLift 4633330
  have htrace : WordTrace (prefixWord ++ tailWord_4633330) baseStart_4633330 baseEnd_4633330 := by
    simpa [prefixWord, tailWord_4633330, baseEnd_4633330] using wordTrace_append hprefix tailTrace_4633330
  have hstable : (prefixWord ++ tailWord_4633330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633330).length < 2 ^ (prefixWord ++ tailWord_4633330).sum := by decide
  have hdescent : baseEnd_4633330 < baseStart_4633330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633340 : List Nat := [2, 2, 2, 1, 3, 3, 1, 1, 8]
def baseStart_4633340 : Nat := 118140960795 + 4633340 * 2 ^ 59
def prefixEnd_4633340 : Nat := 4983230072969 + 3 ^ 40 * 4633340 * 2
def baseEnd_4633340 : Nat := 264347828411445252182407

theorem tailTrace_4633340 : CollatzResearch.WordTrace tailWord_4633340 prefixEnd_4633340 264347828411445252182407 := by
  unfold tailWord_4633340
  simp only [CollatzResearch.WordTrace]
  refine ⟨84495896517103983158792737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112661195356138644211723649 84495896517103983158792737)
  ·
    refine ⟨63371922387827987369094553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84495896517103983158792737 63371922387827987369094553)
    ·
      refine ⟨47528941790870990526820915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63371922387827987369094553 47528941790870990526820915)
      ·
        refine ⟨71293412686306485790231373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47528941790870990526820915 71293412686306485790231373)
        ·
          refine ⟨26735029757364932171336765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71293412686306485790231373 26735029757364932171336765)
          ·
            refine ⟨10025636159011849564251287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26735029757364932171336765 10025636159011849564251287)
            ·
              refine ⟨15038454238517774346376931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10025636159011849564251287 15038454238517774346376931)
              ·
                refine ⟨22557681357776661519565397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15038454238517774346376931 22557681357776661519565397)
                ·
                  refine ⟨264347828411445252182407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22557681357776661519565397 264347828411445252182407)
                  ·
                    rfl

theorem cell23_4633340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 8].length) (baseStart_4633340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633340 prefixEnd_4633340 := by exact prefixLift 4633340
  have htrace : WordTrace (prefixWord ++ tailWord_4633340) baseStart_4633340 baseEnd_4633340 := by
    simpa [prefixWord, tailWord_4633340, baseEnd_4633340] using wordTrace_append hprefix tailTrace_4633340
  have hstable : (prefixWord ++ tailWord_4633340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633340).length < 2 ^ (prefixWord ++ tailWord_4633340).sum := by decide
  have hdescent : baseEnd_4633340 < baseStart_4633340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633377 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 1, 5, 2]
def baseStart_4633377 : Nat := 118140960795 + 4633377 * 2 ^ 59
def prefixEnd_4633377 : Nat := 4983230072969 + 3 ^ 40 * 4633377 * 2
def baseEnd_4633377 : Nat := 2379149454487223624878993

theorem tailTrace_4633377 : CollatzResearch.WordTrace tailWord_4633377 prefixEnd_4633377 2379149454487223624878993 := by
  unfold tailWord_4633377
  simp only [CollatzResearch.WordTrace]
  refine ⟨168993142535073921636682385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112662095023382614424454923 168993142535073921636682385)
  ·
    refine ⟨126744856901305441227511789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168993142535073921636682385 126744856901305441227511789)
    ·
      refine ⟨47529321337989540460316921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126744856901305441227511789 47529321337989540460316921)
      ·
        refine ⟨35646991003492155345237691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47529321337989540460316921 35646991003492155345237691)
        ·
          refine ⟨53470486505238233017856537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35646991003492155345237691 53470486505238233017856537)
          ·
            refine ⟨40102864878928674763392403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53470486505238233017856537 40102864878928674763392403)
            ·
              refine ⟨60154297318393012145088605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40102864878928674763392403 60154297318393012145088605)
              ·
                refine ⟨22557861494397379554408227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60154297318393012145088605 22557861494397379554408227)
                ·
                  refine ⟨33836792241596069331612341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22557861494397379554408227 33836792241596069331612341)
                  ·
                    refine ⟨3172199272649631499838657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33836792241596069331612341 3172199272649631499838657)
                    ·
                      refine ⟨2379149454487223624878993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172199272649631499838657 2379149454487223624878993)
                      ·
                        rfl

theorem cell23_4633377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_4633377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633377 prefixEnd_4633377 := by exact prefixLift 4633377
  have htrace : WordTrace (prefixWord ++ tailWord_4633377) baseStart_4633377 baseEnd_4633377 := by
    simpa [prefixWord, tailWord_4633377, baseEnd_4633377] using wordTrace_append hprefix tailTrace_4633377
  have hstable : (prefixWord ++ tailWord_4633377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633377).length < 2 ^ (prefixWord ++ tailWord_4633377).sum := by decide
  have hdescent : baseEnd_4633377 < baseStart_4633377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633394 : List Nat := [3, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2]
def baseStart_4633394 : Nat := 118140960795 + 4633394 * 2 ^ 59
def prefixEnd_4633394 : Nat := 4983230072969 + 3 ^ 40 * 4633394 * 2
def baseEnd_4633394 : Nat := 2379158183658350058366415

theorem tailTrace_4633394 : CollatzResearch.WordTrace tailWord_4633394 prefixEnd_4633394 2379158183658350058366415 := by
  unfold tailWord_4633394
  simp only [CollatzResearch.WordTrace]
  refine ⟨42248440644003083385012809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112662508384008222360034157 42248440644003083385012809)
  ·
    refine ⟨31686330483002312538759607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42248440644003083385012809 31686330483002312538759607)
    ·
      refine ⟨47529495724503468808139411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31686330483002312538759607 47529495724503468808139411)
      ·
        refine ⟨71294243586755203212209117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47529495724503468808139411 71294243586755203212209117)
        ·
          refine ⟨26735341345033201204578419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71294243586755203212209117 26735341345033201204578419)
          ·
            refine ⟨40103012017549801806867629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26735341345033201204578419 40103012017549801806867629)
            ·
              refine ⟨15038629506581175677575361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40103012017549801806867629 15038629506581175677575361)
              ·
                refine ⟨11278972129935881758181521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15038629506581175677575361 11278972129935881758181521)
                ·
                  refine ⟨8459229097451911318636141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11278972129935881758181521 8459229097451911318636141)
                  ·
                    refine ⟨3172210911544466744488553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8459229097451911318636141 3172210911544466744488553)
                    ·
                      refine ⟨2379158183658350058366415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172210911544466744488553 2379158183658350058366415)
                      ·
                        rfl

theorem cell23_4633394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2].length) (baseStart_4633394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633394 prefixEnd_4633394 := by exact prefixLift 4633394
  have htrace : WordTrace (prefixWord ++ tailWord_4633394) baseStart_4633394 baseEnd_4633394 := by
    simpa [prefixWord, tailWord_4633394, baseEnd_4633394] using wordTrace_append hprefix tailTrace_4633394
  have hstable : (prefixWord ++ tailWord_4633394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633394).length < 2 ^ (prefixWord ++ tailWord_4633394).sum := by decide
  have hdescent : baseEnd_4633394 < baseStart_4633394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633424 : List Nat := [2, 1, 1, 1, 1, 4, 2, 4, 3, 2, 2]
def baseStart_4633424 : Nat := 118140960795 + 4633424 * 2 ^ 59
def prefixEnd_4633424 : Nat := 4983230072969 + 3 ^ 40 * 4633424 * 2
def baseEnd_4633424 : Nat := 2379173588077984940991277

theorem tailTrace_4633424 : CollatzResearch.WordTrace tailWord_4633424 prefixEnd_4633424 2379173588077984940991277 := by
  unfold tailWord_4633424
  simp only [CollatzResearch.WordTrace]
  refine ⟨84497428382951824331821663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112663237843935765775762217 84497428382951824331821663)
  ·
    refine ⟨126746142574427736497732495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84497428382951824331821663 126746142574427736497732495)
    ·
      refine ⟨190119213861641604746598743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126746142574427736497732495 190119213861641604746598743)
      ·
        refine ⟨285178820792462407119898115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190119213861641604746598743 285178820792462407119898115)
        ·
          refine ⟨427768231188693610679847173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285178820792462407119898115 427768231188693610679847173)
          ·
            refine ⟨80206543347880052002471345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 427768231188693610679847173 80206543347880052002471345)
            ·
              refine ⟨60154907510910039001853509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80206543347880052002471345 60154907510910039001853509)
              ·
                refine ⟨11279045158295632312847533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60154907510910039001853509 11279045158295632312847533)
                ·
                  refine ⟨4229641934360862117317825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11279045158295632312847533 4229641934360862117317825)
                  ·
                    refine ⟨3172231450770646587988369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4229641934360862117317825 3172231450770646587988369)
                    ·
                      refine ⟨2379173588077984940991277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172231450770646587988369 2379173588077984940991277)
                      ·
                        rfl

theorem cell23_4633424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 4, 3, 2, 2].length) (baseStart_4633424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633424 prefixEnd_4633424 := by exact prefixLift 4633424
  have htrace : WordTrace (prefixWord ++ tailWord_4633424) baseStart_4633424 baseEnd_4633424 := by
    simpa [prefixWord, tailWord_4633424, baseEnd_4633424] using wordTrace_append hprefix tailTrace_4633424
  have hstable : (prefixWord ++ tailWord_4633424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633424).length < 2 ^ (prefixWord ++ tailWord_4633424).sum := by decide
  have hdescent : baseEnd_4633424 < baseStart_4633424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633444 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 1, 1, 5]
def baseStart_4633444 : Nat := 118140960795 + 4633444 * 2 ^ 59
def prefixEnd_4633444 : Nat := 4983230072969 + 3 ^ 40 * 4633444 * 2
def baseEnd_4633444 : Nat := 2379183857691074862741185

theorem tailTrace_4633444 : CollatzResearch.WordTrace tailWord_4633444 prefixEnd_4633444 2379183857691074862741185 := by
  unfold tailWord_4633444
  simp only [CollatzResearch.WordTrace]
  refine ⟨84497793112915596039685693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112663724150554128052914257 84497793112915596039685693)
  ·
    refine ⟨31686672417343348514882135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84497793112915596039685693 31686672417343348514882135)
    ·
      refine ⟨47530008626015022772323203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31686672417343348514882135 47530008626015022772323203)
      ·
        refine ⟨71295012939022534158484805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47530008626015022772323203 71295012939022534158484805)
        ·
          refine ⟨13367814926066725154715901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71295012939022534158484805 13367814926066725154715901)
          ·
            refine ⟨5012930597275021933018463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13367814926066725154715901 5012930597275021933018463)
            ·
              refine ⟨7519395895912532899527695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5012930597275021933018463 7519395895912532899527695)
              ·
                refine ⟨11279093843868799349291543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7519395895912532899527695 11279093843868799349291543)
                ·
                  refine ⟨16918640765803199023937315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11279093843868799349291543 16918640765803199023937315)
                  ·
                    refine ⟨25377961148704798535905973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16918640765803199023937315 25377961148704798535905973)
                    ·
                      refine ⟨2379183857691074862741185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25377961148704798535905973 2379183857691074862741185)
                      ·
                        rfl

theorem cell23_4633444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 1, 5].length) (baseStart_4633444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633444 prefixEnd_4633444 := by exact prefixLift 4633444
  have htrace : WordTrace (prefixWord ++ tailWord_4633444) baseStart_4633444 baseEnd_4633444 := by
    simpa [prefixWord, tailWord_4633444, baseEnd_4633444] using wordTrace_append hprefix tailTrace_4633444
  have hstable : (prefixWord ++ tailWord_4633444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633444).length < 2 ^ (prefixWord ++ tailWord_4633444).sum := by decide
  have hdescent : baseEnd_4633444 < baseStart_4633444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633484 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 3, 3, 2]
def baseStart_4633484 : Nat := 118140960795 + 4633484 * 2 ^ 59
def prefixEnd_4633484 : Nat := 4983230072969 + 3 ^ 40 * 4633484 * 2
def baseEnd_4633484 : Nat := 2379204396917254706241001

theorem tailTrace_4633484 : CollatzResearch.WordTrace tailWord_4633484 prefixEnd_4633484 2379204396917254706241001 := by
  unfold tailWord_4633484
  simp only [CollatzResearch.WordTrace]
  refine ⟨84498522572843139455413753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112664696763790852607218337 84498522572843139455413753)
  ·
    refine ⟨63373891929632354591560315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84498522572843139455413753 63373891929632354591560315)
    ·
      refine ⟨95060837894448531887340473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63373891929632354591560315 95060837894448531887340473)
      ·
        refine ⟨71295628420836398915505355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95060837894448531887340473 71295628420836398915505355)
        ·
          refine ⟨106943442631254598373258033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71295628420836398915505355 106943442631254598373258033)
          ·
            refine ⟨80207581973440948779943525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106943442631254598373258033 80207581973440948779943525)
            ·
              refine ⟨15038921620020177896239411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80207581973440948779943525 15038921620020177896239411)
              ·
                refine ⟨22558382430030266844359117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15038921620020177896239411 22558382430030266844359117)
                ·
                  refine ⟨8459393411261350066634669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22558382430030266844359117 8459393411261350066634669)
                  ·
                    refine ⟨3172272529223006274988001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8459393411261350066634669 3172272529223006274988001)
                    ·
                      refine ⟨2379204396917254706241001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172272529223006274988001 2379204396917254706241001)
                      ·
                        rfl

theorem cell23_4633484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_4633484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633484 prefixEnd_4633484 := by exact prefixLift 4633484
  have htrace : WordTrace (prefixWord ++ tailWord_4633484) baseStart_4633484 baseEnd_4633484 := by
    simpa [prefixWord, tailWord_4633484, baseEnd_4633484] using wordTrace_append hprefix tailTrace_4633484
  have hstable : (prefixWord ++ tailWord_4633484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633484).length < 2 ^ (prefixWord ++ tailWord_4633484).sum := by decide
  have hdescent : baseEnd_4633484 < baseStart_4633484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633501 : List Nat := [1, 4, 2, 1, 2, 1, 3, 3, 1, 3, 2]
def baseStart_4633501 : Nat := 118140960795 + 4633501 * 2 ^ 59
def prefixEnd_4633501 : Nat := 4983230072969 + 3 ^ 40 * 4633501 * 2
def baseEnd_4633501 : Nat := 2379213126088381139728423

theorem tailTrace_4633501 : CollatzResearch.WordTrace tailWord_4633501 prefixEnd_4633501 2379213126088381139728423 := by
  unfold tailWord_4633501
  simp only [CollatzResearch.WordTrace]
  refine ⟨168997665186624690814196357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112665110124416460542797571 168997665186624690814196357)
  ·
    refine ⟨31687062222492129527661817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168997665186624690814196357 31687062222492129527661817)
    ·
      refine ⟨23765296666869097145746363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31687062222492129527661817 23765296666869097145746363)
      ·
        refine ⟨35647945000303645718619545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23765296666869097145746363 35647945000303645718619545)
        ·
          refine ⟨26735958750227734288964659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35647945000303645718619545 26735958750227734288964659)
          ·
            refine ⟨40103938125341601433446989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26735958750227734288964659 40103938125341601433446989)
            ·
              refine ⟨15038976797003100537542621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40103938125341601433446989 15038976797003100537542621)
              ·
                refine ⟨5639616298876162701578483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15038976797003100537542621 5639616298876162701578483)
                ·
                  refine ⟨8459424448314244052367725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5639616298876162701578483 8459424448314244052367725)
                  ·
                    refine ⟨3172284168117841519637897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8459424448314244052367725 3172284168117841519637897)
                    ·
                      refine ⟨2379213126088381139728423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172284168117841519637897 2379213126088381139728423)
                      ·
                        rfl

theorem cell23_4633501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_4633501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633501 prefixEnd_4633501 := by exact prefixLift 4633501
  have htrace : WordTrace (prefixWord ++ tailWord_4633501) baseStart_4633501 baseEnd_4633501 := by
    simpa [prefixWord, tailWord_4633501, baseEnd_4633501] using wordTrace_append hprefix tailTrace_4633501
  have hstable : (prefixWord ++ tailWord_4633501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633501).length < 2 ^ (prefixWord ++ tailWord_4633501).sum := by decide
  have hdescent : baseEnd_4633501 < baseStart_4633501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633527 : List Nat := [1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 4]
def baseStart_4633527 : Nat := 118140960795 + 4633527 * 2 ^ 59
def prefixEnd_4633527 : Nat := 4983230072969 + 3 ^ 40 * 4633527 * 2
def baseEnd_4633527 : Nat := 2379226476585398038003303

theorem tailTrace_4633527 : CollatzResearch.WordTrace tailWord_4633527 prefixEnd_4633527 2379226476585398038003303 := by
  unfold tailWord_4633527
  simp only [CollatzResearch.WordTrace]
  refine ⟨168998613484530497254642835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112665742323020331503095223 168998613484530497254642835)
  ·
    refine ⟨253497920226795745881964253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168998613484530497254642835 253497920226795745881964253)
    ·
      refine ⟨95061720085048404705736595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253497920226795745881964253 95061720085048404705736595)
      ·
        refine ⟨142592580127572607058604893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95061720085048404705736595 142592580127572607058604893)
        ·
          refine ⟨53472217547839727646976835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142592580127572607058604893 53472217547839727646976835)
          ·
            refine ⟨80208326321759591470465253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53472217547839727646976835 80208326321759591470465253)
            ·
              refine ⟨15039061185329923400712235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80208326321759591470465253 15039061185329923400712235)
              ·
                refine ⟨22558591777994885101068353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15039061185329923400712235 22558591777994885101068353)
                ·
                  refine ⟨16918943833496163825801265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22558591777994885101068353 16918943833496163825801265)
                  ·
                    refine ⟨12689207875122122869350949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16918943833496163825801265 12689207875122122869350949)
                    ·
                      refine ⟨2379226476585398038003303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12689207875122122869350949 2379226476585398038003303)
                      ·
                        rfl

theorem cell23_4633527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_4633527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633527 prefixEnd_4633527 := by exact prefixLift 4633527
  have htrace : WordTrace (prefixWord ++ tailWord_4633527) baseStart_4633527 baseEnd_4633527 := by
    simpa [prefixWord, tailWord_4633527, baseEnd_4633527] using wordTrace_append hprefix tailTrace_4633527
  have hstable : (prefixWord ++ tailWord_4633527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633527).length < 2 ^ (prefixWord ++ tailWord_4633527).sum := by decide
  have hdescent : baseEnd_4633527 < baseStart_4633527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633571 : List Nat := [1, 1, 1, 6, 1, 1, 5, 2, 5]
def baseStart_4633571 : Nat := 118140960795 + 4633571 * 2 ^ 59
def prefixEnd_4633571 : Nat := 4983230072969 + 3 ^ 40 * 4633571 * 2
def baseEnd_4633571 : Nat := 264361007748243985094789

theorem tailTrace_4633571 : CollatzResearch.WordTrace tailWord_4633571 prefixEnd_4633571 264361007748243985094789 := by
  unfold tailWord_4633571
  simp only [CollatzResearch.WordTrace]
  refine ⟨169000218296371092769244567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112666812197580728512829711 169000218296371092769244567)
  ·
    refine ⟨253500327444556639153866851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169000218296371092769244567 253500327444556639153866851)
    ·
      refine ⟨380250491166834958730800277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253500327444556639153866851 380250491166834958730800277)
      ·
        refine ⟨17824241773445388690506263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 380250491166834958730800277 17824241773445388690506263)
        ·
          refine ⟨26736362660168083035759395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17824241773445388690506263 26736362660168083035759395)
          ·
            refine ⟨40104543990252124553639093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26736362660168083035759395 40104543990252124553639093)
            ·
              refine ⟨3759800999086136676903665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40104543990252124553639093 3759800999086136676903665)
              ·
                refine ⟨2819850749314602507677749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759800999086136676903665 2819850749314602507677749)
                ·
                  refine ⟨264361007748243985094789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2819850749314602507677749 264361007748243985094789)
                  ·
                    rfl

theorem cell23_4633571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 5, 2, 5].length) (baseStart_4633571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633571 prefixEnd_4633571 := by exact prefixLift 4633571
  have htrace : WordTrace (prefixWord ++ tailWord_4633571) baseStart_4633571 baseEnd_4633571 := by
    simpa [prefixWord, tailWord_4633571, baseEnd_4633571] using wordTrace_append hprefix tailTrace_4633571
  have hstable : (prefixWord ++ tailWord_4633571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633571).length < 2 ^ (prefixWord ++ tailWord_4633571).sum := by decide
  have hdescent : baseEnd_4633571 < baseStart_4633571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633582 : List Nat := [4, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2]
def baseStart_4633582 : Nat := 118140960795 + 4633582 * 2 ^ 59
def prefixEnd_4633582 : Nat := 4983230072969 + 3 ^ 40 * 4633582 * 2
def baseEnd_4633582 : Nat := 2379254718021395322815551

theorem tailTrace_4633582 : CollatzResearch.WordTrace tailWord_4633582 prefixEnd_4633582 2379254718021395322815551 := by
  unfold tailWord_4633582
  simp only [CollatzResearch.WordTrace]
  refine ⟨21125077437416405205986875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112667079666220827765263333 21125077437416405205986875)
  ·
    refine ⟨31687616156124607808980313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21125077437416405205986875 31687616156124607808980313)
    ·
      refine ⟨23765712117093455856735235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31687616156124607808980313 23765712117093455856735235)
      ·
        refine ⟨35648568175640183785102853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23765712117093455856735235 35648568175640183785102853)
        ·
          refine ⟨6684106532932534459706785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35648568175640183785102853 6684106532932534459706785)
          ·
            refine ⟨5013079899699400844780089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6684106532932534459706785 5013079899699400844780089)
            ·
              refine ⟨3759809924774550633585067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5013079899699400844780089 3759809924774550633585067)
              ·
                refine ⟨5639714887161825950377601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3759809924774550633585067 5639714887161825950377601)
                ·
                  refine ⟨4229786165371369462783201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5639714887161825950377601 4229786165371369462783201)
                  ·
                    refine ⟨3172339624028527097087401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4229786165371369462783201 3172339624028527097087401)
                    ·
                      refine ⟨2379254718021395322815551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172339624028527097087401 2379254718021395322815551)
                      ·
                        rfl

theorem cell23_4633582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 2, 1, 2, 2, 2].length) (baseStart_4633582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633582 prefixEnd_4633582 := by exact prefixLift 4633582
  have htrace : WordTrace (prefixWord ++ tailWord_4633582) baseStart_4633582 baseEnd_4633582 := by
    simpa [prefixWord, tailWord_4633582, baseEnd_4633582] using wordTrace_append hprefix tailTrace_4633582
  have hstable : (prefixWord ++ tailWord_4633582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633582).length < 2 ^ (prefixWord ++ tailWord_4633582).sum := by decide
  have hdescent : baseEnd_4633582 < baseStart_4633582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633665 : List Nat := [1, 2, 5, 1, 3, 1, 2, 3, 1, 4]
def baseStart_4633665 : Nat := 118140960795 + 4633665 * 2 ^ 59
def prefixEnd_4633665 : Nat := 4983230072969 + 3 ^ 40 * 4633665 * 2
def baseEnd_4633665 : Nat := 793099112305239499359223

theorem tailTrace_4633665 : CollatzResearch.WordTrace tailWord_4633665 prefixEnd_4633665 793099112305239499359223 := by
  unfold tailWord_4633665
  simp only [CollatzResearch.WordTrace]
  refine ⟨169003646758030546823166449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112669097838687031215444299 169003646758030546823166449)
  ·
    refine ⟨126752735068522910117374837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169003646758030546823166449 126752735068522910117374837)
    ·
      refine ⟨11883068912674022823503891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126752735068522910117374837 11883068912674022823503891)
      ·
        refine ⟨17824603369011034235255837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11883068912674022823503891 17824603369011034235255837)
        ·
          refine ⟨6684226263379137838220939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17824603369011034235255837 6684226263379137838220939)
          ·
            refine ⟨10026339395068706757331409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6684226263379137838220939 10026339395068706757331409)
            ·
              refine ⟨7519754546301530067998557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10026339395068706757331409 7519754546301530067998557)
              ·
                refine ⟨2819907954863073775499459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7519754546301530067998557 2819907954863073775499459)
                ·
                  refine ⟨4229861932294610663249189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819907954863073775499459 4229861932294610663249189)
                  ·
                    refine ⟨793099112305239499359223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4229861932294610663249189 793099112305239499359223)
                    ·
                      rfl

theorem cell23_4633665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_4633665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633665 prefixEnd_4633665 := by exact prefixLift 4633665
  have htrace : WordTrace (prefixWord ++ tailWord_4633665) baseStart_4633665 baseEnd_4633665 := by
    simpa [prefixWord, tailWord_4633665, baseEnd_4633665] using wordTrace_append hprefix tailTrace_4633665
  have hstable : (prefixWord ++ tailWord_4633665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633665).length < 2 ^ (prefixWord ++ tailWord_4633665).sum := by decide
  have hdescent : baseEnd_4633665 < baseStart_4633665 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633681 : List Nat := [1, 2, 2, 1, 3, 1, 2, 4, 2, 3, 2]
def baseStart_4633681 : Nat := 118140960795 + 4633681 * 2 ^ 59
def prefixEnd_4633681 : Nat := 4983230072969 + 3 ^ 40 * 4633681 * 2
def baseEnd_4633681 : Nat := 2379305552606190435477595

theorem tailTrace_4633681 : CollatzResearch.WordTrace tailWord_4633681 prefixEnd_4633681 2379305552606190435477595 := by
  unfold tailWord_4633681
  simp only [CollatzResearch.WordTrace]
  refine ⟨169004230325972581555748897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112669486883981721037165931 169004230325972581555748897)
  ·
    refine ⟨126753172744479436166811673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169004230325972581555748897 126753172744479436166811673)
    ·
      refine ⟨95064879558359577125108755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126753172744479436166811673 95064879558359577125108755)
      ·
        refine ⟨142597319337539365687663133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95064879558359577125108755 142597319337539365687663133)
        ·
          refine ⟨53473994751577262132873675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142597319337539365687663133 53473994751577262132873675)
          ·
            refine ⟨80210992127365893199310513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53473994751577262132873675 80210992127365893199310513)
            ·
              refine ⟨60158244095524419899482885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80210992127365893199310513 60158244095524419899482885)
              ·
                refine ⟨11279670767910828731153041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60158244095524419899482885 11279670767910828731153041)
                ·
                  refine ⟨8459753075933121548364781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11279670767910828731153041 8459753075933121548364781)
                  ·
                    refine ⟨3172407403474920580636793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8459753075933121548364781 3172407403474920580636793)
                    ·
                      refine ⟨2379305552606190435477595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172407403474920580636793 2379305552606190435477595)
                      ·
                        rfl

theorem cell23_4633681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 4, 2, 3, 2].length) (baseStart_4633681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633681 prefixEnd_4633681 := by exact prefixLift 4633681
  have htrace : WordTrace (prefixWord ++ tailWord_4633681) baseStart_4633681 baseEnd_4633681 := by
    simpa [prefixWord, tailWord_4633681, baseEnd_4633681] using wordTrace_append hprefix tailTrace_4633681
  have hstable : (prefixWord ++ tailWord_4633681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633681).length < 2 ^ (prefixWord ++ tailWord_4633681).sum := by decide
  have hdescent : baseEnd_4633681 < baseStart_4633681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633688 : List Nat := [2, 1, 2, 2, 1, 3, 1, 6, 1, 1, 3]
def baseStart_4633688 : Nat := 118140960795 + 4633688 * 2 ^ 59
def prefixEnd_4633688 : Nat := 4983230072969 + 3 ^ 40 * 4633688 * 2
def baseEnd_4633688 : Nat := 2379309146970771908090063

theorem tailTrace_4633688 : CollatzResearch.WordTrace tailWord_4633688 prefixEnd_4633688 2379309146970771908090063 := by
  unfold tailWord_4633688
  simp only [CollatzResearch.WordTrace]
  refine ⟨84502242818473610875626859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112669657091298147834169145 84502242818473610875626859)
  ·
    refine ⟨126753364227710416313440289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84502242818473610875626859 126753364227710416313440289)
    ·
      refine ⟨95065023170782812235080217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126753364227710416313440289 95065023170782812235080217)
      ·
        refine ⟨71298767378087109176310163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95065023170782812235080217 71298767378087109176310163)
        ·
          refine ⟨106948151067130663764465245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71298767378087109176310163 106948151067130663764465245)
          ·
            refine ⟨40105556650173998911674467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106948151067130663764465245 40105556650173998911674467)
            ·
              refine ⟨60158334975260998367511701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40105556650173998911674467 60158334975260998367511701)
              ·
                refine ⟨2819921951965359298477111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 60158334975260998367511701 2819921951965359298477111)
                ·
                  refine ⟨4229882927948038947715667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819921951965359298477111 4229882927948038947715667)
                  ·
                    refine ⟨6344824391922058421573501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4229882927948038947715667 6344824391922058421573501)
                    ·
                      refine ⟨2379309146970771908090063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6344824391922058421573501 2379309146970771908090063)
                      ·
                        rfl

theorem cell23_4633688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_4633688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633688 prefixEnd_4633688 := by exact prefixLift 4633688
  have htrace : WordTrace (prefixWord ++ tailWord_4633688) baseStart_4633688 baseEnd_4633688 := by
    simpa [prefixWord, tailWord_4633688, baseEnd_4633688] using wordTrace_append hprefix tailTrace_4633688
  have hstable : (prefixWord ++ tailWord_4633688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633688).length < 2 ^ (prefixWord ++ tailWord_4633688).sum := by decide
  have hdescent : baseEnd_4633688 < baseStart_4633688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633698 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4633698 : Nat := 118140960795 + 4633698 * 2 ^ 59
def prefixEnd_4633698 : Nat := 4983230072969 + 3 ^ 40 * 4633698 * 2
def baseEnd_4633698 : Nat := 2379314281777316868965017

theorem tailTrace_4633698 : CollatzResearch.WordTrace tailWord_4633698 prefixEnd_4633698 2379314281777316868965017 := by
  unfold tailWord_4633698
  simp only [CollatzResearch.WordTrace]
  refine ⟨42251212591727748364779437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112669900244607328972745165 42251212591727748364779437)
  ·
    refine ⟨15844204721897905636792289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42251212591727748364779437 15844204721897905636792289)
    ·
      refine ⟨11883153541423429227594217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15844204721897905636792289 11883153541423429227594217)
      ·
        refine ⟨8912365156067571920695663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11883153541423429227594217 8912365156067571920695663)
        ·
          refine ⟨13368547734101357881043495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8912365156067571920695663 13368547734101357881043495)
          ·
            refine ⟨20052821601152036821565243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13368547734101357881043495 20052821601152036821565243)
            ·
              refine ⟨30079232401728055232347865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20052821601152036821565243 30079232401728055232347865)
              ·
                refine ⟨22559424301296041424260899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30079232401728055232347865 22559424301296041424260899)
                ·
                  refine ⟨33839136451944062136391349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22559424301296041424260899 33839136451944062136391349)
                  ·
                    refine ⟨3172419042369755825286689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33839136451944062136391349 3172419042369755825286689)
                    ·
                      refine ⟨2379314281777316868965017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172419042369755825286689 2379314281777316868965017)
                      ·
                        rfl

theorem cell23_4633698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4633698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633698 prefixEnd_4633698 := by exact prefixLift 4633698
  have htrace : WordTrace (prefixWord ++ tailWord_4633698) baseStart_4633698 baseEnd_4633698 := by
    simpa [prefixWord, tailWord_4633698, baseEnd_4633698] using wordTrace_append hprefix tailTrace_4633698
  have hstable : (prefixWord ++ tailWord_4633698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633698).length < 2 ^ (prefixWord ++ tailWord_4633698).sum := by decide
  have hdescent : baseEnd_4633698 < baseStart_4633698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633711 : List Nat := [1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 4]
def baseStart_4633711 : Nat := 118140960795 + 4633711 * 2 ^ 59
def prefixEnd_4633711 : Nat := 4983230072969 + 3 ^ 40 * 4633711 * 2
def baseEnd_4633711 : Nat := 2379320957025825318102457

theorem tailTrace_4633711 : CollatzResearch.WordTrace tailWord_4633711 prefixEnd_4633711 2379320957025825318102457 := by
  unfold tailWord_4633711
  simp only [CollatzResearch.WordTrace]
  refine ⟨169005324515863896679340987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112670216343909264452893991 169005324515863896679340987)
  ·
    refine ⟨253507986773795845019011481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169005324515863896679340987 253507986773795845019011481)
    ·
      refine ⟨190130990080346883764258611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253507986773795845019011481 190130990080346883764258611)
      ·
        refine ⟨285196485120520325646387917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190130990080346883764258611 285196485120520325646387917)
        ·
          refine ⟨106948681920195122117395469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285196485120520325646387917 106948681920195122117395469)
          ·
            refine ⟨40105755720073170794023301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106948681920195122117395469 40105755720073170794023301)
            ·
              refine ⟨7519829197513719523879369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40105755720073170794023301 7519829197513719523879369)
              ·
                refine ⟨5639871898135289642909527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7519829197513719523879369 5639871898135289642909527)
                ·
                  refine ⟨8459807847202934464364291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5639871898135289642909527 8459807847202934464364291)
                  ·
                    refine ⟨12689711770804401696546437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8459807847202934464364291 12689711770804401696546437)
                    ·
                      refine ⟨2379320957025825318102457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12689711770804401696546437 2379320957025825318102457)
                      ·
                        rfl

theorem cell23_4633711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2, 1, 1, 4].length) (baseStart_4633711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633711 prefixEnd_4633711 := by exact prefixLift 4633711
  have htrace : WordTrace (prefixWord ++ tailWord_4633711) baseStart_4633711 baseEnd_4633711 := by
    simpa [prefixWord, tailWord_4633711, baseEnd_4633711] using wordTrace_append hprefix tailTrace_4633711
  have hstable : (prefixWord ++ tailWord_4633711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633711).length < 2 ^ (prefixWord ++ tailWord_4633711).sum := by decide
  have hdescent : baseEnd_4633711 < baseStart_4633711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633714 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 3, 1, 5]
def baseStart_4633714 : Nat := 118140960795 + 4633714 * 2 ^ 59
def prefixEnd_4633714 : Nat := 4983230072969 + 3 ^ 40 * 4633714 * 2
def baseEnd_4633714 : Nat := 2379322497467788806364943

theorem tailTrace_4633714 : CollatzResearch.WordTrace tailWord_4633714 prefixEnd_4633714 2379322497467788806364943 := by
  unfold tailWord_4633714
  simp only [CollatzResearch.WordTrace]
  refine ⟨42251358483713257047925049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112670289289902018794466797 42251358483713257047925049)
  ·
    refine ⟨31688518862784942785943787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42251358483713257047925049 31688518862784942785943787)
    ·
      refine ⟨47532778294177414178915681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31688518862784942785943787 47532778294177414178915681)
      ·
        refine ⟨35649583720633060634186761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47532778294177414178915681 35649583720633060634186761)
        ·
          refine ⟨26737187790474795475640071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35649583720633060634186761 26737187790474795475640071)
          ·
            refine ⟨40105781685712193213460107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26737187790474795475640071 40105781685712193213460107)
            ·
              refine ⟨60158672528568289820190161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40105781685712193213460107 60158672528568289820190161)
              ·
                refine ⟨45119004396426217365142621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60158672528568289820190161 45119004396426217365142621)
                ·
                  refine ⟨16919626648659831511928483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45119004396426217365142621 16919626648659831511928483)
                  ·
                    refine ⟨25379439972989747267892725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16919626648659831511928483 25379439972989747267892725)
                    ·
                      refine ⟨2379322497467788806364943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25379439972989747267892725 2379322497467788806364943)
                      ·
                        rfl

theorem cell23_4633714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_4633714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633714 prefixEnd_4633714 := by exact prefixLift 4633714
  have htrace : WordTrace (prefixWord ++ tailWord_4633714) baseStart_4633714 baseEnd_4633714 := by
    simpa [prefixWord, tailWord_4633714, baseEnd_4633714] using wordTrace_append hprefix tailTrace_4633714
  have hstable : (prefixWord ++ tailWord_4633714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633714).length < 2 ^ (prefixWord ++ tailWord_4633714).sum := by decide
  have hdescent : baseEnd_4633714 < baseStart_4633714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633724 : List Nat := [2, 2, 2, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_4633724 : Nat := 118140960795 + 4633724 * 2 ^ 59
def prefixEnd_4633724 : Nat := 4983230072969 + 3 ^ 40 * 4633724 * 2
def baseEnd_4633724 : Nat := 2379327632274333767239897

theorem tailTrace_4633724 : CollatzResearch.WordTrace tailWord_4633724 prefixEnd_4633724 2379327632274333767239897 := by
  unfold tailWord_4633724
  simp only [CollatzResearch.WordTrace]
  refine ⟨84502899332408399949782113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112670532443211199933042817 84502899332408399949782113)
  ·
    refine ⟨63377174499306299962336585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84502899332408399949782113 63377174499306299962336585)
    ·
      refine ⟨47532880874479724971752439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63377174499306299962336585 47532880874479724971752439)
      ·
        refine ⟨71299321311719587457628659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47532880874479724971752439 71299321311719587457628659)
        ·
          refine ⟨106948981967579381186442989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71299321311719587457628659 106948981967579381186442989)
          ·
            refine ⟨40105868237842267944916121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106948981967579381186442989 40105868237842267944916121)
            ·
              refine ⟨30079401178381700958687091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40105868237842267944916121 30079401178381700958687091)
              ·
                refine ⟨45119101767572551438030637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30079401178381700958687091 45119101767572551438030637)
                ·
                  refine ⟨16919663162839706789261489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45119101767572551438030637 16919663162839706789261489)
                  ·
                    refine ⟨12689747372129780091946117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16919663162839706789261489 12689747372129780091946117)
                    ·
                      refine ⟨2379327632274333767239897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12689747372129780091946117 2379327632274333767239897)
                      ·
                        rfl

theorem cell23_4633724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_4633724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633724 prefixEnd_4633724 := by exact prefixLift 4633724
  have htrace : WordTrace (prefixWord ++ tailWord_4633724) baseStart_4633724 baseEnd_4633724 := by
    simpa [prefixWord, tailWord_4633724, baseEnd_4633724] using wordTrace_append hprefix tailTrace_4633724
  have hstable : (prefixWord ++ tailWord_4633724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633724).length < 2 ^ (prefixWord ++ tailWord_4633724).sum := by decide
  have hdescent : baseEnd_4633724 < baseStart_4633724 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633731 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 3]
def baseStart_4633731 : Nat := 118140960795 + 4633731 * 2 ^ 59
def prefixEnd_4633731 : Nat := 4983230072969 + 3 ^ 40 * 4633731 * 2
def baseEnd_4633731 : Nat := 2379331226638915239852365

theorem tailTrace_4633731 : CollatzResearch.WordTrace tailWord_4633731 prefixEnd_4633731 2379331226638915239852365 := by
  unfold tailWord_4633731
  simp only [CollatzResearch.WordTrace]
  refine ⟨169006053975791440095069047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112670702650527626730046031 169006053975791440095069047)
  ·
    refine ⟨253509080963687160142603571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169006053975791440095069047 253509080963687160142603571)
    ·
      refine ⟨380263621445530740213905357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253509080963687160142603571 380263621445530740213905357)
      ·
        refine ⟨142598858042074027580214509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380263621445530740213905357 142598858042074027580214509)
        ·
          refine ⟨53474571765777760342580441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142598858042074027580214509 53474571765777760342580441)
          ·
            refine ⟨40105928824333320256935331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53474571765777760342580441 40105928824333320256935331)
            ·
              refine ⟨60158893236499980385402997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40105928824333320256935331 60158893236499980385402997)
              ·
                refine ⟨5639896240921873161131531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 60158893236499980385402997 5639896240921873161131531)
                ·
                  refine ⟨8459844361382809741697297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5639896240921873161131531 8459844361382809741697297)
                  ·
                    refine ⟨6344883271037107306272973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8459844361382809741697297 6344883271037107306272973)
                    ·
                      refine ⟨2379331226638915239852365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6344883271037107306272973 2379331226638915239852365)
                      ·
                        rfl

theorem cell23_4633731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 1, 2, 3].length) (baseStart_4633731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633731 prefixEnd_4633731 := by exact prefixLift 4633731
  have htrace : WordTrace (prefixWord ++ tailWord_4633731) baseStart_4633731 baseEnd_4633731 := by
    simpa [prefixWord, tailWord_4633731, baseEnd_4633731] using wordTrace_append hprefix tailTrace_4633731
  have hstable : (prefixWord ++ tailWord_4633731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633731).length < 2 ^ (prefixWord ++ tailWord_4633731).sum := by decide
  have hdescent : baseEnd_4633731 < baseStart_4633731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633744 : List Nat := [2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 3]
def baseStart_4633744 : Nat := 118140960795 + 4633744 * 2 ^ 59
def prefixEnd_4633744 : Nat := 4983230072969 + 3 ^ 40 * 4633744 * 2
def baseEnd_4633744 : Nat := 2379337901887423688989805

theorem tailTrace_4633744 : CollatzResearch.WordTrace tailWord_4633744 prefixEnd_4633744 2379337901887423688989805 := by
  unfold tailWord_4633744
  simp only [CollatzResearch.WordTrace]
  refine ⟨84503264062372171657646143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112671018749829562210194857 84503264062372171657646143)
  ·
    refine ⟨126754896093558257486469215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84503264062372171657646143 126754896093558257486469215)
    ·
      refine ⟨190132344140337386229703823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126754896093558257486469215 190132344140337386229703823)
      ·
        refine ⟨285198516210506079344555735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190132344140337386229703823 285198516210506079344555735)
        ·
          refine ⟨427797774315759119016833603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 285198516210506079344555735 427797774315759119016833603)
          ·
            refine ⟨641696661473638678525250405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427797774315759119016833603 641696661473638678525250405)
            ·
              refine ⟨120318124026307252223484451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 641696661473638678525250405 120318124026307252223484451)
              ·
                refine ⟨180477186039460878335226677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120318124026307252223484451 180477186039460878335226677)
                ·
                  refine ⟨16919736191199457343927501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 180477186039460878335226677 16919736191199457343927501)
                  ·
                    refine ⟨6344901071699796503972813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16919736191199457343927501 6344901071699796503972813)
                    ·
                      refine ⟨2379337901887423688989805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6344901071699796503972813 2379337901887423688989805)
                      ·
                        rfl

theorem cell23_4633744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 3].length) (baseStart_4633744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633744 prefixEnd_4633744 := by exact prefixLift 4633744
  have htrace : WordTrace (prefixWord ++ tailWord_4633744) baseStart_4633744 baseEnd_4633744 := by
    simpa [prefixWord, tailWord_4633744, baseEnd_4633744] using wordTrace_append hprefix tailTrace_4633744
  have hstable : (prefixWord ++ tailWord_4633744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633744).length < 2 ^ (prefixWord ++ tailWord_4633744).sum := by decide
  have hdescent : baseEnd_4633744 < baseStart_4633744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633761 : List Nat := [1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 3]
def baseStart_4633761 : Nat := 118140960795 + 4633761 * 2 ^ 59
def prefixEnd_4633761 : Nat := 4983230072969 + 3 ^ 40 * 4633761 * 2
def baseEnd_4633761 : Nat := 2379346631058550122477227

theorem tailTrace_4633761 : CollatzResearch.WordTrace tailWord_4633761 prefixEnd_4633761 2379346631058550122477227 := by
  unfold tailWord_4633761
  simp only [CollatzResearch.WordTrace]
  refine ⟨169007148165682755218661137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112671432110455170145774091 169007148165682755218661137)
  ·
    refine ⟨126755361124262066413995853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169007148165682755218661137 126755361124262066413995853)
    ·
      refine ⟨47533260421598274905248445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126755361124262066413995853 47533260421598274905248445)
      ·
        refine ⟨17824972658099353089468167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47533260421598274905248445 17824972658099353089468167)
        ·
          refine ⟨26737458987149029634202251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17824972658099353089468167 26737458987149029634202251)
          ·
            refine ⟨40106188480723544451303377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26737458987149029634202251 40106188480723544451303377)
            ·
              refine ⟨30079641360542658338477533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40106188480723544451303377 30079641360542658338477533)
              ·
                refine ⟨11279865510203496876929075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30079641360542658338477533 11279865510203496876929075)
                ·
                  refine ⟨16919798265305245315393613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11279865510203496876929075 16919798265305245315393613)
                  ·
                    refine ⟨6344924349489466993272605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16919798265305245315393613 6344924349489466993272605)
                    ·
                      refine ⟨2379346631058550122477227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6344924349489466993272605 2379346631058550122477227)
                      ·
                        rfl

theorem cell23_4633761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 3].length) (baseStart_4633761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633761 prefixEnd_4633761 := by exact prefixLift 4633761
  have htrace : WordTrace (prefixWord ++ tailWord_4633761) baseStart_4633761 baseEnd_4633761 := by
    simpa [prefixWord, tailWord_4633761, baseEnd_4633761] using wordTrace_append hprefix tailTrace_4633761
  have hstable : (prefixWord ++ tailWord_4633761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633761).length < 2 ^ (prefixWord ++ tailWord_4633761).sum := by decide
  have hdescent : baseEnd_4633761 < baseStart_4633761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633762 : List Nat := [3, 3, 1, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_4633762 : Nat := 118140960795 + 4633762 * 2 ^ 59
def prefixEnd_4633762 : Nat := 4983230072969 + 3 ^ 40 * 4633762 * 2
def baseEnd_4633762 : Nat := 2379347144539204618564723

theorem tailTrace_4633762 : CollatzResearch.WordTrace tailWord_4633762 prefixEnd_4633762 2379347144539204618564723 := by
  unfold tailWord_4633762
  simp only [CollatzResearch.WordTrace]
  refine ⟨42251796159669783097361885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112671456425786088259631693 42251796159669783097361885)
  ·
    refine ⟨15844423559876168661510707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42251796159669783097361885 15844423559876168661510707)
    ·
      refine ⟨23766635339814252992266061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15844423559876168661510707 23766635339814252992266061)
      ·
        refine ⟨8912488252430344872099773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23766635339814252992266061 8912488252430344872099773)
        ·
          refine ⟨3342183094661379327037415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8912488252430344872099773 3342183094661379327037415)
          ·
            refine ⟨5013274641992068990556123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3342183094661379327037415 5013274641992068990556123)
            ·
              refine ⟨7519911962988103485834185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5013274641992068990556123 7519911962988103485834185)
              ·
                refine ⟨5639933972241077614375639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7519911962988103485834185 5639933972241077614375639)
                ·
                  refine ⟨8459900958361616421563459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5639933972241077614375639 8459900958361616421563459)
                  ·
                    refine ⟨12689851437542424632345189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8459900958361616421563459 12689851437542424632345189)
                    ·
                      refine ⟨2379347144539204618564723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12689851437542424632345189 2379347144539204618564723)
                      ·
                        rfl

theorem cell23_4633762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_4633762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633762 prefixEnd_4633762 := by exact prefixLift 4633762
  have htrace : WordTrace (prefixWord ++ tailWord_4633762) baseStart_4633762 baseEnd_4633762 := by
    simpa [prefixWord, tailWord_4633762, baseEnd_4633762] using wordTrace_append hprefix tailTrace_4633762
  have hstable : (prefixWord ++ tailWord_4633762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633762).length < 2 ^ (prefixWord ++ tailWord_4633762).sum := by decide
  have hdescent : baseEnd_4633762 < baseStart_4633762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633782 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4633782 : Nat := 118140960795 + 4633782 * 2 ^ 59
def prefixEnd_4633782 : Nat := 4983230072969 + 3 ^ 40 * 4633782 * 2
def baseEnd_4633782 : Nat := 2379357414152294540314631

theorem tailTrace_4633782 : CollatzResearch.WordTrace tailWord_4633782 prefixEnd_4633782 2379357414152294540314631 := by
  unfold tailWord_4633782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10562994631162917237823475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112671942732404450536783733 10562994631162917237823475)
  ·
    refine ⟨15844491946744375856735213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10562994631162917237823475 15844491946744375856735213)
    ·
      refine ⟨5941684480029140946275705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15844491946744375856735213 5941684480029140946275705)
      ·
        refine ⟨4456263360021855709706779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5941684480029140946275705 4456263360021855709706779)
        ·
          refine ⟨6684395040032783564560169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4456263360021855709706779 6684395040032783564560169)
          ·
            refine ⟨5013296280024587673420127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6684395040032783564560169 5013296280024587673420127)
            ·
              refine ⟨7519944420036881510130191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5013296280024587673420127 7519944420036881510130191)
              ·
                refine ⟨11279916630055322265195287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7519944420036881510130191 11279916630055322265195287)
                ·
                  refine ⟨16919874945082983397792931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11279916630055322265195287 16919874945082983397792931)
                  ·
                    refine ⟨25379812417624475096689397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16919874945082983397792931 25379812417624475096689397)
                    ·
                      refine ⟨2379357414152294540314631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25379812417624475096689397 2379357414152294540314631)
                      ·
                        rfl

theorem cell23_4633782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4633782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633782 prefixEnd_4633782 := by exact prefixLift 4633782
  have htrace : WordTrace (prefixWord ++ tailWord_4633782) baseStart_4633782 baseEnd_4633782 := by
    simpa [prefixWord, tailWord_4633782, baseEnd_4633782] using wordTrace_append hprefix tailTrace_4633782
  have hstable : (prefixWord ++ tailWord_4633782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633782).length < 2 ^ (prefixWord ++ tailWord_4633782).sum := by decide
  have hdescent : baseEnd_4633782 < baseStart_4633782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633796 : List Nat := [2, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2]
def baseStart_4633796 : Nat := 118140960795 + 4633796 * 2 ^ 59
def prefixEnd_4633796 : Nat := 4983230072969 + 3 ^ 40 * 4633796 * 2
def baseEnd_4633796 : Nat := 2379364602881457485539567

theorem tailTrace_4633796 : CollatzResearch.WordTrace tailWord_4633796 prefixEnd_4633796 2379364602881457485539567 := by
  unfold tailWord_4633796
  simp only [CollatzResearch.WordTrace]
  refine ⟨84504212360277978098092621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112672283147037304130790161 84504212360277978098092621)
  ·
    refine ⟨31689079635104241786784733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84504212360277978098092621 31689079635104241786784733)
    ·
      refine ⟨11883404863164090670044275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31689079635104241786784733 11883404863164090670044275)
      ·
        refine ⟨17825107294746136005066413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11883404863164090670044275 17825107294746136005066413)
        ·
          refine ⟨6684415235529801001899905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17825107294746136005066413 6684415235529801001899905)
          ·
            refine ⟨5013311426647350751424929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6684415235529801001899905 5013311426647350751424929)
            ·
              refine ⟨3759983569985513063568697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5013311426647350751424929 3759983569985513063568697)
              ·
                refine ⟨2819987677489134797676523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3759983569985513063568697 2819987677489134797676523)
                ·
                  refine ⟨4229981516233702196514785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2819987677489134797676523 4229981516233702196514785)
                  ·
                    refine ⟨3172486137175276647386089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4229981516233702196514785 3172486137175276647386089)
                    ·
                      refine ⟨2379364602881457485539567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172486137175276647386089 2379364602881457485539567)
                      ·
                        rfl

theorem cell23_4633796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 2, 2, 1, 2, 2].length) (baseStart_4633796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633796 prefixEnd_4633796 := by exact prefixLift 4633796
  have htrace : WordTrace (prefixWord ++ tailWord_4633796) baseStart_4633796 baseEnd_4633796 := by
    simpa [prefixWord, tailWord_4633796, baseEnd_4633796] using wordTrace_append hprefix tailTrace_4633796
  have hstable : (prefixWord ++ tailWord_4633796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633796).length < 2 ^ (prefixWord ++ tailWord_4633796).sum := by decide
  have hdescent : baseEnd_4633796 < baseStart_4633796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633818 : List Nat := [3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2]
def baseStart_4633818 : Nat := 118140960795 + 4633818 * 2 ^ 59
def prefixEnd_4633818 : Nat := 4983230072969 + 3 ^ 40 * 4633818 * 2
def baseEnd_4633818 : Nat := 2379375899455856399464465

theorem tailTrace_4633818 : CollatzResearch.WordTrace tailWord_4633818 prefixEnd_4633818 2379375899455856399464465 := by
  unfold tailWord_4633818
  simp only [CollatzResearch.WordTrace]
  refine ⟨42252306781619063488371527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112672818084317502635657405 42252306781619063488371527)
  ·
    refine ⟨63378460172428595232557291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42252306781619063488371527 63378460172428595232557291)
    ·
      refine ⟨95067690258642892848835937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63378460172428595232557291 95067690258642892848835937)
      ·
        refine ⟨71300767693982169636626953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95067690258642892848835937 71300767693982169636626953)
        ·
          refine ⟨53475575770486627227470215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71300767693982169636626953 53475575770486627227470215)
          ·
            refine ⟨80213363655729940841205323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53475575770486627227470215 80213363655729940841205323)
            ·
              refine ⟨120320045483594911261807985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80213363655729940841205323 120320045483594911261807985)
              ·
                refine ⟨90240034112696183446355989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120320045483594911261807985 90240034112696183446355989)
                ·
                  refine ⟨4230001599032633599047937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90240034112696183446355989 4230001599032633599047937)
                  ·
                    refine ⟨3172501199274475199285953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4230001599032633599047937 3172501199274475199285953)
                    ·
                      refine ⟨2379375899455856399464465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172501199274475199285953 2379375899455856399464465)
                      ·
                        rfl

theorem cell23_4633818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_4633818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633818 prefixEnd_4633818 := by exact prefixLift 4633818
  have htrace : WordTrace (prefixWord ++ tailWord_4633818) baseStart_4633818 baseEnd_4633818 := by
    simpa [prefixWord, tailWord_4633818, baseEnd_4633818] using wordTrace_append hprefix tailTrace_4633818
  have hstable : (prefixWord ++ tailWord_4633818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633818).length < 2 ^ (prefixWord ++ tailWord_4633818).sum := by decide
  have hdescent : baseEnd_4633818 < baseStart_4633818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633824 : List Nat := [2, 1, 1, 3, 1, 4, 1, 1, 9]
def baseStart_4633824 : Nat := 118140960795 + 4633824 * 2 ^ 59
def prefixEnd_4633824 : Nat := 4983230072969 + 3 ^ 40 * 4633824 * 2
def baseEnd_4633824 : Nat := 264375442259975930665493

theorem tailTrace_4633824 : CollatzResearch.WordTrace tailWord_4633824 prefixEnd_4633824 264375442259975930665493 := by
  unfold tailWord_4633824
  simp only [CollatzResearch.WordTrace]
  refine ⟨84504722982227258489102263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112672963976303011318803017 84504722982227258489102263)
  ·
    refine ⟨126757084473340887733653395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84504722982227258489102263 126757084473340887733653395)
    ·
      refine ⟨190135626710011331600480093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126757084473340887733653395 190135626710011331600480093)
      ·
        refine ⟨71300860016254249350180035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190135626710011331600480093 71300860016254249350180035)
        ·
          refine ⟨106951290024381374025270053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71300860016254249350180035 106951290024381374025270053)
          ·
            refine ⟨20053366879571507629738135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106951290024381374025270053 20053366879571507629738135)
            ·
              refine ⟨30080050319357261444607203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20053366879571507629738135 30080050319357261444607203)
              ·
                refine ⟨45120075479035892166910805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30080050319357261444607203 45120075479035892166910805)
                ·
                  refine ⟨264375442259975930665493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 45120075479035892166910805 264375442259975930665493)
                  ·
                    rfl

theorem cell23_4633824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 1, 9].length) (baseStart_4633824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633824 prefixEnd_4633824 := by exact prefixLift 4633824
  have htrace : WordTrace (prefixWord ++ tailWord_4633824) baseStart_4633824 baseEnd_4633824 := by
    simpa [prefixWord, tailWord_4633824, baseEnd_4633824] using wordTrace_append hprefix tailTrace_4633824
  have hstable : (prefixWord ++ tailWord_4633824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633824).length < 2 ^ (prefixWord ++ tailWord_4633824).sum := by decide
  have hdescent : baseEnd_4633824 < baseStart_4633824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633839 : List Nat := [1, 1, 2, 1, 8, 1, 2, 1, 1, 3, 2]
def baseStart_4633839 : Nat := 118140960795 + 4633839 * 2 ^ 59
def prefixEnd_4633839 : Nat := 4983230072969 + 3 ^ 40 * 4633839 * 2
def baseEnd_4633839 : Nat := 2379386682549600817301869

theorem tailTrace_4633839 : CollatzResearch.WordTrace tailWord_4633839 prefixEnd_4633839 2379386682549600817301869 := by
  unfold tailWord_4633839
  simp only [CollatzResearch.WordTrace]
  refine ⟨169009993059400174540000571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112673328706266783026667047 169009993059400174540000571)
  ·
    refine ⟨253514989589100261810000857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169009993059400174540000571 253514989589100261810000857)
    ·
      refine ⟨190136242191825196357500643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253514989589100261810000857 190136242191825196357500643)
      ·
        refine ⟨285204363287737794536250965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190136242191825196357500643 285204363287737794536250965)
        ·
          refine ⟨3342238632278177279721691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 285204363287737794536250965 3342238632278177279721691)
          ·
            refine ⟨5013357948417265919582537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3342238632278177279721691 5013357948417265919582537)
            ·
              refine ⟨3760018461312949439686903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5013357948417265919582537 3760018461312949439686903)
              ·
                refine ⟨5640027691969424159530355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760018461312949439686903 5640027691969424159530355)
                ·
                  refine ⟨8460041537954136239295533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640027691969424159530355 8460041537954136239295533)
                  ·
                    refine ⟨3172515576732801089735825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8460041537954136239295533 3172515576732801089735825)
                    ·
                      refine ⟨2379386682549600817301869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172515576732801089735825 2379386682549600817301869)
                      ·
                        rfl

theorem cell23_4633839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 2, 1, 1, 3, 2].length) (baseStart_4633839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633839 prefixEnd_4633839 := by exact prefixLift 4633839
  have htrace : WordTrace (prefixWord ++ tailWord_4633839) baseStart_4633839 baseEnd_4633839 := by
    simpa [prefixWord, tailWord_4633839, baseEnd_4633839] using wordTrace_append hprefix tailTrace_4633839
  have hstable : (prefixWord ++ tailWord_4633839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633839).length < 2 ^ (prefixWord ++ tailWord_4633839).sum := by decide
  have hdescent : baseEnd_4633839 < baseStart_4633839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4633891 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 4]
def baseStart_4633891 : Nat := 118140960795 + 4633891 * 2 ^ 59
def prefixEnd_4633891 : Nat := 4983230072969 + 3 ^ 40 * 4633891 * 2
def baseEnd_4633891 : Nat := 2379413383543634613851629

theorem tailTrace_4633891 : CollatzResearch.WordTrace tailWord_4633891 prefixEnd_4633891 2379413383543634613851629 := by
  unfold tailWord_4633891
  simp only [CollatzResearch.WordTrace]
  refine ⟨169011889655211787420893527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112674593103474524947262351 169011889655211787420893527)
  ·
    refine ⟨253517834482817681131340291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169011889655211787420893527 253517834482817681131340291)
    ·
      refine ⟨380276751724226521697010437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253517834482817681131340291 380276751724226521697010437)
      ·
        refine ⟨71301890948292472818189457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 380276751724226521697010437 71301890948292472818189457)
        ·
          refine ⟨53476418211219354613642093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71301890948292472818189457 53476418211219354613642093)
          ·
            refine ⟨20053656829207257980115785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53476418211219354613642093 20053656829207257980115785)
            ·
              refine ⟨15040242621905443485086839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20053656829207257980115785 15040242621905443485086839)
              ·
                refine ⟨22560363932858165227630259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15040242621905443485086839 22560363932858165227630259)
                ·
                  refine ⟨33840545899287247841445389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22560363932858165227630259 33840545899287247841445389)
                  ·
                    refine ⟨12690204712232717940542021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33840545899287247841445389 12690204712232717940542021)
                    ·
                      refine ⟨2379413383543634613851629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12690204712232717940542021 2379413383543634613851629)
                      ·
                        rfl

theorem cell23_4633891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 1, 3, 4].length) (baseStart_4633891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4633891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4633891 prefixEnd_4633891 := by exact prefixLift 4633891
  have htrace : WordTrace (prefixWord ++ tailWord_4633891) baseStart_4633891 baseEnd_4633891 := by
    simpa [prefixWord, tailWord_4633891, baseEnd_4633891] using wordTrace_append hprefix tailTrace_4633891
  have hstable : (prefixWord ++ tailWord_4633891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4633891).length < 2 ^ (prefixWord ++ tailWord_4633891).sum := by decide
  have hdescent : baseEnd_4633891 < baseStart_4633891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4633891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634001 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 5]
def baseStart_4634001 : Nat := 118140960795 + 4634001 * 2 ^ 59
def prefixEnd_4634001 : Nat := 4983230072969 + 3 ^ 40 * 4634001 * 2
def baseEnd_4634001 : Nat := 2379469866415629183476123

theorem tailTrace_4634001 : CollatzResearch.WordTrace tailWord_4634001 prefixEnd_4634001 2379469866415629183476123 := by
  unfold tailWord_4634001
  simp only [CollatzResearch.WordTrace]
  refine ⟨169015901684813276207397857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112677267789875517471598571 169015901684813276207397857)
  ·
    refine ⟨126761926263609957155548393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169015901684813276207397857 126761926263609957155548393)
    ·
      refine ⟨95071444697707467866661295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126761926263609957155548393 95071444697707467866661295)
      ·
        refine ⟨142607167046561201799991943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95071444697707467866661295 142607167046561201799991943)
        ·
          refine ⟨213910750569841802699987915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142607167046561201799991943 213910750569841802699987915)
          ·
            refine ⟨320866125854762704049981873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213910750569841802699987915 320866125854762704049981873)
            ·
              refine ⟨240649594391072028037486405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320866125854762704049981873 240649594391072028037486405)
              ·
                refine ⟨45121798948326005257028701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 240649594391072028037486405 45121798948326005257028701)
                ·
                  refine ⟨16920674605622251971385763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45121798948326005257028701 16920674605622251971385763)
                  ·
                    refine ⟨25381011908433377957078645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16920674605622251971385763 25381011908433377957078645)
                    ·
                      refine ⟨2379469866415629183476123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25381011908433377957078645 2379469866415629183476123)
                      ·
                        rfl

theorem cell23_4634001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 5].length) (baseStart_4634001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634001 prefixEnd_4634001 := by exact prefixLift 4634001
  have htrace : WordTrace (prefixWord ++ tailWord_4634001) baseStart_4634001 baseEnd_4634001 := by
    simpa [prefixWord, tailWord_4634001, baseEnd_4634001] using wordTrace_append hprefix tailTrace_4634001
  have hstable : (prefixWord ++ tailWord_4634001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634001).length < 2 ^ (prefixWord ++ tailWord_4634001).sum := by decide
  have hdescent : baseEnd_4634001 < baseStart_4634001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634012 : List Nat := [2, 2, 3, 4, 1, 1, 1, 3, 1, 5]
def baseStart_4634012 : Nat := 118140960795 + 4634012 * 2 ^ 59
def prefixEnd_4634012 : Nat := 4983230072969 + 3 ^ 40 * 4634012 * 2
def baseEnd_4634012 : Nat := 793158504900942880146191

theorem tailTrace_4634012 : CollatzResearch.WordTrace tailWord_4634012 prefixEnd_4634012 793158504900942880146191 := by
  unfold tailWord_4634012
  simp only [CollatzResearch.WordTrace]
  refine ⟨84508151443886712543024145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112677535258515616724032193 84508151443886712543024145)
  ·
    refine ⟨63381113582915034407268109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84508151443886712543024145 63381113582915034407268109)
    ·
      refine ⟨23767917593593137902725541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63381113582915034407268109 23767917593593137902725541)
      ·
        refine ⟨4456484548798713356761039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23767917593593137902725541 4456484548798713356761039)
        ·
          refine ⟨6684726823198070035141559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4456484548798713356761039 6684726823198070035141559)
          ·
            refine ⟨10027090234797105052712339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6684726823198070035141559 10027090234797105052712339)
            ·
              refine ⟨15040635352195657579068509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10027090234797105052712339 15040635352195657579068509)
              ·
                refine ⟨5640238257073371592150691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15040635352195657579068509 5640238257073371592150691)
                ·
                  refine ⟨8460357385610057388226037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640238257073371592150691 8460357385610057388226037)
                  ·
                    refine ⟨793158504900942880146191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8460357385610057388226037 793158504900942880146191)
                    ·
                      rfl

theorem cell23_4634012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_4634012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634012 prefixEnd_4634012 := by exact prefixLift 4634012
  have htrace : WordTrace (prefixWord ++ tailWord_4634012) baseStart_4634012 baseEnd_4634012 := by
    simpa [prefixWord, tailWord_4634012, baseEnd_4634012] using wordTrace_append hprefix tailTrace_4634012
  have hstable : (prefixWord ++ tailWord_4634012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634012).length < 2 ^ (prefixWord ++ tailWord_4634012).sum := by decide
  have hdescent : baseEnd_4634012 < baseStart_4634012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634015 : List Nat := [1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 4]
def baseStart_4634015 : Nat := 118140960795 + 4634015 * 2 ^ 59
def prefixEnd_4634015 : Nat := 4983230072969 + 3 ^ 40 * 4634015 * 2
def baseEnd_4634015 : Nat := 2379477055144792128701059

theorem tailTrace_4634015 : CollatzResearch.WordTrace tailWord_4634015 prefixEnd_4634015 2379477055144792128701059 := by
  unfold tailWord_4634015
  simp only [CollatzResearch.WordTrace]
  refine ⟨169016412306762556598407499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112677608204508371065604999 169016412306762556598407499)
  ·
    refine ⟨253524618460143834897611249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169016412306762556598407499 253524618460143834897611249)
    ·
      refine ⟨190143463845107876173208437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253524618460143834897611249 190143463845107876173208437)
      ·
        refine ⟨17825949735478863391238291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190143463845107876173208437 17825949735478863391238291)
        ·
          refine ⟨26738924603218295086857437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17825949735478863391238291 26738924603218295086857437)
          ·
            refine ⟨10027096726206860657571539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26738924603218295086857437 10027096726206860657571539)
            ·
              refine ⟨15040645089310290986357309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10027096726206860657571539 15040645089310290986357309)
              ·
                refine ⟨5640241908491359119883991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15040645089310290986357309 5640241908491359119883991)
                ·
                  refine ⟨8460362862737038679825987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640241908491359119883991 8460362862737038679825987)
                  ·
                    refine ⟨12690544294105558019738981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8460362862737038679825987 12690544294105558019738981)
                    ·
                      refine ⟨2379477055144792128701059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12690544294105558019738981 2379477055144792128701059)
                      ·
                        rfl

theorem cell23_4634015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_4634015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634015 prefixEnd_4634015 := by exact prefixLift 4634015
  have htrace : WordTrace (prefixWord ++ tailWord_4634015) baseStart_4634015 baseEnd_4634015 := by
    simpa [prefixWord, tailWord_4634015, baseEnd_4634015] using wordTrace_append hprefix tailTrace_4634015
  have hstable : (prefixWord ++ tailWord_4634015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634015).length < 2 ^ (prefixWord ++ tailWord_4634015).sum := by decide
  have hdescent : baseEnd_4634015 < baseStart_4634015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634051 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 2, 7]
def baseStart_4634051 : Nat := 118140960795 + 4634051 * 2 ^ 59
def prefixEnd_4634051 : Nat := 4983230072969 + 3 ^ 40 * 4634051 * 2
def baseEnd_4634051 : Nat := 793165180149451329283631

theorem tailTrace_4634051 : CollatzResearch.WordTrace tailWord_4634051 prefixEnd_4634051 793165180149451329283631 := by
  unfold tailWord_4634051
  simp only [CollatzResearch.WordTrace]
  refine ⟨169017725334632134746718007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112678483556421423164478671 169017725334632134746718007)
  ·
    refine ⟨253526588001948202120077011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169017725334632134746718007 253526588001948202120077011)
    ·
      refine ⟨380289882002922303180115517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253526588001948202120077011 380289882002922303180115517)
      ·
        refine ⟨142608705751095863692543319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380289882002922303180115517 142608705751095863692543319)
        ·
          refine ⟨213913058626643795538814979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142608705751095863692543319 213913058626643795538814979)
          ·
            refine ⟨320869587939965693308222469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213913058626643795538814979 320869587939965693308222469)
            ·
              refine ⟨60163047738743567495291713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 320869587939965693308222469 60163047738743567495291713)
              ·
                refine ⟨45122285804057675621468785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60163047738743567495291713 45122285804057675621468785)
                ·
                  refine ⟨33841714353043256716101589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45122285804057675621468785 33841714353043256716101589)
                  ·
                    refine ⟨793165180149451329283631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33841714353043256716101589 793165180149451329283631)
                    ·
                      rfl

theorem cell23_4634051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 2, 7].length) (baseStart_4634051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634051 prefixEnd_4634051 := by exact prefixLift 4634051
  have htrace : WordTrace (prefixWord ++ tailWord_4634051) baseStart_4634051 baseEnd_4634051 := by
    simpa [prefixWord, tailWord_4634051, baseEnd_4634051] using wordTrace_append hprefix tailTrace_4634051
  have hstable : (prefixWord ++ tailWord_4634051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634051).length < 2 ^ (prefixWord ++ tailWord_4634051).sum := by decide
  have hdescent : baseEnd_4634051 < baseStart_4634051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634052 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 1, 2, 3]
def baseStart_4634052 : Nat := 118140960795 + 4634052 * 2 ^ 59
def prefixEnd_4634052 : Nat := 4983230072969 + 3 ^ 40 * 4634052 * 2
def baseEnd_4634052 : Nat := 2379496053929008483938389

theorem tailTrace_4634052 : CollatzResearch.WordTrace tailWord_4634052 prefixEnd_4634052 2379496053929008483938389 := by
  unfold tailWord_4634052
  simp only [CollatzResearch.WordTrace]
  refine ⟨84508880903814255958752205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112678507871752341278336273 84508880903814255958752205)
  ·
    refine ⟨31690830338930345984532077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84508880903814255958752205 31690830338930345984532077)
    ·
      refine ⟨11884061377098879744199529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31690830338930345984532077 11884061377098879744199529)
      ·
        refine ⟨8913046032824159808149647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11884061377098879744199529 8913046032824159808149647)
        ·
          refine ⟨13369569049236239712224471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8913046032824159808149647 13369569049236239712224471)
          ·
            refine ⟨20054353573854359568336707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13369569049236239712224471 20054353573854359568336707)
            ·
              refine ⟨30081530360781539352505061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20054353573854359568336707 30081530360781539352505061)
              ·
                refine ⟨5640286942646538628594699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 30081530360781539352505061 5640286942646538628594699)
                ·
                  refine ⟨8460430413969807942892049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640286942646538628594699 8460430413969807942892049)
                  ·
                    refine ⟨6345322810477355957169037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8460430413969807942892049 6345322810477355957169037)
                    ·
                      refine ⟨2379496053929008483938389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6345322810477355957169037 2379496053929008483938389)
                      ·
                        rfl

theorem cell23_4634052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 1, 2, 3].length) (baseStart_4634052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634052 prefixEnd_4634052 := by exact prefixLift 4634052
  have htrace : WordTrace (prefixWord ++ tailWord_4634052) baseStart_4634052 baseEnd_4634052 := by
    simpa [prefixWord, tailWord_4634052, baseEnd_4634052] using wordTrace_append hprefix tailTrace_4634052
  have hstable : (prefixWord ++ tailWord_4634052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634052).length < 2 ^ (prefixWord ++ tailWord_4634052).sum := by decide
  have hdescent : baseEnd_4634052 < baseStart_4634052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634071 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 8]
def baseStart_4634071 : Nat := 118140960795 + 4634071 * 2 ^ 59
def prefixEnd_4634071 : Nat := 4983230072969 + 3 ^ 40 * 4634071 * 2
def baseEnd_4634071 : Nat := 2379505810061443909600801

theorem tailTrace_4634071 : CollatzResearch.WordTrace tailWord_4634071 prefixEnd_4634071 2379505810061443909600801 := by
  unfold tailWord_4634071
  simp only [CollatzResearch.WordTrace]
  refine ⟨169018454794559678162446067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112678969863039785441630711 169018454794559678162446067)
  ·
    refine ⟨253527682191839517243669101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169018454794559678162446067 253527682191839517243669101)
    ·
      refine ⟨95072880821939818966375913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253527682191839517243669101 95072880821939818966375913)
      ·
        refine ⟨71304660616454864224781935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95072880821939818966375913 71304660616454864224781935)
        ·
          refine ⟨106956990924682296337172903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71304660616454864224781935 106956990924682296337172903)
          ·
            refine ⟨160435486387023444505759355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106956990924682296337172903 160435486387023444505759355)
            ·
              refine ⟨240653229580535166758639033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160435486387023444505759355 240653229580535166758639033)
              ·
                refine ⟨180489922185401375068979275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240653229580535166758639033 180489922185401375068979275)
                ·
                  refine ⟨270734883278102062603468913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180489922185401375068979275 270734883278102062603468913)
                  ·
                    refine ⟨203051162458576546952601685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 270734883278102062603468913 203051162458576546952601685)
                    ·
                      refine ⟨2379505810061443909600801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 203051162458576546952601685 2379505810061443909600801)
                      ·
                        rfl

theorem cell23_4634071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_4634071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634071 prefixEnd_4634071 := by exact prefixLift 4634071
  have htrace : WordTrace (prefixWord ++ tailWord_4634071) baseStart_4634071 baseEnd_4634071 := by
    simpa [prefixWord, tailWord_4634071, baseEnd_4634071] using wordTrace_append hprefix tailTrace_4634071
  have hstable : (prefixWord ++ tailWord_4634071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634071).length < 2 ^ (prefixWord ++ tailWord_4634071).sum := by decide
  have hdescent : baseEnd_4634071 < baseStart_4634071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634088 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 2, 3, 4]
def baseStart_4634088 : Nat := 118140960795 + 4634088 * 2 ^ 59
def prefixEnd_4634088 : Nat := 4983230072969 + 3 ^ 40 * 4634088 * 2
def baseEnd_4634088 : Nat := 2379514539232570343088223

theorem tailTrace_4634088 : CollatzResearch.WordTrace tailWord_4634088 prefixEnd_4634088 2379514539232570343088223 := by
  unfold tailWord_4634088
  simp only [CollatzResearch.WordTrace]
  refine ⟨84509537417749045032907459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112679383223665393377209945 84509537417749045032907459)
  ·
    refine ⟨126764306126623567549361189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84509537417749045032907459 126764306126623567549361189)
    ·
      refine ⟨23768307398741918915505223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126764306126623567549361189 23768307398741918915505223)
      ·
        refine ⟨35652461098112878373257835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23768307398741918915505223 35652461098112878373257835)
        ·
          refine ⟨53478691647169317559886753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35652461098112878373257835 53478691647169317559886753)
          ·
            refine ⟨40109018735376988169915065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53478691647169317559886753 40109018735376988169915065)
            ·
              refine ⟨30081764051532741127436299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40109018735376988169915065 30081764051532741127436299)
              ·
                refine ⟨45122646077299111691154449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30081764051532741127436299 45122646077299111691154449)
                ·
                  refine ⟨33841984557974333768365837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45122646077299111691154449 33841984557974333768365837)
                  ·
                    refine ⟨12690744209240375163137189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33841984557974333768365837 12690744209240375163137189)
                    ·
                      refine ⟨2379514539232570343088223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12690744209240375163137189 2379514539232570343088223)
                      ·
                        rfl

theorem cell23_4634088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_4634088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634088 prefixEnd_4634088 := by exact prefixLift 4634088
  have htrace : WordTrace (prefixWord ++ tailWord_4634088) baseStart_4634088 baseEnd_4634088 := by
    simpa [prefixWord, tailWord_4634088, baseEnd_4634088] using wordTrace_append hprefix tailTrace_4634088
  have hstable : (prefixWord ++ tailWord_4634088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634088).length < 2 ^ (prefixWord ++ tailWord_4634088).sum := by decide
  have hdescent : baseEnd_4634088 < baseStart_4634088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634105 : List Nat := [1, 2, 1, 3, 1, 2, 1, 5, 1, 4, 2]
def baseStart_4634105 : Nat := 118140960795 + 4634105 * 2 ^ 59
def prefixEnd_4634105 : Nat := 4983230072969 + 3 ^ 40 * 4634105 * 2
def baseEnd_4634105 : Nat := 2379523268403696776575645

theorem tailTrace_4634105 : CollatzResearch.WordTrace tailWord_4634105 prefixEnd_4634105 2379523268403696776575645 := by
  unfold tailWord_4634105
  simp only [CollatzResearch.WordTrace]
  refine ⟨169019694876436501969183769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112679796584291001312789179 169019694876436501969183769)
  ·
    refine ⟨126764771157327376476887827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169019694876436501969183769 126764771157327376476887827)
    ·
      refine ⟨190147156735991064715331741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126764771157327376476887827 190147156735991064715331741)
      ·
        refine ⟨71305183775996649268249403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190147156735991064715331741 71305183775996649268249403)
        ·
          refine ⟨106957775663994973902374105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71305183775996649268249403 106957775663994973902374105)
          ·
            refine ⟨80218331747996230426780579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106957775663994973902374105 80218331747996230426780579)
            ·
              refine ⟨120327497621994345640170869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80218331747996230426780579 120327497621994345640170869)
              ·
                refine ⟨11280702902061969903766019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120327497621994345640170869 11280702902061969903766019)
                ·
                  refine ⟨16921054353092954855649029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11280702902061969903766019 16921054353092954855649029)
                  ·
                    refine ⟨3172697691204929035434193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16921054353092954855649029 3172697691204929035434193)
                    ·
                      refine ⟨2379523268403696776575645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172697691204929035434193 2379523268403696776575645)
                      ·
                        rfl

theorem cell23_4634105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 5, 1, 4, 2].length) (baseStart_4634105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634105 prefixEnd_4634105 := by exact prefixLift 4634105
  have htrace : WordTrace (prefixWord ++ tailWord_4634105) baseStart_4634105 baseEnd_4634105 := by
    simpa [prefixWord, tailWord_4634105, baseEnd_4634105] using wordTrace_append hprefix tailTrace_4634105
  have hstable : (prefixWord ++ tailWord_4634105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634105).length < 2 ^ (prefixWord ++ tailWord_4634105).sum := by decide
  have hdescent : baseEnd_4634105 < baseStart_4634105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634108 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_4634108 : Nat := 118140960795 + 4634108 * 2 ^ 59
def prefixEnd_4634108 : Nat := 4983230072969 + 3 ^ 40 * 4634108 * 2
def baseEnd_4634108 : Nat := 2379524808845660264838131

theorem tailTrace_4634108 : CollatzResearch.WordTrace tailWord_4634108 prefixEnd_4634108 2379524808845660264838131 := by
  unfold tailWord_4634108
  simp only [CollatzResearch.WordTrace]
  refine ⟨84509902147712816740771489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112679869530283755654361985 84509902147712816740771489)
  ·
    refine ⟨63382426610784612555578617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84509902147712816740771489 63382426610784612555578617)
    ·
      refine ⟨47536819958088459416683963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63382426610784612555578617 47536819958088459416683963)
      ·
        refine ⟨71305229937132689125025945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47536819958088459416683963 71305229937132689125025945)
        ·
          refine ⟨53478922452849516843769459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71305229937132689125025945 53478922452849516843769459)
          ·
            refine ⟨80218383679274275265654189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53478922452849516843769459 80218383679274275265654189)
            ·
              refine ⟨30081893879727853224620321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80218383679274275265654189 30081893879727853224620321)
              ·
                refine ⟨22561420409795889918465241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30081893879727853224620321 22561420409795889918465241)
                ·
                  refine ⟨16921065307346917438848931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22561420409795889918465241 16921065307346917438848931)
                  ·
                    refine ⟨25381597961020376158273397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16921065307346917438848931 25381597961020376158273397)
                    ·
                      refine ⟨2379524808845660264838131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25381597961020376158273397 2379524808845660264838131)
                      ·
                        rfl

theorem cell23_4634108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_4634108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634108 prefixEnd_4634108 := by exact prefixLift 4634108
  have htrace : WordTrace (prefixWord ++ tailWord_4634108) baseStart_4634108 baseEnd_4634108 := by
    simpa [prefixWord, tailWord_4634108, baseEnd_4634108] using wordTrace_append hprefix tailTrace_4634108
  have hstable : (prefixWord ++ tailWord_4634108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634108).length < 2 ^ (prefixWord ++ tailWord_4634108).sum := by decide
  have hdescent : baseEnd_4634108 < baseStart_4634108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634109 : List Nat := [1, 4, 1, 1, 1, 6, 1, 2, 1, 3, 2]
def baseStart_4634109 : Nat := 118140960795 + 4634109 * 2 ^ 59
def prefixEnd_4634109 : Nat := 4983230072969 + 3 ^ 40 * 4634109 * 2
def baseEnd_4634109 : Nat := 2379525322326314760925627

theorem tailTrace_4634109 : CollatzResearch.WordTrace tailWord_4634109 prefixEnd_4634109 2379525322326314760925627 := by
  unfold tailWord_4634109
  simp only [CollatzResearch.WordTrace]
  refine ⟨169019840768422010652329381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112679893845614673768219587 169019840768422010652329381)
  ·
    refine ⟨31691220144079126997311759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169019840768422010652329381 31691220144079126997311759)
    ·
      refine ⟨47536830216118690495967639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31691220144079126997311759 47536830216118690495967639)
      ·
        refine ⟨71305245324178035743951459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47536830216118690495967639 71305245324178035743951459)
        ·
          refine ⟨106957867986267053615927189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71305245324178035743951459 106957867986267053615927189)
          ·
            refine ⟨5013650061856268138246587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106957867986267053615927189 5013650061856268138246587)
            ·
              refine ⟨7520475092784402207369881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5013650061856268138246587 7520475092784402207369881)
              ·
                refine ⟨5640356319588301655527411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7520475092784402207369881 5640356319588301655527411)
                ·
                  refine ⟨8460534479382452483291117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640356319588301655527411 8460534479382452483291117)
                  ·
                    refine ⟨3172700429768419681234169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8460534479382452483291117 3172700429768419681234169)
                    ·
                      refine ⟨2379525322326314760925627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172700429768419681234169 2379525322326314760925627)
                      ·
                        rfl

theorem cell23_4634109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 2, 1, 3, 2].length) (baseStart_4634109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634109 prefixEnd_4634109 := by exact prefixLift 4634109
  have htrace : WordTrace (prefixWord ++ tailWord_4634109) baseStart_4634109 baseEnd_4634109 := by
    simpa [prefixWord, tailWord_4634109, baseEnd_4634109] using wordTrace_append hprefix tailTrace_4634109
  have hstable : (prefixWord ++ tailWord_4634109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634109).length < 2 ^ (prefixWord ++ tailWord_4634109).sum := by decide
  have hdescent : baseEnd_4634109 < baseStart_4634109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634122 : List Nat := [3, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2]
def baseStart_4634122 : Nat := 118140960795 + 4634122 * 2 ^ 59
def prefixEnd_4634122 : Nat := 4983230072969 + 3 ^ 40 * 4634122 * 2
def baseEnd_4634122 : Nat := 2379531997574823210063067

theorem tailTrace_4634122 : CollatzResearch.WordTrace tailWord_4634122 prefixEnd_4634122 2379531997574823210063067 := by
  unfold tailWord_4634122
  simp only [CollatzResearch.WordTrace]
  refine ⟨42255078729343728468138155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112680209944916609248368413 42255078729343728468138155)
  ·
    refine ⟨63382618094015592702207233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42255078729343728468138155 63382618094015592702207233)
    ·
      refine ⟨47536963570511694526655425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63382618094015592702207233 47536963570511694526655425)
      ·
        refine ⟨35652722677883770894991569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47536963570511694526655425 35652722677883770894991569)
        ·
          refine ⟨26739542008412828171243677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35652722677883770894991569 26739542008412828171243677)
          ·
            refine ⟨10027328253154810564216379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26739542008412828171243677 10027328253154810564216379)
            ·
              refine ⟨15040992379732215846324569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10027328253154810564216379 15040992379732215846324569)
              ·
                refine ⟨11280744284799161884743427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15040992379732215846324569 11280744284799161884743427)
                ·
                  refine ⟨16921116427198742827115141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11280744284799161884743427 16921116427198742827115141)
                  ·
                    refine ⟨3172709330099764280084089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16921116427198742827115141 3172709330099764280084089)
                    ·
                      refine ⟨2379531997574823210063067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172709330099764280084089 2379531997574823210063067)
                      ·
                        rfl

theorem cell23_4634122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2].length) (baseStart_4634122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634122 prefixEnd_4634122 := by exact prefixLift 4634122
  have htrace : WordTrace (prefixWord ++ tailWord_4634122) baseStart_4634122 baseEnd_4634122 := by
    simpa [prefixWord, tailWord_4634122, baseEnd_4634122] using wordTrace_append hprefix tailTrace_4634122
  have hstable : (prefixWord ++ tailWord_4634122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634122).length < 2 ^ (prefixWord ++ tailWord_4634122).sum := by decide
  have hdescent : baseEnd_4634122 < baseStart_4634122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634126 : List Nat := [4, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2]
def baseStart_4634126 : Nat := 118140960795 + 4634126 * 2 ^ 59
def prefixEnd_4634126 : Nat := 4983230072969 + 3 ^ 40 * 4634126 * 2
def baseEnd_4634126 : Nat := 2379534051497441194413049

theorem tailTrace_4634126 : CollatzResearch.WordTrace tailWord_4634126 prefixEnd_4634126 2379534051497441194413049 := by
  unfold tailWord_4634126
  simp only [CollatzResearch.WordTrace]
  refine ⟨21127557601170052819462279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112680307206240281703798821 21127557601170052819462279)
  ·
    refine ⟨31691336401755079229193419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21127557601170052819462279 31691336401755079229193419)
    ·
      refine ⟨47537004602632618843790129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31691336401755079229193419 47537004602632618843790129)
      ·
        refine ⟨35652753451974464132842597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47537004602632618843790129 35652753451974464132842597)
        ·
          refine ⟨6684891272245212024907987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35652753451974464132842597 6684891272245212024907987)
          ·
            refine ⟨10027336908367818037361981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6684891272245212024907987 10027336908367818037361981)
            ·
              refine ⟨3760251340637931764010743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10027336908367818037361981 3760251340637931764010743)
              ·
                refine ⟨5640377010956897646016115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760251340637931764010743 5640377010956897646016115)
                ·
                  refine ⟨8460565516435346469024173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640377010956897646016115 8460565516435346469024173)
                  ·
                    refine ⟨3172712068663254925884065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8460565516435346469024173 3172712068663254925884065)
                    ·
                      refine ⟨2379534051497441194413049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172712068663254925884065 2379534051497441194413049)
                      ·
                        rfl

theorem cell23_4634126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 3, 1, 1, 3, 2].length) (baseStart_4634126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634126 prefixEnd_4634126 := by exact prefixLift 4634126
  have htrace : WordTrace (prefixWord ++ tailWord_4634126) baseStart_4634126 baseEnd_4634126 := by
    simpa [prefixWord, tailWord_4634126, baseEnd_4634126] using wordTrace_append hprefix tailTrace_4634126
  have hstable : (prefixWord ++ tailWord_4634126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634126).length < 2 ^ (prefixWord ++ tailWord_4634126).sum := by decide
  have hdescent : baseEnd_4634126 < baseStart_4634126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634152 : List Nat := [2, 1, 5, 2, 2, 1, 1, 1, 2, 2, 4]
def baseStart_4634152 : Nat := 118140960795 + 4634152 * 2 ^ 59
def prefixEnd_4634152 : Nat := 4983230072969 + 3 ^ 40 * 4634152 * 2
def baseEnd_4634152 : Nat := 2379547401994458092687929

theorem tailTrace_4634152 : CollatzResearch.WordTrace tailWord_4634152 prefixEnd_4634152 2379547401994458092687929 := by
  unfold tailWord_4634152
  simp only [CollatzResearch.WordTrace]
  refine ⟨84510704553633114498072355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112680939404844152664096473 84510704553633114498072355)
  ·
    refine ⟨126766056830449671747108533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84510704553633114498072355 126766056830449671747108533)
    ·
      refine ⟨11884317827854656726291425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126766056830449671747108533 11884317827854656726291425)
      ·
        refine ⟨8913238370890992544718569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11884317827854656726291425 8913238370890992544718569)
        ·
          refine ⟨6684928778168244408538927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8913238370890992544718569 6684928778168244408538927)
          ·
            refine ⟨10027393167252366612808391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6684928778168244408538927 10027393167252366612808391)
            ·
              refine ⟨15041089750878549919212587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10027393167252366612808391 15041089750878549919212587)
              ·
                refine ⟨22561634626317824878818881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15041089750878549919212587 22561634626317824878818881)
                ·
                  refine ⟨16921225969738368659114161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22561634626317824878818881 16921225969738368659114161)
                  ·
                    refine ⟨12690919477303776494335621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16921225969738368659114161 12690919477303776494335621)
                    ·
                      refine ⟨2379547401994458092687929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12690919477303776494335621 2379547401994458092687929)
                      ·
                        rfl

theorem cell23_4634152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_4634152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634152 prefixEnd_4634152 := by exact prefixLift 4634152
  have htrace : WordTrace (prefixWord ++ tailWord_4634152) baseStart_4634152 baseEnd_4634152 := by
    simpa [prefixWord, tailWord_4634152, baseEnd_4634152] using wordTrace_append hprefix tailTrace_4634152
  have hstable : (prefixWord ++ tailWord_4634152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634152).length < 2 ^ (prefixWord ++ tailWord_4634152).sum := by decide
  have hdescent : baseEnd_4634152 < baseStart_4634152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634175 : List Nat := [1, 1, 2, 2, 3, 3, 3, 1, 2, 5]
def baseStart_4634175 : Nat := 118140960795 + 4634175 * 2 ^ 59
def prefixEnd_4634175 : Nat := 4983230072969 + 3 ^ 40 * 4634175 * 2
def baseEnd_4634175 : Nat := 793186404016503834233441

theorem tailTrace_4634175 : CollatzResearch.WordTrace tailWord_4634175 prefixEnd_4634175 793186404016503834233441 := by
  unfold tailWord_4634175
  simp only [CollatzResearch.WordTrace]
  refine ⟨169022247986182903924231979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112681498657455269282821319 169022247986182903924231979)
  ·
    refine ⟨253533371979274355886347969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169022247986182903924231979 253533371979274355886347969)
    ·
      refine ⟨190150028984455766914760977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253533371979274355886347969 190150028984455766914760977)
      ·
        refine ⟨142612521738341825186070733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190150028984455766914760977 142612521738341825186070733)
        ·
          refine ⟨53479695651878184444776525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142612521738341825186070733 53479695651878184444776525)
          ·
            refine ⟨20054885869454319166791197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53479695651878184444776525 20054885869454319166791197)
            ·
              refine ⟨7520582201045369687546699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20054885869454319166791197 7520582201045369687546699)
              ·
                refine ⟨11280873301568054531320049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7520582201045369687546699 11280873301568054531320049)
                ·
                  refine ⟨8460654976176040898490037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11280873301568054531320049 8460654976176040898490037)
                  ·
                    refine ⟨793186404016503834233441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8460654976176040898490037 793186404016503834233441)
                    ·
                      rfl

theorem cell23_4634175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 1, 2, 5].length) (baseStart_4634175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634175 prefixEnd_4634175 := by exact prefixLift 4634175
  have htrace : WordTrace (prefixWord ++ tailWord_4634175) baseStart_4634175 baseEnd_4634175 := by
    simpa [prefixWord, tailWord_4634175, baseEnd_4634175] using wordTrace_append hprefix tailTrace_4634175
  have hstable : (prefixWord ++ tailWord_4634175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634175).length < 2 ^ (prefixWord ++ tailWord_4634175).sum := by decide
  have hdescent : baseEnd_4634175 < baseStart_4634175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634208 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 6]
def baseStart_4634208 : Nat := 118140960795 + 4634208 * 2 ^ 59
def prefixEnd_4634208 : Nat := 4983230072969 + 3 ^ 40 * 4634208 * 2
def baseEnd_4634208 : Nat := 2379576156911109873587671

theorem tailTrace_4634208 : CollatzResearch.WordTrace tailWord_4634208 prefixEnd_4634208 2379576156911109873587671 := by
  unfold tailWord_4634208
  simp only [CollatzResearch.WordTrace]
  refine ⟨84511725797531675280091639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112682301063375567040122185 84511725797531675280091639)
  ·
    refine ⟨126767588696297512920137459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84511725797531675280091639 126767588696297512920137459)
    ·
      refine ⟨190151383044446269380206189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126767588696297512920137459 190151383044446269380206189)
      ·
        refine ⟨71306768641667351017577321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190151383044446269380206189 71306768641667351017577321)
        ·
          refine ⟨53480076481250513263182991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71306768641667351017577321 53480076481250513263182991)
          ·
            refine ⟨80220114721875769894774487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53480076481250513263182991 80220114721875769894774487)
            ·
              refine ⟨120330172082813654842161731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80220114721875769894774487 120330172082813654842161731)
              ·
                refine ⟨180495258124220482263242597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120330172082813654842161731 180495258124220482263242597)
                ·
                  refine ⟨33842860898291340424357987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180495258124220482263242597 33842860898291340424357987)
                  ·
                    refine ⟨50764291347437010636536981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33842860898291340424357987 50764291347437010636536981)
                    ·
                      refine ⟨2379576156911109873587671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50764291347437010636536981 2379576156911109873587671)
                      ·
                        rfl

theorem cell23_4634208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_4634208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634208 prefixEnd_4634208 := by exact prefixLift 4634208
  have htrace : WordTrace (prefixWord ++ tailWord_4634208) baseStart_4634208 baseEnd_4634208 := by
    simpa [prefixWord, tailWord_4634208, baseEnd_4634208] using wordTrace_append hprefix tailTrace_4634208
  have hstable : (prefixWord ++ tailWord_4634208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634208).length < 2 ^ (prefixWord ++ tailWord_4634208).sum := by decide
  have hdescent : baseEnd_4634208 < baseStart_4634208 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634212 : List Nat := [2, 3, 1, 1, 2, 3, 2, 1, 2, 4, 2]
def baseStart_4634212 : Nat := 118140960795 + 4634212 * 2 ^ 59
def prefixEnd_4634212 : Nat := 4983230072969 + 3 ^ 40 * 4634212 * 2
def baseEnd_4634212 : Nat := 2379578210833727857937653

theorem tailTrace_4634212 : CollatzResearch.WordTrace tailWord_4634212 prefixEnd_4634212 2379578210833727857937653 := by
  unfold tailWord_4634212
  simp only [CollatzResearch.WordTrace]
  refine ⟨84511798743524429621664445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112682398324699239495552593 84511798743524429621664445)
  ·
    refine ⟨31691924528821661108124167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84511798743524429621664445 31691924528821661108124167)
    ·
      refine ⟨47537886793232491662186251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31691924528821661108124167 47537886793232491662186251)
      ·
        refine ⟨71306830189848737493279377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47537886793232491662186251 71306830189848737493279377)
        ·
          refine ⟨53480122642386553119959533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71306830189848737493279377 53480122642386553119959533)
          ·
            refine ⟨20055045990894957419984825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53480122642386553119959533 20055045990894957419984825)
            ·
              refine ⟨15041284493171218064988619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20055045990894957419984825 15041284493171218064988619)
              ·
                refine ⟨22561926739756827097482929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15041284493171218064988619 22561926739756827097482929)
                ·
                  refine ⟨16921445054817620323112197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22561926739756827097482929 16921445054817620323112197)
                  ·
                    refine ⟨3172770947778303810583537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16921445054817620323112197 3172770947778303810583537)
                    ·
                      refine ⟨2379578210833727857937653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172770947778303810583537 2379578210833727857937653)
                      ·
                        rfl

theorem cell23_4634212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 1, 2, 4, 2].length) (baseStart_4634212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634212 prefixEnd_4634212 := by exact prefixLift 4634212
  have htrace : WordTrace (prefixWord ++ tailWord_4634212) baseStart_4634212 baseEnd_4634212 := by
    simpa [prefixWord, tailWord_4634212, baseEnd_4634212] using wordTrace_append hprefix tailTrace_4634212
  have hstable : (prefixWord ++ tailWord_4634212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634212).length < 2 ^ (prefixWord ++ tailWord_4634212).sum := by decide
  have hdescent : baseEnd_4634212 < baseStart_4634212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634215 : List Nat := [1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 3]
def baseStart_4634215 : Nat := 118140960795 + 4634215 * 2 ^ 59
def prefixEnd_4634215 : Nat := 4983230072969 + 3 ^ 40 * 4634215 * 2
def baseEnd_4634215 : Nat := 2379579751275691346200139

theorem tailTrace_4634215 : CollatzResearch.WordTrace tailWord_4634215 prefixEnd_4634215 2379579751275691346200139 := by
  unfold tailWord_4634215
  simp only [CollatzResearch.WordTrace]
  refine ⟨169023706906037990755688099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112682471270691993837125399 169023706906037990755688099)
  ·
    refine ⟨253535560359056986133532149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169023706906037990755688099 253535560359056986133532149)
    ·
      refine ⟨23768958783661592450018639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 253535560359056986133532149 23768958783661592450018639)
      ·
        refine ⟨35653438175492388675027959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23768958783661592450018639 35653438175492388675027959)
        ·
          refine ⟨53480157263238583012541939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35653438175492388675027959 53480157263238583012541939)
          ·
            refine ⟨80220235894857874518812909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53480157263238583012541939 80220235894857874518812909)
            ·
              refine ⟨30082588460571702944554841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80220235894857874518812909 30082588460571702944554841)
              ·
                refine ⟨22561941345428777208416131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30082588460571702944554841 22561941345428777208416131)
                ·
                  refine ⟨33842912018143165812624197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22561941345428777208416131 33842912018143165812624197)
                  ·
                    refine ⟨6345546003401843589867037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33842912018143165812624197 6345546003401843589867037)
                    ·
                      refine ⟨2379579751275691346200139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6345546003401843589867037 2379579751275691346200139)
                      ·
                        rfl

theorem cell23_4634215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 3].length) (baseStart_4634215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634215 prefixEnd_4634215 := by exact prefixLift 4634215
  have htrace : WordTrace (prefixWord ++ tailWord_4634215) baseStart_4634215 baseEnd_4634215 := by
    simpa [prefixWord, tailWord_4634215, baseEnd_4634215] using wordTrace_append hprefix tailTrace_4634215
  have hstable : (prefixWord ++ tailWord_4634215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634215).length < 2 ^ (prefixWord ++ tailWord_4634215).sum := by decide
  have hdescent : baseEnd_4634215 < baseStart_4634215 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634295 : List Nat := [1, 1, 3, 1, 5, 1, 1, 1, 3, 6]
def baseStart_4634295 : Nat := 118140960795 + 4634295 * 2 ^ 59
def prefixEnd_4634295 : Nat := 4983230072969 + 3 ^ 40 * 4634295 * 2
def baseEnd_4634295 : Nat := 793206943242683677733257

theorem tailTrace_4634295 : CollatzResearch.WordTrace tailWord_4634295 prefixEnd_4634295 793206943242683677733257 := by
  unfold tailWord_4634295
  simp only [CollatzResearch.WordTrace]
  refine ⟨169026624745748164418600339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112684416497165442945733559 169026624745748164418600339)
  ·
    refine ⟨253539937118622246627900509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169026624745748164418600339 253539937118622246627900509)
    ·
      refine ⟨95077476419483342485462691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253539937118622246627900509 95077476419483342485462691)
      ·
        refine ⟨142616214629225013728194037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95077476419483342485462691 142616214629225013728194037)
        ·
          refine ⟨13370270121489845037018191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142616214629225013728194037 13370270121489845037018191)
          ·
            refine ⟨20055405182234767555527287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13370270121489845037018191 20055405182234767555527287)
            ·
              refine ⟨30083107773352151333290931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20055405182234767555527287 30083107773352151333290931)
              ·
                refine ⟨45124661660028226999936397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30083107773352151333290931 45124661660028226999936397)
                ·
                  refine ⟨16921748122510585124976149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45124661660028226999936397 16921748122510585124976149)
                  ·
                    refine ⟨793206943242683677733257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16921748122510585124976149 793206943242683677733257)
                    ·
                      rfl

theorem cell23_4634295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 3, 6].length) (baseStart_4634295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634295 prefixEnd_4634295 := by exact prefixLift 4634295
  have htrace : WordTrace (prefixWord ++ tailWord_4634295) baseStart_4634295 baseEnd_4634295 := by
    simpa [prefixWord, tailWord_4634295, baseEnd_4634295] using wordTrace_append hprefix tailTrace_4634295
  have hstable : (prefixWord ++ tailWord_4634295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634295).length < 2 ^ (prefixWord ++ tailWord_4634295).sum := by decide
  have hdescent : baseEnd_4634295 < baseStart_4634295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634353 : List Nat := [1, 2, 2, 2, 2, 4, 2, 3, 1, 2, 2]
def baseStart_4634353 : Nat := 118140960795 + 4634353 * 2 ^ 59
def prefixEnd_4634353 : Nat := 4983230072969 + 3 ^ 40 * 4634353 * 2
def baseEnd_4634353 : Nat := 2379650611606011806274505

theorem tailTrace_4634353 : CollatzResearch.WordTrace tailWord_4634353 prefixEnd_4634353 2379650611606011806274505 := by
  unfold tailWord_4634353
  simp only [CollatzResearch.WordTrace]
  refine ⟨169028740179538040324211713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112685826786358693549474475 169028740179538040324211713)
  ·
    refine ⟨126771555134653530243158785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169028740179538040324211713 126771555134653530243158785)
    ·
      refine ⟨95078666350990147682369089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126771555134653530243158785 95078666350990147682369089)
      ·
        refine ⟨71308999763242610761776817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95078666350990147682369089 71308999763242610761776817)
        ·
          refine ⟨53481749822431958071332613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71308999763242610761776817 53481749822431958071332613)
          ·
            refine ⟨10027828091705992138374865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53481749822431958071332613 10027828091705992138374865)
            ·
              refine ⟨7520871068779494103781149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10027828091705992138374865 7520871068779494103781149)
              ·
                refine ⟨2820326650792310288917931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7520871068779494103781149 2820326650792310288917931)
                ·
                  refine ⟨4230489976188465433376897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2820326650792310288917931 4230489976188465433376897)
                  ·
                    refine ⟨3172867482141349075032673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4230489976188465433376897 3172867482141349075032673)
                    ·
                      refine ⟨2379650611606011806274505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172867482141349075032673 2379650611606011806274505)
                      ·
                        rfl

theorem cell23_4634353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 3, 1, 2, 2].length) (baseStart_4634353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634353 prefixEnd_4634353 := by exact prefixLift 4634353
  have htrace : WordTrace (prefixWord ++ tailWord_4634353) baseStart_4634353 baseEnd_4634353 := by
    simpa [prefixWord, tailWord_4634353, baseEnd_4634353] using wordTrace_append hprefix tailTrace_4634353
  have hstable : (prefixWord ++ tailWord_4634353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634353).length < 2 ^ (prefixWord ++ tailWord_4634353).sum := by decide
  have hdescent : baseEnd_4634353 < baseStart_4634353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634365 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_4634365 : Nat := 118140960795 + 4634365 * 2 ^ 59
def prefixEnd_4634365 : Nat := 4983230072969 + 3 ^ 40 * 4634365 * 2
def baseEnd_4634365 : Nat := 2379656773373865759324449

theorem tailTrace_4634365 : CollatzResearch.WordTrace tailWord_4634365 prefixEnd_4634365 2379656773373865759324449 := by
  unfold tailWord_4634365
  simp only [CollatzResearch.WordTrace]
  refine ⟨169029177855494566373648549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112686118570329710915765699 169029177855494566373648549)
  ·
    refine ⟨31692970847905231195059103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169029177855494566373648549 31692970847905231195059103)
    ·
      refine ⟨47539456271857846792588655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31692970847905231195059103 47539456271857846792588655)
      ·
        refine ⟨71309184407786770188882983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47539456271857846792588655 71309184407786770188882983)
        ·
          refine ⟨106963776611680155283324475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71309184407786770188882983 106963776611680155283324475)
          ·
            refine ⟨160445664917520232924986713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106963776611680155283324475 160445664917520232924986713)
            ·
              refine ⟨120334248688140174693740035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160445664917520232924986713 120334248688140174693740035)
              ·
                refine ⟨180501373032210262040610053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120334248688140174693740035 180501373032210262040610053)
                ·
                  refine ⟨33844007443539424132614385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180501373032210262040610053 33844007443539424132614385)
                  ·
                    refine ⟨25383005582654568099460789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33844007443539424132614385 25383005582654568099460789)
                    ·
                      refine ⟨2379656773373865759324449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25383005582654568099460789 2379656773373865759324449)
                      ·
                        rfl

theorem cell23_4634365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_4634365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634365 prefixEnd_4634365 := by exact prefixLift 4634365
  have htrace : WordTrace (prefixWord ++ tailWord_4634365) baseStart_4634365 baseEnd_4634365 := by
    simpa [prefixWord, tailWord_4634365, baseEnd_4634365] using wordTrace_append hprefix tailTrace_4634365
  have hstable : (prefixWord ++ tailWord_4634365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634365).length < 2 ^ (prefixWord ++ tailWord_4634365).sum := by decide
  have hdescent : baseEnd_4634365 < baseStart_4634365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634386 : List Nat := [3, 2, 4, 1, 1, 1, 3, 1, 1, 3, 3]
def baseStart_4634386 : Nat := 118140960795 + 4634386 * 2 ^ 59
def prefixEnd_4634386 : Nat := 4983230072969 + 3 ^ 40 * 4634386 * 2
def baseEnd_4634386 : Nat := 2379667556467610177161853

theorem tailTrace_4634386 : CollatzResearch.WordTrace tailWord_4634386 prefixEnd_4634386 2379667556467610177161853 := by
  unfold tailWord_4634386
  simp only [CollatzResearch.WordTrace]
  refine ⟨42257485947104621740040753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112686629192278991306775341 42257485947104621740040753)
  ·
    refine ⟨31693114460328466305030565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42257485947104621740040753 31693114460328466305030565)
    ·
      refine ⟨5942458961311587432193231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31693114460328466305030565 5942458961311587432193231)
      ·
        refine ⟨8913688441967381148289847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5942458961311587432193231 8913688441967381148289847)
        ·
          refine ⟨13370532662951071722434771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8913688441967381148289847 13370532662951071722434771)
          ·
            refine ⟨20055798994426607583652157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13370532662951071722434771 20055798994426607583652157)
            ·
              refine ⟨7520924622909977843869559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20055798994426607583652157 7520924622909977843869559)
              ·
                refine ⟨11281386934364966765804339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7520924622909977843869559 11281386934364966765804339)
                ·
                  refine ⟨16922080401547450148706509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11281386934364966765804339 16922080401547450148706509)
                  ·
                    refine ⟨6345780150580293805764941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16922080401547450148706509 6345780150580293805764941)
                    ·
                      refine ⟨2379667556467610177161853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6345780150580293805764941 2379667556467610177161853)
                      ·
                        rfl

theorem cell23_4634386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_4634386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634386 prefixEnd_4634386 := by exact prefixLift 4634386
  have htrace : WordTrace (prefixWord ++ tailWord_4634386) baseStart_4634386 baseEnd_4634386 := by
    simpa [prefixWord, tailWord_4634386, baseEnd_4634386] using wordTrace_append hprefix tailTrace_4634386
  have hstable : (prefixWord ++ tailWord_4634386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634386).length < 2 ^ (prefixWord ++ tailWord_4634386).sum := by decide
  have hdescent : baseEnd_4634386 < baseStart_4634386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634395 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 5]
def baseStart_4634395 : Nat := 118140960795 + 4634395 * 2 ^ 59
def prefixEnd_4634395 : Nat := 4983230072969 + 3 ^ 40 * 4634395 * 2
def baseEnd_4634395 : Nat := 2379672177793500641949311

theorem tailTrace_4634395 : CollatzResearch.WordTrace tailWord_4634395 prefixEnd_4634395 2379672177793500641949311 := by
  unfold tailWord_4634395
  simp only [CollatzResearch.WordTrace]
  refine ⟨169030272045385881497240639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112686848030257254331493759 169030272045385881497240639)
  ·
    refine ⟨253545408068078822245860959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169030272045385881497240639 253545408068078822245860959)
    ·
      refine ⟨380318112102118233368791439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253545408068078822245860959 380318112102118233368791439)
      ·
        refine ⟨570477168153177350053187159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380318112102118233368791439 570477168153177350053187159)
        ·
          refine ⟨855715752229766025079780739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570477168153177350053187159 855715752229766025079780739)
          ·
            refine ⟨1283573628344649037619671109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 855715752229766025079780739 1283573628344649037619671109)
            ·
              refine ⟨240670055314621694553688333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1283573628344649037619671109 240670055314621694553688333)
              ·
                refine ⟨90251270742983135457633125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240670055314621694553688333 90251270742983135457633125)
                ·
                  refine ⟨16922113264309337898306211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 90251270742983135457633125 16922113264309337898306211)
                  ·
                    refine ⟨25383169896464006847459317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16922113264309337898306211 25383169896464006847459317)
                    ·
                      refine ⟨2379672177793500641949311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25383169896464006847459317 2379672177793500641949311)
                      ·
                        rfl

theorem cell23_4634395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 5].length) (baseStart_4634395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634395 prefixEnd_4634395 := by exact prefixLift 4634395
  have htrace : WordTrace (prefixWord ++ tailWord_4634395) baseStart_4634395 baseEnd_4634395 := by
    simpa [prefixWord, tailWord_4634395, baseEnd_4634395] using wordTrace_append hprefix tailTrace_4634395
  have hstable : (prefixWord ++ tailWord_4634395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634395).length < 2 ^ (prefixWord ++ tailWord_4634395).sum := by decide
  have hdescent : baseEnd_4634395 < baseStart_4634395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634396 : List Nat := [2, 2, 3, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_4634396 : Nat := 118140960795 + 4634396 * 2 ^ 59
def prefixEnd_4634396 : Nat := 4983230072969 + 3 ^ 40 * 4634396 * 2
def baseEnd_4634396 : Nat := 2379672691274155138036807

theorem tailTrace_4634396 : CollatzResearch.WordTrace tailWord_4634396 prefixEnd_4634396 2379672691274155138036807 := by
  unfold tailWord_4634396
  simp only [CollatzResearch.WordTrace]
  refine ⟨84515154259191129334013521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112686872345588172445351361 84515154259191129334013521)
  ·
    refine ⟨63386365694393347000510141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84515154259191129334013521 63386365694393347000510141)
    ·
      refine ⟨23769887135397505125191303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63386365694393347000510141 23769887135397505125191303)
      ·
        refine ⟨35654830703096257687786955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23769887135397505125191303 35654830703096257687786955)
        ·
          refine ⟨53482246054644386531680433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35654830703096257687786955 53482246054644386531680433)
          ·
            refine ⟨40111684540983289898760325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53482246054644386531680433 40111684540983289898760325)
            ·
              refine ⟨7520940851434366856017561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40111684540983289898760325 7520940851434366856017561)
              ·
                refine ⟨5640705638575775142013171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7520940851434366856017561 5640705638575775142013171)
                ·
                  refine ⟨8461058457863662713019757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5640705638575775142013171 8461058457863662713019757)
                  ·
                    refine ⟨3172896921698873517382409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8461058457863662713019757 3172896921698873517382409)
                    ·
                      refine ⟨2379672691274155138036807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172896921698873517382409 2379672691274155138036807)
                      ·
                        rfl

theorem cell23_4634396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_4634396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634396 prefixEnd_4634396 := by exact prefixLift 4634396
  have htrace : WordTrace (prefixWord ++ tailWord_4634396) baseStart_4634396 baseEnd_4634396 := by
    simpa [prefixWord, tailWord_4634396, baseEnd_4634396] using wordTrace_append hprefix tailTrace_4634396
  have hstable : (prefixWord ++ tailWord_4634396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634396).length < 2 ^ (prefixWord ++ tailWord_4634396).sum := by decide
  have hdescent : baseEnd_4634396 < baseStart_4634396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634412 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_4634412 : Nat := 118140960795 + 4634412 * 2 ^ 59
def prefixEnd_4634412 : Nat := 4983230072969 + 3 ^ 40 * 4634412 * 2
def baseEnd_4634412 : Nat := 2379680906964627075436733

theorem tailTrace_4634412 : CollatzResearch.WordTrace tailWord_4634412 prefixEnd_4634412 2379680906964627075436733 := by
  unfold tailWord_4634412
  simp only [CollatzResearch.WordTrace]
  refine ⟨84515446043162146700304745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112687261390882862267072993 84515446043162146700304745)
  ·
    refine ⟨63386584532371610025228559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84515446043162146700304745 63386584532371610025228559)
    ·
      refine ⟨95079876798557415037842839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63386584532371610025228559 95079876798557415037842839)
      ·
        refine ⟨142619815197836122556764259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95079876798557415037842839 142619815197836122556764259)
        ·
          refine ⟨213929722796754183835146389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142619815197836122556764259 213929722796754183835146389)
          ·
            refine ⟨10027955756097852367272487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 213929722796754183835146389 10027955756097852367272487)
            ·
              refine ⟨15041933634146778550908731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10027955756097852367272487 15041933634146778550908731)
              ·
                refine ⟨22562900451220167826363097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15041933634146778550908731 22562900451220167826363097)
                ·
                  refine ⟨16922175338415125869772323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22562900451220167826363097 16922175338415125869772323)
                  ·
                    refine ⟨25383263007622688804658485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16922175338415125869772323 25383263007622688804658485)
                    ·
                      refine ⟨2379680906964627075436733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25383263007622688804658485 2379680906964627075436733)
                      ·
                        rfl

theorem cell23_4634412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_4634412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634412 prefixEnd_4634412 := by exact prefixLift 4634412
  have htrace : WordTrace (prefixWord ++ tailWord_4634412) baseStart_4634412 baseEnd_4634412 := by
    simpa [prefixWord, tailWord_4634412, baseEnd_4634412] using wordTrace_append hprefix tailTrace_4634412
  have hstable : (prefixWord ++ tailWord_4634412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634412).length < 2 ^ (prefixWord ++ tailWord_4634412).sum := by decide
  have hdescent : baseEnd_4634412 < baseStart_4634412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634426 : List Nat := [3, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2]
def baseStart_4634426 : Nat := 118140960795 + 4634426 * 2 ^ 59
def prefixEnd_4634426 : Nat := 4983230072969 + 3 ^ 40 * 4634426 * 2
def baseEnd_4634426 : Nat := 2379688095693790020661669

theorem tailTrace_4634426 : CollatzResearch.WordTrace tailWord_4634426 prefixEnd_4634426 2379688095693790020661669 := by
  unfold tailWord_4634426
  simp only [CollatzResearch.WordTrace]
  refine ⟨42257850677068393447904783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112687601805515715861079421 42257850677068393447904783)
  ·
    refine ⟨63386776015602590171857175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42257850677068393447904783 63386776015602590171857175)
    ·
      refine ⟨95080164023403885257785763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63386776015602590171857175 95080164023403885257785763)
      ·
        refine ⟨142620246035105827886678645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95080164023403885257785763 142620246035105827886678645)
        ·
          refine ⟨13370648065791171364376123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 142620246035105827886678645 13370648065791171364376123)
          ·
            refine ⟨20055972098686757046564185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13370648065791171364376123 20055972098686757046564185)
            ·
              refine ⟨15041979074015067784923139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20055972098686757046564185 15041979074015067784923139)
              ·
                refine ⟨22562968611022601677384709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15041979074015067784923139 22562968611022601677384709)
                ·
                  refine ⟨4230556614566737814509633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22562968611022601677384709 4230556614566737814509633)
                  ·
                    refine ⟨3172917460925053360882225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4230556614566737814509633 3172917460925053360882225)
                    ·
                      refine ⟨2379688095693790020661669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172917460925053360882225 2379688095693790020661669)
                      ·
                        rfl

theorem cell23_4634426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_4634426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634426 prefixEnd_4634426 := by exact prefixLift 4634426
  have htrace : WordTrace (prefixWord ++ tailWord_4634426) baseStart_4634426 baseEnd_4634426 := by
    simpa [prefixWord, tailWord_4634426, baseEnd_4634426] using wordTrace_append hprefix tailTrace_4634426
  have hstable : (prefixWord ++ tailWord_4634426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634426).length < 2 ^ (prefixWord ++ tailWord_4634426).sum := by decide
  have hdescent : baseEnd_4634426 < baseStart_4634426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634442 : List Nat := [3, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3]
def baseStart_4634442 : Nat := 118140960795 + 4634442 * 2 ^ 59
def prefixEnd_4634442 : Nat := 4983230072969 + 3 ^ 40 * 4634442 * 2
def baseEnd_4634442 : Nat := 2379696311384261958061595

theorem tailTrace_4634442 : CollatzResearch.WordTrace tailWord_4634442 prefixEnd_4634442 2379696311384261958061595 := by
  unfold tailWord_4634442
  simp only [CollatzResearch.WordTrace]
  refine ⟨42257996569053902131050395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112687990850810405682801053 42257996569053902131050395)
  ·
    refine ⟨63386994853580853196575593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42257996569053902131050395 63386994853580853196575593)
    ·
      refine ⟨47540246140185639897431695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63386994853580853196575593 47540246140185639897431695)
      ·
        refine ⟨71310369210278459846147543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47540246140185639897431695 71310369210278459846147543)
        ·
          refine ⟨106965553815417689769221315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71310369210278459846147543 106965553815417689769221315)
          ·
            refine ⟨160448330723126534653831973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106965553815417689769221315 160448330723126534653831973)
            ·
              refine ⟨30084062010586225247593495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160448330723126534653831973 30084062010586225247593495)
              ·
                refine ⟨45126093015879337871390243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30084062010586225247593495 45126093015879337871390243)
                ·
                  refine ⟨67689139523819006807085365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45126093015879337871390243 67689139523819006807085365)
                  ·
                    refine ⟨6345856830358031888164253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67689139523819006807085365 6345856830358031888164253)
                    ·
                      refine ⟨2379696311384261958061595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6345856830358031888164253 2379696311384261958061595)
                      ·
                        rfl

theorem cell23_4634442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_4634442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634442 prefixEnd_4634442 := by exact prefixLift 4634442
  have htrace : WordTrace (prefixWord ++ tailWord_4634442) baseStart_4634442 baseEnd_4634442 := by
    simpa [prefixWord, tailWord_4634442, baseEnd_4634442] using wordTrace_append hprefix tailTrace_4634442
  have hstable : (prefixWord ++ tailWord_4634442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634442).length < 2 ^ (prefixWord ++ tailWord_4634442).sum := by decide
  have hdescent : baseEnd_4634442 < baseStart_4634442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634472 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 3, 2, 5]
def baseStart_4634472 : Nat := 118140960795 + 4634472 * 2 ^ 59
def prefixEnd_4634472 : Nat := 4983230072969 + 3 ^ 40 * 4634472 * 2
def baseEnd_4634472 : Nat := 2379711715803896840686457

theorem tailTrace_4634472 : CollatzResearch.WordTrace tailWord_4634472 prefixEnd_4634472 2379711715803896840686457 := by
  unfold tailWord_4634472
  simp only [CollatzResearch.WordTrace]
  refine ⟨84516540233053461823896835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112688720310737949098529113 84516540233053461823896835)
  ·
    refine ⟨126774810349580192735845253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84516540233053461823896835 126774810349580192735845253)
    ·
      refine ⟨23770276940546286137970985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126774810349580192735845253 23770276940546286137970985)
      ·
        refine ⟨17827707705409714603478239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23770276940546286137970985 17827707705409714603478239)
        ·
          refine ⟨26741561558114571905217359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17827707705409714603478239 26741561558114571905217359)
          ·
            refine ⟨40112342337171857857826039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26741561558114571905217359 40112342337171857857826039)
            ·
              refine ⟨60168513505757786786739059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40112342337171857857826039 60168513505757786786739059)
              ·
                refine ⟨90252770258636680180108589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60168513505757786786739059 90252770258636680180108589)
                ·
                  refine ⟨33844788846988755067540721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90252770258636680180108589 33844788846988755067540721)
                  ·
                    refine ⟨25383591635241566300655541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33844788846988755067540721 25383591635241566300655541)
                    ·
                      refine ⟨2379711715803896840686457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25383591635241566300655541 2379711715803896840686457)
                      ·
                        rfl

theorem cell23_4634472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_4634472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634472 prefixEnd_4634472 := by exact prefixLift 4634472
  have htrace : WordTrace (prefixWord ++ tailWord_4634472) baseStart_4634472 baseEnd_4634472 := by
    simpa [prefixWord, tailWord_4634472, baseEnd_4634472] using wordTrace_append hprefix tailTrace_4634472
  have hstable : (prefixWord ++ tailWord_4634472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634472).length < 2 ^ (prefixWord ++ tailWord_4634472).sum := by decide
  have hdescent : baseEnd_4634472 < baseStart_4634472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634482 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 3, 3, 4]
def baseStart_4634482 : Nat := 118140960795 + 4634482 * 2 ^ 59
def prefixEnd_4634482 : Nat := 4983230072969 + 3 ^ 40 * 4634482 * 2
def baseEnd_4634482 : Nat := 2379716850610441801561411

theorem tailTrace_4634482 : CollatzResearch.WordTrace tailWord_4634482 prefixEnd_4634482 2379716850610441801561411 := by
  unfold tailWord_4634482
  simp only [CollatzResearch.WordTrace]
  refine ⟨42258361299017673838914425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112688963464047130237105133 42258361299017673838914425)
  ·
    refine ⟨31693770974263255379185819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42258361299017673838914425 31693770974263255379185819)
    ·
      refine ⟨47540656461394883068778729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31693770974263255379185819 47540656461394883068778729)
      ·
        refine ⟨35655492346046162301584047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47540656461394883068778729 35655492346046162301584047)
        ·
          refine ⟨53483238519069243452376071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35655492346046162301584047 53483238519069243452376071)
          ·
            refine ⟨80224857778603865178564107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53483238519069243452376071 80224857778603865178564107)
            ·
              refine ⟨120337286667905797767846161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80224857778603865178564107 120337286667905797767846161)
              ·
                refine ⟨90252965000929348325884621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120337286667905797767846161 90252965000929348325884621)
                ·
                  refine ⟨33844861875348505622206733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90252965000929348325884621 33844861875348505622206733)
                  ·
                    refine ⟨12691823203255689608327525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33844861875348505622206733 12691823203255689608327525)
                    ·
                      refine ⟨2379716850610441801561411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12691823203255689608327525 2379716850610441801561411)
                      ·
                        rfl

theorem cell23_4634482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_4634482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634482 prefixEnd_4634482 := by exact prefixLift 4634482
  have htrace : WordTrace (prefixWord ++ tailWord_4634482) baseStart_4634482 baseEnd_4634482 := by
    simpa [prefixWord, tailWord_4634482, baseEnd_4634482] using wordTrace_append hprefix tailTrace_4634482
  have hstable : (prefixWord ++ tailWord_4634482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634482).length < 2 ^ (prefixWord ++ tailWord_4634482).sum := by decide
  have hdescent : baseEnd_4634482 < baseStart_4634482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634499 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 1, 6, 2]
def baseStart_4634499 : Nat := 118140960795 + 4634499 * 2 ^ 59
def prefixEnd_4634499 : Nat := 4983230072969 + 3 ^ 40 * 4634499 * 2
def baseEnd_4634499 : Nat := 2379725579781568235048833

theorem tailTrace_4634499 : CollatzResearch.WordTrace tailWord_4634499 prefixEnd_4634499 2379725579781568235048833 := by
  unfold tailWord_4634499
  simp only [CollatzResearch.WordTrace]
  refine ⟨169034065237009107259026551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112689376824672738172684367 169034065237009107259026551)
  ·
    refine ⟨253551097855513660888539827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169034065237009107259026551 253551097855513660888539827)
    ·
      refine ⟨380326646783270491332809741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253551097855513660888539827 380326646783270491332809741)
      ·
        refine ⟨142622492543726434249803653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380326646783270491332809741 142622492543726434249803653)
        ·
          refine ⟨26741717351948706421838185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142622492543726434249803653 26741717351948706421838185)
          ·
            refine ⟨20056288013961529816378639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26741717351948706421838185 20056288013961529816378639)
            ·
              refine ⟨30084432020942294724567959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20056288013961529816378639 30084432020942294724567959)
              ·
                refine ⟨45126648031413442086851939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30084432020942294724567959 45126648031413442086851939)
                ·
                  refine ⟨67689972047120163130277909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45126648031413442086851939 67689972047120163130277909)
                  ·
                    refine ⟨3172967439708757646731777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67689972047120163130277909 3172967439708757646731777)
                    ·
                      refine ⟨2379725579781568235048833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3172967439708757646731777 2379725579781568235048833)
                      ·
                        rfl

theorem cell23_4634499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 1, 6, 2].length) (baseStart_4634499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634499 prefixEnd_4634499 := by exact prefixLift 4634499
  have htrace : WordTrace (prefixWord ++ tailWord_4634499) baseStart_4634499 baseEnd_4634499 := by
    simpa [prefixWord, tailWord_4634499, baseEnd_4634499] using wordTrace_append hprefix tailTrace_4634499
  have hstable : (prefixWord ++ tailWord_4634499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634499).length < 2 ^ (prefixWord ++ tailWord_4634499).sum := by decide
  have hdescent : baseEnd_4634499 < baseStart_4634499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634516 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 2, 1, 4]
def baseStart_4634516 : Nat := 118140960795 + 4634516 * 2 ^ 59
def prefixEnd_4634516 : Nat := 4983230072969 + 3 ^ 40 * 4634516 * 2
def baseEnd_4634516 : Nat := 2379734308952694668536255

theorem tailTrace_4634516 : CollatzResearch.WordTrace tailWord_4634516 prefixEnd_4634516 2379734308952694668536255 := by
  unfold tailWord_4634516
  simp only [CollatzResearch.WordTrace]
  refine ⟨84517342638973759581197701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112689790185298346108263601 84517342638973759581197701)
  ·
    refine ⟨15847001744807579921474569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84517342638973759581197701 15847001744807579921474569)
    ·
      refine ⟨11885251308605684941105927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15847001744807579921474569 11885251308605684941105927)
      ·
        refine ⟨17827876962908527411658891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11885251308605684941105927 17827876962908527411658891)
        ·
          refine ⟨26741815444362791117488337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17827876962908527411658891 26741815444362791117488337)
          ·
            refine ⟨20056361583272093338116253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26741815444362791117488337 20056361583272093338116253)
            ·
              refine ⟨7521135593727035001793595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20056361583272093338116253 7521135593727035001793595)
              ·
                refine ⟨11281703390590552502690393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7521135593727035001793595 11281703390590552502690393)
                ·
                  refine ⟨8461277542942914377017795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11281703390590552502690393 8461277542942914377017795)
                  ·
                    refine ⟨12691916314414371565526693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8461277542942914377017795 12691916314414371565526693)
                    ·
                      refine ⟨2379734308952694668536255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12691916314414371565526693 2379734308952694668536255)
                      ·
                        rfl

theorem cell23_4634516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_4634516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634516 prefixEnd_4634516 := by exact prefixLift 4634516
  have htrace : WordTrace (prefixWord ++ tailWord_4634516) baseStart_4634516 baseEnd_4634516 := by
    simpa [prefixWord, tailWord_4634516, baseEnd_4634516] using wordTrace_append hprefix tailTrace_4634516
  have hstable : (prefixWord ++ tailWord_4634516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634516).length < 2 ^ (prefixWord ++ tailWord_4634516).sum := by decide
  have hdescent : baseEnd_4634516 < baseStart_4634516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634519 : List Nat := [1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 3]
def baseStart_4634519 : Nat := 118140960795 + 4634519 * 2 ^ 59
def prefixEnd_4634519 : Nat := 4983230072969 + 3 ^ 40 * 4634519 * 2
def baseEnd_4634519 : Nat := 2379735849394658156798741

theorem tailTrace_4634519 : CollatzResearch.WordTrace tailWord_4634519 prefixEnd_4634519 2379735849394658156798741 := by
  unfold tailWord_4634519
  simp only [CollatzResearch.WordTrace]
  refine ⟨169034794696936650674754611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112689863131291100449836407 169034794696936650674754611)
  ·
    refine ⟨253552192045404976012131917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169034794696936650674754611 253552192045404976012131917)
    ·
      refine ⟨95082072017026866004549469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253552192045404976012131917 95082072017026866004549469)
      ·
        refine ⟨35655777006385074751706051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95082072017026866004549469 35655777006385074751706051)
        ·
          refine ⟨53483665509577612127559077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35655777006385074751706051 53483665509577612127559077)
          ·
            refine ⟨10028187283045802273917327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53483665509577612127559077 10028187283045802273917327)
            ·
              refine ⟨15042280924568703410875991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10028187283045802273917327 15042280924568703410875991)
              ·
                refine ⟨22563421386853055116313987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15042280924568703410875991 22563421386853055116313987)
                ·
                  refine ⟨33845132080279582674470981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22563421386853055116313987 33845132080279582674470981)
                  ·
                    refine ⟨6345962265052421751463309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33845132080279582674470981 6345962265052421751463309)
                    ·
                      refine ⟨2379735849394658156798741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6345962265052421751463309 2379735849394658156798741)
                      ·
                        rfl

theorem cell23_4634519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_4634519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634519 prefixEnd_4634519 := by exact prefixLift 4634519
  have htrace : WordTrace (prefixWord ++ tailWord_4634519) baseStart_4634519 baseEnd_4634519 := by
    simpa [prefixWord, tailWord_4634519, baseEnd_4634519] using wordTrace_append hprefix tailTrace_4634519
  have hstable : (prefixWord ++ tailWord_4634519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634519).length < 2 ^ (prefixWord ++ tailWord_4634519).sum := by decide
  have hdescent : baseEnd_4634519 < baseStart_4634519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634559 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 3, 5, 2]
def baseStart_4634559 : Nat := 118140960795 + 4634559 * 2 ^ 59
def prefixEnd_4634559 : Nat := 4983230072969 + 3 ^ 40 * 4634559 * 2
def baseEnd_4634559 : Nat := 2379756388620838000298557

theorem tailTrace_4634559 : CollatzResearch.WordTrace tailWord_4634559 prefixEnd_4634559 2379756388620838000298557 := by
  unfold tailWord_4634559
  simp only [CollatzResearch.WordTrace]
  refine ⟨169036253616791737506210731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112690835744527825004140487 169036253616791737506210731)
  ·
    refine ⟨253554380425187606259316097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169036253616791737506210731 253554380425187606259316097)
    ·
      refine ⟨190165785318890704694487073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253554380425187606259316097 190165785318890704694487073)
      ·
        refine ⟨142624338989168028520865305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190165785318890704694487073 142624338989168028520865305)
        ·
          refine ⟨106968254241876021390648979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142624338989168028520865305 106968254241876021390648979)
          ·
            refine ⟨160452381362814032085973469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106968254241876021390648979 160452381362814032085973469)
            ·
              refine ⟨60169643011055262032240051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 160452381362814032085973469 60169643011055262032240051)
              ·
                refine ⟨90254464516582893048360077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60169643011055262032240051 90254464516582893048360077)
                ·
                  refine ⟨33845424193718584893135029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 90254464516582893048360077 33845424193718584893135029)
                  ·
                    refine ⟨3173008518161117333731409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33845424193718584893135029 3173008518161117333731409)
                    ·
                      refine ⟨2379756388620838000298557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173008518161117333731409 2379756388620838000298557)
                      ·
                        rfl

theorem cell23_4634559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 3, 5, 2].length) (baseStart_4634559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634559 prefixEnd_4634559 := by exact prefixLift 4634559
  have htrace : WordTrace (prefixWord ++ tailWord_4634559) baseStart_4634559 baseEnd_4634559 := by
    simpa [prefixWord, tailWord_4634559, baseEnd_4634559] using wordTrace_append hprefix tailTrace_4634559
  have hstable : (prefixWord ++ tailWord_4634559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634559).length < 2 ^ (prefixWord ++ tailWord_4634559).sum := by decide
  have hdescent : baseEnd_4634559 < baseStart_4634559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634657 : List Nat := [1, 2, 3, 2, 4, 1, 1, 4, 1, 2, 2]
def baseStart_4634657 : Nat := 118140960795 + 4634657 * 2 ^ 59
def prefixEnd_4634657 : Nat := 4983230072969 + 3 ^ 40 * 4634657 * 2
def baseEnd_4634657 : Nat := 2379806709724978616873107

theorem tailTrace_4634657 : CollatzResearch.WordTrace tailWord_4634657 prefixEnd_4634657 2379806709724978616873107 := by
  unfold tailWord_4634657
  simp only [CollatzResearch.WordTrace]
  refine ⟨169039827970436700243278225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112693218646957800162185483 169039827970436700243278225)
  ·
    refine ⟨126779870977827525182458669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169039827970436700243278225 126779870977827525182458669)
    ·
      refine ⟨47542451616685321943422001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126779870977827525182458669 47542451616685321943422001)
      ·
        refine ⟨35656838712513991457566501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47542451616685321943422001 35656838712513991457566501)
        ·
          refine ⟨6685657258596373398293719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35656838712513991457566501 6685657258596373398293719)
          ·
            refine ⟨10028485887894560097440579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6685657258596373398293719 10028485887894560097440579)
            ·
              refine ⟨15042728831841840146160869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10028485887894560097440579 15042728831841840146160869)
              ·
                refine ⟨2820511655970345027405163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15042728831841840146160869 2820511655970345027405163)
                ·
                  refine ⟨4230767483955517541107745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2820511655970345027405163 4230767483955517541107745)
                  ·
                    refine ⟨3173075612966638155830809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4230767483955517541107745 3173075612966638155830809)
                    ·
                      refine ⟨2379806709724978616873107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173075612966638155830809 2379806709724978616873107)
                      ·
                        rfl

theorem cell23_4634657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 4, 1, 2, 2].length) (baseStart_4634657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634657 prefixEnd_4634657 := by exact prefixLift 4634657
  have htrace : WordTrace (prefixWord ++ tailWord_4634657) baseStart_4634657 baseEnd_4634657 := by
    simpa [prefixWord, tailWord_4634657, baseEnd_4634657] using wordTrace_append hprefix tailTrace_4634657
  have hstable : (prefixWord ++ tailWord_4634657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634657).length < 2 ^ (prefixWord ++ tailWord_4634657).sum := by decide
  have hdescent : baseEnd_4634657 < baseStart_4634657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634663 : List Nat := [1, 1, 7, 1, 2, 2, 1, 8]
def baseStart_4634663 : Nat := 118140960795 + 4634663 * 2 ^ 59
def prefixEnd_4634663 : Nat := 4983230072969 + 3 ^ 40 * 4634663 * 2
def baseEnd_4634663 : Nat := 88141103355885392348077

theorem tailTrace_4634663 : CollatzResearch.WordTrace tailWord_4634663 prefixEnd_4634663 88141103355885392348077 := by
  unfold tailWord_4634663
  simp only [CollatzResearch.WordTrace]
  refine ⟨169040046808414963267996643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112693364538943308845331095 169040046808414963267996643)
  ·
    refine ⟨253560070212622444901994965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169040046808414963267996643 253560070212622444901994965)
    ·
      refine ⟨5942814145608338552390507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 253560070212622444901994965 5942814145608338552390507)
      ·
        refine ⟨8914221218412507828585761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5942814145608338552390507 8914221218412507828585761)
        ·
          refine ⟨6685665913809380871439321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8914221218412507828585761 6685665913809380871439321)
          ·
            refine ⟨5014249435357035653579491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6685665913809380871439321 5014249435357035653579491)
            ·
              refine ⟨7521374153035553480369237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5014249435357035653579491 7521374153035553480369237)
              ·
                refine ⟨88141103355885392348077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7521374153035553480369237 88141103355885392348077)
                ·
                  rfl

theorem cell23_4634663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 8].length) (baseStart_4634663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634663 prefixEnd_4634663 := by exact prefixLift 4634663
  have htrace : WordTrace (prefixWord ++ tailWord_4634663) baseStart_4634663 baseEnd_4634663 := by
    simpa [prefixWord, tailWord_4634663, baseEnd_4634663] using wordTrace_append hprefix tailTrace_4634663
  have hstable : (prefixWord ++ tailWord_4634663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634663).length < 2 ^ (prefixWord ++ tailWord_4634663).sum := by decide
  have hdescent : baseEnd_4634663 < baseStart_4634663 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634673 : List Nat := [1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 3]
def baseStart_4634673 : Nat := 118140960795 + 4634673 * 2 ^ 59
def prefixEnd_4634673 : Nat := 4983230072969 + 3 ^ 40 * 4634673 * 2
def baseEnd_4634673 : Nat := 2379814925415450554273033

theorem tailTrace_4634673 : CollatzResearch.WordTrace tailWord_4634673 prefixEnd_4634673 2379814925415450554273033 := by
  unfold tailWord_4634673
  simp only [CollatzResearch.WordTrace]
  refine ⟨169040411538378734975860673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112693607692252489983907115 169040411538378734975860673)
  ·
    refine ⟨126780308653784051231895505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169040411538378734975860673 126780308653784051231895505)
    ·
      refine ⟨95085231490338038423921629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126780308653784051231895505 95085231490338038423921629)
      ·
        refine ⟨35656961808876764408970611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95085231490338038423921629 35656961808876764408970611)
        ·
          refine ⟨53485442713315146613455917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35656961808876764408970611 53485442713315146613455917)
          ·
            refine ⟨20057041017493179980045969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53485442713315146613455917 20057041017493179980045969)
            ·
              refine ⟨15042780763119884985034477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20057041017493179980045969 15042780763119884985034477)
              ·
                refine ⟨5641042786169956869387929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15042780763119884985034477 5641042786169956869387929)
                ·
                  refine ⟨4230782089627467652040947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5641042786169956869387929 4230782089627467652040947)
                  ·
                    refine ⟨6346173134441201478061421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4230782089627467652040947 6346173134441201478061421)
                    ·
                      refine ⟨2379814925415450554273033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6346173134441201478061421 2379814925415450554273033)
                      ·
                        rfl

theorem cell23_4634673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 3, 2, 1, 3].length) (baseStart_4634673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634673 prefixEnd_4634673 := by exact prefixLift 4634673
  have htrace : WordTrace (prefixWord ++ tailWord_4634673) baseStart_4634673 baseEnd_4634673 := by
    simpa [prefixWord, tailWord_4634673, baseEnd_4634673] using wordTrace_append hprefix tailTrace_4634673
  have hstable : (prefixWord ++ tailWord_4634673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634673).length < 2 ^ (prefixWord ++ tailWord_4634673).sum := by decide
  have hdescent : baseEnd_4634673 < baseStart_4634673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634696 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 3, 4, 2]
def baseStart_4634696 : Nat := 118140960795 + 4634696 * 2 ^ 59
def prefixEnd_4634696 : Nat := 4983230072969 + 3 ^ 40 * 4634696 * 2
def baseEnd_4634696 : Nat := 2379826735470503964285427

theorem tailTrace_4634696 : CollatzResearch.WordTrace tailWord_4634696 prefixEnd_4634696 2379826735470503964285427 := by
  unfold tailWord_4634696
  simp only [CollatzResearch.WordTrace]
  refine ⟨84520625208647704951973971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112694166944863606602631961 84520625208647704951973971)
  ·
    refine ⟨126780937812971557427960957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84520625208647704951973971 126780937812971557427960957)
    ·
      refine ⟨47542851679864334035485359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126780937812971557427960957 47542851679864334035485359)
      ·
        refine ⟨71314277519796501053228039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47542851679864334035485359 71314277519796501053228039)
        ·
          refine ⟨106971416279694751579842059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71314277519796501053228039 106971416279694751579842059)
          ·
            refine ⟨160457124419542127369763089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106971416279694751579842059 160457124419542127369763089)
            ·
              refine ⟨120342843314656595527322317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160457124419542127369763089 120342843314656595527322317)
              ·
                refine ⟨45128566242996223322745869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120342843314656595527322317 45128566242996223322745869)
                ·
                  refine ⟨16923212341123583746029701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 45128566242996223322745869 16923212341123583746029701)
                  ·
                    refine ⟨3173102313960671952380569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16923212341123583746029701 3173102313960671952380569)
                    ·
                      refine ⟨2379826735470503964285427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173102313960671952380569 2379826735470503964285427)
                      ·
                        rfl

theorem cell23_4634696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_4634696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634696 prefixEnd_4634696 := by exact prefixLift 4634696
  have htrace : WordTrace (prefixWord ++ tailWord_4634696) baseStart_4634696 baseEnd_4634696 := by
    simpa [prefixWord, tailWord_4634696, baseEnd_4634696] using wordTrace_append hprefix tailTrace_4634696
  have hstable : (prefixWord ++ tailWord_4634696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634696).length < 2 ^ (prefixWord ++ tailWord_4634696).sum := by decide
  have hdescent : baseEnd_4634696 < baseStart_4634696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634699 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 3]
def baseStart_4634699 : Nat := 118140960795 + 4634699 * 2 ^ 59
def prefixEnd_4634699 : Nat := 4983230072969 + 3 ^ 40 * 4634699 * 2
def baseEnd_4634699 : Nat := 2379828275912467452547913

theorem tailTrace_4634699 : CollatzResearch.WordTrace tailWord_4634699 prefixEnd_4634699 2379828275912467452547913 := by
  unfold tailWord_4634699
  simp only [CollatzResearch.WordTrace]
  refine ⟨169041359836284541416307151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112694239890856360944204767 169041359836284541416307151)
  ·
    refine ⟨253562039754426812124460727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169041359836284541416307151 253562039754426812124460727)
    ·
      refine ⟨380343059631640218186691091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253562039754426812124460727 380343059631640218186691091)
      ·
        refine ⟨570514589447460327280036637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380343059631640218186691091 570514589447460327280036637)
        ·
          refine ⟨213942971042797622730013739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 570514589447460327280036637 213942971042797622730013739)
          ·
            refine ⟨320914456564196434095020609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213942971042797622730013739 320914456564196434095020609)
            ·
              refine ⟨240685842423147325571265457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320914456564196434095020609 240685842423147325571265457)
              ·
                refine ⟨180514381817360494178449093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 240685842423147325571265457 180514381817360494178449093)
                ·
                  refine ⟨33846446590755092658459205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180514381817360494178449093 33846446590755092658459205)
                  ·
                    refine ⟨6346208735766579873461101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33846446590755092658459205 6346208735766579873461101)
                    ·
                      refine ⟨2379828275912467452547913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6346208735766579873461101 2379828275912467452547913)
                      ·
                        rfl

theorem cell23_4634699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 4, 4, 3].length) (baseStart_4634699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634699 prefixEnd_4634699 := by exact prefixLift 4634699
  have htrace : WordTrace (prefixWord ++ tailWord_4634699) baseStart_4634699 baseEnd_4634699 := by
    simpa [prefixWord, tailWord_4634699, baseEnd_4634699] using wordTrace_append hprefix tailTrace_4634699
  have hstable : (prefixWord ++ tailWord_4634699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634699).length < 2 ^ (prefixWord ++ tailWord_4634699).sum := by decide
  have hdescent : baseEnd_4634699 < baseStart_4634699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634700 : List Nat := [2, 2, 1, 3, 1, 1, 6, 1, 1, 3, 2]
def baseStart_4634700 : Nat := 118140960795 + 4634700 * 2 ^ 59
def prefixEnd_4634700 : Nat := 4983230072969 + 3 ^ 40 * 4634700 * 2
def baseEnd_4634700 : Nat := 2379828789393121948635409

theorem tailTrace_4634700 : CollatzResearch.WordTrace tailWord_4634700 prefixEnd_4634700 2379828789393121948635409 := by
  unfold tailWord_4634700
  simp only [CollatzResearch.WordTrace]
  refine ⟨84520698154640459293546777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112694264206187279058062369 84520698154640459293546777)
  ·
    refine ⟨63390523615980344470160083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84520698154640459293546777 63390523615980344470160083)
    ·
      refine ⟨95085785423970516705240125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63390523615980344470160083 95085785423970516705240125)
      ·
        refine ⟨35657169533988943764465047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95085785423970516705240125 35657169533988943764465047)
        ·
          refine ⟨53485754300983415646697571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35657169533988943764465047 53485754300983415646697571)
          ·
            refine ⟨80228631451475123470046357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53485754300983415646697571 80228631451475123470046357)
            ·
              refine ⟨3760717099287896412658423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80228631451475123470046357 3760717099287896412658423)
              ·
                refine ⟨5641075648931844618987635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760717099287896412658423 5641075648931844618987635)
                ·
                  refine ⟨8461613473397766928481453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5641075648931844618987635 8461613473397766928481453)
                  ·
                    refine ⟨3173105052524162598180545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8461613473397766928481453 3173105052524162598180545)
                    ·
                      refine ⟨2379828789393121948635409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173105052524162598180545 2379828789393121948635409)
                      ·
                        rfl

theorem cell23_4634700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_4634700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634700 prefixEnd_4634700 := by exact prefixLift 4634700
  have htrace : WordTrace (prefixWord ++ tailWord_4634700) baseStart_4634700 baseEnd_4634700 := by
    simpa [prefixWord, tailWord_4634700, baseEnd_4634700] using wordTrace_append hprefix tailTrace_4634700
  have hstable : (prefixWord ++ tailWord_4634700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634700).length < 2 ^ (prefixWord ++ tailWord_4634700).sum := by decide
  have hdescent : baseEnd_4634700 < baseStart_4634700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634713 : List Nat := [1, 2, 1, 2, 2, 1, 5, 1, 4, 2, 2]
def baseStart_4634713 : Nat := 118140960795 + 4634713 * 2 ^ 59
def prefixEnd_4634713 : Nat := 4983230072969 + 3 ^ 40 * 4634713 * 2
def baseEnd_4634713 : Nat := 2379835464641630397772849

theorem tailTrace_4634713 : CollatzResearch.WordTrace tailWord_4634713 prefixEnd_4634713 2379835464641630397772849 := by
  unfold tailWord_4634713
  simp only [CollatzResearch.WordTrace]
  refine ⟨169041870458233821807316793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112694580305489214538211195 169041870458233821807316793)
  ·
    refine ⟨126781402843675366355487595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169041870458233821807316793 126781402843675366355487595)
    ·
      refine ⟨190172104265513049533231393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126781402843675366355487595 190172104265513049533231393)
      ·
        refine ⟨142629078199134787149923545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190172104265513049533231393 142629078199134787149923545)
        ·
          refine ⟨106971808649351090362442659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142629078199134787149923545 106971808649351090362442659)
          ·
            refine ⟨160457712974026635543663989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106971808649351090362442659 160457712974026635543663989)
            ·
              refine ⟨15042910591314997082218499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 160457712974026635543663989 15042910591314997082218499)
              ·
                refine ⟨22564365886972495623327749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15042910591314997082218499 22564365886972495623327749)
                ·
                  refine ⟨4230818603807342929373953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22564365886972495623327749 4230818603807342929373953)
                  ·
                    refine ⟨3173113952855507197030465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4230818603807342929373953 3173113952855507197030465)
                    ·
                      refine ⟨2379835464641630397772849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173113952855507197030465 2379835464641630397772849)
                      ·
                        rfl

theorem cell23_4634713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 1, 4, 2, 2].length) (baseStart_4634713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634713 prefixEnd_4634713 := by exact prefixLift 4634713
  have htrace : WordTrace (prefixWord ++ tailWord_4634713) baseStart_4634713 baseEnd_4634713 := by
    simpa [prefixWord, tailWord_4634713, baseEnd_4634713] using wordTrace_append hprefix tailTrace_4634713
  have hstable : (prefixWord ++ tailWord_4634713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634713).length < 2 ^ (prefixWord ++ tailWord_4634713).sum := by decide
  have hdescent : baseEnd_4634713 < baseStart_4634713 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634769 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 4]
def baseStart_4634769 : Nat := 118140960795 + 4634769 * 2 ^ 59
def prefixEnd_4634769 : Nat := 4983230072969 + 3 ^ 40 * 4634769 * 2
def baseEnd_4634769 : Nat := 2379864219558282178672591

theorem tailTrace_4634769 : CollatzResearch.WordTrace tailWord_4634769 prefixEnd_4634769 2379864219558282178672591 := by
  unfold tailWord_4634769
  simp only [CollatzResearch.WordTrace]
  refine ⟨169043912946030943371355361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112695941964020628914236907 169043912946030943371355361)
  ·
    refine ⟨126782934709523207528516521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169043912946030943371355361 126782934709523207528516521)
    ·
      refine ⟨95087201032142405646387391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126782934709523207528516521 95087201032142405646387391)
      ·
        refine ⟨142630801548213608469581087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95087201032142405646387391 142630801548213608469581087)
        ·
          refine ⟨213946202322320412704371631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142630801548213608469581087 213946202322320412704371631)
          ·
            refine ⟨320919303483480619056557447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213946202322320412704371631 320919303483480619056557447)
            ·
              refine ⟨481378955225220928584836171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 320919303483480619056557447 481378955225220928584836171)
              ·
                refine ⟨722068432837831392877254257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 481378955225220928584836171 722068432837831392877254257)
                ·
                  refine ⟨541551324628373544657940693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 722068432837831392877254257 541551324628373544657940693)
                  ·
                    refine ⟨12692609170977504952920485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 541551324628373544657940693 12692609170977504952920485)
                    ·
                      refine ⟨2379864219558282178672591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12692609170977504952920485 2379864219558282178672591)
                      ·
                        rfl

theorem cell23_4634769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 4].length) (baseStart_4634769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634769 prefixEnd_4634769 := by exact prefixLift 4634769
  have htrace : WordTrace (prefixWord ++ tailWord_4634769) baseStart_4634769 baseEnd_4634769 := by
    simpa [prefixWord, tailWord_4634769, baseEnd_4634769] using wordTrace_append hprefix tailTrace_4634769
  have hstable : (prefixWord ++ tailWord_4634769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634769).length < 2 ^ (prefixWord ++ tailWord_4634769).sum := by decide
  have hdescent : baseEnd_4634769 < baseStart_4634769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634770 : List Nat := [3, 2, 3, 1, 1, 1, 5, 2, 5]
def baseStart_4634770 : Nat := 118140960795 + 4634770 * 2 ^ 59
def prefixEnd_4634770 : Nat := 4983230072969 + 3 ^ 40 * 4634770 * 2
def baseEnd_4634770 : Nat := 264429414782104074973343

theorem tailTrace_4634770 : CollatzResearch.WordTrace tailWord_4634770 prefixEnd_4634770 264429414782104074973343 := by
  unfold tailWord_4634770
  simp only [CollatzResearch.WordTrace]
  refine ⟨42260987354756830135535441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112695966279351547028094509 42260987354756830135535441)
  ·
    refine ⟨31695740516067622601651581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42260987354756830135535441 31695740516067622601651581)
    ·
      refine ⟨11885902693525358475619343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31695740516067622601651581 11885902693525358475619343)
      ·
        refine ⟨17828854040288037713429015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11885902693525358475619343 17828854040288037713429015)
        ·
          refine ⟨26743281060432056570143523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17828854040288037713429015 26743281060432056570143523)
          ·
            refine ⟨40114921590648084855215285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26743281060432056570143523 40114921590648084855215285)
            ·
              refine ⟨3760773899123257955176433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 40114921590648084855215285 3760773899123257955176433)
              ·
                refine ⟨2820580424342443466382325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3760773899123257955176433 2820580424342443466382325)
                ·
                  refine ⟨264429414782104074973343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2820580424342443466382325 264429414782104074973343)
                  ·
                    rfl

theorem cell23_4634770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 5, 2, 5].length) (baseStart_4634770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634770 prefixEnd_4634770 := by exact prefixLift 4634770
  have htrace : WordTrace (prefixWord ++ tailWord_4634770) baseStart_4634770 baseEnd_4634770 := by
    simpa [prefixWord, tailWord_4634770, baseEnd_4634770] using wordTrace_append hprefix tailTrace_4634770
  have hstable : (prefixWord ++ tailWord_4634770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634770).length < 2 ^ (prefixWord ++ tailWord_4634770).sum := by decide
  have hdescent : baseEnd_4634770 < baseStart_4634770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634799 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 6]
def baseStart_4634799 : Nat := 118140960795 + 4634799 * 2 ^ 59
def prefixEnd_4634799 : Nat := 4983230072969 + 3 ^ 40 * 4634799 * 2
def baseEnd_4634799 : Nat := 2379879623977917061297453

theorem tailTrace_4634799 : CollatzResearch.WordTrace tailWord_4634799 prefixEnd_4634799 2379879623977917061297453 := by
  unfold tailWord_4634799
  simp only [CollatzResearch.WordTrace]
  refine ⟨169045007135922258494947451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112696671423948172329964967 169045007135922258494947451)
  ·
    refine ⟨253567510703883387742421177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169045007135922258494947451 253567510703883387742421177)
    ·
      refine ⟨190175633027912540806815883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253567510703883387742421177 190175633027912540806815883)
      ·
        refine ⟨285263449541868811210223825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190175633027912540806815883 285263449541868811210223825)
        ·
          refine ⟨213947587156401608407667869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285263449541868811210223825 213947587156401608407667869)
          ·
            refine ⟨80230345183650603152875451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213947587156401608407667869 80230345183650603152875451)
            ·
              refine ⟨120345517775475904729313177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80230345183650603152875451 120345517775475904729313177)
              ·
                refine ⟨90259138331606928546984883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120345517775475904729313177 90259138331606928546984883)
                ·
                  refine ⟨135388707497410392820477325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90259138331606928546984883 135388707497410392820477325)
                  ·
                    refine ⟨50770765311528897307678997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 135388707497410392820477325 50770765311528897307678997)
                    ·
                      refine ⟨2379879623977917061297453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50770765311528897307678997 2379879623977917061297453)
                      ·
                        rfl

theorem cell23_4634799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_4634799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634799 prefixEnd_4634799 := by exact prefixLift 4634799
  have htrace : WordTrace (prefixWord ++ tailWord_4634799) baseStart_4634799 baseEnd_4634799 := by
    simpa [prefixWord, tailWord_4634799, baseEnd_4634799] using wordTrace_append hprefix tailTrace_4634799
  have hstable : (prefixWord ++ tailWord_4634799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634799).length < 2 ^ (prefixWord ++ tailWord_4634799).sum := by decide
  have hdescent : baseEnd_4634799 < baseStart_4634799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634903 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 1, 6]
def baseStart_4634903 : Nat := 118140960795 + 4634903 * 2 ^ 59
def prefixEnd_4634903 : Nat := 4983230072969 + 3 ^ 40 * 4634903 * 2
def baseEnd_4634903 : Nat := 793311008655328218132325

theorem tailTrace_4634903 : CollatzResearch.WordTrace tailWord_4634903 prefixEnd_4634903 793311008655328218132325 := by
  unfold tailWord_4634903
  simp only [CollatzResearch.WordTrace]
  refine ⟨169048800327545484256733363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112699200218363656171155575 169048800327545484256733363)
  ·
    refine ⟨253573200491318226385100045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169048800327545484256733363 253573200491318226385100045)
    ·
      refine ⟨95089950184244334894412517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253573200491318226385100045 95089950184244334894412517)
      ·
        refine ⟨17829365659545812792702347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95089950184244334894412517 17829365659545812792702347)
        ·
          refine ⟨26744048489318719189053521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17829365659545812792702347 26744048489318719189053521)
          ·
            refine ⟨20058036366989039391790141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26744048489318719189053521 20058036366989039391790141)
            ·
              refine ⟨7521763637620889771921303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20058036366989039391790141 7521763637620889771921303)
              ·
                refine ⟨11282645456431334657881955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7521763637620889771921303 11282645456431334657881955)
                ·
                  refine ⟨16923968184647001986822933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11282645456431334657881955 16923968184647001986822933)
                  ·
                    refine ⟨793311008655328218132325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16923968184647001986822933 793311008655328218132325)
                    ·
                      rfl

theorem cell23_4634903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 6].length) (baseStart_4634903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634903 prefixEnd_4634903 := by exact prefixLift 4634903
  have htrace : WordTrace (prefixWord ++ tailWord_4634903) baseStart_4634903 baseEnd_4634903 := by
    simpa [prefixWord, tailWord_4634903, baseEnd_4634903] using wordTrace_append hprefix tailTrace_4634903
  have hstable : (prefixWord ++ tailWord_4634903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634903).length < 2 ^ (prefixWord ++ tailWord_4634903).sum := by decide
  have hdescent : baseEnd_4634903 < baseStart_4634903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634913 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 3]
def baseStart_4634913 : Nat := 118140960795 + 4634913 * 2 ^ 59
def prefixEnd_4634913 : Nat := 4983230072969 + 3 ^ 40 * 4634913 * 2
def baseEnd_4634913 : Nat := 2379938160772529615271929

theorem tailTrace_4634913 : CollatzResearch.WordTrace tailWord_4634913 prefixEnd_4634913 2379938160772529615271929 := by
  unfold tailWord_4634913
  simp only [CollatzResearch.WordTrace]
  refine ⟨169049165057509255964597393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112699443371672837309731595 169049165057509255964597393)
  ·
    refine ⟨126786873793131941973448045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169049165057509255964597393 126786873793131941973448045)
    ·
      refine ⟨47545077672424478240043017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126786873793131941973448045 47545077672424478240043017)
      ·
        refine ⟨35658808254318358680032263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47545077672424478240043017 35658808254318358680032263)
        ·
          refine ⟨53488212381477538020048395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35658808254318358680032263 53488212381477538020048395)
          ·
            refine ⟨80232318572216307030072593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53488212381477538020048395 80232318572216307030072593)
            ·
              refine ⟨60174238929162230272554445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 80232318572216307030072593 60174238929162230272554445)
              ·
                refine ⟨22565339598435836352207917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60174238929162230272554445 22565339598435836352207917)
                ·
                  refine ⟨8462002349413438632077969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22565339598435836352207917 8462002349413438632077969)
                  ·
                    refine ⟨6346501762060078974058477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8462002349413438632077969 6346501762060078974058477)
                    ·
                      refine ⟨2379938160772529615271929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6346501762060078974058477 2379938160772529615271929)
                      ·
                        rfl

theorem cell23_4634913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_4634913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634913 prefixEnd_4634913 := by exact prefixLift 4634913
  have htrace : WordTrace (prefixWord ++ tailWord_4634913) baseStart_4634913 baseEnd_4634913 := by
    simpa [prefixWord, tailWord_4634913, baseEnd_4634913] using wordTrace_append hprefix tailTrace_4634913
  have hstable : (prefixWord ++ tailWord_4634913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634913).length < 2 ^ (prefixWord ++ tailWord_4634913).sum := by decide
  have hdescent : baseEnd_4634913 < baseStart_4634913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634930 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5]
def baseStart_4634930 : Nat := 118140960795 + 4634930 * 2 ^ 59
def prefixEnd_4634930 : Nat := 4983230072969 + 3 ^ 40 * 4634930 * 2
def baseEnd_4634930 : Nat := 2379946889943656048759351

theorem tailTrace_4634930 : CollatzResearch.WordTrace tailWord_4634930 prefixEnd_4634930 2379946889943656048759351 := by
  unfold tailWord_4634930
  simp only [CollatzResearch.WordTrace]
  refine ⟨42262446274611916966991561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112699856732298445245310829 42262446274611916966991561)
  ·
    refine ⟨31696834705958937725243671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42262446274611916966991561 31696834705958937725243671)
    ·
      refine ⟨47545252058938406587865507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31696834705958937725243671 47545252058938406587865507)
      ·
        refine ⟨71317878088407609881798261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47545252058938406587865507 71317878088407609881798261)
        ·
          refine ⟨6686051070788213426418587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71317878088407609881798261 6686051070788213426418587)
          ·
            refine ⟨10029076606182320139627881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6686051070788213426418587 10029076606182320139627881)
            ·
              refine ⟨7521807454636740104720911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10029076606182320139627881 7521807454636740104720911)
              ·
                refine ⟨11282711181955110157081367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7521807454636740104720911 11282711181955110157081367)
                ·
                  refine ⟨16924066772932665235622051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11282711181955110157081367 16924066772932665235622051)
                  ·
                    refine ⟨25386100159398997853433077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16924066772932665235622051 25386100159398997853433077)
                    ·
                      refine ⟨2379946889943656048759351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25386100159398997853433077 2379946889943656048759351)
                      ·
                        rfl

theorem cell23_4634930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5].length) (baseStart_4634930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634930 prefixEnd_4634930 := by exact prefixLift 4634930
  have htrace : WordTrace (prefixWord ++ tailWord_4634930) baseStart_4634930 baseEnd_4634930 := by
    simpa [prefixWord, tailWord_4634930, baseEnd_4634930] using wordTrace_append hprefix tailTrace_4634930
  have hstable : (prefixWord ++ tailWord_4634930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634930).length < 2 ^ (prefixWord ++ tailWord_4634930).sum := by decide
  have hdescent : baseEnd_4634930 < baseStart_4634930 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4634953 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 2, 7, 2]
def baseStart_4634953 : Nat := 118140960795 + 4634953 * 2 ^ 59
def prefixEnd_4634953 : Nat := 4983230072969 + 3 ^ 40 * 4634953 * 2
def baseEnd_4634953 : Nat := 2379958699998709458771745

theorem tailTrace_4634953 : CollatzResearch.WordTrace tailWord_4634953 prefixEnd_4634953 2379958699998709458771745 := by
  unfold tailWord_4634953
  simp only [CollatzResearch.WordTrace]
  refine ⟨169050623977364342796053513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112700415984909561864035675 169050623977364342796053513)
  ·
    refine ⟨126787967983023257097040135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169050623977364342796053513 126787967983023257097040135)
    ·
      refine ⟨190181951974534885645560203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126787967983023257097040135 190181951974534885645560203)
      ·
        refine ⟨285272927961802328468340305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190181951974534885645560203 285272927961802328468340305)
        ·
          refine ⟨213954695971351746351255229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285272927961802328468340305 213954695971351746351255229)
          ·
            refine ⟨80233010989256904881720711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 213954695971351746351255229 80233010989256904881720711)
            ·
              refine ⟨120349516483885357322581067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80233010989256904881720711 120349516483885357322581067)
              ·
                refine ⟨180524274725828035983871601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120349516483885357322581067 180524274725828035983871601)
                ·
                  refine ⟨135393206044371026987903701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180524274725828035983871601 135393206044371026987903701)
                  ·
                    refine ⟨3173278266664945945028993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 135393206044371026987903701 3173278266664945945028993)
                    ·
                      refine ⟨2379958699998709458771745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173278266664945945028993 2379958699998709458771745)
                      ·
                        rfl

theorem cell23_4634953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 2, 7, 2].length) (baseStart_4634953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4634953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4634953 prefixEnd_4634953 := by exact prefixLift 4634953
  have htrace : WordTrace (prefixWord ++ tailWord_4634953) baseStart_4634953 baseEnd_4634953 := by
    simpa [prefixWord, tailWord_4634953, baseEnd_4634953] using wordTrace_append hprefix tailTrace_4634953
  have hstable : (prefixWord ++ tailWord_4634953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4634953).length < 2 ^ (prefixWord ++ tailWord_4634953).sum := by decide
  have hdescent : baseEnd_4634953 < baseStart_4634953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4634953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635003 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 3]
def baseStart_4635003 : Nat := 118140960795 + 4635003 * 2 ^ 59
def prefixEnd_4635003 : Nat := 4983230072969 + 3 ^ 40 * 4635003 * 2
def baseEnd_4635003 : Nat := 2379984374031434263146515

theorem tailTrace_4635003 : CollatzResearch.WordTrace tailWord_4635003 prefixEnd_4635003 2379984374031434263146515 := by
  unfold tailWord_4635003
  simp only [CollatzResearch.WordTrace]
  refine ⟨169052447627183201335373663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112701631751455467556915775 169052447627183201335373663)
  ·
    refine ⟨253578671440774802003060495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169052447627183201335373663 253578671440774802003060495)
    ·
      refine ⟨380368007161162203004590743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253578671440774802003060495 380368007161162203004590743)
      ·
        refine ⟨570552010741743304506886115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380368007161162203004590743 570552010741743304506886115)
        ·
          refine ⟨855828016112614956760329173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570552010741743304506886115 855828016112614956760329173)
          ·
            refine ⟨20058469127639413049070215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 855828016112614956760329173 20058469127639413049070215)
            ·
              refine ⟨30087703691459119573605323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20058469127639413049070215 30087703691459119573605323)
              ·
                refine ⟨45131555537188679360407985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30087703691459119573605323 45131555537188679360407985)
                ·
                  refine ⟨33848666652891509520305989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45131555537188679360407985 33848666652891509520305989)
                  ·
                    refine ⟨6346624997417158035057373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33848666652891509520305989 6346624997417158035057373)
                    ·
                      refine ⟨2379984374031434263146515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6346624997417158035057373 2379984374031434263146515)
                      ·
                        rfl

theorem cell23_4635003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 3].length) (baseStart_4635003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635003 prefixEnd_4635003 := by exact prefixLift 4635003
  have htrace : WordTrace (prefixWord ++ tailWord_4635003) baseStart_4635003 baseEnd_4635003 := by
    simpa [prefixWord, tailWord_4635003, baseEnd_4635003] using wordTrace_append hprefix tailTrace_4635003
  have hstable : (prefixWord ++ tailWord_4635003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635003).length < 2 ^ (prefixWord ++ tailWord_4635003).sum := by decide
  have hdescent : baseEnd_4635003 < baseStart_4635003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635017 : List Nat := [1, 2, 1, 1, 6, 2, 2, 1, 1, 4, 2]
def baseStart_4635017 : Nat := 118140960795 + 4635017 * 2 ^ 59
def prefixEnd_4635017 : Nat := 4983230072969 + 3 ^ 40 * 4635017 * 2
def baseEnd_4635017 : Nat := 2379991562760597208371451

theorem tailTrace_4635017 : CollatzResearch.WordTrace tailWord_4635017 prefixEnd_4635017 2379991562760597208371451 := by
  unfold tailWord_4635017
  simp only [CollatzResearch.WordTrace]
  refine ⟨169052958249132481726383305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112701972166088321150922203 169052958249132481726383305)
  ·
    refine ⟨126789718686849361294787479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169052958249132481726383305 126789718686849361294787479)
    ·
      refine ⟨190184578030274041942181219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126789718686849361294787479 190184578030274041942181219)
      ·
        refine ⟨285276867045411062913271829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190184578030274041942181219 285276867045411062913271829)
        ·
          refine ⟨13372353142753643574059617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 285276867045411062913271829 13372353142753643574059617)
          ·
            refine ⟨10029264857065232680544713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13372353142753643574059617 10029264857065232680544713)
            ·
              refine ⟨7521948642798924510408535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10029264857065232680544713 7521948642798924510408535)
              ·
                refine ⟨11282922964198386765612803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7521948642798924510408535 11282922964198386765612803)
                ·
                  refine ⟨16924384446297580148419205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11282922964198386765612803 16924384446297580148419205)
                  ·
                    refine ⟨3173322083680796277828601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16924384446297580148419205 3173322083680796277828601)
                    ·
                      refine ⟨2379991562760597208371451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173322083680796277828601 2379991562760597208371451)
                      ·
                        rfl

theorem cell23_4635017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 1, 1, 4, 2].length) (baseStart_4635017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635017 prefixEnd_4635017 := by exact prefixLift 4635017
  have htrace : WordTrace (prefixWord ++ tailWord_4635017) baseStart_4635017 baseEnd_4635017 := by
    simpa [prefixWord, tailWord_4635017, baseEnd_4635017] using wordTrace_append hprefix tailTrace_4635017
  have hstable : (prefixWord ++ tailWord_4635017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635017).length < 2 ^ (prefixWord ++ tailWord_4635017).sum := by decide
  have hdescent : baseEnd_4635017 < baseStart_4635017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635033 : List Nat := [1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 3]
def baseStart_4635033 : Nat := 118140960795 + 4635033 * 2 ^ 59
def prefixEnd_4635033 : Nat := 4983230072969 + 3 ^ 40 * 4635033 * 2
def baseEnd_4635033 : Nat := 2379999778451069145771377

theorem tailTrace_4635033 : CollatzResearch.WordTrace tailWord_4635033 prefixEnd_4635033 2379999778451069145771377 := by
  unfold tailWord_4635033
  simp only [CollatzResearch.WordTrace]
  refine ⟨169053541817074516458965753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112702361211383010972643835 169053541817074516458965753)
  ·
    refine ⟨126790156362805887344224315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169053541817074516458965753 126790156362805887344224315)
    ·
      refine ⟨190185234544208831016336473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126790156362805887344224315 190185234544208831016336473)
      ·
        refine ⟨142638925908156623262252355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190185234544208831016336473 142638925908156623262252355)
        ·
          refine ⟨213958388862234934893378533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142638925908156623262252355 213958388862234934893378533)
          ·
            refine ⟨40117197911669050292508475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 213958388862234934893378533 40117197911669050292508475)
            ·
              refine ⟨60175796867503575438762713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40117197911669050292508475 60175796867503575438762713)
              ·
                refine ⟨45131847650627681579072035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60175796867503575438762713 45131847650627681579072035)
                ·
                  refine ⟨67697771475941522368608053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45131847650627681579072035 67697771475941522368608053)
                  ·
                    refine ⟨6346666075869517722057005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67697771475941522368608053 6346666075869517722057005)
                    ·
                      refine ⟨2379999778451069145771377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6346666075869517722057005 2379999778451069145771377)
                      ·
                        rfl

theorem cell23_4635033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 5, 3].length) (baseStart_4635033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635033 prefixEnd_4635033 := by exact prefixLift 4635033
  have htrace : WordTrace (prefixWord ++ tailWord_4635033) baseStart_4635033 baseEnd_4635033 := by
    simpa [prefixWord, tailWord_4635033, baseEnd_4635033] using wordTrace_append hprefix tailTrace_4635033
  have hstable : (prefixWord ++ tailWord_4635033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635033).length < 2 ^ (prefixWord ++ tailWord_4635033).sum := by decide
  have hdescent : baseEnd_4635033 < baseStart_4635033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635038 : List Nat := [4, 3, 1, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_4635038 : Nat := 118140960795 + 4635038 * 2 ^ 59
def prefixEnd_4635038 : Nat := 4983230072969 + 3 ^ 40 * 4635038 * 2
def baseEnd_4635038 : Nat := 2380002345854341626208855

theorem tailTrace_4635038 : CollatzResearch.WordTrace tailWord_4635038 prefixEnd_4635038 2380002345854341626208855 := by
  unfold tailWord_4635038
  simp only [CollatzResearch.WordTrace]
  refine ⟨21131715522757050289112221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112702482788037601541931845 21131715522757050289112221)
  ·
    refine ⟨7924393321033893858417083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21131715522757050289112221 7924393321033893858417083)
    ·
      refine ⟨11886589981550840787625625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7924393321033893858417083 11886589981550840787625625)
      ·
        refine ⟨8914942486163130590719219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11886589981550840787625625 8914942486163130590719219)
        ·
          refine ⟨13372413729244695886078829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8914942486163130590719219 13372413729244695886078829)
          ·
            refine ⟨5014655148466760957279561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13372413729244695886078829 5014655148466760957279561)
            ·
              refine ⟨3760991361350070717959671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5014655148466760957279561 3760991361350070717959671)
              ·
                refine ⟨5641487042025106076939507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3760991361350070717959671 5641487042025106076939507)
                ·
                  refine ⟨8462230563037659115409261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5641487042025106076939507 8462230563037659115409261)
                  ·
                    refine ⟨3173336461139122168278473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8462230563037659115409261 3173336461139122168278473)
                    ·
                      refine ⟨2380002345854341626208855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173336461139122168278473 2380002345854341626208855)
                      ·
                        rfl

theorem cell23_4635038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_4635038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635038 prefixEnd_4635038 := by exact prefixLift 4635038
  have htrace : WordTrace (prefixWord ++ tailWord_4635038) baseStart_4635038 baseEnd_4635038 := by
    simpa [prefixWord, tailWord_4635038, baseEnd_4635038] using wordTrace_append hprefix tailTrace_4635038
  have hstable : (prefixWord ++ tailWord_4635038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635038).length < 2 ^ (prefixWord ++ tailWord_4635038).sum := by decide
  have hdescent : baseEnd_4635038 < baseStart_4635038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635040 : List Nat := [2, 1, 1, 4, 1, 3, 1, 5, 5]
def baseStart_4635040 : Nat := 118140960795 + 4635040 * 2 ^ 59
def prefixEnd_4635040 : Nat := 4983230072969 + 3 ^ 40 * 4635040 * 2
def baseEnd_4635040 : Nat := 264444819201738957598205

theorem tailTrace_4635040 : CollatzResearch.WordTrace tailWord_4635040 prefixEnd_4635040 264444819201738957598205 := by
  unfold tailWord_4635040
  simp only [CollatzResearch.WordTrace]
  refine ⟨84526898564024578327235287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112702531418699437769647049 84526898564024578327235287)
  ·
    refine ⟨126790347846036867490852931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84526898564024578327235287 126790347846036867490852931)
    ·
      refine ⟨190185521769055301236279397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126790347846036867490852931 190185521769055301236279397)
      ·
        refine ⟨35659785331697868981802387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190185521769055301236279397 35659785331697868981802387)
        ·
          refine ⟨53489677997546803472703581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35659785331697868981802387 53489677997546803472703581)
          ·
            refine ⟨20058629249080051302263843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53489677997546803472703581 20058629249080051302263843)
            ·
              refine ⟨30087943873620076953395765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20058629249080051302263843 30087943873620076953395765)
              ·
                refine ⟨2820744738151882214380853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30087943873620076953395765 2820744738151882214380853)
                ·
                  refine ⟨264444819201738957598205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2820744738151882214380853 264444819201738957598205)
                  ·
                    rfl

theorem cell23_4635040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 5, 5].length) (baseStart_4635040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635040 prefixEnd_4635040 := by exact prefixLift 4635040
  have htrace : WordTrace (prefixWord ++ tailWord_4635040) baseStart_4635040 baseEnd_4635040 := by
    simpa [prefixWord, tailWord_4635040, baseEnd_4635040] using wordTrace_append hprefix tailTrace_4635040
  have hstable : (prefixWord ++ tailWord_4635040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635040).length < 2 ^ (prefixWord ++ tailWord_4635040).sum := by decide
  have hdescent : baseEnd_4635040 < baseStart_4635040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635107 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 4]
def baseStart_4635107 : Nat := 118140960795 + 4635107 * 2 ^ 59
def prefixEnd_4635107 : Nat := 4983230072969 + 3 ^ 40 * 4635107 * 2
def baseEnd_4635107 : Nat := 2380037776019501856246037

theorem tailTrace_4635107 : CollatzResearch.WordTrace tailWord_4635107 prefixEnd_4635107 2380037776019501856246037 := by
  unfold tailWord_4635107
  simp only [CollatzResearch.WordTrace]
  refine ⟨169056240818806427097159575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112704160545870951398106383 169056240818806427097159575)
  ·
    refine ⟨253584361228209640645739363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169056240818806427097159575 253584361228209640645739363)
    ·
      refine ⟨380376541842314460968609045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253584361228209640645739363 380376541842314460968609045)
      ·
        refine ⟨17830150398858490357903549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 380376541842314460968609045 17830150398858490357903549)
        ·
          refine ⟨6686306399571933884213831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17830150398858490357903549 6686306399571933884213831)
          ·
            refine ⟨10029459599357900826320747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6686306399571933884213831 10029459599357900826320747)
            ·
              refine ⟨15044189399036851239481121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10029459599357900826320747 15044189399036851239481121)
              ·
                refine ⟨11283142049277638429610841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15044189399036851239481121 11283142049277638429610841)
                ·
                  refine ⟨8462356536958228822208131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11283142049277638429610841 8462356536958228822208131)
                  ·
                    refine ⟨12693534805437343233312197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8462356536958228822208131 12693534805437343233312197)
                    ·
                      refine ⟨2380037776019501856246037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12693534805437343233312197 2380037776019501856246037)
                      ·
                        rfl

theorem cell23_4635107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_4635107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635107 prefixEnd_4635107 := by exact prefixLift 4635107
  have htrace : WordTrace (prefixWord ++ tailWord_4635107) baseStart_4635107 baseEnd_4635107 := by
    simpa [prefixWord, tailWord_4635107, baseEnd_4635107] using wordTrace_append hprefix tailTrace_4635107
  have hstable : (prefixWord ++ tailWord_4635107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635107).length < 2 ^ (prefixWord ++ tailWord_4635107).sum := by decide
  have hdescent : baseEnd_4635107 < baseStart_4635107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635153 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 5]
def baseStart_4635153 : Nat := 118140960795 + 4635153 * 2 ^ 59
def prefixEnd_4635153 : Nat := 4983230072969 + 3 ^ 40 * 4635153 * 2
def baseEnd_4635153 : Nat := 2380061396129608676270825

theorem tailTrace_4635153 : CollatzResearch.WordTrace tailWord_4635153 prefixEnd_4635153 2380061396129608676270825 := by
  unfold tailWord_4635153
  simp only [CollatzResearch.WordTrace]
  refine ⟨169057918576639776953334113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112705279051093184635556075 169057918576639776953334113)
  ·
    refine ⟨126793438932479832715000585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169057918576639776953334113 126793438932479832715000585)
    ·
      refine ⟨95095079199359874536250439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126793438932479832715000585 95095079199359874536250439)
      ·
        refine ⟨142642618799039811804375659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95095079199359874536250439 142642618799039811804375659)
        ·
          refine ⟨213963928198559717706563489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142642618799039811804375659 213963928198559717706563489)
          ·
            refine ⟨160472946148919788279922617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213963928198559717706563489 160472946148919788279922617)
            ·
              refine ⟨120354709611689841209941963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160472946148919788279922617 120354709611689841209941963)
              ·
                refine ⟨180532064417534761814912945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120354709611689841209941963 180532064417534761814912945)
                ·
                  refine ⟨135399048313151071361184709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 180532064417534761814912945 135399048313151071361184709)
                  ·
                    refine ⟨25387321558715825880222133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 135399048313151071361184709 25387321558715825880222133)
                    ·
                      refine ⟨2380061396129608676270825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25387321558715825880222133 2380061396129608676270825)
                      ·
                        rfl

theorem cell23_4635153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 5].length) (baseStart_4635153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635153 prefixEnd_4635153 := by exact prefixLift 4635153
  have htrace : WordTrace (prefixWord ++ tailWord_4635153) baseStart_4635153 baseEnd_4635153 := by
    simpa [prefixWord, tailWord_4635153, baseEnd_4635153] using wordTrace_append hprefix tailTrace_4635153
  have hstable : (prefixWord ++ tailWord_4635153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635153).length < 2 ^ (prefixWord ++ tailWord_4635153).sum := by decide
  have hdescent : baseEnd_4635153 < baseStart_4635153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635168 : List Nat := [2, 1, 1, 6, 2, 2, 2, 2, 1, 4]
def baseStart_4635168 : Nat := 118140960795 + 4635168 * 2 ^ 59
def prefixEnd_4635168 : Nat := 4983230072969 + 3 ^ 40 * 4635168 * 2
def baseEnd_4635168 : Nat := 793356366113142039194419

theorem tailTrace_4635168 : CollatzResearch.WordTrace tailWord_4635168 prefixEnd_4635168 793356366113142039194419 := by
  unfold tailWord_4635168
  simp only [CollatzResearch.WordTrace]
  refine ⟨84529232835792717257565079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112705643781056956343420105 84529232835792717257565079)
  ·
    refine ⟨126793849253689075886347619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84529232835792717257565079 126793849253689075886347619)
    ·
      refine ⟨190190773880533613829521429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126793849253689075886347619 190190773880533613829521429)
      ·
        refine ⟨8915192525650013148258817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 190190773880533613829521429 8915192525650013148258817)
        ·
          refine ⟨6686394394237509861194113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8915192525650013148258817 6686394394237509861194113)
          ·
            refine ⟨5014795795678132395895585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6686394394237509861194113 5014795795678132395895585)
            ·
              refine ⟨3761096846758599296921689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5014795795678132395895585 3761096846758599296921689)
              ·
                refine ⟨2820822635068949472691267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3761096846758599296921689 2820822635068949472691267)
                ·
                  refine ⟨4231233952603424209036901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2820822635068949472691267 4231233952603424209036901)
                  ·
                    refine ⟨793356366113142039194419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4231233952603424209036901 793356366113142039194419)
                    ·
                      rfl

theorem cell23_4635168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 2, 1, 4].length) (baseStart_4635168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635168 prefixEnd_4635168 := by exact prefixLift 4635168
  have htrace : WordTrace (prefixWord ++ tailWord_4635168) baseStart_4635168 baseEnd_4635168 := by
    simpa [prefixWord, tailWord_4635168, baseEnd_4635168] using wordTrace_append hprefix tailTrace_4635168
  have hstable : (prefixWord ++ tailWord_4635168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635168).length < 2 ^ (prefixWord ++ tailWord_4635168).sum := by decide
  have hdescent : baseEnd_4635168 < baseStart_4635168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635197 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4635197 : Nat := 118140960795 + 4635197 * 2 ^ 59
def prefixEnd_4635197 : Nat := 4983230072969 + 3 ^ 40 * 4635197 * 2
def baseEnd_4635197 : Nat := 2380083989278406504120623

theorem tailTrace_4635197 : CollatzResearch.WordTrace tailWord_4635197 prefixEnd_4635197 2380083989278406504120623 := by
  unfold tailWord_4635197
  simp only [CollatzResearch.WordTrace]
  refine ⟨169059523388480372467935845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112706348925653581645290563 169059523388480372467935845)
  ·
    refine ⟨31698660635340069837737971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169059523388480372467935845 31698660635340069837737971)
    ·
      refine ⟨47547990953010104756606957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31698660635340069837737971 47547990953010104756606957)
      ·
        refine ⟨17830496607378789283727609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47547990953010104756606957 17830496607378789283727609)
        ·
          refine ⟨13372872455534091962795707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17830496607378789283727609 13372872455534091962795707)
          ·
            refine ⟨20059308683301137944193561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13372872455534091962795707 20059308683301137944193561)
            ·
              refine ⟨15044481512475853458145171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20059308683301137944193561 15044481512475853458145171)
              ·
                refine ⟨22566722268713780187217757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15044481512475853458145171 22566722268713780187217757)
                ·
                  refine ⟨8462520850767667570206659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22566722268713780187217757 8462520850767667570206659)
                  ·
                    refine ⟨12693781276151501355309989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8462520850767667570206659 12693781276151501355309989)
                    ·
                      refine ⟨2380083989278406504120623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12693781276151501355309989 2380083989278406504120623)
                      ·
                        rfl

theorem cell23_4635197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4635197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635197 prefixEnd_4635197 := by exact prefixLift 4635197
  have htrace : WordTrace (prefixWord ++ tailWord_4635197) baseStart_4635197 baseEnd_4635197 := by
    simpa [prefixWord, tailWord_4635197, baseEnd_4635197] using wordTrace_append hprefix tailTrace_4635197
  have hstable : (prefixWord ++ tailWord_4635197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635197).length < 2 ^ (prefixWord ++ tailWord_4635197).sum := by decide
  have hdescent : baseEnd_4635197 < baseStart_4635197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635201 : List Nat := [1, 2, 5, 1, 1, 4, 1, 1, 2, 3, 2]
def baseStart_4635201 : Nat := 118140960795 + 4635201 * 2 ^ 59
def prefixEnd_4635201 : Nat := 4983230072969 + 3 ^ 40 * 4635201 * 2
def baseEnd_4635201 : Nat := 2380086043201024488470605

theorem tailTrace_4635201 : CollatzResearch.WordTrace tailWord_4635201 prefixEnd_4635201 2380086043201024488470605 := by
  unfold tailWord_4635201
  simp only [CollatzResearch.WordTrace]
  refine ⟨169059669280465881151081457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112706446186977254100720971 169059669280465881151081457)
  ·
    refine ⟨126794751960349410863311093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169059669280465881151081457 126794751960349410863311093)
    ·
      refine ⟨11887007996282757268435415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126794751960349410863311093 11887007996282757268435415)
      ·
        refine ⟨17830511994424135902653123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11887007996282757268435415 17830511994424135902653123)
        ·
          refine ⟨26745767991636203853979685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17830511994424135902653123 26745767991636203853979685)
          ·
            refine ⟨5014831498431788222621191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26745767991636203853979685 5014831498431788222621191)
            ·
              refine ⟨7522247247647682333931787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5014831498431788222621191 7522247247647682333931787)
              ·
                refine ⟨11283370871471523500897681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7522247247647682333931787 11283370871471523500897681)
                ·
                  refine ⟨8462528153603642625673261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11283370871471523500897681 8462528153603642625673261)
                  ·
                    refine ⟨3173448057601365984627473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8462528153603642625673261 3173448057601365984627473)
                    ·
                      refine ⟨2380086043201024488470605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173448057601365984627473 2380086043201024488470605)
                      ·
                        rfl

theorem cell23_4635201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 1, 1, 2, 3, 2].length) (baseStart_4635201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635201 prefixEnd_4635201 := by exact prefixLift 4635201
  have htrace : WordTrace (prefixWord ++ tailWord_4635201) baseStart_4635201 baseEnd_4635201 := by
    simpa [prefixWord, tailWord_4635201, baseEnd_4635201] using wordTrace_append hprefix tailTrace_4635201
  have hstable : (prefixWord ++ tailWord_4635201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635201).length < 2 ^ (prefixWord ++ tailWord_4635201).sum := by decide
  have hdescent : baseEnd_4635201 < baseStart_4635201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635203 : List Nat := [1, 1, 1, 3, 1, 2, 1, 13]
def baseStart_4635203 : Nat := 118140960795 + 4635203 * 2 ^ 59
def prefixEnd_4635203 : Nat := 4983230072969 + 3 ^ 40 * 4635203 * 2
def baseEnd_4635203 : Nat := 88151372968975314097985

theorem tailTrace_4635203 : CollatzResearch.WordTrace tailWord_4635203 prefixEnd_4635203 88151372968975314097985 := by
  unfold tailWord_4635203
  simp only [CollatzResearch.WordTrace]
  refine ⟨169059742226458635492654263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112706494817639090328436175 169059742226458635492654263)
  ·
    refine ⟨253589613339687953238981395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169059742226458635492654263 253589613339687953238981395)
    ·
      refine ⟨380384420009531929858472093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253589613339687953238981395 380384420009531929858472093)
      ·
        refine ⟨142644157503574473696927035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 380384420009531929858472093 142644157503574473696927035)
        ·
          refine ⟨213966236255361710545390553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142644157503574473696927035 213966236255361710545390553)
          ·
            refine ⟨160474677191521282909042915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 213966236255361710545390553 160474677191521282909042915)
            ·
              refine ⟨240712015787281924363564373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160474677191521282909042915 240712015787281924363564373)
              ·
                refine ⟨88151372968975314097985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 240712015787281924363564373 88151372968975314097985)
                ·
                  rfl

theorem cell23_4635203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 13].length) (baseStart_4635203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635203 prefixEnd_4635203 := by exact prefixLift 4635203
  have htrace : WordTrace (prefixWord ++ tailWord_4635203) baseStart_4635203 baseEnd_4635203 := by
    simpa [prefixWord, tailWord_4635203, baseEnd_4635203] using wordTrace_append hprefix tailTrace_4635203
  have hstable : (prefixWord ++ tailWord_4635203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635203).length < 2 ^ (prefixWord ++ tailWord_4635203).sum := by decide
  have hdescent : baseEnd_4635203 < baseStart_4635203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635214 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4]
def baseStart_4635214 : Nat := 118140960795 + 4635214 * 2 ^ 59
def prefixEnd_4635214 : Nat := 4983230072969 + 3 ^ 40 * 4635214 * 2
def baseEnd_4635214 : Nat := 2380092718449532937608045

theorem tailTrace_4635214 : CollatzResearch.WordTrace tailWord_4635214 prefixEnd_4635214 2380092718449532937608045 := by
  unfold tailWord_4635214
  simp only [CollatzResearch.WordTrace]
  refine ⟨21132517928677348046413087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112706762286279189580869797 21132517928677348046413087)
  ·
    refine ⟨31698776893016022069619631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21132517928677348046413087 31698776893016022069619631)
    ·
      refine ⟨47548165339524033104429447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31698776893016022069619631 47548165339524033104429447)
      ·
        refine ⟨71322248009286049656644171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47548165339524033104429447 71322248009286049656644171)
        ·
          refine ⟨106983372013929074484966257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71322248009286049656644171 106983372013929074484966257)
          ·
            refine ⟨80237529010446805863724693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106983372013929074484966257 80237529010446805863724693)
            ·
              refine ⟨3761134172364694024862095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 80237529010446805863724693 3761134172364694024862095)
              ·
                refine ⟨5641701258547041037293143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3761134172364694024862095 5641701258547041037293143)
                ·
                  refine ⟨8462551887820561555939715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5641701258547041037293143 8462551887820561555939715)
                  ·
                    refine ⟨12693827831730842333909573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8462551887820561555939715 12693827831730842333909573)
                    ·
                      refine ⟨2380092718449532937608045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12693827831730842333909573 2380092718449532937608045)
                      ·
                        rfl

theorem cell23_4635214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 1, 4].length) (baseStart_4635214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635214 prefixEnd_4635214 := by exact prefixLift 4635214
  have htrace : WordTrace (prefixWord ++ tailWord_4635214) baseStart_4635214 baseEnd_4635214 := by
    simpa [prefixWord, tailWord_4635214, baseEnd_4635214] using wordTrace_append hprefix tailTrace_4635214
  have hstable : (prefixWord ++ tailWord_4635214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635214).length < 2 ^ (prefixWord ++ tailWord_4635214).sum := by decide
  have hdescent : baseEnd_4635214 < baseStart_4635214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635220 : List Nat := [2, 4, 1, 1, 1, 4, 10]
def baseStart_4635220 : Nat := 118140960795 + 4635220 * 2 ^ 59
def prefixEnd_4635220 : Nat := 4983230072969 + 3 ^ 40 * 4635220 * 2
def baseEnd_4635220 : Nat := 29383898757203208816457

theorem tailTrace_4635220 : CollatzResearch.WordTrace tailWord_4635220 prefixEnd_4635220 29383898757203208816457 := by
  unfold tailWord_4635220
  simp only [CollatzResearch.WordTrace]
  refine ⟨84530181133698523698011557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112706908178264698264015409 84530181133698523698011557)
  ·
    refine ⟨15849408962568473193377167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84530181133698523698011557 15849408962568473193377167)
    ·
      refine ⟨23774113443852709790065751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15849408962568473193377167 23774113443852709790065751)
      ·
        refine ⟨35661170165779064685098627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23774113443852709790065751 35661170165779064685098627)
        ·
          refine ⟨53491755248668597027647941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35661170165779064685098627 53491755248668597027647941)
          ·
            refine ⟨10029704109125361942683989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53491755248668597027647941 10029704109125361942683989)
            ·
              refine ⟨29383898757203208816457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10029704109125361942683989 29383898757203208816457)
              ·
                rfl

theorem cell23_4635220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 10].length) (baseStart_4635220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635220 prefixEnd_4635220 := by exact prefixLift 4635220
  have htrace : WordTrace (prefixWord ++ tailWord_4635220) baseStart_4635220 baseEnd_4635220 := by
    simpa [prefixWord, tailWord_4635220, baseEnd_4635220] using wordTrace_append hprefix tailTrace_4635220
  have hstable : (prefixWord ++ tailWord_4635220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635220).length < 2 ^ (prefixWord ++ tailWord_4635220).sum := by decide
  have hdescent : baseEnd_4635220 < baseStart_4635220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635247 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 3]
def baseStart_4635247 : Nat := 118140960795 + 4635247 * 2 ^ 59
def prefixEnd_4635247 : Nat := 4983230072969 + 3 ^ 40 * 4635247 * 2
def baseEnd_4635247 : Nat := 2380109663311131308495393

theorem tailTrace_4635247 : CollatzResearch.WordTrace tailWord_4635247 prefixEnd_4635247 2380109663311131308495393 := by
  unfold tailWord_4635247
  simp only [CollatzResearch.WordTrace]
  refine ⟨169061347038299231007255995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112707564692199487338170663 169061347038299231007255995)
  ·
    refine ⟨253592020557448846510883993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169061347038299231007255995 253592020557448846510883993)
    ·
      refine ⟨190194015418086634883162995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253592020557448846510883993 190194015418086634883162995)
      ·
        refine ⟨285291023127129952324744493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190194015418086634883162995 285291023127129952324744493)
        ·
          refine ⟨106984133672673732121779185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285291023127129952324744493 106984133672673732121779185)
          ·
            refine ⟨80238100254505299091334389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106984133672673732121779185 80238100254505299091334389)
            ·
              refine ⟨7522321898859871789812599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80238100254505299091334389 7522321898859871789812599)
              ·
                refine ⟨11283482848289807684718899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7522321898859871789812599 11283482848289807684718899)
                ·
                  refine ⟨16925224272434711527078349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11283482848289807684718899 16925224272434711527078349)
                  ·
                    refine ⟨6346959102163016822654381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16925224272434711527078349 6346959102163016822654381)
                    ·
                      refine ⟨2380109663311131308495393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6346959102163016822654381 2380109663311131308495393)
                      ·
                        rfl

theorem cell23_4635247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_4635247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635247 prefixEnd_4635247 := by exact prefixLift 4635247
  have htrace : WordTrace (prefixWord ++ tailWord_4635247) baseStart_4635247 baseEnd_4635247 := by
    simpa [prefixWord, tailWord_4635247, baseEnd_4635247] using wordTrace_append hprefix tailTrace_4635247
  have hstable : (prefixWord ++ tailWord_4635247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635247).length < 2 ^ (prefixWord ++ tailWord_4635247).sum := by decide
  have hdescent : baseEnd_4635247 < baseStart_4635247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635260 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 2, 2, 5]
def baseStart_4635260 : Nat := 118140960795 + 4635260 * 2 ^ 59
def prefixEnd_4635260 : Nat := 4983230072969 + 3 ^ 40 * 4635260 * 2
def baseEnd_4635260 : Nat := 2380116338559639757632833

theorem tailTrace_4635260 : CollatzResearch.WordTrace tailWord_4635260 prefixEnd_4635260 2380116338559639757632833 := by
  unfold tailWord_4635260
  simp only [CollatzResearch.WordTrace]
  refine ⟨84530910593626067113739617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112707880791501422818319489 84530910593626067113739617)
  ·
    refine ⟨63398182945219550335304713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84530910593626067113739617 63398182945219550335304713)
    ·
      refine ⟨47548637208914662751478535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63398182945219550335304713 47548637208914662751478535)
      ·
        refine ⟨71322955813371994127217803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47548637208914662751478535 71322955813371994127217803)
        ·
          refine ⟨106984433720057991190826705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71322955813371994127217803 106984433720057991190826705)
          ·
            refine ⟨80238325290043493393120029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106984433720057991190826705 80238325290043493393120029)
            ·
              refine ⟨30089371983766310022420011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80238325290043493393120029 30089371983766310022420011)
              ·
                refine ⟨45134057975649465033630017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30089371983766310022420011 45134057975649465033630017)
                ·
                  refine ⟨33850543481737098775222513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45134057975649465033630017 33850543481737098775222513)
                  ·
                    refine ⟨25387907611302824081416885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33850543481737098775222513 25387907611302824081416885)
                    ·
                      refine ⟨2380116338559639757632833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25387907611302824081416885 2380116338559639757632833)
                      ·
                        rfl

theorem cell23_4635260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_4635260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635260 prefixEnd_4635260 := by exact prefixLift 4635260
  have htrace : WordTrace (prefixWord ++ tailWord_4635260) baseStart_4635260 baseEnd_4635260 := by
    simpa [prefixWord, tailWord_4635260, baseEnd_4635260] using wordTrace_append hprefix tailTrace_4635260
  have hstable : (prefixWord ++ tailWord_4635260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635260).length < 2 ^ (prefixWord ++ tailWord_4635260).sum := by decide
  have hdescent : baseEnd_4635260 < baseStart_4635260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635338 : List Nat := [3, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2]
def baseStart_4635338 : Nat := 118140960795 + 4635338 * 2 ^ 59
def prefixEnd_4635338 : Nat := 4983230072969 + 3 ^ 40 * 4635338 * 2
def baseEnd_4635338 : Nat := 2380156390050690452457475

theorem tailTrace_4635338 : CollatzResearch.WordTrace tailWord_4635338 prefixEnd_4635338 2380156390050690452457475 := by
  unfold tailWord_4635338
  simp only [CollatzResearch.WordTrace]
  refine ⟨42266166520242388387204667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112709777387313035699212445 42266166520242388387204667)
  ·
    refine ⟨63399249780363582580807001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42266166520242388387204667 63399249780363582580807001)
    ·
      refine ⟨47549437335272686935605251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63399249780363582580807001 47549437335272686935605251)
      ·
        refine ⟨71324156002909030403407877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47549437335272686935605251 71324156002909030403407877)
        ·
          refine ⟨13373279250545443200638977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71324156002909030403407877 13373279250545443200638977)
          ·
            refine ⟨10029959437909082400479233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13373279250545443200638977 10029959437909082400479233)
            ·
              refine ⟨7522469578431811800359425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10029959437909082400479233 7522469578431811800359425)
              ·
                refine ⟨5641852183823858850269569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7522469578431811800359425 5641852183823858850269569)
                ·
                  refine ⟨4231389137867894137702177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5641852183823858850269569 4231389137867894137702177)
                  ·
                    refine ⟨3173541853400920603276633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4231389137867894137702177 3173541853400920603276633)
                    ·
                      refine ⟨2380156390050690452457475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173541853400920603276633 2380156390050690452457475)
                      ·
                        rfl

theorem cell23_4635338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2].length) (baseStart_4635338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635338 prefixEnd_4635338 := by exact prefixLift 4635338
  have htrace : WordTrace (prefixWord ++ tailWord_4635338) baseStart_4635338 baseEnd_4635338 := by
    simpa [prefixWord, tailWord_4635338, baseEnd_4635338] using wordTrace_append hprefix tailTrace_4635338
  have hstable : (prefixWord ++ tailWord_4635338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635338).length < 2 ^ (prefixWord ++ tailWord_4635338).sum := by decide
  have hdescent : baseEnd_4635338 < baseStart_4635338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635374 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 2, 5]
def baseStart_4635374 : Nat := 118140960795 + 4635374 * 2 ^ 59
def prefixEnd_4635374 : Nat := 4983230072969 + 3 ^ 40 * 4635374 * 2
def baseEnd_4635374 : Nat := 793391625118084103869103

theorem tailTrace_4635374 : CollatzResearch.WordTrace tailWord_4635374 prefixEnd_4635374 793391625118084103869103 := by
  unfold tailWord_4635374
  simp only [CollatzResearch.WordTrace]
  refine ⟨21133247388604891462141147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112710652739226087798086117 21133247388604891462141147)
  ·
    refine ⟨31699871082907337193211721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21133247388604891462141147 31699871082907337193211721)
    ·
      refine ⟨23774903312180502894908791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31699871082907337193211721 23774903312180502894908791)
      ·
        refine ⟨35662354968270754342363187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23774903312180502894908791 35662354968270754342363187)
        ·
          refine ⟨53493532452406131513544781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35662354968270754342363187 53493532452406131513544781)
          ·
            refine ⟨20060074669652299317579293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53493532452406131513544781 20060074669652299317579293)
            ·
              refine ⟨7522528001119612244092235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20060074669652299317579293 7522528001119612244092235)
              ·
                refine ⟨11283792001679418366138353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7522528001119612244092235 11283792001679418366138353)
                ·
                  refine ⟨8462844001259563774603765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11283792001679418366138353 8462844001259563774603765)
                  ·
                    refine ⟨793391625118084103869103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8462844001259563774603765 793391625118084103869103)
                    ·
                      rfl

theorem cell23_4635374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 5].length) (baseStart_4635374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635374 prefixEnd_4635374 := by exact prefixLift 4635374
  have htrace : WordTrace (prefixWord ++ tailWord_4635374) baseStart_4635374 baseEnd_4635374 := by
    simpa [prefixWord, tailWord_4635374, baseEnd_4635374] using wordTrace_append hprefix tailTrace_4635374
  have hstable : (prefixWord ++ tailWord_4635374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635374).length < 2 ^ (prefixWord ++ tailWord_4635374).sum := by decide
  have hdescent : baseEnd_4635374 < baseStart_4635374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635377 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 4]
def baseStart_4635377 : Nat := 118140960795 + 4635377 * 2 ^ 59
def prefixEnd_4635377 : Nat := 4983230072969 + 3 ^ 40 * 4635377 * 2
def baseEnd_4635377 : Nat := 2380176415796215799869795

theorem tailTrace_4635377 : CollatzResearch.WordTrace tailWord_4635377 prefixEnd_4635377 2380176415796215799869795 := by
  unfold tailWord_4635377
  simp only [CollatzResearch.WordTrace]
  refine ⟨169066088527828263209488385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112710725685218842139658923 169066088527828263209488385)
  ·
    refine ⟨126799566395871197407116289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169066088527828263209488385 126799566395871197407116289)
    ·
      refine ⟨95099674796903398055337217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126799566395871197407116289 95099674796903398055337217)
      ·
        refine ⟨71324756097677548541502913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95099674796903398055337217 71324756097677548541502913)
        ·
          refine ⟨53493567073258161406127185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71324756097677548541502913 53493567073258161406127185)
          ·
            refine ⟨40120175304943621054595389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53493567073258161406127185 40120175304943621054595389)
            ·
              refine ⟨15045065739353857895473271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40120175304943621054595389 15045065739353857895473271)
              ·
                refine ⟨22567598609030786843209907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15045065739353857895473271 22567598609030786843209907)
                ·
                  refine ⟨33851397913546180264814861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22567598609030786843209907 33851397913546180264814861)
                  ·
                    refine ⟨12694274217579817599305573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33851397913546180264814861 12694274217579817599305573)
                    ·
                      refine ⟨2380176415796215799869795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12694274217579817599305573 2380176415796215799869795)
                      ·
                        rfl

theorem cell23_4635377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 4].length) (baseStart_4635377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635377 prefixEnd_4635377 := by exact prefixLift 4635377
  have htrace : WordTrace (prefixWord ++ tailWord_4635377) baseStart_4635377 baseEnd_4635377 := by
    simpa [prefixWord, tailWord_4635377, baseEnd_4635377] using wordTrace_append hprefix tailTrace_4635377
  have hstable : (prefixWord ++ tailWord_4635377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635377).length < 2 ^ (prefixWord ++ tailWord_4635377).sum := by decide
  have hdescent : baseEnd_4635377 < baseStart_4635377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635427 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 3]
def baseStart_4635427 : Nat := 118140960795 + 4635427 * 2 ^ 59
def prefixEnd_4635427 : Nat := 4983230072969 + 3 ^ 40 * 4635427 * 2
def baseEnd_4635427 : Nat := 2380202089828940604244565

theorem tailTrace_4635427 : CollatzResearch.WordTrace tailWord_4635427 prefixEnd_4635427 2380202089828940604244565 := by
  unfold tailWord_4635427
  simp only [CollatzResearch.WordTrace]
  refine ⟨169067912177647121748808535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112711941451764747832539023 169067912177647121748808535)
  ·
    refine ⟨253601868266470682623212803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169067912177647121748808535 253601868266470682623212803)
    ·
      refine ⟨380402802399706023934819205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253601868266470682623212803 380402802399706023934819205)
      ·
        refine ⟨71325525449944879487778601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 380402802399706023934819205 71325525449944879487778601)
        ·
          refine ⟨53494144087458659615833951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71325525449944879487778601 53494144087458659615833951)
          ·
            refine ⟨80241216131187989423750927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53494144087458659615833951 80241216131187989423750927)
            ·
              refine ⟨120361824196781984135626391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80241216131187989423750927 120361824196781984135626391)
              ·
                refine ⟨180542736295172976203439587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120361824196781984135626391 180542736295172976203439587)
                ·
                  refine ⟨270814104442759464305159381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 180542736295172976203439587 270814104442759464305159381)
                  ·
                    refine ⟨6347205572877174944652173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 270814104442759464305159381 6347205572877174944652173)
                    ·
                      refine ⟨2380202089828940604244565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6347205572877174944652173 2380202089828940604244565)
                      ·
                        rfl

theorem cell23_4635427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 7, 3].length) (baseStart_4635427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635427 prefixEnd_4635427 := by exact prefixLift 4635427
  have htrace : WordTrace (prefixWord ++ tailWord_4635427) baseStart_4635427 baseEnd_4635427 := by
    simpa [prefixWord, tailWord_4635427, baseEnd_4635427] using wordTrace_append hprefix tailTrace_4635427
  have hstable : (prefixWord ++ tailWord_4635427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635427).length < 2 ^ (prefixWord ++ tailWord_4635427).sum := by decide
  have hdescent : baseEnd_4635427 < baseStart_4635427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635481 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 1, 5]
def baseStart_4635481 : Nat := 118140960795 + 4635481 * 2 ^ 59
def prefixEnd_4635481 : Nat := 4983230072969 + 3 ^ 40 * 4635481 * 2
def baseEnd_4635481 : Nat := 793409939261427797656439

theorem tailTrace_4635481 : CollatzResearch.WordTrace tailWord_4635481 prefixEnd_4635481 793409939261427797656439 := by
  unfold tailWord_4635481
  simp only [CollatzResearch.WordTrace]
  refine ⟨169069881719451488971274297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112713254479634325980849531 169069881719451488971274297)
  ·
    refine ⟨126802411289588616728455723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169069881719451488971274297 126802411289588616728455723)
    ·
      refine ⟨190203616934382925092683585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126802411289588616728455723 190203616934382925092683585)
      ·
        refine ⟨142652712700787193819512689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190203616934382925092683585 142652712700787193819512689)
        ·
          refine ⟨106989534525590395364634517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142652712700787193819512689 106989534525590395364634517)
          ·
            refine ⟨5015134430887049782717243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106989534525590395364634517 5015134430887049782717243)
            ·
              refine ⟨7522701646330574674075865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015134430887049782717243 7522701646330574674075865)
              ·
                refine ⟨5642026234747931005556899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7522701646330574674075865 5642026234747931005556899)
                ·
                  refine ⟨8463039352121896508335349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5642026234747931005556899 8463039352121896508335349)
                  ·
                    refine ⟨793409939261427797656439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8463039352121896508335349 793409939261427797656439)
                    ·
                      rfl

theorem cell23_4635481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 5].length) (baseStart_4635481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635481 prefixEnd_4635481 := by exact prefixLift 4635481
  have htrace : WordTrace (prefixWord ++ tailWord_4635481) baseStart_4635481 baseEnd_4635481 := by
    simpa [prefixWord, tailWord_4635481, baseEnd_4635481] using wordTrace_append hprefix tailTrace_4635481
  have hstable : (prefixWord ++ tailWord_4635481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635481).length < 2 ^ (prefixWord ++ tailWord_4635481).sum := by decide
  have hdescent : baseEnd_4635481 < baseStart_4635481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635504 : List Nat := [2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 5]
def baseStart_4635504 : Nat := 118140960795 + 4635504 * 2 ^ 59
def prefixEnd_4635504 : Nat := 4983230072969 + 3 ^ 40 * 4635504 * 2
def baseEnd_4635504 : Nat := 2380241627839336802981711

theorem tailTrace_4635504 : CollatzResearch.WordTrace tailWord_4635504 prefixEnd_4635504 2380241627839336802981711 := by
  unfold tailWord_4635504
  simp only [CollatzResearch.WordTrace]
  refine ⟨84535360299184081949680783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112713813732245442599574377 84535360299184081949680783)
  ·
    refine ⟨126803040448776122924521175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84535360299184081949680783 126803040448776122924521175)
    ·
      refine ⟨190204560673164184386781763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126803040448776122924521175 190204560673164184386781763)
      ·
        refine ⟨285306841009746276580172645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190204560673164184386781763 285306841009746276580172645)
        ·
          refine ⟨53495032689327426858782371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 285306841009746276580172645 53495032689327426858782371)
          ·
            refine ⟨80242549033991140288173557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53495032689327426858782371 80242549033991140288173557)
            ·
              refine ⟨7522738971936669402016271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 80242549033991140288173557 7522738971936669402016271)
              ·
                refine ⟨11284108457905004103024407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7522738971936669402016271 11284108457905004103024407)
                ·
                  refine ⟨16926162686857506154536611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11284108457905004103024407 16926162686857506154536611)
                  ·
                    refine ⟨25389244030286259231804917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16926162686857506154536611 25389244030286259231804917)
                    ·
                      refine ⟨2380241627839336802981711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25389244030286259231804917 2380241627839336802981711)
                      ·
                        rfl

theorem cell23_4635504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 5].length) (baseStart_4635504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635504 prefixEnd_4635504 := by exact prefixLift 4635504
  have htrace : WordTrace (prefixWord ++ tailWord_4635504) baseStart_4635504 baseEnd_4635504 := by
    simpa [prefixWord, tailWord_4635504, baseEnd_4635504] using wordTrace_append hprefix tailTrace_4635504
  have hstable : (prefixWord ++ tailWord_4635504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635504).length < 2 ^ (prefixWord ++ tailWord_4635504).sum := by decide
  have hdescent : baseEnd_4635504 < baseStart_4635504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635537 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 4, 7]
def baseStart_4635537 : Nat := 118140960795 + 4635537 * 2 ^ 59
def prefixEnd_4635537 : Nat := 4983230072969 + 3 ^ 40 * 4635537 * 2
def baseEnd_4635537 : Nat := 793419524233645057956353

theorem tailTrace_4635537 : CollatzResearch.WordTrace tailWord_4635537 prefixEnd_4635537 793419524233645057956353 := by
  unfold tailWord_4635537
  simp only [CollatzResearch.WordTrace]
  refine ⟨169071924207248610535312865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112714616138165740356875243 169071924207248610535312865)
  ·
    refine ⟨126803943155436457901484649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169071924207248610535312865 126803943155436457901484649)
    ·
      refine ⟨95102957366577343426113487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126803943155436457901484649 95102957366577343426113487)
      ·
        refine ⟨142654436049866015139170231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95102957366577343426113487 142654436049866015139170231)
        ·
          refine ⟨213981654074799022708755347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142654436049866015139170231 213981654074799022708755347)
          ·
            refine ⟨320972481112198534063133021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213981654074799022708755347 320972481112198534063133021)
            ·
              refine ⟨120364680417074450273674883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 320972481112198534063133021 120364680417074450273674883)
              ·
                refine ⟨180547020625611675410512325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120364680417074450273674883 180547020625611675410512325)
                ·
                  refine ⟨33852566367302189139471061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 180547020625611675410512325 33852566367302189139471061)
                  ·
                    refine ⟨793419524233645057956353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33852566367302189139471061 793419524233645057956353)
                    ·
                      rfl

theorem cell23_4635537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_4635537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635537 prefixEnd_4635537 := by exact prefixLift 4635537
  have htrace : WordTrace (prefixWord ++ tailWord_4635537) baseStart_4635537 baseEnd_4635537 := by
    simpa [prefixWord, tailWord_4635537, baseEnd_4635537] using wordTrace_append hprefix tailTrace_4635537
  have hstable : (prefixWord ++ tailWord_4635537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635537).length < 2 ^ (prefixWord ++ tailWord_4635537).sum := by decide
  have hdescent : baseEnd_4635537 < baseStart_4635537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635551 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 3]
def baseStart_4635551 : Nat := 118140960795 + 4635551 * 2 ^ 59
def prefixEnd_4635551 : Nat := 4983230072969 + 3 ^ 40 * 4635551 * 2
def baseEnd_4635551 : Nat := 2380265761430098119093995

theorem tailTrace_4635551 : CollatzResearch.WordTrace tailWord_4635551 prefixEnd_4635551 2380265761430098119093995 := by
  unfold tailWord_4635551
  simp only [CollatzResearch.WordTrace]
  refine ⟨169072434829197890926322507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112714956552798593950881671 169072434829197890926322507)
  ·
    refine ⟨253608652243796836389483761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169072434829197890926322507 253608652243796836389483761)
    ·
      refine ⟨190206489182847627292112821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253608652243796836389483761 190206489182847627292112821)
      ·
        refine ⟨17831858360891965058635577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 190206489182847627292112821 17831858360891965058635577)
        ·
          refine ⟨13373893770668973793976683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17831858360891965058635577 13373893770668973793976683)
          ·
            refine ⟨20060840656003460690965025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13373893770668973793976683 20060840656003460690965025)
            ·
              refine ⟨15045630492002595518223769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20060840656003460690965025 15045630492002595518223769)
              ·
                refine ⟨11284222869001946638667827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15045630492002595518223769 11284222869001946638667827)
                ·
                  refine ⟨16926334303502919958001741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11284222869001946638667827 16926334303502919958001741)
                  ·
                    refine ⟨6347375363813594984250653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16926334303502919958001741 6347375363813594984250653)
                    ·
                      refine ⟨2380265761430098119093995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6347375363813594984250653 2380265761430098119093995)
                      ·
                        rfl

theorem cell23_4635551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_4635551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635551 prefixEnd_4635551 := by exact prefixLift 4635551
  have htrace : WordTrace (prefixWord ++ tailWord_4635551) baseStart_4635551 baseEnd_4635551 := by
    simpa [prefixWord, tailWord_4635551, baseEnd_4635551] using wordTrace_append hprefix tailTrace_4635551
  have hstable : (prefixWord ++ tailWord_4635551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635551).length < 2 ^ (prefixWord ++ tailWord_4635551).sum := by decide
  have hdescent : baseEnd_4635551 < baseStart_4635551 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635584 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 2, 6]
def baseStart_4635584 : Nat := 118140960795 + 4635584 * 2 ^ 59
def prefixEnd_4635584 : Nat := 4983230072969 + 3 ^ 40 * 4635584 * 2
def baseEnd_4635584 : Nat := 793427568763898829993781

theorem tailTrace_4635584 : CollatzResearch.WordTrace tailWord_4635584 prefixEnd_4635584 793427568763898829993781 := by
  unfold tailWord_4635584
  simp only [CollatzResearch.WordTrace]
  refine ⟨84536819219039168781136903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112715758958718891708182537 84536819219039168781136903)
  ·
    refine ⟨126805228828558753171705355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84536819219039168781136903 126805228828558753171705355)
    ·
      refine ⟨190207843242838129757558033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126805228828558753171705355 190207843242838129757558033)
      ·
        refine ⟨142655882432128597318168525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190207843242838129757558033 142655882432128597318168525)
        ·
          refine ⟨53495955912048223994313197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142655882432128597318168525 53495955912048223994313197)
          ·
            refine ⟨20060983467018083997867449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53495955912048223994313197 20060983467018083997867449)
            ·
              refine ⟨15045737600263562998400587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20060983467018083997867449 15045737600263562998400587)
              ·
                refine ⟨22568606400395344497600881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15045737600263562998400587 22568606400395344497600881)
                ·
                  refine ⟨16926454800296508373200661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22568606400395344497600881 16926454800296508373200661)
                  ·
                    refine ⟨793427568763898829993781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16926454800296508373200661 793427568763898829993781)
                    ·
                      rfl

theorem cell23_4635584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 6].length) (baseStart_4635584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635584 prefixEnd_4635584 := by exact prefixLift 4635584
  have htrace : WordTrace (prefixWord ++ tailWord_4635584) baseStart_4635584 baseEnd_4635584 := by
    simpa [prefixWord, tailWord_4635584, baseEnd_4635584] using wordTrace_append hprefix tailTrace_4635584
  have hstable : (prefixWord ++ tailWord_4635584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635584).length < 2 ^ (prefixWord ++ tailWord_4635584).sum := by decide
  have hdescent : baseEnd_4635584 < baseStart_4635584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635594 : List Nat := [3, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5]
def baseStart_4635594 : Nat := 118140960795 + 4635594 * 2 ^ 59
def prefixEnd_4635594 : Nat := 4983230072969 + 3 ^ 40 * 4635594 * 2
def baseEnd_4635594 : Nat := 2380287841098241450856297

theorem tailTrace_4635594 : CollatzResearch.WordTrace tailWord_4635594 prefixEnd_4635594 2380287841098241450856297 := by
  unfold tailWord_4635594
  simp only [CollatzResearch.WordTrace]
  refine ⟨42268500792010527317534459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112716002112028072846758557 42268500792010527317534459)
  ·
    refine ⟨63402751188015790976301689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42268500792010527317534459 63402751188015790976301689)
    ·
      refine ⟨47552063391011843232226267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63402751188015790976301689 47552063391011843232226267)
      ·
        refine ⟨71328095086517764848339401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47552063391011843232226267 71328095086517764848339401)
        ·
          refine ⟨53496071314888323636254551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71328095086517764848339401 53496071314888323636254551)
          ·
            refine ⟨80244106972332485454381827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53496071314888323636254551 80244106972332485454381827)
            ·
              refine ⟨120366160458498728181572741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80244106972332485454381827 120366160458498728181572741)
              ·
                refine ⟨22568655085968511534044889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120366160458498728181572741 22568655085968511534044889)
                ·
                  refine ⟨16926491314476383650533667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22568655085968511534044889 16926491314476383650533667)
                  ·
                    refine ⟨25389736971714575475800501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16926491314476383650533667 25389736971714575475800501)
                    ·
                      refine ⟨2380287841098241450856297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25389736971714575475800501 2380287841098241450856297)
                      ·
                        rfl

theorem cell23_4635594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_4635594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635594 prefixEnd_4635594 := by exact prefixLift 4635594
  have htrace : WordTrace (prefixWord ++ tailWord_4635594) baseStart_4635594 baseEnd_4635594 := by
    simpa [prefixWord, tailWord_4635594, baseEnd_4635594] using wordTrace_append hprefix tailTrace_4635594
  have hstable : (prefixWord ++ tailWord_4635594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635594).length < 2 ^ (prefixWord ++ tailWord_4635594).sum := by decide
  have hdescent : baseEnd_4635594 < baseStart_4635594 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635608 : List Nat := [2, 1, 2, 2, 2, 3, 1, 2, 4, 2, 2]
def baseStart_4635608 : Nat := 118140960795 + 4635608 * 2 ^ 59
def prefixEnd_4635608 : Nat := 4983230072969 + 3 ^ 40 * 4635608 * 2
def baseEnd_4635608 : Nat := 2380295029827404396081233

theorem tailTrace_4635608 : CollatzResearch.WordTrace tailWord_4635608 prefixEnd_4635608 2380295029827404396081233 := by
  unfold tailWord_4635608
  simp only [CollatzResearch.WordTrace]
  refine ⟨84537256894995694830573739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112716342526660926440764985 84537256894995694830573739)
  ·
    refine ⟨126805885342493542245860609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84537256894995694830573739 126805885342493542245860609)
    ·
      refine ⟨95104414006870156684395457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126805885342493542245860609 95104414006870156684395457)
      ·
        refine ⟨71328310505152617513296593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 95104414006870156684395457 71328310505152617513296593)
        ·
          refine ⟨53496232878864463134972445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71328310505152617513296593 53496232878864463134972445)
          ·
            refine ⟨20061087329574173675614667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53496232878864463134972445 20061087329574173675614667)
            ·
              refine ⟨30091630994361260513422001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20061087329574173675614667 30091630994361260513422001)
              ·
                refine ⟨22568723245770945385066501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30091630994361260513422001 22568723245770945385066501)
                ·
                  refine ⟨4231635608582052259699969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22568723245770945385066501 4231635608582052259699969)
                  ·
                    refine ⟨3173726706436539194774977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4231635608582052259699969 3173726706436539194774977)
                    ·
                      refine ⟨2380295029827404396081233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173726706436539194774977 2380295029827404396081233)
                      ·
                        rfl

theorem cell23_4635608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_4635608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635608 prefixEnd_4635608 := by exact prefixLift 4635608
  have htrace : WordTrace (prefixWord ++ tailWord_4635608) baseStart_4635608 baseEnd_4635608 := by
    simpa [prefixWord, tailWord_4635608, baseEnd_4635608] using wordTrace_append hprefix tailTrace_4635608
  have hstable : (prefixWord ++ tailWord_4635608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635608).length < 2 ^ (prefixWord ++ tailWord_4635608).sum := by decide
  have hdescent : baseEnd_4635608 < baseStart_4635608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635631 : List Nat := [1, 1, 2, 1, 4, 5, 1, 1, 7]
def baseStart_4635631 : Nat := 118140960795 + 4635631 * 2 ^ 59
def prefixEnd_4635631 : Nat := 4983230072969 + 3 ^ 40 * 4635631 * 2
def baseEnd_4635631 : Nat := 264478537764717534010403

theorem tailTrace_4635631 : CollatzResearch.WordTrace tailWord_4635631 prefixEnd_4635631 264478537764717534010403 := by
  unfold tailWord_4635631
  simp only [CollatzResearch.WordTrace]
  refine ⟨169075352668908064589234747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112716901779272043059489831 169075352668908064589234747)
  ·
    refine ⟨253613029003362096883852121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169075352668908064589234747 253613029003362096883852121)
    ·
      refine ⟨190209771752521572662889091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253613029003362096883852121 190209771752521572662889091)
      ·
        refine ⟨285314657628782358994333637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190209771752521572662889091 285314657628782358994333637)
        ·
          refine ⟨53496498305396692311437557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 285314657628782358994333637 53496498305396692311437557)
          ·
            refine ⟨5015296716130939904197271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53496498305396692311437557 5015296716130939904197271)
            ·
              refine ⟨7522945074196409856295907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015296716130939904197271 7522945074196409856295907)
              ·
                refine ⟨11284417611294614784443861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7522945074196409856295907 11284417611294614784443861)
                ·
                  refine ⟨264478537764717534010403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11284417611294614784443861 264478537764717534010403)
                  ·
                    rfl

theorem cell23_4635631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 1, 1, 7].length) (baseStart_4635631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635631 prefixEnd_4635631 := by exact prefixLift 4635631
  have htrace : WordTrace (prefixWord ++ tailWord_4635631) baseStart_4635631 baseEnd_4635631 := by
    simpa [prefixWord, tailWord_4635631, baseEnd_4635631] using wordTrace_append hprefix tailTrace_4635631
  have hstable : (prefixWord ++ tailWord_4635631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635631).length < 2 ^ (prefixWord ++ tailWord_4635631).sum := by decide
  have hdescent : baseEnd_4635631 < baseStart_4635631 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635636 : List Nat := [2, 6, 2, 1, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4635636 : Nat := 118140960795 + 4635636 * 2 ^ 59
def prefixEnd_4635636 : Nat := 4983230072969 + 3 ^ 40 * 4635636 * 2
def baseEnd_4635636 : Nat := 2380309407285730286531105

theorem tailTrace_4635636 : CollatzResearch.WordTrace tailWord_4635636 prefixEnd_4635636 2380309407285730286531105 := by
  unfold tailWord_4635636
  simp only [CollatzResearch.WordTrace]
  refine ⟨84537767516944975221583381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112717023355926633628777841 84537767516944975221583381)
  ·
    refine ⟨3962707852356795713511721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 84537767516944975221583381 3962707852356795713511721)
    ·
      refine ⟨2972030889267596785133791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3962707852356795713511721 2972030889267596785133791)
      ·
        refine ⟨4458046333901395177700687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2972030889267596785133791 4458046333901395177700687)
        ·
          refine ⟨6687069500852092766551031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4458046333901395177700687 6687069500852092766551031)
          ·
            refine ⟨10030604251278139149826547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6687069500852092766551031 10030604251278139149826547)
            ·
              refine ⟨15045906376917208724739821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10030604251278139149826547 15045906376917208724739821)
              ·
                refine ⟨5642214891343953271777433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15045906376917208724739821 5642214891343953271777433)
                ·
                  refine ⟨4231661168507964953833075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5642214891343953271777433 4231661168507964953833075)
                  ·
                    refine ⟨6347491752761947430749613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4231661168507964953833075 6347491752761947430749613)
                    ·
                      refine ⟨2380309407285730286531105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6347491752761947430749613 2380309407285730286531105)
                      ·
                        rfl

theorem cell23_4635636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4635636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635636 prefixEnd_4635636 := by exact prefixLift 4635636
  have htrace : WordTrace (prefixWord ++ tailWord_4635636) baseStart_4635636 baseEnd_4635636 := by
    simpa [prefixWord, tailWord_4635636, baseEnd_4635636] using wordTrace_append hprefix tailTrace_4635636
  have hstable : (prefixWord ++ tailWord_4635636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635636).length < 2 ^ (prefixWord ++ tailWord_4635636).sum := by decide
  have hdescent : baseEnd_4635636 < baseStart_4635636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635671 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 5]
def baseStart_4635671 : Nat := 118140960795 + 4635671 * 2 ^ 59
def prefixEnd_4635671 : Nat := 4983230072969 + 3 ^ 40 * 4635671 * 2
def baseEnd_4635671 : Nat := 2380327379108637649593443

theorem tailTrace_4635671 : CollatzResearch.WordTrace tailWord_4635671 prefixEnd_4635671 2380327379108637649593443 := by
  unfold tailWord_4635671
  simp only [CollatzResearch.WordTrace]
  refine ⟨169076811588763151420690867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112717874392508767613793911 169076811588763151420690867)
  ·
    refine ⟨253615217383144727131036301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169076811588763151420690867 253615217383144727131036301)
    ·
      refine ⟨95105706518679272674138613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253615217383144727131036301 95105706518679272674138613)
      ·
        refine ⟨8916159986126181813200495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95105706518679272674138613 8916159986126181813200495)
        ·
          refine ⟨13374239979189272719800743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8916159986126181813200495 13374239979189272719800743)
          ·
            refine ⟨20061359968783909079701115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13374239979189272719800743 20061359968783909079701115)
            ·
              refine ⟨30092039953175863619551673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20061359968783909079701115 30092039953175863619551673)
              ·
                refine ⟨22569029964881897714663755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30092039953175863619551673 22569029964881897714663755)
                ·
                  refine ⟨33853544947322846571995633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22569029964881897714663755 33853544947322846571995633)
                  ·
                    refine ⟨25390158710492134928996725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33853544947322846571995633 25390158710492134928996725)
                    ·
                      refine ⟨2380327379108637649593443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25390158710492134928996725 2380327379108637649593443)
                      ·
                        rfl

theorem cell23_4635671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_4635671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635671 prefixEnd_4635671 := by exact prefixLift 4635671
  have htrace : WordTrace (prefixWord ++ tailWord_4635671) baseStart_4635671 baseEnd_4635671 := by
    simpa [prefixWord, tailWord_4635671, baseEnd_4635671] using wordTrace_append hprefix tailTrace_4635671
  have hstable : (prefixWord ++ tailWord_4635671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635671).length < 2 ^ (prefixWord ++ tailWord_4635671).sum := by decide
  have hdescent : baseEnd_4635671 < baseStart_4635671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635691 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 3, 4]
def baseStart_4635691 : Nat := 118140960795 + 4635691 * 2 ^ 59
def prefixEnd_4635691 : Nat := 4983230072969 + 3 ^ 40 * 4635691 * 2
def baseEnd_4635691 : Nat := 793445882907242523781117

theorem tailTrace_4635691 : CollatzResearch.WordTrace tailWord_4635691 prefixEnd_4635691 793445882907242523781117 := by
  unfold tailWord_4635691
  simp only [CollatzResearch.WordTrace]
  refine ⟨169077541048690694836418927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112718360699127129890945951 169077541048690694836418927)
  ·
    refine ⟨253616311573036042254628391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169077541048690694836418927 253616311573036042254628391)
    ·
      refine ⟨380424467359554063381942587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253616311573036042254628391 380424467359554063381942587)
      ·
        refine ⟨570636701039331095072913881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380424467359554063381942587 570636701039331095072913881)
        ·
          refine ⟨427977525779498321304685411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 570636701039331095072913881 427977525779498321304685411)
          ·
            refine ⟨641966288669247481957028117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 427977525779498321304685411 641966288669247481957028117)
            ·
              refine ⟨30092169781370975716735693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 641966288669247481957028117 30092169781370975716735693)
              ·
                refine ⟨11284563668014115893775885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30092169781370975716735693 11284563668014115893775885)
                ·
                  refine ⟨4231711375505293460165957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11284563668014115893775885 4231711375505293460165957)
                  ·
                    refine ⟨793445882907242523781117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4231711375505293460165957 793445882907242523781117)
                    ·
                      rfl

theorem cell23_4635691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 3, 4].length) (baseStart_4635691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635691 prefixEnd_4635691 := by exact prefixLift 4635691
  have htrace : WordTrace (prefixWord ++ tailWord_4635691) baseStart_4635691 baseEnd_4635691 := by
    simpa [prefixWord, tailWord_4635691, baseEnd_4635691] using wordTrace_append hprefix tailTrace_4635691
  have hstable : (prefixWord ++ tailWord_4635691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635691).length < 2 ^ (prefixWord ++ tailWord_4635691).sum := by decide
  have hdescent : baseEnd_4635691 < baseStart_4635691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635698 : List Nat := [3, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2]
def baseStart_4635698 : Nat := 118140960795 + 4635698 * 2 ^ 59
def prefixEnd_4635698 : Nat := 4983230072969 + 3 ^ 40 * 4635698 * 2
def baseEnd_4635698 : Nat := 2380341243086309043955819

theorem tailTrace_4635698 : CollatzResearch.WordTrace tailWord_4635698 prefixEnd_4635698 2380341243086309043955819 := by
  unfold tailWord_4635698
  simp only [CollatzResearch.WordTrace]
  refine ⟨42269449089916333757980937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112718530906443556687949165 42269449089916333757980937)
  ·
    refine ⟨31702086817437250318485703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42269449089916333757980937 31702086817437250318485703)
    ·
      refine ⟨47553130226155875477728555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31702086817437250318485703 47553130226155875477728555)
      ·
        refine ⟨71329695339233813216592833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47553130226155875477728555 71329695339233813216592833)
        ·
          refine ⟨53497271504425359912444625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71329695339233813216592833 53497271504425359912444625)
          ·
            refine ⟨40122953628319019934333469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53497271504425359912444625 40122953628319019934333469)
            ·
              refine ⟨15046107610619632475375051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 40122953628319019934333469 15046107610619632475375051)
              ·
                refine ⟨22569161415929448713062577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15046107610619632475375051 22569161415929448713062577)
                ·
                  refine ⟨16926871061947086534796933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22569161415929448713062577 16926871061947086534796933)
                  ·
                    refine ⟨3173788324115078725274425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16926871061947086534796933 3173788324115078725274425)
                    ·
                      refine ⟨2380341243086309043955819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173788324115078725274425 2380341243086309043955819)
                      ·
                        rfl

theorem cell23_4635698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2].length) (baseStart_4635698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635698 prefixEnd_4635698 := by exact prefixLift 4635698
  have htrace : WordTrace (prefixWord ++ tailWord_4635698) baseStart_4635698 baseEnd_4635698 := by
    simpa [prefixWord, tailWord_4635698, baseEnd_4635698] using wordTrace_append hprefix tailTrace_4635698
  have hstable : (prefixWord ++ tailWord_4635698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635698).length < 2 ^ (prefixWord ++ tailWord_4635698).sum := by decide
  have hdescent : baseEnd_4635698 < baseStart_4635698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635701 : List Nat := [1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 3]
def baseStart_4635701 : Nat := 118140960795 + 4635701 * 2 ^ 59
def prefixEnd_4635701 : Nat := 4983230072969 + 3 ^ 40 * 4635701 * 2
def baseEnd_4635701 : Nat := 2380342783528272532218305

theorem tailTrace_4635701 : CollatzResearch.WordTrace tailWord_4635701 prefixEnd_4635701 2380342783528272532218305 := by
  unfold tailWord_4635701
  simp only [CollatzResearch.WordTrace]
  refine ⟨169077905778654466544282957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112718603852436311029521971 169077905778654466544282957)
  ·
    refine ⟨63404214666995424954106109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169077905778654466544282957 63404214666995424954106109)
    ·
      refine ⟨23776580500123284357789791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63404214666995424954106109 23776580500123284357789791)
      ·
        refine ⟨35664870750184926536684687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23776580500123284357789791 35664870750184926536684687)
        ·
          refine ⟨53497306125277389805027031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35664870750184926536684687 53497306125277389805027031)
          ·
            refine ⟨80245959187916084707540547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53497306125277389805027031 80245959187916084707540547)
            ·
              refine ⟨120368938781874127061310821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80245959187916084707540547 120368938781874127061310821)
              ·
                refine ⟨22569176021601398823995779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 120368938781874127061310821 22569176021601398823995779)
                ·
                  refine ⟨33853764032402098235993669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22569176021601398823995779 33853764032402098235993669)
                  ·
                    refine ⟨6347580756075393419248813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33853764032402098235993669 6347580756075393419248813)
                    ·
                      refine ⟨2380342783528272532218305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6347580756075393419248813 2380342783528272532218305)
                      ·
                        rfl

theorem cell23_4635701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 4, 1, 4, 3].length) (baseStart_4635701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635701 prefixEnd_4635701 := by exact prefixLift 4635701
  have htrace : WordTrace (prefixWord ++ tailWord_4635701) baseStart_4635701 baseEnd_4635701 := by
    simpa [prefixWord, tailWord_4635701, baseEnd_4635701] using wordTrace_append hprefix tailTrace_4635701
  have hstable : (prefixWord ++ tailWord_4635701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635701).length < 2 ^ (prefixWord ++ tailWord_4635701).sum := by decide
  have hdescent : baseEnd_4635701 < baseStart_4635701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635708 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 3, 4]
def baseStart_4635708 : Nat := 118140960795 + 4635708 * 2 ^ 59
def prefixEnd_4635708 : Nat := 4983230072969 + 3 ^ 40 * 4635708 * 2
def baseEnd_4635708 : Nat := 793448792630951334943591

theorem tailTrace_4635708 : CollatzResearch.WordTrace tailWord_4635708 prefixEnd_4635708 793448792630951334943591 := by
  unfold tailWord_4635708
  simp only [CollatzResearch.WordTrace]
  refine ⟨84539080544814553369893889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112718774059752737826525185 84539080544814553369893889)
  ·
    refine ⟨63404310408610915027420417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84539080544814553369893889 63404310408610915027420417)
    ·
      refine ⟨47553232806458186270565313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63404310408610915027420417 47553232806458186270565313)
      ·
        refine ⟨35664924604843639702923985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47553232806458186270565313 35664924604843639702923985)
        ·
          refine ⟨26748693453632729777192989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35664924604843639702923985 26748693453632729777192989)
          ·
            refine ⟨10030760045112273666447371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26748693453632729777192989 10030760045112273666447371)
            ·
              refine ⟨15046140067668410499671057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10030760045112273666447371 15046140067668410499671057)
              ·
                refine ⟨11284605050751307874753293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15046140067668410499671057 11284605050751307874753293)
                ·
                  refine ⟨4231726894031740453032485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11284605050751307874753293 4231726894031740453032485)
                  ·
                    refine ⟨793448792630951334943591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4231726894031740453032485 793448792630951334943591)
                    ·
                      rfl

theorem cell23_4635708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 3, 4].length) (baseStart_4635708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635708 prefixEnd_4635708 := by exact prefixLift 4635708
  have htrace : WordTrace (prefixWord ++ tailWord_4635708) baseStart_4635708 baseEnd_4635708 := by
    simpa [prefixWord, tailWord_4635708, baseEnd_4635708] using wordTrace_append hprefix tailTrace_4635708
  have hstable : (prefixWord ++ tailWord_4635708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635708).length < 2 ^ (prefixWord ++ tailWord_4635708).sum := by decide
  have hdescent : baseEnd_4635708 < baseStart_4635708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635742 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 3, 4]
def baseStart_4635742 : Nat := 118140960795 + 4635742 * 2 ^ 59
def prefixEnd_4635742 : Nat := 4983230072969 + 3 ^ 40 * 4635742 * 2
def baseEnd_4635742 : Nat := 793454612078368957268539

theorem tailTrace_4635742 : CollatzResearch.WordTrace tailWord_4635742 prefixEnd_4635742 793454612078368957268539 := by
  unfold tailWord_4635742
  simp only [CollatzResearch.WordTrace]
  refine ⟨21134925146438241318315685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112719600781003953697683653 21134925146438241318315685)
  ·
    refine ⟨3962798464957170247184191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21134925146438241318315685 3962798464957170247184191)
    ·
      refine ⟨5944197697435755370776287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3962798464957170247184191 5944197697435755370776287)
      ·
        refine ⟨8916296546153633056164431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5944197697435755370776287 8916296546153633056164431)
        ·
          refine ⟨13374444819230449584246647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8916296546153633056164431 13374444819230449584246647)
          ·
            refine ⟨20061667228845674376369971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13374444819230449584246647 20061667228845674376369971)
            ·
              refine ⟨30092500843268511564554957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20061667228845674376369971 30092500843268511564554957)
              ·
                refine ⟨11284687816225691836708109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30092500843268511564554957 11284687816225691836708109)
                ·
                  refine ⟨4231757931084634438765541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11284687816225691836708109 4231757931084634438765541)
                  ·
                    refine ⟨793454612078368957268539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4231757931084634438765541 793454612078368957268539)
                    ·
                      rfl

theorem cell23_4635742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_4635742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635742 prefixEnd_4635742 := by exact prefixLift 4635742
  have htrace : WordTrace (prefixWord ++ tailWord_4635742) baseStart_4635742 baseEnd_4635742 := by
    simpa [prefixWord, tailWord_4635742, baseEnd_4635742] using wordTrace_append hprefix tailTrace_4635742
  have hstable : (prefixWord ++ tailWord_4635742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635742).length < 2 ^ (prefixWord ++ tailWord_4635742).sum := by decide
  have hdescent : baseEnd_4635742 < baseStart_4635742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635771 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 4]
def baseStart_4635771 : Nat := 118140960795 + 4635771 * 2 ^ 59
def prefixEnd_4635771 : Nat := 4983230072969 + 3 ^ 40 * 4635771 * 2
def baseEnd_4635771 : Nat := 2380378727174087258342983

theorem tailTrace_4635771 : CollatzResearch.WordTrace tailWord_4635771 prefixEnd_4635771 2380378727174087258342983 := by
  unfold tailWord_4635771
  simp only [CollatzResearch.WordTrace]
  refine ⟨169080458888400868499331167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112720305925600578999554111 169080458888400868499331167)
  ·
    refine ⟨253620688332601302748996751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169080458888400868499331167 253620688332601302748996751)
    ·
      refine ⟨380431032498901954123495127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253620688332601302748996751 380431032498901954123495127)
      ·
        refine ⟨570646548748352931185242691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380431032498901954123495127 570646548748352931185242691)
        ·
          refine ⟨855969823122529396777864037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 570646548748352931185242691 855969823122529396777864037)
          ·
            refine ⟨160494341835474261895849507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 855969823122529396777864037 160494341835474261895849507)
            ·
              refine ⟨240741512753211392843774261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160494341835474261895849507 240741512753211392843774261)
              ·
                refine ⟨22569516820613568079103837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 240741512753211392843774261 22569516820613568079103837)
                ·
                  refine ⟨8463568807730088029663939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22569516820613568079103837 8463568807730088029663939)
                  ·
                    refine ⟨12695353211595132044495909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8463568807730088029663939 12695353211595132044495909)
                    ·
                      refine ⟨2380378727174087258342983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12695353211595132044495909 2380378727174087258342983)
                      ·
                        rfl

theorem cell23_4635771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 1, 4].length) (baseStart_4635771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635771 prefixEnd_4635771 := by exact prefixLift 4635771
  have htrace : WordTrace (prefixWord ++ tailWord_4635771) baseStart_4635771 baseEnd_4635771 := by
    simpa [prefixWord, tailWord_4635771, baseEnd_4635771] using wordTrace_append hprefix tailTrace_4635771
  have hstable : (prefixWord ++ tailWord_4635771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635771).length < 2 ^ (prefixWord ++ tailWord_4635771).sum := by decide
  have hdescent : baseEnd_4635771 < baseStart_4635771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635799 : List Nat := [1, 1, 3, 3, 3, 2, 3, 2, 1, 1, 3]
def baseStart_4635799 : Nat := 118140960795 + 4635799 * 2 ^ 59
def prefixEnd_4635799 : Nat := 4983230072969 + 3 ^ 40 * 4635799 * 2
def baseEnd_4635799 : Nat := 2380393104632413148792855

theorem tailTrace_4635799 : CollatzResearch.WordTrace tailWord_4635799 prefixEnd_4635799 2380393104632413148792855 := by
  unfold tailWord_4635799
  simp only [CollatzResearch.WordTrace]
  refine ⟨169081480132299429281350451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112720986754866286187566967 169081480132299429281350451)
  ·
    refine ⟨253622220198449143922025677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169081480132299429281350451 253622220198449143922025677)
    ·
      refine ⟨95108332574418428970759629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253622220198449143922025677 95108332574418428970759629)
      ·
        refine ⟨35665624715406910864034861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95108332574418428970759629 35665624715406910864034861)
        ·
          refine ⟨13374609268277591574013073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35665624715406910864034861 13374609268277591574013073)
          ·
            refine ⟨10030956951208193680509805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13374609268277591574013073 10030956951208193680509805)
            ·
              refine ⟨3761608856703072630191177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10030956951208193680509805 3761608856703072630191177)
              ·
                refine ⟨2821206642527304472643383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3761608856703072630191177 2821206642527304472643383)
                ·
                  refine ⟨4231809963790956708965075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2821206642527304472643383 4231809963790956708965075)
                  ·
                    refine ⟨6347714945686435063447613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4231809963790956708965075 6347714945686435063447613)
                    ·
                      refine ⟨2380393104632413148792855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6347714945686435063447613 2380393104632413148792855)
                      ·
                        rfl

theorem cell23_4635799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_4635799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635799 prefixEnd_4635799 := by exact prefixLift 4635799
  have htrace : WordTrace (prefixWord ++ tailWord_4635799) baseStart_4635799 baseEnd_4635799 := by
    simpa [prefixWord, tailWord_4635799, baseEnd_4635799] using wordTrace_append hprefix tailTrace_4635799
  have hstable : (prefixWord ++ tailWord_4635799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635799).length < 2 ^ (prefixWord ++ tailWord_4635799).sum := by decide
  have hdescent : baseEnd_4635799 < baseStart_4635799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635808 : List Nat := [2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 3]
def baseStart_4635808 : Nat := 118140960795 + 4635808 * 2 ^ 59
def prefixEnd_4635808 : Nat := 4983230072969 + 3 ^ 40 * 4635808 * 2
def baseEnd_4635808 : Nat := 2380397725958303613580313

theorem tailTrace_4635808 : CollatzResearch.WordTrace tailWord_4635808 prefixEnd_4635808 2380397725958303613580313 := by
  unfold tailWord_4635808
  simp only [CollatzResearch.WordTrace]
  refine ⟨84540904194633411909214039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112721205592844549212285385 84540904194633411909214039)
  ·
    refine ⟨126811356291950117863821059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84540904194633411909214039 126811356291950117863821059)
    ·
      refine ⟨190217034437925176795731589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126811356291950117863821059 190217034437925176795731589)
      ·
        refine ⟨35665693957110970649199673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190217034437925176795731589 35665693957110970649199673)
        ·
          refine ⟨26749270467833227986899755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35665693957110970649199673 26749270467833227986899755)
          ·
            refine ⟨40123905701749841980349633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26749270467833227986899755 40123905701749841980349633)
            ·
              refine ⟨30092929276312381485262225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40123905701749841980349633 30092929276312381485262225)
              ·
                refine ⟨22569696957234286113946669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30092929276312381485262225 22569696957234286113946669)
                ·
                  refine ⟨8463636358962857292730001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22569696957234286113946669 8463636358962857292730001)
                  ·
                    refine ⟨6347727269222142969547501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8463636358962857292730001 6347727269222142969547501)
                    ·
                      refine ⟨2380397725958303613580313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6347727269222142969547501 2380397725958303613580313)
                      ·
                        rfl

theorem cell23_4635808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 3].length) (baseStart_4635808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635808 prefixEnd_4635808 := by exact prefixLift 4635808
  have htrace : WordTrace (prefixWord ++ tailWord_4635808) baseStart_4635808 baseEnd_4635808 := by
    simpa [prefixWord, tailWord_4635808, baseEnd_4635808] using wordTrace_append hprefix tailTrace_4635808
  have hstable : (prefixWord ++ tailWord_4635808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635808).length < 2 ^ (prefixWord ++ tailWord_4635808).sum := by decide
  have hdescent : baseEnd_4635808 < baseStart_4635808 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635825 : List Nat := [1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 3]
def baseStart_4635825 : Nat := 118140960795 + 4635825 * 2 ^ 59
def prefixEnd_4635825 : Nat := 4983230072969 + 3 ^ 40 * 4635825 * 2
def baseEnd_4635825 : Nat := 2380406455129430047067735

theorem tailTrace_4635825 : CollatzResearch.WordTrace tailWord_4635825 prefixEnd_4635825 2380406455129430047067735 := by
  unfold tailWord_4635825
  simp only [CollatzResearch.WordTrace]
  refine ⟨169082428430205235721796929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112721618953470157147864619 169082428430205235721796929)
  ·
    refine ⟨126811821322653926791347697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169082428430205235721796929 126811821322653926791347697)
    ·
      refine ⟨95108865991990445093510773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126811821322653926791347697 95108865991990445093510773)
      ·
        refine ⟨8916456186749104227516635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95108865991990445093510773 8916456186749104227516635)
        ·
          refine ⟨13374684280123656341274953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8916456186749104227516635 13374684280123656341274953)
          ·
            refine ⟨10031013210092742255956215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13374684280123656341274953 10031013210092742255956215)
            ·
              refine ⟨15046519815139113383934323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10031013210092742255956215 15046519815139113383934323)
              ·
                refine ⟨22569779722708670075901485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15046519815139113383934323 22569779722708670075901485)
                ·
                  refine ⟨8463667396015751278463057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22569779722708670075901485 8463667396015751278463057)
                  ·
                    refine ⟨6347750547011813458847293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8463667396015751278463057 6347750547011813458847293)
                    ·
                      refine ⟨2380406455129430047067735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6347750547011813458847293 2380406455129430047067735)
                      ·
                        rfl

theorem cell23_4635825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 1, 3, 2, 3].length) (baseStart_4635825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635825 prefixEnd_4635825 := by exact prefixLift 4635825
  have htrace : WordTrace (prefixWord ++ tailWord_4635825) baseStart_4635825 baseEnd_4635825 := by
    simpa [prefixWord, tailWord_4635825, baseEnd_4635825] using wordTrace_append hprefix tailTrace_4635825
  have hstable : (prefixWord ++ tailWord_4635825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635825).length < 2 ^ (prefixWord ++ tailWord_4635825).sum := by decide
  have hdescent : baseEnd_4635825 < baseStart_4635825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635862 : List Nat := [5, 2, 1, 2, 2, 2, 1, 8]
def baseStart_4635862 : Nat := 118140960795 + 4635862 * 2 ^ 59
def prefixEnd_4635862 : Nat := 4983230072969 + 3 ^ 40 * 4635862 * 2
def baseEnd_4635862 : Nat := 88163905700505422307595

theorem tailTrace_4635862 : CollatzResearch.WordTrace tailWord_4635862 prefixEnd_4635862 88163905700505422307595 := by
  unfold tailWord_4635862
  simp only [CollatzResearch.WordTrace]
  refine ⟨10567736120691949440055865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 112722518620714127360595893 10567736120691949440055865)
  ·
    refine ⟨7925802090518962080041899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10567736120691949440055865 7925802090518962080041899)
    ·
      refine ⟨11888703135778443120062849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7925802090518962080041899 11888703135778443120062849)
      ·
        refine ⟨8916527351833832340047137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11888703135778443120062849 8916527351833832340047137)
        ·
          refine ⟨6687395513875374255035353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8916527351833832340047137 6687395513875374255035353)
          ·
            refine ⟨5015546635406530691276515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6687395513875374255035353 5015546635406530691276515)
            ·
              refine ⟨7523319953109796036914773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015546635406530691276515 7523319953109796036914773)
              ·
                refine ⟨88163905700505422307595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7523319953109796036914773 88163905700505422307595)
                ·
                  rfl

theorem cell23_4635862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_4635862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635862 prefixEnd_4635862 := by exact prefixLift 4635862
  have htrace : WordTrace (prefixWord ++ tailWord_4635862) baseStart_4635862 baseEnd_4635862 := by
    simpa [prefixWord, tailWord_4635862, baseEnd_4635862] using wordTrace_append hprefix tailTrace_4635862
  have hstable : (prefixWord ++ tailWord_4635862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635862).length < 2 ^ (prefixWord ++ tailWord_4635862).sum := by decide
  have hdescent : baseEnd_4635862 < baseStart_4635862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635871 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 1, 8]
def baseStart_4635871 : Nat := 118140960795 + 4635871 * 2 ^ 59
def prefixEnd_4635871 : Nat := 4983230072969 + 3 ^ 40 * 4635871 * 2
def baseEnd_4635871 : Nat := 793476691746512289030841

theorem tailTrace_4635871 : CollatzResearch.WordTrace tailWord_4635871 prefixEnd_4635871 793476691746512289030841 := by
  unfold tailWord_4635871
  simp only [CollatzResearch.WordTrace]
  refine ⟨169084106188038585577971467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112722737458692390385314311 169084106188038585577971467)
  ·
    refine ⟨253626159282057878366957201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169084106188038585577971467 253626159282057878366957201)
    ·
      refine ⟨190219619461543408775217901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253626159282057878366957201 190219619461543408775217901)
      ·
        refine ⟨71332357298078778290706713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 190219619461543408775217901 71332357298078778290706713)
        ·
          refine ⟨53499267973559083718030035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 71332357298078778290706713 53499267973559083718030035)
          ·
            refine ⟨80248901960338625577045053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53499267973559083718030035 80248901960338625577045053)
            ·
              refine ⟨30093338235126984591391895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80248901960338625577045053 30093338235126984591391895)
              ·
                refine ⟨45140007352690476887087843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30093338235126984591391895 45140007352690476887087843)
                ·
                  refine ⟨67710011029035715330631765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45140007352690476887087843 67710011029035715330631765)
                  ·
                    refine ⟨793476691746512289030841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67710011029035715330631765 793476691746512289030841)
                    ·
                      rfl

theorem cell23_4635871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 8].length) (baseStart_4635871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635871 prefixEnd_4635871 := by exact prefixLift 4635871
  have htrace : WordTrace (prefixWord ++ tailWord_4635871) baseStart_4635871 baseEnd_4635871 := by
    simpa [prefixWord, tailWord_4635871, baseEnd_4635871] using wordTrace_append hprefix tailTrace_4635871
  have hstable : (prefixWord ++ tailWord_4635871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635871).length < 2 ^ (prefixWord ++ tailWord_4635871).sum := by decide
  have hdescent : baseEnd_4635871 < baseStart_4635871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635895 : List Nat := [1, 1, 3, 1, 1, 1, 2, 3, 6, 2, 2]
def baseStart_4635895 : Nat := 118140960795 + 4635895 * 2 ^ 59
def prefixEnd_4635895 : Nat := 4983230072969 + 3 ^ 40 * 4635895 * 2
def baseEnd_4635895 : Nat := 2380442398775244773192413

theorem tailTrace_4635895 : CollatzResearch.WordTrace tailWord_4635895 prefixEnd_4635895 2380442398775244773192413 := by
  unfold tailWord_4635895
  simp only [CollatzResearch.WordTrace]
  refine ⟨169084981539951637676845139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112723321026634425117896759 169084981539951637676845139)
  ·
    refine ⟨253627472309927456515267709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169084981539951637676845139 253627472309927456515267709)
    ·
      refine ⟨95110302116222796193225391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253627472309927456515267709 95110302116222796193225391)
      ·
        refine ⟨142665453174334194289838087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95110302116222796193225391 142665453174334194289838087)
        ·
          refine ⟨213998179761501291434757131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142665453174334194289838087 213998179761501291434757131)
          ·
            refine ⟨320997269642251937152135697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 213998179761501291434757131 320997269642251937152135697)
            ·
              refine ⟨240747952231688952864101773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 320997269642251937152135697 240747952231688952864101773)
              ·
                refine ⟨90280482086883357324038165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240747952231688952864101773 90280482086883357324038165)
                ·
                  refine ⟨4231897597822657374564289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 90280482086883357324038165 4231897597822657374564289)
                  ·
                    refine ⟨3173923198366993030923217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4231897597822657374564289 3173923198366993030923217)
                    ·
                      refine ⟨2380442398775244773192413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173923198366993030923217 2380442398775244773192413)
                      ·
                        rfl

theorem cell23_4635895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_4635895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635895 prefixEnd_4635895 := by exact prefixLift 4635895
  have htrace : WordTrace (prefixWord ++ tailWord_4635895) baseStart_4635895 baseEnd_4635895 := by
    simpa [prefixWord, tailWord_4635895, baseEnd_4635895] using wordTrace_append hprefix tailTrace_4635895
  have hstable : (prefixWord ++ tailWord_4635895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635895).length < 2 ^ (prefixWord ++ tailWord_4635895).sum := by decide
  have hdescent : baseEnd_4635895 < baseStart_4635895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635906 : List Nat := [3, 4, 1, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_4635906 : Nat := 118140960795 + 4635906 * 2 ^ 59
def prefixEnd_4635906 : Nat := 4983230072969 + 3 ^ 40 * 4635906 * 2
def baseEnd_4635906 : Nat := 2380448047062444230154863

theorem tailTrace_4635906 : CollatzResearch.WordTrace tailWord_4635906 prefixEnd_4635906 2380448047062444230154863 := by
  unfold tailWord_4635906
  simp only [CollatzResearch.WordTrace]
  refine ⟨42271345685727946638873893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112723588495274524370330381 42271345685727946638873893)
  ·
    refine ⟨7925877316073989994788855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 42271345685727946638873893 7925877316073989994788855)
    ·
      refine ⟨11888815974110984992183283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7925877316073989994788855 11888815974110984992183283)
      ·
        refine ⟨17833223961166477488274925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11888815974110984992183283 17833223961166477488274925)
        ·
          refine ⟨6687458985437429058103097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17833223961166477488274925 6687458985437429058103097)
          ·
            refine ⟨5015594239078071793577323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6687458985437429058103097 5015594239078071793577323)
            ·
              refine ⟨7523391358617107690365985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015594239078071793577323 7523391358617107690365985)
              ·
                refine ⟨5642543518962830767774489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7523391358617107690365985 5642543518962830767774489)
                ·
                  refine ⟨4231907639222123075830867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5642543518962830767774489 4231907639222123075830867)
                  ·
                    refine ⟨6347861458833184613746301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4231907639222123075830867 6347861458833184613746301)
                    ·
                      refine ⟨2380448047062444230154863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6347861458833184613746301 2380448047062444230154863)
                      ·
                        rfl

theorem cell23_4635906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_4635906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635906 prefixEnd_4635906 := by exact prefixLift 4635906
  have htrace : WordTrace (prefixWord ++ tailWord_4635906) baseStart_4635906 baseEnd_4635906 := by
    simpa [prefixWord, tailWord_4635906, baseEnd_4635906] using wordTrace_append hprefix tailTrace_4635906
  have hstable : (prefixWord ++ tailWord_4635906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635906).length < 2 ^ (prefixWord ++ tailWord_4635906).sum := by decide
  have hdescent : baseEnd_4635906 < baseStart_4635906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635918 : List Nat := [4, 1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_4635918 : Nat := 118140960795 + 4635918 * 2 ^ 59
def prefixEnd_4635918 : Nat := 4983230072969 + 3 ^ 40 * 4635918 * 2
def baseEnd_4635918 : Nat := 264494912092255353689423

theorem tailTrace_4635918 : CollatzResearch.WordTrace tailWord_4635918 prefixEnd_4635918 264494912092255353689423 := by
  unfold tailWord_4635918
  simp only [CollatzResearch.WordTrace]
  refine ⟨21135727552358539075616551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112723880279245541736621605 21135727552358539075616551)
  ·
    refine ⟨31703591328537808613424827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21135727552358539075616551 31703591328537808613424827)
    ·
      refine ⟨47555386992806712920137241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31703591328537808613424827 47555386992806712920137241)
      ·
        refine ⟨35666540244605034690102931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47555386992806712920137241 35666540244605034690102931)
        ·
          refine ⟨53499810366907552035154397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35666540244605034690102931 53499810366907552035154397)
          ·
            refine ⟨20062428887590332013182899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53499810366907552035154397 20062428887590332013182899)
            ·
              refine ⟨30093643331385498019774349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20062428887590332013182899 30093643331385498019774349)
              ·
                refine ⟨11285116249269561757415381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30093643331385498019774349 11285116249269561757415381)
                ·
                  refine ⟨264494912092255353689423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11285116249269561757415381 264494912092255353689423)
                  ·
                    rfl

theorem cell23_4635918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_4635918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635918 prefixEnd_4635918 := by exact prefixLift 4635918
  have htrace : WordTrace (prefixWord ++ tailWord_4635918) baseStart_4635918 baseEnd_4635918 := by
    simpa [prefixWord, tailWord_4635918, baseEnd_4635918] using wordTrace_append hprefix tailTrace_4635918
  have hstable : (prefixWord ++ tailWord_4635918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635918).length < 2 ^ (prefixWord ++ tailWord_4635918).sum := by decide
  have hdescent : baseEnd_4635918 < baseStart_4635918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635948 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 2, 5]
def baseStart_4635948 : Nat := 118140960795 + 4635948 * 2 ^ 59
def prefixEnd_4635948 : Nat := 4983230072969 + 3 ^ 40 * 4635948 * 2
def baseEnd_4635948 : Nat := 793489871083311021943223

theorem tailTrace_4635948 : CollatzResearch.WordTrace tailWord_4635948 prefixEnd_4635948 793489871083311021943223 := by
  unfold tailWord_4635948
  simp only [CollatzResearch.WordTrace]
  refine ⟨84543457304379813864262249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112724609739173085152349665 84543457304379813864262249)
  ·
    refine ⟨63407592978284860398196687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84543457304379813864262249 63407592978284860398196687)
    ·
      refine ⟨95111389467427290597295031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63407592978284860398196687 95111389467427290597295031)
      ·
        refine ⟨142667084201140935895942547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95111389467427290597295031 142667084201140935895942547)
        ·
          refine ⟨214000626301711403843913821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142667084201140935895942547 214000626301711403843913821)
          ·
            refine ⟨80250234863141776441467683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 214000626301711403843913821 80250234863141776441467683)
            ·
              refine ⟨120375352294712664662201525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80250234863141776441467683 120375352294712664662201525)
              ·
                refine ⟨11285189277629312312081393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 120375352294712664662201525 11285189277629312312081393)
                ·
                  refine ⟨8463891958221984234061045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11285189277629312312081393 8463891958221984234061045)
                  ·
                    refine ⟨793489871083311021943223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8463891958221984234061045 793489871083311021943223)
                    ·
                      rfl

theorem cell23_4635948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 5].length) (baseStart_4635948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635948 prefixEnd_4635948 := by exact prefixLift 4635948
  have htrace : WordTrace (prefixWord ++ tailWord_4635948) baseStart_4635948 baseEnd_4635948 := by
    simpa [prefixWord, tailWord_4635948, baseEnd_4635948] using wordTrace_append hprefix tailTrace_4635948
  have hstable : (prefixWord ++ tailWord_4635948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635948).length < 2 ^ (prefixWord ++ tailWord_4635948).sum := by decide
  have hdescent : baseEnd_4635948 < baseStart_4635948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635969 : List Nat := [1, 2, 5, 2, 1, 2, 3, 2, 5]
def baseStart_4635969 : Nat := 118140960795 + 4635969 * 2 ^ 59
def prefixEnd_4635969 : Nat := 4983230072969 + 3 ^ 40 * 4635969 * 2
def baseEnd_4635969 : Nat := 264497821815964164851897

theorem tailTrace_4635969 : CollatzResearch.WordTrace tailWord_4635969 prefixEnd_4635969 264497821815964164851897 := by
  unfold tailWord_4635969
  simp only [CollatzResearch.WordTrace]
  refine ⟨169087680541683548315038961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112725120361122365543359307 169087680541683548315038961)
  ·
    refine ⟨126815760406262661236279221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169087680541683548315038961 126815760406262661236279221)
    ·
      refine ⟨11888977538087124490901177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 126815760406262661236279221 11888977538087124490901177)
      ·
        refine ⟨8916733153565343368175883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11888977538087124490901177 8916733153565343368175883)
        ·
          refine ⟨13375099730348015052263825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8916733153565343368175883 13375099730348015052263825)
          ·
            refine ⟨10031324797761011289197869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13375099730348015052263825 10031324797761011289197869)
            ·
              refine ⟨3761746799160379233449201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10031324797761011289197869 3761746799160379233449201)
              ·
                refine ⟨2821310099370284425086901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3761746799160379233449201 2821310099370284425086901)
                ·
                  refine ⟨264497821815964164851897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2821310099370284425086901 264497821815964164851897)
                  ·
                    rfl

theorem cell23_4635969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2, 5].length) (baseStart_4635969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635969 prefixEnd_4635969 := by exact prefixLift 4635969
  have htrace : WordTrace (prefixWord ++ tailWord_4635969) baseStart_4635969 baseEnd_4635969 := by
    simpa [prefixWord, tailWord_4635969, baseEnd_4635969] using wordTrace_append hprefix tailTrace_4635969
  have hstable : (prefixWord ++ tailWord_4635969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635969).length < 2 ^ (prefixWord ++ tailWord_4635969).sum := by decide
  have hdescent : baseEnd_4635969 < baseStart_4635969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4635985 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 1, 6, 2]
def baseStart_4635985 : Nat := 118140960795 + 4635985 * 2 ^ 59
def prefixEnd_4635985 : Nat := 4983230072969 + 3 ^ 40 * 4635985 * 2
def baseEnd_4635985 : Nat := 2380488612034149421066999

theorem tailTrace_4635985 : CollatzResearch.WordTrace tailWord_4635985 prefixEnd_4635985 2380488612034149421066999 := by
  unfold tailWord_4635985
  simp only [CollatzResearch.WordTrace]
  refine ⟨169088264109625583047621409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112725509406417055365080939 169088264109625583047621409)
  ·
    refine ⟨126816198082219187285716057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169088264109625583047621409 126816198082219187285716057)
    ·
      refine ⟨95112148561664390464287043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126816198082219187285716057 95112148561664390464287043)
      ·
        refine ⟨142668222842496585696430565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95112148561664390464287043 142668222842496585696430565)
        ·
          refine ⟨26750291782968109818080731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142668222842496585696430565 26750291782968109818080731)
          ·
            refine ⟨40125437674452164727121097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26750291782968109818080731 40125437674452164727121097)
            ·
              refine ⟨30094078255839123545340823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40125437674452164727121097 30094078255839123545340823)
              ·
                refine ⟨45141117383758685318011235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30094078255839123545340823 45141117383758685318011235)
                ·
                  refine ⟨67711676075638027977016853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45141117383758685318011235 67711676075638027977016853)
                  ·
                    refine ⟨3173984816045532561422665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67711676075638027977016853 3173984816045532561422665)
                    ·
                      refine ⟨2380488612034149421066999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3173984816045532561422665 2380488612034149421066999)
                      ·
                        rfl

theorem cell23_4635985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 1, 6, 2].length) (baseStart_4635985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4635985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4635985 prefixEnd_4635985 := by exact prefixLift 4635985
  have htrace : WordTrace (prefixWord ++ tailWord_4635985) baseStart_4635985 baseEnd_4635985 := by
    simpa [prefixWord, tailWord_4635985, baseEnd_4635985] using wordTrace_append hprefix tailTrace_4635985
  have hstable : (prefixWord ++ tailWord_4635985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4635985).length < 2 ^ (prefixWord ++ tailWord_4635985).sum := by decide
  have hdescent : baseEnd_4635985 < baseStart_4635985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4635985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636002 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 2, 1, 4]
def baseStart_4636002 : Nat := 118140960795 + 4636002 * 2 ^ 59
def prefixEnd_4636002 : Nat := 4983230072969 + 3 ^ 40 * 4636002 * 2
def baseEnd_4636002 : Nat := 2380497341205275854554421

theorem tailTrace_4636002 : CollatzResearch.WordTrace tailWord_4636002 prefixEnd_4636002 2380497341205275854554421 := by
  unfold tailWord_4636002
  simp only [CollatzResearch.WordTrace]
  refine ⟨42272221037640998737747565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112725922767042663300660173 42272221037640998737747565)
  ·
    refine ⟨15852082889115374526655337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 42272221037640998737747565 15852082889115374526655337)
    ·
      refine ⟨11889062166836530894991503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15852082889115374526655337 11889062166836530894991503)
      ·
        refine ⟨17833593250254796342487255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11889062166836530894991503 17833593250254796342487255)
        ·
          refine ⟨26750389875382194513730883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17833593250254796342487255 26750389875382194513730883)
          ·
            refine ⟨40125584813073291770596325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26750389875382194513730883 40125584813073291770596325)
            ·
              refine ⟨7523547152451242206986811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40125584813073291770596325 7523547152451242206986811)
              ·
                refine ⟨11285320728676863310480217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7523547152451242206986811 11285320728676863310480217)
                ·
                  refine ⟨8463990546507647482860163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11285320728676863310480217 8463990546507647482860163)
                  ·
                    refine ⟨12695985819761471224290245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8463990546507647482860163 12695985819761471224290245)
                    ·
                      refine ⟨2380497341205275854554421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12695985819761471224290245 2380497341205275854554421)
                      ·
                        rfl

theorem cell23_4636002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_4636002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636002 prefixEnd_4636002 := by exact prefixLift 4636002
  have htrace : WordTrace (prefixWord ++ tailWord_4636002) baseStart_4636002 baseEnd_4636002 := by
    simpa [prefixWord, tailWord_4636002, baseEnd_4636002] using wordTrace_append hprefix tailTrace_4636002
  have hstable : (prefixWord ++ tailWord_4636002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636002).length < 2 ^ (prefixWord ++ tailWord_4636002).sum := by decide
  have hdescent : baseEnd_4636002 < baseStart_4636002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636028 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 1, 2, 6]
def baseStart_4636028 : Nat := 118140960795 + 4636028 * 2 ^ 59
def prefixEnd_4636028 : Nat := 4983230072969 + 3 ^ 40 * 4636028 * 2
def baseEnd_4636028 : Nat := 2380510691702292752829301

theorem tailTrace_4636028 : CollatzResearch.WordTrace tailWord_4636028 prefixEnd_4636028 2380510691702292752829301 := by
  unfold tailWord_4636028
  simp only [CollatzResearch.WordTrace]
  refine ⟨84544916224234900695718369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112726554965646534260957825 84544916224234900695718369)
  ·
    refine ⟨63408687168176175521788777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84544916224234900695718369 63408687168176175521788777)
    ·
      refine ⟨47556515376132131641341583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63408687168176175521788777 47556515376132131641341583)
      ·
        refine ⟨71334773064198197462012375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47556515376132131641341583 71334773064198197462012375)
        ·
          refine ⟨107002159596297296193018563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71334773064198197462012375 107002159596297296193018563)
          ·
            refine ⟨160503239394445944289527845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107002159596297296193018563 160503239394445944289527845)
            ·
              refine ⟨30094357386458614554286471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 160503239394445944289527845 30094357386458614554286471)
              ·
                refine ⟨45141536079687921831429707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30094357386458614554286471 45141536079687921831429707)
                ·
                  refine ⟨67712304119531882747144561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45141536079687921831429707 67712304119531882747144561)
                  ·
                    refine ⟨50784228089648912060358421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67712304119531882747144561 50784228089648912060358421)
                    ·
                      refine ⟨2380510691702292752829301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50784228089648912060358421 2380510691702292752829301)
                      ·
                        rfl

theorem cell23_4636028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_4636028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636028 prefixEnd_4636028 := by exact prefixLift 4636028
  have htrace : WordTrace (prefixWord ++ tailWord_4636028) baseStart_4636028 baseEnd_4636028 := by
    simpa [prefixWord, tailWord_4636028, baseEnd_4636028] using wordTrace_append hprefix tailTrace_4636028
  have hstable : (prefixWord ++ tailWord_4636028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636028).length < 2 ^ (prefixWord ++ tailWord_4636028).sum := by decide
  have hdescent : baseEnd_4636028 < baseStart_4636028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636055 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 1, 5]
def baseStart_4636055 : Nat := 118140960795 + 4636055 * 2 ^ 59
def prefixEnd_4636055 : Nat := 4983230072969 + 3 ^ 40 * 4636055 * 2
def baseEnd_4636055 : Nat := 793508185226654715730559

theorem tailTrace_4636055 : CollatzResearch.WordTrace tailWord_4636055 prefixEnd_4636055 793508185226654715730559 := by
  unfold tailWord_4636055
  simp only [CollatzResearch.WordTrace]
  refine ⟨169090817219371985002669619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112727211479581323335113079 169090817219371985002669619)
  ·
    refine ⟨253636225829057977504004429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169090817219371985002669619 253636225829057977504004429)
    ·
      refine ⟨95113584685896741564001661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 253636225829057977504004429 95113584685896741564001661)
      ·
        refine ⟨35667594257211278086500623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 95113584685896741564001661 35667594257211278086500623)
        ·
          refine ⟨53501391385816917129750935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35667594257211278086500623 53501391385816917129750935)
          ·
            refine ⟨80252087078725375694626403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53501391385816917129750935 80252087078725375694626403)
            ·
              refine ⟨120378130618088063541939605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80252087078725375694626403 120378130618088063541939605)
              ·
                refine ⟨5642724872722877978528419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 120378130618088063541939605 5642724872722877978528419)
                ·
                  refine ⟨8464087309084316967792629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5642724872722877978528419 8464087309084316967792629)
                  ·
                    refine ⟨793508185226654715730559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8464087309084316967792629 793508185226654715730559)
                    ·
                      rfl

theorem cell23_4636055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 5].length) (baseStart_4636055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636055 prefixEnd_4636055 := by exact prefixLift 4636055
  have htrace : WordTrace (prefixWord ++ tailWord_4636055) baseStart_4636055 baseEnd_4636055 := by
    simpa [prefixWord, tailWord_4636055, baseEnd_4636055] using wordTrace_append hprefix tailTrace_4636055
  have hstable : (prefixWord ++ tailWord_4636055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636055).length < 2 ^ (prefixWord ++ tailWord_4636055).sum := by decide
  have hdescent : baseEnd_4636055 < baseStart_4636055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636056 : List Nat := [2, 1, 2, 5, 3, 1, 1, 1, 2, 2, 3]
def baseStart_4636056 : Nat := 118140960795 + 4636056 * 2 ^ 59
def prefixEnd_4636056 : Nat := 4983230072969 + 3 ^ 40 * 4636056 * 2
def baseEnd_4636056 : Nat := 2380525069160618643279173

theorem tailTrace_4636056 : CollatzResearch.WordTrace tailWord_4636056 prefixEnd_4636056 2380525069160618643279173 := by
  unfold tailWord_4636056
  simp only [CollatzResearch.WordTrace]
  refine ⟨84545426846184181086728011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112727235794912241448970681 84545426846184181086728011)
  ·
    refine ⟨126818140269276271630092017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84545426846184181086728011 126818140269276271630092017)
    ·
      refine ⟨95113605201957203722569013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126818140269276271630092017 95113605201957203722569013)
      ·
        refine ⟨8916900487683487848990845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 95113605201957203722569013 8916900487683487848990845)
        ·
          refine ⟨3343837682881307943371567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8916900487683487848990845 3343837682881307943371567)
          ·
            refine ⟨5015756524321961915057351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3343837682881307943371567 5015756524321961915057351)
            ·
              refine ⟨7523634786482942872586027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5015756524321961915057351 7523634786482942872586027)
              ·
                refine ⟨11285452179724414308879041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7523634786482942872586027 11285452179724414308879041)
                ·
                  refine ⟨8464089134793310731659281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11285452179724414308879041 8464089134793310731659281)
                  ·
                    refine ⟨6348066851094983048744461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8464089134793310731659281 6348066851094983048744461)
                    ·
                      refine ⟨2380525069160618643279173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6348066851094983048744461 2380525069160618643279173)
                      ·
                        rfl

theorem cell23_4636056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_4636056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636056 prefixEnd_4636056 := by exact prefixLift 4636056
  have htrace : WordTrace (prefixWord ++ tailWord_4636056) baseStart_4636056 baseEnd_4636056 := by
    simpa [prefixWord, tailWord_4636056, baseEnd_4636056] using wordTrace_append hprefix tailTrace_4636056
  have hstable : (prefixWord ++ tailWord_4636056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636056).length < 2 ^ (prefixWord ++ tailWord_4636056).sum := by decide
  have hdescent : baseEnd_4636056 < baseStart_4636056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636095 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 3]
def baseStart_4636095 : Nat := 118140960795 + 4636095 * 2 ^ 59
def prefixEnd_4636095 : Nat := 4983230072969 + 3 ^ 40 * 4636095 * 2
def baseEnd_4636095 : Nat := 2380545094906143990691493

theorem tailTrace_4636095 : CollatzResearch.WordTrace tailWord_4636095 prefixEnd_4636095 2380545094906143990691493 := by
  unfold tailWord_4636095
  simp only [CollatzResearch.WordTrace]
  refine ⟨169092276139227071834125739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112728184092818047889417159 169092276139227071834125739)
  ·
    refine ⟨253638414208840607751188609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169092276139227071834125739 253638414208840607751188609)
    ·
      refine ⟨190228810656630455813391457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253638414208840607751188609 190228810656630455813391457)
      ·
        refine ⟨142671607992472841860043593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190228810656630455813391457 142671607992472841860043593)
        ·
          refine ⟨107003705994354631395032695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142671607992472841860043593 107003705994354631395032695)
          ·
            refine ⟨160505558991531947092549043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107003705994354631395032695 160505558991531947092549043)
            ·
              refine ⟨240758338487297920638823565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 160505558991531947092549043 240758338487297920638823565)
              ·
                refine ⟨90284376932736720239558837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 240758338487297920638823565 90284376932736720239558837)
                ·
                  refine ⟨8464160337444067522458641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90284376932736720239558837 8464160337444067522458641)
                  ·
                    refine ⟨6348120253083050641843981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8464160337444067522458641 6348120253083050641843981)
                    ·
                      refine ⟨2380545094906143990691493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6348120253083050641843981 2380545094906143990691493)
                      ·
                        rfl

theorem cell23_4636095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_4636095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636095 prefixEnd_4636095 := by exact prefixLift 4636095
  have htrace : WordTrace (prefixWord ++ tailWord_4636095) baseStart_4636095 baseEnd_4636095 := by
    simpa [prefixWord, tailWord_4636095, baseEnd_4636095] using wordTrace_append hprefix tailTrace_4636095
  have hstable : (prefixWord ++ tailWord_4636095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636095).length < 2 ^ (prefixWord ++ tailWord_4636095).sum := by decide
  have hdescent : baseEnd_4636095 < baseStart_4636095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636185 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 3]
def baseStart_4636185 : Nat := 118140960795 + 4636185 * 2 ^ 59
def prefixEnd_4636185 : Nat := 4983230072969 + 3 ^ 40 * 4636185 * 2
def baseEnd_4636185 : Nat := 2380591308165048638566079

theorem tailTrace_4636185 : CollatzResearch.WordTrace tailWord_4636185 prefixEnd_4636185 2380591308165048638566079 := by
  unfold tailWord_4636185
  simp only [CollatzResearch.WordTrace]
  refine ⟨169095558708901017204902009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112730372472600678136601339 169095558708901017204902009)
  ·
    refine ⟨126821669031675762903676507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169095558708901017204902009 126821669031675762903676507)
    ·
      refine ⟨190232503547513644355514761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126821669031675762903676507 190232503547513644355514761)
      ·
        refine ⟨142674377660635233266636071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 190232503547513644355514761 142674377660635233266636071)
        ·
          refine ⟨214011566490952849899954107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142674377660635233266636071 214011566490952849899954107)
          ·
            refine ⟨321017349736429274849931161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214011566490952849899954107 321017349736429274849931161)
            ·
              refine ⟨240763012302321956137448371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 321017349736429274849931161 240763012302321956137448371)
              ·
                refine ⟨361144518453482934206172557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 240763012302321956137448371 361144518453482934206172557)
                ·
                  refine ⟨135429194420056100327314709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 361144518453482934206172557 135429194420056100327314709)
                  ·
                    refine ⟨6348243488440129702842877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 135429194420056100327314709 6348243488440129702842877)
                    ·
                      refine ⟨2380591308165048638566079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6348243488440129702842877 2380591308165048638566079)
                      ·
                        rfl

theorem cell23_4636185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 6, 3].length) (baseStart_4636185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636185 prefixEnd_4636185 := by exact prefixLift 4636185
  have htrace : WordTrace (prefixWord ++ tailWord_4636185) baseStart_4636185 baseEnd_4636185 := by
    simpa [prefixWord, tailWord_4636185, baseEnd_4636185] using wordTrace_append hprefix tailTrace_4636185
  have hstable : (prefixWord ++ tailWord_4636185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636185).length < 2 ^ (prefixWord ++ tailWord_4636185).sum := by decide
  have hdescent : baseEnd_4636185 < baseStart_4636185 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636202 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_4636202 : Nat := 118140960795 + 4636202 * 2 ^ 59
def prefixEnd_4636202 : Nat := 4983230072969 + 3 ^ 40 * 4636202 * 2
def baseEnd_4636202 : Nat := 2380600037336175072053501

theorem tailTrace_4636202 : CollatzResearch.WordTrace tailWord_4636202 prefixEnd_4636202 2380600037336175072053501 := by
  unfold tailWord_4636202
  simp only [CollatzResearch.WordTrace]
  refine ⟨42274044687459857277067715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112730785833226286072180573 42274044687459857277067715)
  ·
    refine ⟨63411067031189785915601573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42274044687459857277067715 63411067031189785915601573)
    ·
      refine ⟨11889575068348084859175295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 63411067031189785915601573 11889575068348084859175295)
      ·
        refine ⟨17834362602522127288762943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11889575068348084859175295 17834362602522127288762943)
        ·
          refine ⟨26751543903783190933144415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17834362602522127288762943 26751543903783190933144415)
          ·
            refine ⟨40127315855674786399716623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26751543903783190933144415 40127315855674786399716623)
            ·
              refine ⟨60190973783512179599574935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40127315855674786399716623 60190973783512179599574935)
              ·
                refine ⟨90286460675268269399362403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 60190973783512179599574935 90286460675268269399362403)
                ·
                  refine ⟨135429691012902404099043605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 90286460675268269399362403 135429691012902404099043605)
                  ·
                    refine ⟨6348266766229800192142669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 135429691012902404099043605 6348266766229800192142669)
                    ·
                      refine ⟨2380600037336175072053501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6348266766229800192142669 2380600037336175072053501)
                      ·
                        rfl

theorem cell23_4636202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_4636202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636202 prefixEnd_4636202 := by exact prefixLift 4636202
  have htrace : WordTrace (prefixWord ++ tailWord_4636202) baseStart_4636202 baseEnd_4636202 := by
    simpa [prefixWord, tailWord_4636202, baseEnd_4636202] using wordTrace_append hprefix tailTrace_4636202
  have hstable : (prefixWord ++ tailWord_4636202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636202).length < 2 ^ (prefixWord ++ tailWord_4636202).sum := by decide
  have hdescent : baseEnd_4636202 < baseStart_4636202 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636216 : List Nat := [2, 1, 2, 1, 4, 2, 2, 3, 2, 2, 2]
def baseStart_4636216 : Nat := 118140960795 + 4636216 * 2 ^ 59
def prefixEnd_4636216 : Nat := 4983230072969 + 3 ^ 40 * 4636216 * 2
def baseEnd_4636216 : Nat := 2380607226065338017278437

theorem tailTrace_4636216 : CollatzResearch.WordTrace tailWord_4636216 prefixEnd_4636216 2380607226065338017278437 := by
  unfold tailWord_4636216
  simp only [CollatzResearch.WordTrace]
  refine ⟨84548344685894354749640251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112731126247859139666187001 84548344685894354749640251)
  ·
    refine ⟨126822517028841532124460377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84548344685894354749640251 126822517028841532124460377)
    ·
      refine ⟨95116887771631149093345283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126822517028841532124460377 95116887771631149093345283)
      ·
        refine ⟨142675331657446723640017925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95116887771631149093345283 142675331657446723640017925)
        ·
          refine ⟨26751624685771260682503361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 142675331657446723640017925 26751624685771260682503361)
          ·
            refine ⟨20063718514328445511877521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26751624685771260682503361 20063718514328445511877521)
            ·
              refine ⟨15047788885746334133908141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20063718514328445511877521 15047788885746334133908141)
              ·
                refine ⟨5642920832154875300215553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15047788885746334133908141 5642920832154875300215553)
                ·
                  refine ⟨4232190624116156475161665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5642920832154875300215553 4232190624116156475161665)
                  ·
                    refine ⟨3174142968087117356371249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4232190624116156475161665 3174142968087117356371249)
                    ·
                      refine ⟨2380607226065338017278437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174142968087117356371249 2380607226065338017278437)
                      ·
                        rfl

theorem cell23_4636216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 3, 2, 2, 2].length) (baseStart_4636216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636216 prefixEnd_4636216 := by exact prefixLift 4636216
  have htrace : WordTrace (prefixWord ++ tailWord_4636216) baseStart_4636216 baseEnd_4636216 := by
    simpa [prefixWord, tailWord_4636216, baseEnd_4636216] using wordTrace_append hprefix tailTrace_4636216
  have hstable : (prefixWord ++ tailWord_4636216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636216).length < 2 ^ (prefixWord ++ tailWord_4636216).sum := by decide
  have hdescent : baseEnd_4636216 < baseStart_4636216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636237 : List Nat := [1, 6, 1, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_4636237 : Nat := 118140960795 + 4636237 * 2 ^ 59
def prefixEnd_4636237 : Nat := 4983230072969 + 3 ^ 40 * 4636237 * 2
def baseEnd_4636237 : Nat := 2380618009159082435115841

theorem tailTrace_4636237 : CollatzResearch.WordTrace tailWord_4636237 prefixEnd_4636237 2380618009159082435115841 := by
  unfold tailWord_4636237
  simp only [CollatzResearch.WordTrace]
  refine ⟨169097455304712630085794965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112731636869808420057196643 169097455304712630085794965)
  ·
    refine ⟨7926443217408404535271639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 169097455304712630085794965 7926443217408404535271639)
    ·
      refine ⟨11889664826112606802907459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7926443217408404535271639 11889664826112606802907459)
      ·
        refine ⟨17834497239168910204361189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11889664826112606802907459 17834497239168910204361189)
        ·
          refine ⟨3343968232344170663317723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17834497239168910204361189 3343968232344170663317723)
          ·
            refine ⟨5015952348516255994976585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3343968232344170663317723 5015952348516255994976585)
            ·
              refine ⟨3761964261387191996232439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5015952348516255994976585 3761964261387191996232439)
              ·
                refine ⟨5642946392080787994348659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3761964261387191996232439 5642946392080787994348659)
                ·
                  refine ⟨8464419588121181991522989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5642946392080787994348659 8464419588121181991522989)
                  ·
                    refine ⟨3174157345545443246821121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8464419588121181991522989 3174157345545443246821121)
                    ·
                      refine ⟨2380618009159082435115841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174157345545443246821121 2380618009159082435115841)
                      ·
                        rfl

theorem cell23_4636237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_4636237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636237 prefixEnd_4636237 := by exact prefixLift 4636237
  have htrace : WordTrace (prefixWord ++ tailWord_4636237) baseStart_4636237 baseEnd_4636237 := by
    simpa [prefixWord, tailWord_4636237, baseEnd_4636237] using wordTrace_append hprefix tailTrace_4636237
  have hstable : (prefixWord ++ tailWord_4636237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636237).length < 2 ^ (prefixWord ++ tailWord_4636237).sum := by decide
  have hdescent : baseEnd_4636237 < baseStart_4636237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636272 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 4]
def baseStart_4636272 : Nat := 118140960795 + 4636272 * 2 ^ 59
def prefixEnd_4636272 : Nat := 4983230072969 + 3 ^ 40 * 4636272 * 2
def baseEnd_4636272 : Nat := 2380635980981989798178179

theorem tailTrace_4636272 : CollatzResearch.WordTrace tailWord_4636272 prefixEnd_4636272 2380635980981989798178179 := by
  unfold tailWord_4636272
  simp only [CollatzResearch.WordTrace]
  refine ⟨84549365929792915531659535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112732487906390554042212713 84549365929792915531659535)
  ·
    refine ⟨126824048894689373297489303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84549365929792915531659535 126824048894689373297489303)
    ·
      refine ⟨190236073342034059946233955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126824048894689373297489303 190236073342034059946233955)
      ·
        refine ⟨285354110013051089919350933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190236073342034059946233955 285354110013051089919350933)
        ·
          refine ⟨13375973906861769839969575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 285354110013051089919350933 13375973906861769839969575)
          ·
            refine ⟨20063960860292654759954363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13375973906861769839969575 20063960860292654759954363)
            ·
              refine ⟨30095941290438982139931545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20063960860292654759954363 30095941290438982139931545)
              ·
                refine ⟨22571955967829236604948659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30095941290438982139931545 22571955967829236604948659)
                ·
                  refine ⟨33857933951743854907422989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22571955967829236604948659 33857933951743854907422989)
                  ·
                    refine ⟨12696725231903945590283621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33857933951743854907422989 12696725231903945590283621)
                    ·
                      refine ⟨2380635980981989798178179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12696725231903945590283621 2380635980981989798178179)
                      ·
                        rfl

theorem cell23_4636272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 3, 4].length) (baseStart_4636272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636272 prefixEnd_4636272 := by exact prefixLift 4636272
  have htrace : WordTrace (prefixWord ++ tailWord_4636272) baseStart_4636272 baseEnd_4636272 := by
    simpa [prefixWord, tailWord_4636272, baseEnd_4636272] using wordTrace_append hprefix tailTrace_4636272
  have hstable : (prefixWord ++ tailWord_4636272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636272).length < 2 ^ (prefixWord ++ tailWord_4636272).sum := by decide
  have hdescent : baseEnd_4636272 < baseStart_4636272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636275 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 5]
def baseStart_4636275 : Nat := 118140960795 + 4636275 * 2 ^ 59
def prefixEnd_4636275 : Nat := 4983230072969 + 3 ^ 40 * 4636275 * 2
def baseEnd_4636275 : Nat := 2380637521423953286440665

theorem tailTrace_4636275 : CollatzResearch.WordTrace tailWord_4636275 prefixEnd_4636275 2380637521423953286440665 := by
  unfold tailWord_4636275
  simp only [CollatzResearch.WordTrace]
  refine ⟨169098841278574962575678279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112732560852383308383785519 169098841278574962575678279)
  ·
    refine ⟨253648261917862443863517419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169098841278574962575678279 253648261917862443863517419)
    ·
      refine ⟨380472392876793665795276129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253648261917862443863517419 380472392876793665795276129)
      ·
        refine ⟨285354294657595249346457097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380472392876793665795276129 285354294657595249346457097)
        ·
          refine ⟨214015720993196437009842823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285354294657595249346457097 214015720993196437009842823)
          ·
            refine ⟨321023581489794655514764235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214015720993196437009842823 321023581489794655514764235)
            ·
              refine ⟨481535372234691983272146353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321023581489794655514764235 481535372234691983272146353)
              ·
                refine ⟨361151529176018987454109765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 481535372234691983272146353 361151529176018987454109765)
                ·
                  refine ⟨67715911720503560147645581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 361151529176018987454109765 67715911720503560147645581)
                  ·
                    refine ⟨25393466895188835055367093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67715911720503560147645581 25393466895188835055367093)
                    ·
                      refine ⟨2380637521423953286440665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25393466895188835055367093 2380637521423953286440665)
                      ·
                        rfl

theorem cell23_4636275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_4636275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636275 prefixEnd_4636275 := by exact prefixLift 4636275
  have htrace : WordTrace (prefixWord ++ tailWord_4636275) baseStart_4636275 baseEnd_4636275 := by
    simpa [prefixWord, tailWord_4636275, baseEnd_4636275] using wordTrace_append hprefix tailTrace_4636275
  have hstable : (prefixWord ++ tailWord_4636275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636275).length < 2 ^ (prefixWord ++ tailWord_4636275).sum := by decide
  have hdescent : baseEnd_4636275 < baseStart_4636275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636282 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 5, 4]
def baseStart_4636282 : Nat := 118140960795 + 4636282 * 2 ^ 59
def prefixEnd_4636282 : Nat := 4983230072969 + 3 ^ 40 * 4636282 * 2
def baseEnd_4636282 : Nat := 793547038596178253017711

theorem tailTrace_4636282 : CollatzResearch.WordTrace tailWord_4636282 prefixEnd_4636282 793547038596178253017711 := by
  unfold tailWord_4636282
  simp only [CollatzResearch.WordTrace]
  refine ⟨42274774147387400692795775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112732731059699735180788733 42274774147387400692795775)
  ·
    refine ⟨63412161221081101039193663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42274774147387400692795775 63412161221081101039193663)
    ·
      refine ⟨95118241831621651558790495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63412161221081101039193663 95118241831621651558790495)
      ·
        refine ⟨142677362747432477338185743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95118241831621651558790495 142677362747432477338185743)
        ·
          refine ⟨214016044121148716007278615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 142677362747432477338185743 214016044121148716007278615)
          ·
            refine ⟨321024066181723074010917923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214016044121148716007278615 321024066181723074010917923)
            ·
              refine ⟨481536099272584611016376885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321024066181723074010917923 481536099272584611016376885)
              ·
                refine ⟨45144009306804807282785333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 481536099272584611016376885 45144009306804807282785333)
                ·
                  refine ⟨4232250872512950682761125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45144009306804807282785333 4232250872512950682761125)
                  ·
                    refine ⟨793547038596178253017711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4232250872512950682761125 793547038596178253017711)
                    ·
                      rfl

theorem cell23_4636282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_4636282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636282 prefixEnd_4636282 := by exact prefixLift 4636282
  have htrace : WordTrace (prefixWord ++ tailWord_4636282) baseStart_4636282 baseEnd_4636282 := by
    simpa [prefixWord, tailWord_4636282, baseEnd_4636282] using wordTrace_append hprefix tailTrace_4636282
  have hstable : (prefixWord ++ tailWord_4636282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636282).length < 2 ^ (prefixWord ++ tailWord_4636282).sum := by decide
  have hdescent : baseEnd_4636282 < baseStart_4636282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636306 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 2, 1, 4]
def baseStart_4636306 : Nat := 118140960795 + 4636306 * 2 ^ 59
def prefixEnd_4636306 : Nat := 4983230072969 + 3 ^ 40 * 4636306 * 2
def baseEnd_4636306 : Nat := 2380653439324242665153023

theorem tailTrace_4636306 : CollatzResearch.WordTrace tailWord_4636306 prefixEnd_4636306 2380653439324242665153023 := by
  unfold tailWord_4636306
  simp only [CollatzResearch.WordTrace]
  refine ⟨42274992985365663717514193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112733314627641769913371181 42274992985365663717514193)
  ·
    refine ⟨31706244739024247788135645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42274992985365663717514193 31706244739024247788135645)
    ·
      refine ⟨11889841777134092920550867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31706244739024247788135645 11889841777134092920550867)
      ·
        refine ⟨17834762665701139380826301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11889841777134092920550867 17834762665701139380826301)
        ·
          refine ⟨6688035999637927267809863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17834762665701139380826301 6688035999637927267809863)
          ·
            refine ⟨10032053999456890901714795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6688035999637927267809863 10032053999456890901714795)
            ·
              refine ⟨15048080999185336352572193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10032053999456890901714795 15048080999185336352572193)
              ·
                refine ⟨11286060749389002264429145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15048080999185336352572193 11286060749389002264429145)
                ·
                  refine ⟨8464545562041751698321859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11286060749389002264429145 8464545562041751698321859)
                  ·
                    refine ⟨12696818343062627547482789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8464545562041751698321859 12696818343062627547482789)
                    ·
                      refine ⟨2380653439324242665153023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12696818343062627547482789 2380653439324242665153023)
                      ·
                        rfl

theorem cell23_4636306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 1, 4].length) (baseStart_4636306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636306 prefixEnd_4636306 := by exact prefixLift 4636306
  have htrace : WordTrace (prefixWord ++ tailWord_4636306) baseStart_4636306 baseEnd_4636306 := by
    simpa [prefixWord, tailWord_4636306, baseEnd_4636306] using wordTrace_append hprefix tailTrace_4636306
  have hstable : (prefixWord ++ tailWord_4636306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636306).length < 2 ^ (prefixWord ++ tailWord_4636306).sum := by decide
  have hdescent : baseEnd_4636306 < baseStart_4636306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636312 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 8]
def baseStart_4636312 : Nat := 118140960795 + 4636312 * 2 ^ 59
def prefixEnd_4636312 : Nat := 4983230072969 + 3 ^ 40 * 4636312 * 2
def baseEnd_4636312 : Nat := 264517391134241071297555

theorem tailTrace_4636312 : CollatzResearch.WordTrace tailWord_4636312 prefixEnd_4636312 264517391134241071297555 := by
  unfold tailWord_4636312
  simp only [CollatzResearch.WordTrace]
  refine ⟨84550095389720458947387595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112733460519627278596516793 84550095389720458947387595)
  ·
    refine ⟨126825143084580688421081393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84550095389720458947387595 126825143084580688421081393)
    ·
      refine ⟨95118857313435516315811045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126825143084580688421081393 95118857313435516315811045)
      ·
        refine ⟨17834785746269159309214571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95118857313435516315811045 17834785746269159309214571)
        ·
          refine ⟨26752178619403738963821857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17834785746269159309214571 26752178619403738963821857)
          ·
            refine ⟨20064133964552804222866393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26752178619403738963821857 20064133964552804222866393)
            ·
              refine ⟨15048100473414603167149795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20064133964552804222866393 15048100473414603167149795)
              ·
                refine ⟨22572150710121904750724693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15048100473414603167149795 22572150710121904750724693)
                ·
                  refine ⟨264517391134241071297555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22572150710121904750724693 264517391134241071297555)
                  ·
                    rfl

theorem cell23_4636312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 8].length) (baseStart_4636312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636312 prefixEnd_4636312 := by exact prefixLift 4636312
  have htrace : WordTrace (prefixWord ++ tailWord_4636312) baseStart_4636312 baseEnd_4636312 := by
    simpa [prefixWord, tailWord_4636312, baseEnd_4636312] using wordTrace_append hprefix tailTrace_4636312
  have hstable : (prefixWord ++ tailWord_4636312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636312).length < 2 ^ (prefixWord ++ tailWord_4636312).sum := by decide
  have hdescent : baseEnd_4636312 < baseStart_4636312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636339 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 3]
def baseStart_4636339 : Nat := 118140960795 + 4636339 * 2 ^ 59
def prefixEnd_4636339 : Nat := 4983230072969 + 3 ^ 40 * 4636339 * 2
def baseEnd_4636339 : Nat := 2380670384185841036040371

theorem tailTrace_4636339 : CollatzResearch.WordTrace tailWord_4636339 prefixEnd_4636339 2380670384185841036040371 := by
  unfold tailWord_4636339
  simp only [CollatzResearch.WordTrace]
  refine ⟨169101175550343101506008071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112734117033562067670672047 169101175550343101506008071)
  ·
    refine ⟨253651763325514652259012107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169101175550343101506008071 253651763325514652259012107)
    ·
      refine ⟨380477644988271978388518161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253651763325514652259012107 380477644988271978388518161)
      ·
        refine ⟨285358233741203983791388621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 380477644988271978388518161 285358233741203983791388621)
        ·
          refine ⟨107009337652951493921770733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 285358233741203983791388621 107009337652951493921770733)
          ·
            refine ⟨40128501619856810220664025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 107009337652951493921770733 40128501619856810220664025)
            ·
              refine ⟨30096376214892607665498019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40128501619856810220664025 30096376214892607665498019)
              ·
                refine ⟨45144564322338911498247029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30096376214892607665498019 45144564322338911498247029)
                ·
                  refine ⟨4232302905219272952960659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45144564322338911498247029 4232302905219272952960659)
                  ·
                    refine ⟨6348454357828909429440989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4232302905219272952960659 6348454357828909429440989)
                    ·
                      refine ⟨2380670384185841036040371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6348454357828909429440989 2380670384185841036040371)
                      ·
                        rfl

theorem cell23_4636339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 5, 1, 3].length) (baseStart_4636339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636339 prefixEnd_4636339 := by exact prefixLift 4636339
  have htrace : WordTrace (prefixWord ++ tailWord_4636339) baseStart_4636339 baseEnd_4636339 := by
    simpa [prefixWord, tailWord_4636339, baseEnd_4636339] using wordTrace_append hprefix tailTrace_4636339
  have hstable : (prefixWord ++ tailWord_4636339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636339).length < 2 ^ (prefixWord ++ tailWord_4636339).sum := by decide
  have hdescent : baseEnd_4636339 < baseStart_4636339 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636366 : List Nat := [4, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2]
def baseStart_4636366 : Nat := 118140960795 + 4636366 * 2 ^ 59
def prefixEnd_4636366 : Nat := 4983230072969 + 3 ^ 40 * 4636366 * 2
def baseEnd_4636366 : Nat := 2380684248163512430402747

theorem tailTrace_4636366 : CollatzResearch.WordTrace tailWord_4636366 prefixEnd_4636366 2380684248163512430402747 := by
  unfold tailWord_4636366
  simp only [CollatzResearch.WordTrace]
  refine ⟨21137770040155660639655119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112734773547496856744827301 21137770040155660639655119)
  ·
    refine ⟨31706655060233490959482679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21137770040155660639655119 31706655060233490959482679)
    ·
      refine ⟨47559982590350236439224019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31706655060233490959482679 47559982590350236439224019)
      ·
        refine ⟨71339973885525354658836029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47559982590350236439224019 71339973885525354658836029)
        ·
          refine ⟨26752490207072007997063511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 71339973885525354658836029 26752490207072007997063511)
          ·
            refine ⟨40128735310608011995595267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26752490207072007997063511 40128735310608011995595267)
            ·
              refine ⟨60193102965912017993392901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40128735310608011995595267 60193102965912017993392901)
              ·
                refine ⟨11286206806108503373761169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 60193102965912017993392901 11286206806108503373761169)
                ·
                  refine ⟨8464655104581377530320877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11286206806108503373761169 8464655104581377530320877)
                  ·
                    refine ⟨3174245664218016573870329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8464655104581377530320877 3174245664218016573870329)
                    ·
                      refine ⟨2380684248163512430402747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174245664218016573870329 2380684248163512430402747)
                      ·
                        rfl

theorem cell23_4636366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 4, 2, 3, 2].length) (baseStart_4636366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636366 prefixEnd_4636366 := by exact prefixLift 4636366
  have htrace : WordTrace (prefixWord ++ tailWord_4636366) baseStart_4636366 baseEnd_4636366 := by
    simpa [prefixWord, tailWord_4636366, baseEnd_4636366] using wordTrace_append hprefix tailTrace_4636366
  have hstable : (prefixWord ++ tailWord_4636366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636366).length < 2 ^ (prefixWord ++ tailWord_4636366).sum := by decide
  have hdescent : baseEnd_4636366 < baseStart_4636366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636389 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_4636389 : Nat := 118140960795 + 4636389 * 2 ^ 59
def prefixEnd_4636389 : Nat := 4983230072969 + 3 ^ 40 * 4636389 * 2
def baseEnd_4636389 : Nat := 793565352739521946805047

theorem tailTrace_4636389 : CollatzResearch.WordTrace tailWord_4636389 prefixEnd_4636389 793565352739521946805047 := by
  unfold tailWord_4636389
  simp only [CollatzResearch.WordTrace]
  refine ⟨169102999200161960045328221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112735332800107973363552147 169102999200161960045328221)
  ·
    refine ⟨63413624700060735016998083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169102999200161960045328221 63413624700060735016998083)
    ·
      refine ⟨95120437050091102525497125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63413624700060735016998083 95120437050091102525497125)
      ·
        refine ⟨17835081946892081723530711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95120437050091102525497125 17835081946892081723530711)
        ·
          refine ⟨26752622920338122585296067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17835081946892081723530711 26752622920338122585296067)
          ·
            refine ⟨40128934380507183877944101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26752622920338122585296067 40128934380507183877944101)
            ·
              refine ⟨7524175196345096977114519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 40128934380507183877944101 7524175196345096977114519)
              ·
                refine ⟨11286262794517645465671779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7524175196345096977114519 11286262794517645465671779)
                ·
                  refine ⟨16929394191776468198507669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11286262794517645465671779 16929394191776468198507669)
                  ·
                    refine ⟨793565352739521946805047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16929394191776468198507669 793565352739521946805047)
                    ·
                      rfl

theorem cell23_4636389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_4636389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636389 prefixEnd_4636389 := by exact prefixLift 4636389
  have htrace : WordTrace (prefixWord ++ tailWord_4636389) baseStart_4636389 baseEnd_4636389 := by
    simpa [prefixWord, tailWord_4636389, baseEnd_4636389] using wordTrace_append hprefix tailTrace_4636389
  have hstable : (prefixWord ++ tailWord_4636389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636389).length < 2 ^ (prefixWord ++ tailWord_4636389).sum := by decide
  have hdescent : baseEnd_4636389 < baseStart_4636389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636396 : List Nat := [2, 2, 1, 1, 2, 2, 3, 1, 5, 2, 2]
def baseStart_4636396 : Nat := 118140960795 + 4636396 * 2 ^ 59
def prefixEnd_4636396 : Nat := 4983230072969 + 3 ^ 40 * 4636396 * 2
def baseEnd_4636396 : Nat := 2380699652583147313027609

theorem tailTrace_4636396 : CollatzResearch.WordTrace tailWord_4636396 prefixEnd_4636396 2380699652583147313027609 := by
  unfold tailWord_4636396
  simp only [CollatzResearch.WordTrace]
  refine ⟨84551627255568300120416521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112735503007424400160555361 84551627255568300120416521)
  ·
    refine ⟨63413720441676225090312391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84551627255568300120416521 63413720441676225090312391)
    ·
      refine ⟨95120580662514337635468587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63413720441676225090312391 95120580662514337635468587)
      ·
        refine ⟨142680870993771506453202881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95120580662514337635468587 142680870993771506453202881)
        ·
          refine ⟨107010653245328629839902161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142680870993771506453202881 107010653245328629839902161)
          ·
            refine ⟨80257989933996472379926621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107010653245328629839902161 80257989933996472379926621)
            ·
              refine ⟨30096746225248677142472483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 80257989933996472379926621 30096746225248677142472483)
              ·
                refine ⟨45145119337873015713708725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30096746225248677142472483 45145119337873015713708725)
                ·
                  refine ⟨4232354937925595223160193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 45145119337873015713708725 4232354937925595223160193)
                  ·
                    refine ⟨3174266203444196417370145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4232354937925595223160193 3174266203444196417370145)
                    ·
                      refine ⟨2380699652583147313027609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174266203444196417370145 2380699652583147313027609)
                      ·
                        rfl

theorem cell23_4636396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 2, 2].length) (baseStart_4636396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636396 prefixEnd_4636396 := by exact prefixLift 4636396
  have htrace : WordTrace (prefixWord ++ tailWord_4636396) baseStart_4636396 baseEnd_4636396 := by
    simpa [prefixWord, tailWord_4636396, baseEnd_4636396] using wordTrace_append hprefix tailTrace_4636396
  have hstable : (prefixWord ++ tailWord_4636396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636396).length < 2 ^ (prefixWord ++ tailWord_4636396).sum := by decide
  have hdescent : baseEnd_4636396 < baseStart_4636396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636399 : List Nat := [1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 3]
def baseStart_4636399 : Nat := 118140960795 + 4636399 * 2 ^ 59
def prefixEnd_4636399 : Nat := 4983230072969 + 3 ^ 40 * 4636399 * 2
def baseEnd_4636399 : Nat := 2380701193025110801290095

theorem tailTrace_4636399 : CollatzResearch.WordTrace tailWord_4636399 prefixEnd_4636399 2380701193025110801290095 := by
  unfold tailWord_4636399
  simp only [CollatzResearch.WordTrace]
  refine ⟨169103363930125731753192251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112735575953417154502128167 169103363930125731753192251)
  ·
    refine ⟨253655045895188597629788377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169103363930125731753192251 253655045895188597629788377)
    ·
      refine ⟨190241284421391448222341283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 253655045895188597629788377 190241284421391448222341283)
      ·
        refine ⟨285361926632087172333511925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190241284421391448222341283 285361926632087172333511925)
        ·
          refine ⟨26752680621758172406266743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 285361926632087172333511925 26752680621758172406266743)
          ·
            refine ⟨40129020932637258609400115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26752680621758172406266743 40129020932637258609400115)
            ·
              refine ⟨60193531398955887914100173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40129020932637258609400115 60193531398955887914100173)
              ·
                refine ⟨22572574274608457967787565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60193531398955887914100173 22572574274608457967787565)
                ·
                  refine ⟨8464715352978171737920337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22572574274608457967787565 8464715352978171737920337)
                  ·
                    refine ⟨6348536514733628803440253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8464715352978171737920337 6348536514733628803440253)
                    ·
                      refine ⟨2380701193025110801290095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6348536514733628803440253 2380701193025110801290095)
                      ·
                        rfl

theorem cell23_4636399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_4636399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636399 prefixEnd_4636399 := by exact prefixLift 4636399
  have htrace : WordTrace (prefixWord ++ tailWord_4636399) baseStart_4636399 baseEnd_4636399 := by
    simpa [prefixWord, tailWord_4636399, baseEnd_4636399] using wordTrace_append hprefix tailTrace_4636399
  have hstable : (prefixWord ++ tailWord_4636399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636399).length < 2 ^ (prefixWord ++ tailWord_4636399).sum := by decide
  have hdescent : baseEnd_4636399 < baseStart_4636399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636430 : List Nat := [4, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2]
def baseStart_4636430 : Nat := 118140960795 + 4636430 * 2 ^ 59
def prefixEnd_4636430 : Nat := 4983230072969 + 3 ^ 40 * 4636430 * 2
def baseEnd_4636430 : Nat := 2380717110925400180002453

theorem tailTrace_4636430 : CollatzResearch.WordTrace tailWord_4636430 prefixEnd_4636430 2380717110925400180002453 := by
  unfold tailWord_4636430
  simp only [CollatzResearch.WordTrace]
  refine ⟨21138061824126678005946343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112736329728675616031713829 21138061824126678005946343)
  ·
    refine ⟨31707092736190017008919515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21138061824126678005946343 31707092736190017008919515)
    ·
      refine ⟨47560639104285025513379273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31707092736190017008919515 47560639104285025513379273)
      ·
        refine ⟨35670479328213769135034455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47560639104285025513379273 35670479328213769135034455)
        ·
          refine ⟨53505718992320653702551683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35670479328213769135034455 53505718992320653702551683)
          ·
            refine ⟨80258578488480980553827525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53505718992320653702551683 80258578488480980553827525)
            ·
              refine ⟨15048483466590183853842661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 80258578488480980553827525 15048483466590183853842661)
              ·
                refine ⟨2821590649985659472595499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15048483466590183853842661 2821590649985659472595499)
                ·
                  refine ⟨4232385974978489208893249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2821590649985659472595499 4232385974978489208893249)
                  ·
                    refine ⟨3174289481233866906669937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4232385974978489208893249 3174289481233866906669937)
                    ·
                      refine ⟨2380717110925400180002453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174289481233866906669937 2380717110925400180002453)
                      ·
                        rfl

theorem cell23_4636430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2].length) (baseStart_4636430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636430 prefixEnd_4636430 := by exact prefixLift 4636430
  have htrace : WordTrace (prefixWord ++ tailWord_4636430) baseStart_4636430 baseEnd_4636430 := by
    simpa [prefixWord, tailWord_4636430, baseEnd_4636430] using wordTrace_append hprefix tailTrace_4636430
  have hstable : (prefixWord ++ tailWord_4636430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636430).length < 2 ^ (prefixWord ++ tailWord_4636430).sum := by decide
  have hdescent : baseEnd_4636430 < baseStart_4636430 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636489 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 3]
def baseStart_4636489 : Nat := 118140960795 + 4636489 * 2 ^ 59
def prefixEnd_4636489 : Nat := 4983230072969 + 3 ^ 40 * 4636489 * 2
def baseEnd_4636489 : Nat := 2380747406284015449164681

theorem tailTrace_4636489 : CollatzResearch.WordTrace tailWord_4636489 prefixEnd_4636489 2380747406284015449164681 := by
  unfold tailWord_4636489
  simp only [CollatzResearch.WordTrace]
  refine ⟨169106646499799677123968521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112737764333199784749312347 169106646499799677123968521)
  ·
    refine ⟨126829984874849757842976391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169106646499799677123968521 126829984874849757842976391)
    ·
      refine ⟨190244977312274636764464587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126829984874849757842976391 190244977312274636764464587)
      ·
        refine ⟨285367465968411955146696881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190244977312274636764464587 285367465968411955146696881)
        ·
          refine ⟨214025599476308966360022661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285367465968411955146696881 214025599476308966360022661)
          ·
            refine ⟨40129799901807931192504249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214025599476308966360022661 40129799901807931192504249)
            ·
              refine ⟨30097349926355948394378187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 40129799901807931192504249 30097349926355948394378187)
              ·
                refine ⟨45146024889533922591567281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30097349926355948394378187 45146024889533922591567281)
                ·
                  refine ⟨33859518667150441943675461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45146024889533922591567281 33859518667150441943675461)
                  ·
                    refine ⟨6348659750090707864439149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33859518667150441943675461 6348659750090707864439149)
                    ·
                      refine ⟨2380747406284015449164681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6348659750090707864439149 2380747406284015449164681)
                      ·
                        rfl

theorem cell23_4636489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 2, 4, 3].length) (baseStart_4636489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636489 prefixEnd_4636489 := by exact prefixLift 4636489
  have htrace : WordTrace (prefixWord ++ tailWord_4636489) baseStart_4636489 baseEnd_4636489 := by
    simpa [prefixWord, tailWord_4636489, baseEnd_4636489] using wordTrace_append hprefix tailTrace_4636489
  have hstable : (prefixWord ++ tailWord_4636489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636489).length < 2 ^ (prefixWord ++ tailWord_4636489).sum := by decide
  have hdescent : baseEnd_4636489 < baseStart_4636489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636549 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 5]
def baseStart_4636549 : Nat := 118140960795 + 4636549 * 2 ^ 59
def prefixEnd_4636549 : Nat := 4983230072969 + 3 ^ 40 * 4636549 * 2
def baseEnd_4636549 : Nat := 2380778215123285214414405

theorem tailTrace_4636549 : CollatzResearch.WordTrace tailWord_4636549 prefixEnd_4636549 2380778215123285214414405 := by
  unfold tailWord_4636549
  simp only [CollatzResearch.WordTrace]
  refine ⟨169108834879582307371152701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112739223253054871580768467 169108834879582307371152701)
  ·
    refine ⟨63415813079843365264182263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169108834879582307371152701 63415813079843365264182263)
    ·
      refine ⟨95123719619765047896273395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63415813079843365264182263 95123719619765047896273395)
      ·
        refine ⟨142685579429647571844410093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95123719619765047896273395 142685579429647571844410093)
        ·
          refine ⟨53507092286117839441653785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 142685579429647571844410093 53507092286117839441653785)
          ·
            refine ⟨40130319214588379581240339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53507092286117839441653785 40130319214588379581240339)
            ·
              refine ⟨60195478821882569371860509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40130319214588379581240339 60195478821882569371860509)
              ·
                refine ⟨22573304558205963514447691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 60195478821882569371860509 22573304558205963514447691)
                ·
                  refine ⟨33859956837308945271671537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22573304558205963514447691 33859956837308945271671537)
                  ·
                    refine ⟨25394967627981708953753653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33859956837308945271671537 25394967627981708953753653)
                    ·
                      refine ⟨2380778215123285214414405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25394967627981708953753653 2380778215123285214414405)
                      ·
                        rfl

theorem cell23_4636549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_4636549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636549 prefixEnd_4636549 := by exact prefixLift 4636549
  have htrace : WordTrace (prefixWord ++ tailWord_4636549) baseStart_4636549 baseEnd_4636549 := by
    simpa [prefixWord, tailWord_4636549, baseEnd_4636549] using wordTrace_append hprefix tailTrace_4636549
  have hstable : (prefixWord ++ tailWord_4636549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636549).length < 2 ^ (prefixWord ++ tailWord_4636549).sum := by decide
  have hdescent : baseEnd_4636549 < baseStart_4636549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636573 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_4636573 : Nat := 118140960795 + 4636573 * 2 ^ 59
def prefixEnd_4636573 : Nat := 4983230072969 + 3 ^ 40 * 4636573 * 2
def baseEnd_4636573 : Nat := 793596846219664373504765

theorem tailTrace_4636573 : CollatzResearch.WordTrace tailWord_4636573 prefixEnd_4636573 793596846219664373504765 := by
  unfold tailWord_4636573
  simp only [CollatzResearch.WordTrace]
  refine ⟨169109710231495359470026373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112739806820996906313350915 169109710231495359470026373)
  ·
    refine ⟨31708070668405379900629945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 169109710231495359470026373 31708070668405379900629945)
    ·
      refine ⟨23781053001304034925472459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31708070668405379900629945 23781053001304034925472459)
      ·
        refine ⟨35671579501956052388208689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23781053001304034925472459 35671579501956052388208689)
        ·
          refine ⟨26753684626467039291156517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35671579501956052388208689 26753684626467039291156517)
          ·
            refine ⟨5016315867462569867091847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26753684626467039291156517 5016315867462569867091847)
            ·
              refine ⟨7524473801193854800637771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5016315867462569867091847 7524473801193854800637771)
              ·
                refine ⟨11286710701790782200956657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7524473801193854800637771 11286710701790782200956657)
                ·
                  refine ⟨8465033026343086650717493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11286710701790782200956657 8465033026343086650717493)
                  ·
                    refine ⟨793596846219664373504765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8465033026343086650717493 793596846219664373504765)
                    ·
                      rfl

theorem cell23_4636573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_4636573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636573 prefixEnd_4636573 := by exact prefixLift 4636573
  have htrace : WordTrace (prefixWord ++ tailWord_4636573) baseStart_4636573 baseEnd_4636573 := by
    simpa [prefixWord, tailWord_4636573, baseEnd_4636573] using wordTrace_append hprefix tailTrace_4636573
  have hstable : (prefixWord ++ tailWord_4636573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636573).length < 2 ^ (prefixWord ++ tailWord_4636573).sum := by decide
  have hdescent : baseEnd_4636573 < baseStart_4636573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636576 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 3, 6, 2]
def baseStart_4636576 : Nat := 118140960795 + 4636576 * 2 ^ 59
def prefixEnd_4636576 : Nat := 4983230072969 + 3 ^ 40 * 4636576 * 2
def baseEnd_4636576 : Nat := 2380792079100956608776781

theorem tailTrace_4636576 : CollatzResearch.WordTrace tailWord_4636576 prefixEnd_4636576 2380792079100956608776781 := by
  unfold tailWord_4636576
  simp only [CollatzResearch.WordTrace]
  refine ⟨84554909825242245491192791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112739879766989660654923721 84554909825242245491192791)
  ·
    refine ⟨126832364737863368236789187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84554909825242245491192791 126832364737863368236789187)
    ·
      refine ⟨190248547106795052355183781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126832364737863368236789187 190248547106795052355183781)
      ·
        refine ⟨35671602582524072316596959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 190248547106795052355183781 35671602582524072316596959)
        ·
          refine ⟨53507403873786108474895439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35671602582524072316596959 53507403873786108474895439)
          ·
            refine ⟨80261105810679162712343159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53507403873786108474895439 80261105810679162712343159)
            ·
              refine ⟨120391658716018744068514739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80261105810679162712343159 120391658716018744068514739)
              ·
                refine ⟨180587488074028116102772109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 120391658716018744068514739 180587488074028116102772109)
                ·
                  refine ⟨67720308027760543538539541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 180587488074028116102772109 67720308027760543538539541)
                  ·
                    refine ⟨3174389438801275478369041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67720308027760543538539541 3174389438801275478369041)
                    ·
                      refine ⟨2380792079100956608776781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174389438801275478369041 2380792079100956608776781)
                      ·
                        rfl

theorem cell23_4636576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 3, 6, 2].length) (baseStart_4636576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636576 prefixEnd_4636576 := by exact prefixLift 4636576
  have htrace : WordTrace (prefixWord ++ tailWord_4636576) baseStart_4636576 baseEnd_4636576 := by
    simpa [prefixWord, tailWord_4636576, baseEnd_4636576] using wordTrace_append hprefix tailTrace_4636576
  have hstable : (prefixWord ++ tailWord_4636576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636576).length < 2 ^ (prefixWord ++ tailWord_4636576).sum := by decide
  have hdescent : baseEnd_4636576 < baseStart_4636576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636593 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 2, 4, 2]
def baseStart_4636593 : Nat := 118140960795 + 4636593 * 2 ^ 59
def prefixEnd_4636593 : Nat := 4983230072969 + 3 ^ 40 * 4636593 * 2
def baseEnd_4636593 : Nat := 2380800808272083042264203

theorem tailTrace_4636593 : CollatzResearch.WordTrace tailWord_4636593 prefixEnd_4636593 2380800808272083042264203 := by
  unfold tailWord_4636593
  simp only [CollatzResearch.WordTrace]
  refine ⟨169110439691422902885754433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112740293127615268590502955 169110439691422902885754433)
  ·
    refine ⟨126832829768567177164315825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169110439691422902885754433 126832829768567177164315825)
    ·
      refine ⟨95124622326425382873236869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126832829768567177164315825 95124622326425382873236869)
      ·
        refine ⟨17835866686204759288731913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 95124622326425382873236869 17835866686204759288731913)
        ·
          refine ⟨13376900014653569466548935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17835866686204759288731913 13376900014653569466548935)
          ·
            refine ⟨20065350021980354199823403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13376900014653569466548935 20065350021980354199823403)
            ·
              refine ⟨30098025032970531299735105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20065350021980354199823403 30098025032970531299735105)
              ·
                refine ⟨22573518774727898474801329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 30098025032970531299735105 22573518774727898474801329)
                ·
                  refine ⟨16930139081045923856100997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22573518774727898474801329 16930139081045923856100997)
                  ·
                    refine ⟨3174401077696110723018937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16930139081045923856100997 3174401077696110723018937)
                    ·
                      refine ⟨2380800808272083042264203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174401077696110723018937 2380800808272083042264203)
                      ·
                        rfl

theorem cell23_4636593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 2, 4, 2].length) (baseStart_4636593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636593 prefixEnd_4636593 := by exact prefixLift 4636593
  have htrace : WordTrace (prefixWord ++ tailWord_4636593) baseStart_4636593 baseEnd_4636593 := by
    simpa [prefixWord, tailWord_4636593, baseEnd_4636593] using wordTrace_append hprefix tailTrace_4636593
  have hstable : (prefixWord ++ tailWord_4636593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636593).length < 2 ^ (prefixWord ++ tailWord_4636593).sum := by decide
  have hdescent : baseEnd_4636593 < baseStart_4636593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636619 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 6]
def baseStart_4636619 : Nat := 118140960795 + 4636619 * 2 ^ 59
def prefixEnd_4636619 : Nat := 4983230072969 + 3 ^ 40 * 4636619 * 2
def baseEnd_4636619 : Nat := 2380814158769099940539083

theorem tailTrace_4636619 : CollatzResearch.WordTrace tailWord_4636619 prefixEnd_4636619 2380814158769099940539083 := by
  unfold tailWord_4636619
  simp only [CollatzResearch.WordTrace]
  refine ⟨169111387989328709326200911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112740925326219139550800607 169111387989328709326200911)
  ·
    refine ⟨253667081983993063989301367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 169111387989328709326200911 253667081983993063989301367)
    ·
      refine ⟨380500622975989595983952051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 253667081983993063989301367 380500622975989595983952051)
      ·
        refine ⟨570750934463984393975928077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 380500622975989595983952051 570750934463984393975928077)
        ·
          refine ⟨214031600423994147740973029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 570750934463984393975928077 214031600423994147740973029)
          ·
            refine ⟨40130925079498902701432443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 214031600423994147740973029 40130925079498902701432443)
            ·
              refine ⟨60196387619248354052148665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 40130925079498902701432443 60196387619248354052148665)
              ·
                refine ⟨45147290714436265539111499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 60196387619248354052148665 45147290714436265539111499)
                ·
                  refine ⟨67720936071654398308667249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 45147290714436265539111499 67720936071654398308667249)
                  ·
                    refine ⟨50790702053740798731500437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67720936071654398308667249 50790702053740798731500437)
                    ·
                      refine ⟨2380814158769099940539083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50790702053740798731500437 2380814158769099940539083)
                      ·
                        rfl

theorem cell23_4636619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 6].length) (baseStart_4636619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636619 prefixEnd_4636619 := by exact prefixLift 4636619
  have htrace : WordTrace (prefixWord ++ tailWord_4636619) baseStart_4636619 baseEnd_4636619 := by
    simpa [prefixWord, tailWord_4636619, baseEnd_4636619] using wordTrace_append hprefix tailTrace_4636619
  have hstable : (prefixWord ++ tailWord_4636619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636619).length < 2 ^ (prefixWord ++ tailWord_4636619).sum := by decide
  have hdescent : baseEnd_4636619 < baseStart_4636619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636693 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_4636693 : Nat := 118140960795 + 4636693 * 2 ^ 59
def prefixEnd_4636693 : Nat := 4983230072969 + 3 ^ 40 * 4636693 * 2
def baseEnd_4636693 : Nat := 793617385445844217004581

theorem tailTrace_4636693 : CollatzResearch.WordTrace tailWord_4636693 prefixEnd_4636693 793617385445844217004581 := by
  unfold tailWord_4636693
  simp only [CollatzResearch.WordTrace]
  refine ⟨169114086991060619964394733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112742724660707079976263155 169114086991060619964394733)
  ·
    refine ⟨63417782621647732486648025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169114086991060619964394733 63417782621647732486648025)
    ·
      refine ⟨47563336966235799364986019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63417782621647732486648025 47563336966235799364986019)
      ·
        refine ⟨71345005449353699047479029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47563336966235799364986019 71345005449353699047479029)
        ·
          refine ⟨6688594260876909285701159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 71345005449353699047479029 6688594260876909285701159)
          ·
            refine ⟨10032891391315363928551739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6688594260876909285701159 10032891391315363928551739)
            ·
              refine ⟨15049337086973045892827609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10032891391315363928551739 15049337086973045892827609)
              ·
                refine ⟨11287002815229784419620707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15049337086973045892827609 11287002815229784419620707)
                ·
                  refine ⟨16930504222844676629431061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11287002815229784419620707 16930504222844676629431061)
                  ·
                    refine ⟨793617385445844217004581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16930504222844676629431061 793617385445844217004581)
                    ·
                      rfl

theorem cell23_4636693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_4636693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636693 prefixEnd_4636693 := by exact prefixLift 4636693
  have htrace : WordTrace (prefixWord ++ tailWord_4636693) baseStart_4636693 baseEnd_4636693 := by
    simpa [prefixWord, tailWord_4636693, baseEnd_4636693] using wordTrace_append hprefix tailTrace_4636693
  have hstable : (prefixWord ++ tailWord_4636693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636693).length < 2 ^ (prefixWord ++ tailWord_4636693).sum := by decide
  have hdescent : baseEnd_4636693 < baseStart_4636693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636734 : List Nat := [4, 2, 1, 3, 2, 1, 1, 2, 3, 2, 2]
def baseStart_4636734 : Nat := 118140960795 + 4636734 * 2 ^ 59
def prefixEnd_4636734 : Nat := 4983230072969 + 3 ^ 40 * 4636734 * 2
def baseEnd_4636734 : Nat := 2380873209044366990601055

theorem tailTrace_4636734 : CollatzResearch.WordTrace tailWord_4636734 prefixEnd_4636734 2380873209044366990601055 := by
  unfold tailWord_4636734
  simp only [CollatzResearch.WordTrace]
  refine ⟨21139447797989010495829657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112743721589274722644424837 21139447797989010495829657)
  ·
    refine ⟨15854585848491757871872243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21139447797989010495829657 15854585848491757871872243)
    ·
      refine ⟨23781878772737636807808365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15854585848491757871872243 23781878772737636807808365)
      ·
        refine ⟨8918204539776613802928137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23781878772737636807808365 8918204539776613802928137)
        ·
          refine ⟨6688653404832460352196103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8918204539776613802928137 6688653404832460352196103)
          ·
            refine ⟨10032980107248690528294155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6688653404832460352196103 10032980107248690528294155)
            ·
              refine ⟨15049470160873035792441233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10032980107248690528294155 15049470160873035792441233)
              ·
                refine ⟨11287102620654776844330925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15049470160873035792441233 11287102620654776844330925)
                ·
                  refine ⟨4232663482745541316624097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11287102620654776844330925 4232663482745541316624097)
                  ·
                    refine ⟨3174497612059155987468073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4232663482745541316624097 3174497612059155987468073)
                    ·
                      refine ⟨2380873209044366990601055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3174497612059155987468073 2380873209044366990601055)
                      ·
                        rfl

theorem cell23_4636734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_4636734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636734 prefixEnd_4636734 := by exact prefixLift 4636734
  have htrace : WordTrace (prefixWord ++ tailWord_4636734) baseStart_4636734 baseEnd_4636734 := by
    simpa [prefixWord, tailWord_4636734, baseEnd_4636734] using wordTrace_append hprefix tailTrace_4636734
  have hstable : (prefixWord ++ tailWord_4636734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636734).length < 2 ^ (prefixWord ++ tailWord_4636734).sum := by decide
  have hdescent : baseEnd_4636734 < baseStart_4636734 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636746 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_4636746 : Nat := 118140960795 + 4636746 * 2 ^ 59
def prefixEnd_4636746 : Nat := 4983230072969 + 3 ^ 40 * 4636746 * 2
def baseEnd_4636746 : Nat := 2380879370812220943650999

theorem tailTrace_4636746 : CollatzResearch.WordTrace tailWord_4636746 prefixEnd_4636746 2380879370812220943650999 := by
  unfold tailWord_4636746
  simp only [CollatzResearch.WordTrace]
  refine ⟨42279005014967152504018523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112744013373245740010716061 42279005014967152504018523)
  ·
    refine ⟨63418507522450728756027785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42279005014967152504018523 63418507522450728756027785)
    ·
      refine ⟨47563880641838046567020839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63418507522450728756027785 47563880641838046567020839)
      ·
        refine ⟨71345820962757069850531259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47563880641838046567020839 71345820962757069850531259)
        ·
          refine ⟨107018731444135604775796889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 71345820962757069850531259 107018731444135604775796889)
          ·
            refine ⟨80264048583101703581847667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 107018731444135604775796889 80264048583101703581847667)
            ·
              refine ⟨120396072874652555372771501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 80264048583101703581847667 120396072874652555372771501)
              ·
                refine ⟨45148527327994708264789313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 120396072874652555372771501 45148527327994708264789313)
                ·
                  refine ⟨33861395495996031198591985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 45148527327994708264789313 33861395495996031198591985)
                  ·
                    refine ⟨25396046621997023398943989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33861395495996031198591985 25396046621997023398943989)
                    ·
                      refine ⟨2380879370812220943650999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25396046621997023398943989 2380879370812220943650999)
                      ·
                        rfl

theorem cell23_4636746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_4636746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636746 prefixEnd_4636746 := by exact prefixLift 4636746
  have htrace : WordTrace (prefixWord ++ tailWord_4636746) baseStart_4636746 baseEnd_4636746 := by
    simpa [prefixWord, tailWord_4636746, baseEnd_4636746] using wordTrace_append hprefix tailTrace_4636746
  have hstable : (prefixWord ++ tailWord_4636746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636746).length < 2 ^ (prefixWord ++ tailWord_4636746).sum := by decide
  have hdescent : baseEnd_4636746 < baseStart_4636746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636754 : List Nat := [3, 2, 2, 1, 4, 2, 2, 1, 1, 2, 3]
def baseStart_4636754 : Nat := 118140960795 + 4636754 * 2 ^ 59
def prefixEnd_4636754 : Nat := 4983230072969 + 3 ^ 40 * 4636754 * 2
def baseEnd_4636754 : Nat := 2380883478657456912350963

theorem tailTrace_4636754 : CollatzResearch.WordTrace tailWord_4636754 prefixEnd_4636754 2380883478657456912350963 := by
  unfold tailWord_4636754
  simp only [CollatzResearch.WordTrace]
  refine ⟨42279077960959906845591329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112744207895893084921576877 42279077960959906845591329)
  ·
    refine ⟨31709308470719930134193497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42279077960959906845591329 31709308470719930134193497)
    ·
      refine ⟨23781981353039947600645123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31709308470719930134193497 23781981353039947600645123)
      ·
        refine ⟨35672972029559921400967685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23781981353039947600645123 35672972029559921400967685)
        ·
          refine ⟨6688682255542485262681441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35672972029559921400967685 6688682255542485262681441)
          ·
            refine ⟨5016511691656863947011081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6688682255542485262681441 5016511691656863947011081)
            ·
              refine ⟨3762383768742647960258311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5016511691656863947011081 3762383768742647960258311)
              ·
                refine ⟨5643575653113971940387467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3762383768742647960258311 5643575653113971940387467)
                ·
                  refine ⟨8465363479670957910581201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5643575653113971940387467 8465363479670957910581201)
                  ·
                    refine ⟨6349022609753218432935901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8465363479670957910581201 6349022609753218432935901)
                    ·
                      refine ⟨2380883478657456912350963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6349022609753218432935901 2380883478657456912350963)
                      ·
                        rfl

theorem cell23_4636754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 2, 1, 1, 2, 3].length) (baseStart_4636754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636754 prefixEnd_4636754 := by exact prefixLift 4636754
  have htrace : WordTrace (prefixWord ++ tailWord_4636754) baseStart_4636754 baseEnd_4636754 := by
    simpa [prefixWord, tailWord_4636754, baseEnd_4636754] using wordTrace_append hprefix tailTrace_4636754
  have hstable : (prefixWord ++ tailWord_4636754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636754).length < 2 ^ (prefixWord ++ tailWord_4636754).sum := by decide
  have hdescent : baseEnd_4636754 < baseStart_4636754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636873 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 7, 4]
def baseStart_4636873 : Nat := 118140960795 + 4636873 * 2 ^ 59
def prefixEnd_4636873 : Nat := 4983230072969 + 3 ^ 40 * 4636873 * 2
def baseEnd_4636873 : Nat := 793648194285113982254305

theorem tailTrace_4636873 : CollatzResearch.WordTrace tailWord_4636873 prefixEnd_4636873 793648194285113982254305 := by
  unfold tailWord_4636873
  simp only [CollatzResearch.WordTrace]
  refine ⟨169120652130408510705947273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112747101420272340470631515 169120652130408510705947273)
  ·
    refine ⟨126840489097806383029460455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 169120652130408510705947273 126840489097806383029460455)
    ·
      refine ⟨190260733646709574544190683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126840489097806383029460455 190260733646709574544190683)
      ·
        refine ⟨285391100470064361816286025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 190260733646709574544190683 285391100470064361816286025)
        ·
          refine ⟨214043325352548271362214519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 285391100470064361816286025 214043325352548271362214519)
          ·
            refine ⟨321064988028822407043321779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 214043325352548271362214519 321064988028822407043321779)
            ·
              refine ⟨481597482043233610564982669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 321064988028822407043321779 481597482043233610564982669)
              ·
                refine ⟨180599055766212603961868501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 481597482043233610564982669 180599055766212603961868501)
                ·
                  refine ⟨4232790369520607905356293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 180599055766212603961868501 4232790369520607905356293)
                  ·
                    refine ⟨793648194285113982254305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4232790369520607905356293 793648194285113982254305)
                    ·
                      rfl

theorem cell23_4636873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 7, 4].length) (baseStart_4636873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636873 prefixEnd_4636873 := by exact prefixLift 4636873
  have htrace : WordTrace (prefixWord ++ tailWord_4636873) baseStart_4636873 baseEnd_4636873 := by
    simpa [prefixWord, tailWord_4636873, baseEnd_4636873] using wordTrace_append hprefix tailTrace_4636873
  have hstable : (prefixWord ++ tailWord_4636873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636873).length < 2 ^ (prefixWord ++ tailWord_4636873).sum := by decide
  have hdescent : baseEnd_4636873 < baseStart_4636873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636924 : List Nat := [2, 2, 2, 1, 4, 2, 2, 3, 1, 4]
def baseStart_4636924 : Nat := 118140960795 + 4636924 * 2 ^ 59
def prefixEnd_4636924 : Nat := 4983230072969 + 3 ^ 40 * 4636924 * 2
def baseEnd_4636924 : Nat := 793656923456240415741727

theorem tailTrace_4636924 : CollatzResearch.WordTrace tailWord_4636924 prefixEnd_4636924 793656923456240415741727 := by
  unfold tailWord_4636924
  simp only [CollatzResearch.WordTrace]
  refine ⟨84561256126611873208026913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112748341502149164277369217 84561256126611873208026913)
  ·
    refine ⟨63420942094958904906020185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84561256126611873208026913 63420942094958904906020185)
    ·
      refine ⟨47565706571219178679515139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63420942094958904906020185 47565706571219178679515139)
      ·
        refine ⟨71348559856828768019272709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47565706571219178679515139 71348559856828768019272709)
        ·
          refine ⟨13377854973155394003613633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 71348559856828768019272709 13377854973155394003613633)
          ·
            refine ⟨10033391229866545502710225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13377854973155394003613633 10033391229866545502710225)
            ·
              refine ⟨7525043422399909127032669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10033391229866545502710225 7525043422399909127032669)
              ·
                refine ⟨2821891283399965922637251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7525043422399909127032669 2821891283399965922637251)
                ·
                  refine ⟨4232836925099948883955877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2821891283399965922637251 4232836925099948883955877)
                  ·
                    refine ⟨793656923456240415741727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4232836925099948883955877 793656923456240415741727)
                    ·
                      rfl

theorem cell23_4636924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 3, 1, 4].length) (baseStart_4636924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636924 prefixEnd_4636924 := by exact prefixLift 4636924
  have htrace : WordTrace (prefixWord ++ tailWord_4636924) baseStart_4636924 baseEnd_4636924 := by
    simpa [prefixWord, tailWord_4636924, baseEnd_4636924] using wordTrace_append hprefix tailTrace_4636924
  have hstable : (prefixWord ++ tailWord_4636924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636924).length < 2 ^ (prefixWord ++ tailWord_4636924).sum := by decide
  have hdescent : baseEnd_4636924 < baseStart_4636924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4636933 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_4636933 : Nat := 118140960795 + 4636933 * 2 ^ 59
def prefixEnd_4636933 : Nat := 4983230072969 + 3 ^ 40 * 4636933 * 2
def baseEnd_4636933 : Nat := 793658463898203904004213

theorem tailTrace_4636933 : CollatzResearch.WordTrace tailWord_4636933 prefixEnd_4636933 793658463898203904004213 := by
  unfold tailWord_4636933
  simp only [CollatzResearch.WordTrace]
  refine ⟨169122840510191140953131453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112748560340127427302087635 169122840510191140953131453)
  ·
    refine ⟨63421065191321677857424295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 169122840510191140953131453 63421065191321677857424295)
    ·
      refine ⟨95131597786982516786136443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63421065191321677857424295 95131597786982516786136443)
      ·
        refine ⟨142697396680473775179204665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 95131597786982516786136443 142697396680473775179204665)
        ·
          refine ⟨107023047510355331384403499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 142697396680473775179204665 107023047510355331384403499)
          ·
            refine ⟨160534571265532997076605249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 107023047510355331384403499 160534571265532997076605249)
            ·
              refine ⟨120400928449149747807453937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 160534571265532997076605249 120400928449149747807453937)
              ·
                refine ⟨90300696336862310855590453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 120400928449149747807453937 90300696336862310855590453)
                ·
                  refine ⟨8465690281580841642711605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 90300696336862310855590453 8465690281580841642711605)
                  ·
                    refine ⟨793658463898203904004213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8465690281580841642711605 793658463898203904004213)
                    ·
                      rfl

theorem cell23_4636933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_4636933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4636933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4636933 prefixEnd_4636933 := by exact prefixLift 4636933
  have htrace : WordTrace (prefixWord ++ tailWord_4636933) baseStart_4636933 baseEnd_4636933 := by
    simpa [prefixWord, tailWord_4636933, baseEnd_4636933] using wordTrace_append hprefix tailTrace_4636933
  have hstable : (prefixWord ++ tailWord_4636933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4636933).length < 2 ^ (prefixWord ++ tailWord_4636933).sum := by decide
  have hdescent : baseEnd_4636933 < baseStart_4636933 := by decide
  rcases family_descends (prefixWord ++ tailWord_4636933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
