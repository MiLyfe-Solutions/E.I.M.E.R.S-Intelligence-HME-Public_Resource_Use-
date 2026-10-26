import V185TrunkScan22Chunk335

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2997912 : List Nat := [2, 1, 2, 4, 1, 2, 2, 1, 2, 5]
def baseStart_2997912 : Nat := 118140960795 + 2997912 * 2 ^ 59
def prefixEnd_2997912 : Nat := 4983230072969 + 3 ^ 40 * 2997912 * 2
def baseEnd_2997912 : Nat := 1026246543921186592808573

theorem tailTrace_2997912 : CollatzResearch.WordTrace tailWord_2997912 prefixEnd_2997912 1026246543921186592808573 := by
  unfold tailWord_2997912
  simp only [CollatzResearch.WordTrace]
  refine ⟨54671416757542150726049995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72895222343389534301399993 54671416757542150726049995)
  ·
    refine ⟨82007125136313226089074993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54671416757542150726049995 82007125136313226089074993)
    ·
      refine ⟨61505343852234919566806245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82007125136313226089074993 61505343852234919566806245)
      ·
        refine ⟨11532251972294047418776171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61505343852234919566806245 11532251972294047418776171)
        ·
          refine ⟨17298377958441071128164257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11532251972294047418776171 17298377958441071128164257)
          ·
            refine ⟨12973783468830803346123193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17298377958441071128164257 12973783468830803346123193)
            ·
              refine ⟨9730337601623102509592395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12973783468830803346123193 9730337601623102509592395)
              ·
                refine ⟨14595506402434653764388593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9730337601623102509592395 14595506402434653764388593)
                ·
                  refine ⟨10946629801825990323291445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14595506402434653764388593 10946629801825990323291445)
                  ·
                    refine ⟨1026246543921186592808573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10946629801825990323291445 1026246543921186592808573)
                    ·
                      rfl

theorem cell22_2997912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 2, 1, 2, 5].length) (baseStart_2997912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997912 prefixEnd_2997912 := by exact prefixLift 2997912
  have htrace : WordTrace (prefixWord ++ tailWord_2997912) baseStart_2997912 baseEnd_2997912 := by
    simpa [prefixWord, tailWord_2997912, baseEnd_2997912] using wordTrace_append hprefix tailTrace_2997912
  have hstable : (prefixWord ++ tailWord_2997912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997912).length < 2 ^ (prefixWord ++ tailWord_2997912).sum := by decide
  have hdescent : baseEnd_2997912 < baseStart_2997912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997955 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 10]
def baseStart_2997955 : Nat := 118140960795 + 2997955 * 2 ^ 59
def prefixEnd_2997955 : Nat := 4983230072969 + 3 ^ 40 * 2997955 * 2
def baseEnd_2997955 : Nat := 1026261263699948813983441

theorem tailTrace_2997955 : CollatzResearch.WordTrace tailWord_2997955 prefixEnd_2997955 1026261263699948813983441 := by
  unfold tailWord_2997955
  simp only [CollatzResearch.WordTrace]
  refine ⟨109344401853928519795915319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72896267902619013197276879 109344401853928519795915319)
  ·
    refine ⟨164016602780892779693872979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109344401853928519795915319 164016602780892779693872979)
    ·
      refine ⟨246024904171339169540809469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164016602780892779693872979 246024904171339169540809469)
      ·
        refine ⟨92259339064252188577803551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246024904171339169540809469 92259339064252188577803551)
        ·
          refine ⟨138389008596378282866705327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92259339064252188577803551 138389008596378282866705327)
          ·
            refine ⟨207583512894567424300057991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138389008596378282866705327 207583512894567424300057991)
            ·
              refine ⟨311375269341851136450086987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207583512894567424300057991 311375269341851136450086987)
              ·
                refine ⟨467062904012776704675130481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311375269341851136450086987 467062904012776704675130481)
                ·
                  refine ⟨350297178009582528506347861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 467062904012776704675130481 350297178009582528506347861)
                  ·
                    refine ⟨1026261263699948813983441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 350297178009582528506347861 1026261263699948813983441)
                    ·
                      rfl

theorem cell22_2997955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_2997955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997955 prefixEnd_2997955 := by exact prefixLift 2997955
  have htrace : WordTrace (prefixWord ++ tailWord_2997955) baseStart_2997955 baseEnd_2997955 := by
    simpa [prefixWord, tailWord_2997955, baseEnd_2997955] using wordTrace_append hprefix tailTrace_2997955
  have hstable : (prefixWord ++ tailWord_2997955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997955).length < 2 ^ (prefixWord ++ tailWord_2997955).sum := by decide
  have hdescent : baseEnd_2997955 < baseStart_2997955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997989 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_2997989 : Nat := 118140960795 + 2997989 * 2 ^ 59
def prefixEnd_2997989 : Nat := 4983230072969 + 3 ^ 40 * 2997989 * 2
def baseEnd_2997989 : Nat := 1026272902594784058633337

theorem tailTrace_2997989 : CollatzResearch.WordTrace tailWord_2997989 prefixEnd_2997989 1026272902594784058633337 := by
  unfold tailWord_2997989
  simp only [CollatzResearch.WordTrace]
  refine ⟨109345641935805343602653021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72897094623870229068435347 109345641935805343602653021)
  ·
    refine ⟨41004615725927003850994883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109345641935805343602653021 41004615725927003850994883)
    ·
      refine ⟨61506923588890505776492325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41004615725927003850994883 61506923588890505776492325)
      ·
        refine ⟨11532548172916969833092311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61506923588890505776492325 11532548172916969833092311)
        ·
          refine ⟨17298822259375454749638467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11532548172916969833092311 17298822259375454749638467)
          ·
            refine ⟨25948233389063182124457701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17298822259375454749638467 25948233389063182124457701)
            ·
              refine ⟨4865293760449346648335819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25948233389063182124457701 4865293760449346648335819)
              ·
                refine ⟨7297940640674019972503729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4865293760449346648335819 7297940640674019972503729)
                ·
                  refine ⟨5473455480505514979377797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7297940640674019972503729 5473455480505514979377797)
                  ·
                    refine ⟨1026272902594784058633337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5473455480505514979377797 1026272902594784058633337)
                    ·
                      rfl

theorem cell22_2997989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_2997989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997989 prefixEnd_2997989 := by exact prefixLift 2997989
  have htrace : WordTrace (prefixWord ++ tailWord_2997989) baseStart_2997989 baseEnd_2997989 := by
    simpa [prefixWord, tailWord_2997989, baseEnd_2997989] using wordTrace_append hprefix tailTrace_2997989
  have hstable : (prefixWord ++ tailWord_2997989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997989).length < 2 ^ (prefixWord ++ tailWord_2997989).sum := by decide
  have hdescent : baseEnd_2997989 < baseStart_2997989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2997991 : List Nat := [1, 1, 5, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2997991 : Nat := 118140960795 + 2997991 * 2 ^ 59
def prefixEnd_2997991 : Nat := 4983230072969 + 3 ^ 40 * 2997991 * 2
def baseEnd_2997991 : Nat := 1026273587235656720083331

theorem tailTrace_2997991 : CollatzResearch.WordTrace tailWord_2997991 prefixEnd_2997991 1026273587235656720083331 := by
  unfold tailWord_2997991
  simp only [CollatzResearch.WordTrace]
  refine ⟨109345714881798097944225827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72897143254532065296150551 109345714881798097944225827)
  ·
    refine ⟨164018572322697146916338741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109345714881798097944225827 164018572322697146916338741)
    ·
      refine ⟨15376741155252857523406757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164018572322697146916338741 15376741155252857523406757)
      ·
        refine ⟨2883138966609910785638767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15376741155252857523406757 2883138966609910785638767)
        ·
          refine ⟨4324708449914866178458151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883138966609910785638767 4324708449914866178458151)
          ·
            refine ⟨6487062674872299267687227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4324708449914866178458151 6487062674872299267687227)
            ·
              refine ⟨9730594012308448901530841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487062674872299267687227 9730594012308448901530841)
              ·
                refine ⟨7297945509231336676148131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9730594012308448901530841 7297945509231336676148131)
                ·
                  refine ⟨10946918263847005014222197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7297945509231336676148131 10946918263847005014222197)
                  ·
                    refine ⟨1026273587235656720083331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10946918263847005014222197 1026273587235656720083331)
                    ·
                      rfl

theorem cell22_2997991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2997991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2997991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2997991 prefixEnd_2997991 := by exact prefixLift 2997991
  have htrace : WordTrace (prefixWord ++ tailWord_2997991) baseStart_2997991 baseEnd_2997991 := by
    simpa [prefixWord, tailWord_2997991, baseEnd_2997991] using wordTrace_append hprefix tailTrace_2997991
  have hstable : (prefixWord ++ tailWord_2997991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2997991).length < 2 ^ (prefixWord ++ tailWord_2997991).sum := by decide
  have hdescent : baseEnd_2997991 < baseStart_2997991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2997991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998017 : List Nat := [1, 2, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2998017 : Nat := 118140960795 + 2998017 * 2 ^ 59
def prefixEnd_2998017 : Nat := 4983230072969 + 3 ^ 40 * 2998017 * 2
def baseEnd_2998017 : Nat := 1026282487567001318933251

theorem tailTrace_2998017 : CollatzResearch.WordTrace tailWord_2998017 prefixEnd_2998017 1026282487567001318933251 := by
  unfold tailWord_2998017
  simp only [CollatzResearch.WordTrace]
  refine ⟨109346663179703904384672305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72897775453135936256448203 109346663179703904384672305)
  ·
    refine ⟨82009997384777928288504229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109346663179703904384672305 82009997384777928288504229)
    ·
      refine ⟨15376874509645861554094543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82009997384777928288504229 15376874509645861554094543)
      ·
        refine ⟨23065311764468792331141815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15376874509645861554094543 23065311764468792331141815)
        ·
          refine ⟨34597967646703188496712723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23065311764468792331141815 34597967646703188496712723)
          ·
            refine ⟨51896951470054782745069085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34597967646703188496712723 51896951470054782745069085)
            ·
              refine ⟨19461356801270543529400907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51896951470054782745069085 19461356801270543529400907)
              ·
                refine ⟨29192035201905815294101361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19461356801270543529400907 29192035201905815294101361)
                ·
                  refine ⟨21894026401429361470576021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29192035201905815294101361 21894026401429361470576021)
                  ·
                    refine ⟨1026282487567001318933251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21894026401429361470576021 1026282487567001318933251)
                    ·
                      rfl

theorem cell22_2998017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2998017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998017 prefixEnd_2998017 := by exact prefixLift 2998017
  have htrace : WordTrace (prefixWord ++ tailWord_2998017) baseStart_2998017 baseEnd_2998017 := by
    simpa [prefixWord, tailWord_2998017, baseEnd_2998017] using wordTrace_append hprefix tailTrace_2998017
  have hstable : (prefixWord ++ tailWord_2998017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998017).length < 2 ^ (prefixWord ++ tailWord_2998017).sum := by decide
  have hdescent : baseEnd_2998017 < baseStart_2998017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998047 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 1, 7]
def baseStart_2998047 : Nat := 118140960795 + 2998047 * 2 ^ 59
def prefixEnd_2998047 : Nat := 4983230072969 + 3 ^ 40 * 2998047 * 2
def baseEnd_2998047 : Nat := 1026292757180091240683159

theorem tailTrace_2998047 : CollatzResearch.WordTrace tailWord_2998047 prefixEnd_2998047 1026292757180091240683159 := by
  unfold tailWord_2998047
  simp only [CollatzResearch.WordTrace]
  refine ⟨109347757369595219508264395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72898504913063479672176263 109347757369595219508264395)
  ·
    refine ⟨164021636054392829262396593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109347757369595219508264395 164021636054392829262396593)
    ·
      refine ⟨123016227040794621946797445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164021636054392829262396593 123016227040794621946797445)
      ·
        refine ⟨23065542570148991615024521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123016227040794621946797445 23065542570148991615024521)
        ·
          refine ⟨17299156927611743711268391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23065542570148991615024521 17299156927611743711268391)
          ·
            refine ⟨25948735391417615566902587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17299156927611743711268391 25948735391417615566902587)
            ·
              refine ⟨38923103087126423350353881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25948735391417615566902587 38923103087126423350353881)
              ·
                refine ⟨29192327315344817512765411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38923103087126423350353881 29192327315344817512765411)
                ·
                  refine ⟨43788490973017226269148117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29192327315344817512765411 43788490973017226269148117)
                  ·
                    refine ⟨1026292757180091240683159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43788490973017226269148117 1026292757180091240683159)
                    ·
                      rfl

theorem cell22_2998047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_2998047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998047 prefixEnd_2998047 := by exact prefixLift 2998047
  have htrace : WordTrace (prefixWord ++ tailWord_2998047) baseStart_2998047 baseEnd_2998047 := by
    simpa [prefixWord, tailWord_2998047, baseEnd_2998047] using wordTrace_append hprefix tailTrace_2998047
  have hstable : (prefixWord ++ tailWord_2998047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998047).length < 2 ^ (prefixWord ++ tailWord_2998047).sum := by decide
  have hdescent : baseEnd_2998047 < baseStart_2998047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998053 : List Nat := [1, 3, 1, 2, 3, 3, 2, 3, 1, 3]
def baseStart_2998053 : Nat := 118140960795 + 2998053 * 2 ^ 59
def prefixEnd_2998053 : Nat := 4983230072969 + 3 ^ 40 * 2998053 * 2
def baseEnd_2998053 : Nat := 1026294811102709225033141

theorem tailTrace_2998053 : CollatzResearch.WordTrace tailWord_2998053 prefixEnd_2998053 1026294811102709225033141 := by
  unfold tailWord_2998053
  simp only [CollatzResearch.WordTrace]
  refine ⟨109347976207573482532982813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72898650805048988355321875 109347976207573482532982813)
  ·
    refine ⟨41005491077840055949868555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109347976207573482532982813 41005491077840055949868555)
    ·
      refine ⟨61508236616760083924802833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41005491077840055949868555 61508236616760083924802833)
      ·
        refine ⟨46131177462570062943602125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61508236616760083924802833 46131177462570062943602125)
        ·
          refine ⟨17299191548463773603850797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46131177462570062943602125 17299191548463773603850797)
          ·
            refine ⟨6487196830673915101444049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17299191548463773603850797 6487196830673915101444049)
            ·
              refine ⟨4865397623005436326083037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6487196830673915101444049 4865397623005436326083037)
              ·
                refine ⟨1824524108627038622281139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4865397623005436326083037 1824524108627038622281139)
                ·
                  refine ⟨2736786162940557933421709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824524108627038622281139 2736786162940557933421709)
                  ·
                    refine ⟨1026294811102709225033141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2736786162940557933421709 1026294811102709225033141)
                    ·
                      rfl

theorem cell22_2998053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 3, 1, 3].length) (baseStart_2998053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998053 prefixEnd_2998053 := by exact prefixLift 2998053
  have htrace : WordTrace (prefixWord ++ tailWord_2998053) baseStart_2998053 baseEnd_2998053 := by
    simpa [prefixWord, tailWord_2998053, baseEnd_2998053] using wordTrace_append hprefix tailTrace_2998053
  have hstable : (prefixWord ++ tailWord_2998053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998053).length < 2 ^ (prefixWord ++ tailWord_2998053).sum := by decide
  have hdescent : baseEnd_2998053 < baseStart_2998053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998066 : List Nat := [3, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_2998066 : Nat := 118140960795 + 2998066 * 2 ^ 59
def prefixEnd_2998066 : Nat := 4983230072969 + 3 ^ 40 * 2998066 * 2
def baseEnd_2998066 : Nat := 342099753756127174819367

theorem tailTrace_2998066 : CollatzResearch.WordTrace tailWord_2998066 prefixEnd_2998066 342099753756127174819367 := by
  unfold tailWord_2998066
  simp only [CollatzResearch.WordTrace]
  refine ⟨27337112589131596438301513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72898966904350923835470701 27337112589131596438301513)
  ·
    refine ⟨20502834441848697328726135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27337112589131596438301513 20502834441848697328726135)
    ·
      refine ⟨30754251662773045993089203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20502834441848697328726135 30754251662773045993089203)
      ·
        refine ⟨46131377494159568989633805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30754251662773045993089203 46131377494159568989633805)
        ·
          refine ⟨17299266560309838371112677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46131377494159568989633805 17299266560309838371112677)
          ·
            refine ⟨3243612480058094694583627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17299266560309838371112677 3243612480058094694583627)
            ·
              refine ⟨4865418720087142041875441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3243612480058094694583627 4865418720087142041875441)
              ·
                refine ⟨3649064040065356531406581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4865418720087142041875441 3649064040065356531406581)
                ·
                  refine ⟨342099753756127174819367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3649064040065356531406581 342099753756127174819367)
                  ·
                    rfl

theorem cell22_2998066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_2998066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998066 prefixEnd_2998066 := by exact prefixLift 2998066
  have htrace : WordTrace (prefixWord ++ tailWord_2998066) baseStart_2998066 baseEnd_2998066 := by
    simpa [prefixWord, tailWord_2998066, baseEnd_2998066] using wordTrace_append hprefix tailTrace_2998066
  have hstable : (prefixWord ++ tailWord_2998066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998066).length < 2 ^ (prefixWord ++ tailWord_2998066).sum := by decide
  have hdescent : baseEnd_2998066 < baseStart_2998066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998070 : List Nat := [5, 1, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2998070 : Nat := 118140960795 + 2998070 * 2 ^ 59
def prefixEnd_2998070 : Nat := 4983230072969 + 3 ^ 40 * 2998070 * 2
def baseEnd_2998070 : Nat := 1026300630550126847358089

theorem tailTrace_2998070 : CollatzResearch.WordTrace tailWord_2998070 prefixEnd_2998070 1026300630550126847358089 := by
  unfold tailWord_2998070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6834287265531993402271979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72899064165674596290901109 6834287265531993402271979)
  ·
    refine ⟨10251430898297990103407969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6834287265531993402271979 10251430898297990103407969)
    ·
      refine ⟨7688573173723492577555977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10251430898297990103407969 7688573173723492577555977)
      ·
        refine ⟨5766429880292619433166983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7688573173723492577555977 5766429880292619433166983)
        ·
          refine ⟨8649644820438929149750475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5766429880292619433166983 8649644820438929149750475)
          ·
            refine ⟨12974467230658393724625713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8649644820438929149750475 12974467230658393724625713)
            ·
              refine ⟨9730850422993795293469285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12974467230658393724625713 9730850422993795293469285)
              ·
                refine ⟨1824534454311336617525491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9730850422993795293469285 1824534454311336617525491)
                ·
                  refine ⟨2736801681467004926288237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824534454311336617525491 2736801681467004926288237)
                  ·
                    refine ⟨1026300630550126847358089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2736801681467004926288237 1026300630550126847358089)
                    ·
                      rfl

theorem cell22_2998070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2998070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998070 prefixEnd_2998070 := by exact prefixLift 2998070
  have htrace : WordTrace (prefixWord ++ tailWord_2998070) baseStart_2998070 baseEnd_2998070 := by
    simpa [prefixWord, tailWord_2998070, baseEnd_2998070] using wordTrace_append hprefix tailTrace_2998070
  have hstable : (prefixWord ++ tailWord_2998070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998070).length < 2 ^ (prefixWord ++ tailWord_2998070).sum := by decide
  have hdescent : baseEnd_2998070 < baseStart_2998070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998111 : List Nat := [1, 1, 2, 3, 1, 4, 3, 3, 4]
def baseStart_2998111 : Nat := 118140960795 + 2998111 * 2 ^ 59
def prefixEnd_2998111 : Nat := 4983230072969 + 3 ^ 40 * 2998111 * 2
def baseEnd_2998111 : Nat := 342104888562672135694321

theorem tailTrace_2998111 : CollatzResearch.WordTrace tailWord_2998111 prefixEnd_2998111 342104888562672135694321 := by
  unfold tailWord_2998111
  simp only [CollatzResearch.WordTrace]
  refine ⟨109350091641363358438594187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72900061094242238959062791 109350091641363358438594187)
  ·
    refine ⟨164025137462045037657891281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109350091641363358438594187 164025137462045037657891281)
    ·
      refine ⟨123018853096533778243418461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164025137462045037657891281 123018853096533778243418461)
      ·
        refine ⟨46132069911200166841281923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123018853096533778243418461 46132069911200166841281923)
        ·
          refine ⟨69198104866800250261922885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46132069911200166841281923 69198104866800250261922885)
          ·
            refine ⟨12974644662525046924110541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69198104866800250261922885 12974644662525046924110541)
            ·
              refine ⟨4865491748446892596541453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12974644662525046924110541 4865491748446892596541453)
              ·
                refine ⟨1824559405667584723703045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4865491748446892596541453 1824559405667584723703045)
                ·
                  refine ⟨342104888562672135694321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1824559405667584723703045 342104888562672135694321)
                  ·
                    rfl

theorem cell22_2998111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 4].length) (baseStart_2998111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998111 prefixEnd_2998111 := by exact prefixLift 2998111
  have htrace : WordTrace (prefixWord ++ tailWord_2998111) baseStart_2998111 baseEnd_2998111 := by
    simpa [prefixWord, tailWord_2998111, baseEnd_2998111] using wordTrace_append hprefix tailTrace_2998111
  have hstable : (prefixWord ++ tailWord_2998111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998111).length < 2 ^ (prefixWord ++ tailWord_2998111).sum := by decide
  have hdescent : baseEnd_2998111 < baseStart_2998111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998124 : List Nat := [2, 2, 1, 1, 4, 2, 1, 1, 4, 4]
def baseStart_2998124 : Nat := 118140960795 + 2998124 * 2 ^ 59
def prefixEnd_2998124 : Nat := 4983230072969 + 3 ^ 40 * 2998124 * 2
def baseEnd_2998124 : Nat := 1026319115853688706507923

theorem tailTrace_2998124 : CollatzResearch.WordTrace tailWord_2998124 prefixEnd_2998124 1026319115853688706507923 := by
  unfold tailWord_2998124
  simp only [CollatzResearch.WordTrace]
  refine ⟨54675282895158130829408713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72900377193544174439211617 54675282895158130829408713)
  ·
    refine ⟨41006462171368598122056535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54675282895158130829408713 41006462171368598122056535)
    ·
      refine ⟨61509693257052897183084803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41006462171368598122056535 61509693257052897183084803)
      ·
        refine ⟨92264539885579345774627205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61509693257052897183084803 92264539885579345774627205)
        ·
          refine ⟨17299601228546127332742601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92264539885579345774627205 17299601228546127332742601)
          ·
            refine ⟨12974700921409595499556951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17299601228546127332742601 12974700921409595499556951)
            ·
              refine ⟨19462051382114393249335427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12974700921409595499556951 19462051382114393249335427)
              ·
                refine ⟨29193077073171589874003141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19462051382114393249335427 29193077073171589874003141)
                ·
                  refine ⟨5473701951219673101375589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29193077073171589874003141 5473701951219673101375589)
                  ·
                    refine ⟨1026319115853688706507923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5473701951219673101375589 1026319115853688706507923)
                    ·
                      rfl

theorem cell22_2998124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 4].length) (baseStart_2998124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998124 prefixEnd_2998124 := by exact prefixLift 2998124
  have htrace : WordTrace (prefixWord ++ tailWord_2998124) baseStart_2998124 baseEnd_2998124 := by
    simpa [prefixWord, tailWord_2998124, baseEnd_2998124] using wordTrace_append hprefix tailTrace_2998124
  have hstable : (prefixWord ++ tailWord_2998124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998124).length < 2 ^ (prefixWord ++ tailWord_2998124).sum := by decide
  have hdescent : baseEnd_2998124 < baseStart_2998124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998231 : List Nat := [1, 1, 3, 2, 1, 1, 5, 3, 1, 4]
def baseStart_2998231 : Nat := 118140960795 + 2998231 * 2 ^ 59
def prefixEnd_2998231 : Nat := 4983230072969 + 3 ^ 40 * 2998231 * 2
def baseEnd_2998231 : Nat := 1026355744140376094082595

theorem tailTrace_2998231 : CollatzResearch.WordTrace tailWord_2998231 prefixEnd_2998231 1026355744140376094082595 := by
  unfold tailWord_2998231
  simp only [CollatzResearch.WordTrace]
  refine ⟨109354468400928618932962547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72902978933952412621975031 109354468400928618932962547)
  ·
    refine ⟨164031702601392928399443821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109354468400928618932962547 164031702601392928399443821)
    ·
      refine ⟨61511888475522348149791433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164031702601392928399443821 61511888475522348149791433)
      ·
        refine ⟨46133916356641761112343575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61511888475522348149791433 46133916356641761112343575)
        ·
          refine ⟨69200874534962641668515363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46133916356641761112343575 69200874534962641668515363)
          ·
            refine ⟨103801311802443962502773045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69200874534962641668515363 103801311802443962502773045)
            ·
              refine ⟨9731372981479121484634973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103801311802443962502773045 9731372981479121484634973)
              ·
                refine ⟨3649264868054670556738115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9731372981479121484634973 3649264868054670556738115)
                ·
                  refine ⟨5473897302082005835107173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649264868054670556738115 5473897302082005835107173)
                  ·
                    refine ⟨1026355744140376094082595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5473897302082005835107173 1026355744140376094082595)
                    ·
                      rfl

theorem cell22_2998231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_2998231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998231 prefixEnd_2998231 := by exact prefixLift 2998231
  have htrace : WordTrace (prefixWord ++ tailWord_2998231) baseStart_2998231 baseEnd_2998231 := by
    simpa [prefixWord, tailWord_2998231, baseEnd_2998231] using wordTrace_append hprefix tailTrace_2998231
  have hstable : (prefixWord ++ tailWord_2998231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998231).length < 2 ^ (prefixWord ++ tailWord_2998231).sum := by decide
  have hdescent : baseEnd_2998231 < baseStart_2998231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998293 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_2998293 : Nat := 118140960795 + 2998293 * 2 ^ 59
def prefixEnd_2998293 : Nat := 4983230072969 + 3 ^ 40 * 2998293 * 2
def baseEnd_2998293 : Nat := 1026376968007428599032405

theorem tailTrace_2998293 : CollatzResearch.WordTrace tailWord_2998293 prefixEnd_2998293 1026376968007428599032405 := by
  unfold tailWord_2998293
  simp only [CollatzResearch.WordTrace]
  refine ⟨109356729726704003521719533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72904486484469335681146355 109356729726704003521719533)
  ·
    refine ⟨41008773647514001320644825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109356729726704003521719533 41008773647514001320644825)
    ·
      refine ⟨30756580235635500990483619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41008773647514001320644825 30756580235635500990483619)
      ·
        refine ⟨46134870353453251485725429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30756580235635500990483619 46134870353453251485725429)
        ·
          refine ⟨4325144095636242326786759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46134870353453251485725429 4325144095636242326786759)
          ·
            refine ⟨6487716143454363490180139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325144095636242326786759 6487716143454363490180139)
            ·
              refine ⟨9731574215181545235270209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487716143454363490180139 9731574215181545235270209)
              ·
                refine ⟨7298680661386158926452657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9731574215181545235270209 7298680661386158926452657)
                ·
                  refine ⟨5474010496039619194839493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7298680661386158926452657 5474010496039619194839493)
                  ·
                    refine ⟨1026376968007428599032405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5474010496039619194839493 1026376968007428599032405)
                    ·
                      rfl

theorem cell22_2998293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_2998293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998293 prefixEnd_2998293 := by exact prefixLift 2998293
  have htrace : WordTrace (prefixWord ++ tailWord_2998293) baseStart_2998293 baseEnd_2998293 := by
    simpa [prefixWord, tailWord_2998293, baseEnd_2998293] using wordTrace_append hprefix tailTrace_2998293
  have hstable : (prefixWord ++ tailWord_2998293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998293).length < 2 ^ (prefixWord ++ tailWord_2998293).sum := by decide
  have hdescent : baseEnd_2998293 < baseStart_2998293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998308 : List Nat := [2, 3, 1, 4, 2, 1, 2, 7]
def baseStart_2998308 : Nat := 118140960795 + 2998308 * 2 ^ 59
def prefixEnd_2998308 : Nat := 4983230072969 + 3 ^ 40 * 2998308 * 2
def baseEnd_2998308 : Nat := 114042455868219284434151

theorem tailTrace_2998308 : CollatzResearch.WordTrace tailWord_2998308 prefixEnd_2998308 114042455868219284434151 := by
  unfold tailWord_2998308
  simp only [CollatzResearch.WordTrace]
  refine ⟨54678638410824830541757789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72904851214433107389010385 54678638410824830541757789)
  ·
    refine ⟨20504489404059311453159171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54678638410824830541757789 20504489404059311453159171)
    ·
      refine ⟨30756734106088967179738757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20504489404059311453159171 30756734106088967179738757)
      ·
        refine ⟨5766887644891681346201017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30756734106088967179738757 5766887644891681346201017)
        ·
          refine ⟨4325165733668761009650763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5766887644891681346201017 4325165733668761009650763)
          ·
            refine ⟨6487748600503141514476145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325165733668761009650763 6487748600503141514476145)
            ·
              refine ⟨4865811450377356135857109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6487748600503141514476145 4865811450377356135857109)
              ·
                refine ⟨114042455868219284434151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4865811450377356135857109 114042455868219284434151)
                ·
                  rfl

theorem cell22_2998308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 2, 7].length) (baseStart_2998308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998308 prefixEnd_2998308 := by exact prefixLift 2998308
  have htrace : WordTrace (prefixWord ++ tailWord_2998308) baseStart_2998308 baseEnd_2998308 := by
    simpa [prefixWord, tailWord_2998308, baseEnd_2998308] using wordTrace_append hprefix tailTrace_2998308
  have hstable : (prefixWord ++ tailWord_2998308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998308).length < 2 ^ (prefixWord ++ tailWord_2998308).sum := by decide
  have hdescent : baseEnd_2998308 < baseStart_2998308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998312 : List Nat := [2, 1, 5, 3, 1, 1, 1, 3, 2, 3]
def baseStart_2998312 : Nat := 118140960795 + 2998312 * 2 ^ 59
def prefixEnd_2998312 : Nat := 4983230072969 + 3 ^ 40 * 2998312 * 2
def baseEnd_2998312 : Nat := 1026383472095718882807347

theorem tailTrace_2998312 : CollatzResearch.WordTrace tailWord_2998312 prefixEnd_2998312 1026383472095718882807347 := by
  unfold tailWord_2998312
  simp only [CollatzResearch.WordTrace]
  refine ⟨54678711356817584883330595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72904948475756779844440793 54678711356817584883330595)
  ·
    refine ⟨82018067035226377324995893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54678711356817584883330595 82018067035226377324995893)
    ·
      refine ⟨7689193784552472874218365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82018067035226377324995893 7689193784552472874218365)
      ·
        refine ⟨2883447669207177327831887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7689193784552472874218365 2883447669207177327831887)
        ·
          refine ⟨4325171503810765991747831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883447669207177327831887 4325171503810765991747831)
          ·
            refine ⟨6487757255716148987621747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325171503810765991747831 6487757255716148987621747)
            ·
              refine ⟨9731635883574223481432621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6487757255716148987621747 9731635883574223481432621)
              ·
                refine ⟨3649363456340333805537233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9731635883574223481432621 3649363456340333805537233)
                ·
                  refine ⟨2737022592255250354152925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3649363456340333805537233 2737022592255250354152925)
                  ·
                    refine ⟨1026383472095718882807347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737022592255250354152925 1026383472095718882807347)
                    ·
                      rfl

theorem cell22_2998312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_2998312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998312 prefixEnd_2998312 := by exact prefixLift 2998312
  have htrace : WordTrace (prefixWord ++ tailWord_2998312) baseStart_2998312 baseEnd_2998312 := by
    simpa [prefixWord, tailWord_2998312, baseEnd_2998312] using wordTrace_append hprefix tailTrace_2998312
  have hstable : (prefixWord ++ tailWord_2998312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998312).length < 2 ^ (prefixWord ++ tailWord_2998312).sum := by decide
  have hdescent : baseEnd_2998312 < baseStart_2998312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998319 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 9]
def baseStart_2998319 : Nat := 118140960795 + 2998319 * 2 ^ 59
def prefixEnd_2998319 : Nat := 4983230072969 + 3 ^ 40 * 2998319 * 2
def baseEnd_2998319 : Nat := 342128622779591065960775

theorem tailTrace_2998319 : CollatzResearch.WordTrace tailWord_2998319 prefixEnd_2998319 342128622779591065960775 := by
  unfold tailWord_2998319
  simp only [CollatzResearch.WordTrace]
  refine ⟨109357678024609809962166011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72905118683073206641444007 109357678024609809962166011)
  ·
    refine ⟨164036517036914714943249017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109357678024609809962166011 164036517036914714943249017)
    ·
      refine ⟨123027387777686036207436763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164036517036914714943249017 123027387777686036207436763)
      ·
        refine ⟨184541081666529054311155145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123027387777686036207436763 184541081666529054311155145)
        ·
          refine ⟨138405811249896790733366359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184541081666529054311155145 138405811249896790733366359)
          ·
            refine ⟨207608716874845186100049539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138405811249896790733366359 207608716874845186100049539)
            ·
              refine ⟨311413075312267779150074309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207608716874845186100049539 311413075312267779150074309)
              ·
                refine ⟨58389951621050208590638933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 311413075312267779150074309 58389951621050208590638933)
                ·
                  refine ⟨342128622779591065960775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58389951621050208590638933 342128622779591065960775)
                  ·
                    rfl

theorem cell22_2998319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 9].length) (baseStart_2998319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998319 prefixEnd_2998319 := by exact prefixLift 2998319
  have htrace : WordTrace (prefixWord ++ tailWord_2998319) baseStart_2998319 baseEnd_2998319 := by
    simpa [prefixWord, tailWord_2998319, baseEnd_2998319] using wordTrace_append hprefix tailTrace_2998319
  have hstable : (prefixWord ++ tailWord_2998319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998319).length < 2 ^ (prefixWord ++ tailWord_2998319).sum := by decide
  have hdescent : baseEnd_2998319 < baseStart_2998319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998357 : List Nat := [1, 3, 2, 2, 1, 3, 4, 2, 1, 3]
def baseStart_2998357 : Nat := 118140960795 + 2998357 * 2 ^ 59
def prefixEnd_2998357 : Nat := 4983230072969 + 3 ^ 40 * 2998357 * 2
def baseEnd_2998357 : Nat := 1026398876515353765432209

theorem tailTrace_2998357 : CollatzResearch.WordTrace tailWord_2998357 prefixEnd_2998357 1026398876515353765432209 := by
  unfold tailWord_2998357
  simp only [CollatzResearch.WordTrace]
  refine ⟨109359063998472142452049325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72906042665648094968032883 109359063998472142452049325)
  ·
    refine ⟨41009648999427053419518497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109359063998472142452049325 41009648999427053419518497)
    ·
      refine ⟨30757236749570290064638873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41009648999427053419518497 30757236749570290064638873)
      ·
        refine ⟨23067927562177717548479155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30757236749570290064638873 23067927562177717548479155)
        ·
          refine ⟨34601891343266576322718733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23067927562177717548479155 34601891343266576322718733)
          ·
            refine ⟨12975709253724966121019525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34601891343266576322718733 12975709253724966121019525)
            ·
              refine ⟨2432945485073431147691161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12975709253724966121019525 2432945485073431147691161)
              ·
                refine ⟨1824709113805073360768371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2432945485073431147691161 1824709113805073360768371)
                ·
                  refine ⟨2737063670707610041152557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824709113805073360768371 2737063670707610041152557)
                  ·
                    refine ⟨1026398876515353765432209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737063670707610041152557 1026398876515353765432209)
                    ·
                      rfl

theorem cell22_2998357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_2998357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998357 prefixEnd_2998357 := by exact prefixLift 2998357
  have htrace : WordTrace (prefixWord ++ tailWord_2998357) baseStart_2998357 baseEnd_2998357 := by
    simpa [prefixWord, tailWord_2998357, baseEnd_2998357] using wordTrace_append hprefix tailTrace_2998357
  have hstable : (prefixWord ++ tailWord_2998357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998357).length < 2 ^ (prefixWord ++ tailWord_2998357).sum := by decide
  have hdescent : baseEnd_2998357 < baseStart_2998357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998449 : List Nat := [1, 2, 2, 5, 3, 1, 1, 3, 4]
def baseStart_2998449 : Nat := 118140960795 + 2998449 * 2 ^ 59
def prefixEnd_2998449 : Nat := 4983230072969 + 3 ^ 40 * 2998449 * 2
def baseEnd_2998449 : Nat := 342143456665165397377309

theorem tailTrace_2998449 : CollatzResearch.WordTrace tailWord_2998449 prefixEnd_2998449 342143456665165397377309 := by
  unfold tailWord_2998449
  simp only [CollatzResearch.WordTrace]
  refine ⟨109362419514138842164398401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72908279676092561442932267 109362419514138842164398401)
  ·
    refine ⟨82021814635604131623298801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109362419514138842164398401 82021814635604131623298801)
    ·
      refine ⟨61516360976703098717474101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82021814635604131623298801 61516360976703098717474101)
      ·
        refine ⟨5767158841565915504763197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61516360976703098717474101 5767158841565915504763197)
        ·
          refine ⟨2162684565587218314286199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5767158841565915504763197 2162684565587218314286199)
          ·
            refine ⟨3244026848380827471429299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162684565587218314286199 3244026848380827471429299)
            ·
              refine ⟨4866040272571241207143949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244026848380827471429299 4866040272571241207143949)
              ·
                refine ⟨1824765102214215452678981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4866040272571241207143949 1824765102214215452678981)
                ·
                  refine ⟨342143456665165397377309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1824765102214215452678981 342143456665165397377309)
                  ·
                    rfl

theorem cell22_2998449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 4].length) (baseStart_2998449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998449 prefixEnd_2998449 := by exact prefixLift 2998449
  have htrace : WordTrace (prefixWord ++ tailWord_2998449) baseStart_2998449 baseEnd_2998449 := by
    simpa [prefixWord, tailWord_2998449, baseEnd_2998449] using wordTrace_append hprefix tailTrace_2998449
  have hstable : (prefixWord ++ tailWord_2998449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998449).length < 2 ^ (prefixWord ++ tailWord_2998449).sum := by decide
  have hdescent : baseEnd_2998449 < baseStart_2998449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998458 : List Nat := [3, 1, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_2998458 : Nat := 118140960795 + 2998458 * 2 ^ 59
def prefixEnd_2998458 : Nat := 4983230072969 + 3 ^ 40 * 2998458 * 2
def baseEnd_2998458 : Nat := 1026433450879423168656899

theorem tailTrace_2998458 : CollatzResearch.WordTrace tailWord_2998458 prefixEnd_2998458 1026433450879423168656899 := by
  unfold tailWord_2998458
  simp only [CollatzResearch.WordTrace]
  refine ⟨27340686942776559175369007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72908498514070824467650685 27340686942776559175369007)
  ·
    refine ⟨41011030414164838763053511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27340686942776559175369007 41011030414164838763053511)
    ·
      refine ⟨61516545621247258144580267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41011030414164838763053511 61516545621247258144580267)
      ·
        refine ⟨92274818431870887216870401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61516545621247258144580267 92274818431870887216870401)
        ·
          refine ⟨69206113823903165412652801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92274818431870887216870401 69206113823903165412652801)
          ·
            refine ⟨51904585367927374059489601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69206113823903165412652801 51904585367927374059489601)
            ·
              refine ⟨38928439025945530544617201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51904585367927374059489601 38928439025945530544617201)
              ·
                refine ⟨29196329269459147908462901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38928439025945530544617201 29196329269459147908462901)
                ·
                  refine ⟨2737155869011795116418397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29196329269459147908462901 2737155869011795116418397)
                  ·
                    refine ⟨1026433450879423168656899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737155869011795116418397 1026433450879423168656899)
                    ·
                      rfl

theorem cell22_2998458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_2998458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998458 prefixEnd_2998458 := by exact prefixLift 2998458
  have htrace : WordTrace (prefixWord ++ tailWord_2998458) baseStart_2998458 baseEnd_2998458 := by
    simpa [prefixWord, tailWord_2998458, baseEnd_2998458] using wordTrace_append hprefix tailTrace_2998458
  have hstable : (prefixWord ++ tailWord_2998458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998458).length < 2 ^ (prefixWord ++ tailWord_2998458).sum := by decide
  have hdescent : baseEnd_2998458 < baseStart_2998458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998460 : List Nat := [2, 2, 2, 3, 4, 1, 8]
def baseStart_2998460 : Nat := 118140960795 + 2998460 * 2 ^ 59
def prefixEnd_2998460 : Nat := 4983230072969 + 3 ^ 40 * 2998460 * 2
def baseEnd_2998460 : Nat := 38016079093344290003959

theorem tailTrace_2998460 : CollatzResearch.WordTrace tailWord_2998460 prefixEnd_2998460 38016079093344290003959 := by
  unfold tailWord_2998460
  simp only [CollatzResearch.WordTrace]
  refine ⟨54681410358549495521524417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72908547144732660695365889 54681410358549495521524417)
  ·
    refine ⟨41011057768912121641143313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54681410358549495521524417 41011057768912121641143313)
    ·
      refine ⟨30758293326684091230857485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41011057768912121641143313 30758293326684091230857485)
      ·
        refine ⟨11534359997506534211571557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30758293326684091230857485 11534359997506534211571557)
        ·
          refine ⟨2162692499532475164669667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11534359997506534211571557 2162692499532475164669667)
          ·
            refine ⟨3244038749298712747004501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2162692499532475164669667 3244038749298712747004501)
            ·
              refine ⟨38016079093344290003959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3244038749298712747004501 38016079093344290003959)
              ·
                rfl

theorem cell22_2998460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 8].length) (baseStart_2998460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998460 prefixEnd_2998460 := by exact prefixLift 2998460
  have htrace : WordTrace (prefixWord ++ tailWord_2998460) baseStart_2998460 baseEnd_2998460 := by
    simpa [prefixWord, tailWord_2998460, baseEnd_2998460] using wordTrace_append hprefix tailTrace_2998460
  have hstable : (prefixWord ++ tailWord_2998460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998460).length < 2 ^ (prefixWord ++ tailWord_2998460).sum := by decide
  have hdescent : baseEnd_2998460 < baseStart_2998460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998466 : List Nat := [3, 5, 1, 1, 1, 2, 3, 2, 4]
def baseStart_2998466 : Nat := 118140960795 + 2998466 * 2 ^ 59
def prefixEnd_2998466 : Nat := 4983230072969 + 3 ^ 40 * 2998466 * 2
def baseEnd_2998466 : Nat := 342145396480971271485625

theorem tailTrace_2998466 : CollatzResearch.WordTrace tailWord_2998466 prefixEnd_2998466 342145396480971271485625 := by
  unfold tailWord_2998466
  simp only [CollatzResearch.WordTrace]
  refine ⟨27340759888769313516941813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72908693036718169378511501 27340759888769313516941813)
  ·
    refine ⟨2563196239572123142213295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27340759888769313516941813 2563196239572123142213295)
    ·
      refine ⟨3844794359358184713319943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2563196239572123142213295 3844794359358184713319943)
      ·
        refine ⟨5767191539037277069979915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3844794359358184713319943 5767191539037277069979915)
        ·
          refine ⟨8650787308555915604969873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5767191539037277069979915 8650787308555915604969873)
          ·
            refine ⟨6488090481416936703727405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8650787308555915604969873 6488090481416936703727405)
            ·
              refine ⟨2433033930531351263897777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6488090481416936703727405 2433033930531351263897777)
              ·
                refine ⟨1824775447898513447923333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2433033930531351263897777 1824775447898513447923333)
                ·
                  refine ⟨342145396480971271485625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1824775447898513447923333 342145396480971271485625)
                  ·
                    rfl

theorem cell22_2998466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_2998466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998466 prefixEnd_2998466 := by exact prefixLift 2998466
  have htrace : WordTrace (prefixWord ++ tailWord_2998466) baseStart_2998466 baseEnd_2998466 := by
    simpa [prefixWord, tailWord_2998466, baseEnd_2998466] using wordTrace_append hprefix tailTrace_2998466
  have hstable : (prefixWord ++ tailWord_2998466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998466).length < 2 ^ (prefixWord ++ tailWord_2998466).sum := by decide
  have hdescent : baseEnd_2998466 < baseStart_2998466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998563 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 1, 6]
def baseStart_2998563 : Nat := 118140960795 + 2998563 * 2 ^ 59
def prefixEnd_2998563 : Nat := 4983230072969 + 3 ^ 40 * 2998563 * 2
def baseEnd_2998563 : Nat := 1026469394525237894781577

theorem tailTrace_2998563 : CollatzResearch.WordTrace tailWord_2998563 prefixEnd_2998563 1026469394525237894781577 := by
  unfold tailWord_2998563
  simp only [CollatzResearch.WordTrace]
  refine ⟨109366577435725839634048343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72911051623817226422698895 109366577435725839634048343)
  ·
    refine ⟨164049866153588759451072515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109366577435725839634048343 164049866153588759451072515)
    ·
      refine ⟨246074799230383139176608773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164049866153588759451072515 246074799230383139176608773)
      ·
        refine ⟨46139024855696838595614145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246074799230383139176608773 46139024855696838595614145)
        ·
          refine ⟨34604268641772628946710609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46139024855696838595614145 34604268641772628946710609)
          ·
            refine ⟨25953201481329471710032957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34604268641772628946710609 25953201481329471710032957)
            ·
              refine ⟨9732450555498551891262359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25953201481329471710032957 9732450555498551891262359)
              ·
                refine ⟨14598675833247827836893539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9732450555498551891262359 14598675833247827836893539)
                ·
                  refine ⟨21898013749871741755340309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14598675833247827836893539 21898013749871741755340309)
                  ·
                    refine ⟨1026469394525237894781577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21898013749871741755340309 1026469394525237894781577)
                    ·
                      rfl

theorem cell22_2998563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_2998563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998563 prefixEnd_2998563 := by exact prefixLift 2998563
  have htrace : WordTrace (prefixWord ++ tailWord_2998563) baseStart_2998563 baseEnd_2998563 := by
    simpa [prefixWord, tailWord_2998563, baseEnd_2998563] using wordTrace_append hprefix tailTrace_2998563
  have hstable : (prefixWord ++ tailWord_2998563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998563).length < 2 ^ (prefixWord ++ tailWord_2998563).sum := by decide
  have hdescent : baseEnd_2998563 < baseStart_2998563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998612 : List Nat := [2, 4, 1, 1, 2, 4, 2, 6]
def baseStart_2998612 : Nat := 118140960795 + 2998612 * 2 ^ 59
def prefixEnd_2998612 : Nat := 4983230072969 + 3 ^ 40 * 2998612 * 2
def baseEnd_2998612 : Nat := 114054018691846455589603

theorem tailTrace_2998612 : CollatzResearch.WordTrace tailWord_2998612 prefixEnd_2998612 114054018691846455589603 := by
  unfold tailWord_2998612
  simp only [CollatzResearch.WordTrace]
  refine ⟨54684182306274160501291045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72912243075032214001721393 54684182306274160501291045)
  ·
    refine ⟨10253284182426405093992071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54684182306274160501291045 10253284182426405093992071)
    ·
      refine ⟨15379926273639607640988107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10253284182426405093992071 15379926273639607640988107)
      ·
        refine ⟨23069889410459411461482161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15379926273639607640988107 23069889410459411461482161)
        ·
          refine ⟨17302417057844558596111621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23069889410459411461482161 17302417057844558596111621)
          ·
            refine ⟨3244203198345854736770929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17302417057844558596111621 3244203198345854736770929)
            ·
              refine ⟨2433152398759391052578197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244203198345854736770929 2433152398759391052578197)
              ·
                refine ⟨114054018691846455589603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2433152398759391052578197 114054018691846455589603)
                ·
                  rfl

theorem cell22_2998612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 2, 6].length) (baseStart_2998612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998612 prefixEnd_2998612 := by exact prefixLift 2998612
  have htrace : WordTrace (prefixWord ++ tailWord_2998612) baseStart_2998612 baseEnd_2998612 := by
    simpa [prefixWord, tailWord_2998612, baseEnd_2998612] using wordTrace_append hprefix tailTrace_2998612
  have hstable : (prefixWord ++ tailWord_2998612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998612).length < 2 ^ (prefixWord ++ tailWord_2998612).sum := by decide
  have hdescent : baseEnd_2998612 < baseStart_2998612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998623 : List Nat := [1, 1, 2, 3, 1, 2, 3, 2, 7]
def baseStart_2998623 : Nat := 118140960795 + 2998623 * 2 ^ 59
def prefixEnd_2998623 : Nat := 4983230072969 + 3 ^ 40 * 2998623 * 2
def baseEnd_2998623 : Nat := 342163311250472579427131

theorem tailTrace_2998623 : CollatzResearch.WordTrace tailWord_2998623 prefixEnd_2998623 342163311250472579427131 := by
  unfold tailWord_2998623
  simp only [CollatzResearch.WordTrace]
  refine ⟨109368765815508469881232523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72912510543672313254155015 109368765815508469881232523)
  ·
    refine ⟨164053148723262704821848785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109368765815508469881232523 164053148723262704821848785)
    ·
      refine ⟨123039861542447028616386589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164053148723262704821848785 123039861542447028616386589)
      ·
        refine ⟨46139948078417635731144971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123039861542447028616386589 46139948078417635731144971)
        ·
          refine ⟨69209922117626453596717457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46139948078417635731144971 69209922117626453596717457)
          ·
            refine ⟨51907441588219840197538093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69209922117626453596717457 51907441588219840197538093)
            ·
              refine ⟨19465290595582440074076785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51907441588219840197538093 19465290595582440074076785)
              ·
                refine ⟨14598967946686830055557589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19465290595582440074076785 14598967946686830055557589)
                ·
                  refine ⟨342163311250472579427131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14598967946686830055557589 342163311250472579427131)
                  ·
                    rfl

theorem cell22_2998623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 7].length) (baseStart_2998623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998623 prefixEnd_2998623 := by exact prefixLift 2998623
  have htrace : WordTrace (prefixWord ++ tailWord_2998623) baseStart_2998623 baseEnd_2998623 := by
    simpa [prefixWord, tailWord_2998623, baseEnd_2998623] using wordTrace_append hprefix tailTrace_2998623
  have hstable : (prefixWord ++ tailWord_2998623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998623).length < 2 ^ (prefixWord ++ tailWord_2998623).sum := by decide
  have hdescent : baseEnd_2998623 < baseStart_2998623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998657 : List Nat := [1, 2, 4, 3, 1, 2, 1, 3, 5]
def baseStart_2998657 : Nat := 118140960795 + 2998657 * 2 ^ 59
def prefixEnd_2998657 : Nat := 4983230072969 + 3 ^ 40 * 2998657 * 2
def baseEnd_2998657 : Nat := 342167190882084327643763

theorem tailTrace_2998657 : CollatzResearch.WordTrace tailWord_2998657 prefixEnd_2998657 342167190882084327643763 := by
  unfold tailWord_2998657
  simp only [CollatzResearch.WordTrace]
  refine ⟨109370005897385293687970225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72913337264923529125313483 109370005897385293687970225)
  ·
    refine ⟨82027504423038970265977669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109370005897385293687970225 82027504423038970265977669)
    ·
      refine ⟨15380157079319806924870813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82027504423038970265977669 15380157079319806924870813)
      ·
        refine ⟨5767558904744927596826555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15380157079319806924870813 5767558904744927596826555)
        ·
          refine ⟨8651338357117391395239833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5767558904744927596826555 8651338357117391395239833)
          ·
            refine ⟨6488503767838043546429875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8651338357117391395239833 6488503767838043546429875)
            ·
              refine ⟨9732755651757065319644813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488503767838043546429875 9732755651757065319644813)
              ·
                refine ⟨3649783369408899494866805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9732755651757065319644813 3649783369408899494866805)
                ·
                  refine ⟨342167190882084327643763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3649783369408899494866805 342167190882084327643763)
                  ·
                    rfl

theorem cell22_2998657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_2998657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998657 prefixEnd_2998657 := by exact prefixLift 2998657
  have htrace : WordTrace (prefixWord ++ tailWord_2998657) baseStart_2998657 baseEnd_2998657 := by
    simpa [prefixWord, tailWord_2998657, baseEnd_2998657] using wordTrace_append hprefix tailTrace_2998657
  have hstable : (prefixWord ++ tailWord_2998657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998657).length < 2 ^ (prefixWord ++ tailWord_2998657).sum := by decide
  have hdescent : baseEnd_2998657 < baseStart_2998657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998717 : List Nat := [1, 4, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2998717 : Nat := 118140960795 + 2998717 * 2 ^ 59
def prefixEnd_2998717 : Nat := 4983230072969 + 3 ^ 40 * 2998717 * 2
def baseEnd_2998717 : Nat := 1026522111872432826431105

theorem tailTrace_2998717 : CollatzResearch.WordTrace tailWord_2998717 prefixEnd_2998717 1026522111872432826431105 := by
  unfold tailWord_2998717
  simp only [CollatzResearch.WordTrace]
  refine ⟨109372194277167923935154405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72914796184778615956769603 109372194277167923935154405)
  ·
    refine ⟨20507286426968985737841451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109372194277167923935154405 20507286426968985737841451)
    ·
      refine ⟨30760929640453478606762177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20507286426968985737841451 30760929640453478606762177)
      ·
        refine ⟨23070697230340108955071633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30760929640453478606762177 23070697230340108955071633)
        ·
          refine ⟨17303022922755081716303725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23070697230340108955071633 17303022922755081716303725)
          ·
            refine ⟨6488633596033155643613897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17303022922755081716303725 6488633596033155643613897)
            ·
              refine ⟨4866475197024866732710423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6488633596033155643613897 4866475197024866732710423)
              ·
                refine ⟨7299712795537300099065635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866475197024866732710423 7299712795537300099065635)
                ·
                  refine ⟨10949569193305950148598453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7299712795537300099065635 10949569193305950148598453)
                  ·
                    refine ⟨1026522111872432826431105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10949569193305950148598453 1026522111872432826431105)
                    ·
                      rfl

theorem cell22_2998717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2998717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998717 prefixEnd_2998717 := by exact prefixLift 2998717
  have htrace : WordTrace (prefixWord ++ tailWord_2998717) baseStart_2998717 baseEnd_2998717 := by
    simpa [prefixWord, tailWord_2998717, baseEnd_2998717] using wordTrace_append hprefix tailTrace_2998717
  have hstable : (prefixWord ++ tailWord_2998717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998717).length < 2 ^ (prefixWord ++ tailWord_2998717).sum := by decide
  have hdescent : baseEnd_2998717 < baseStart_2998717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998732 : List Nat := [2, 2, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_2998732 : Nat := 118140960795 + 2998732 * 2 ^ 59
def prefixEnd_2998732 : Nat := 4983230072969 + 3 ^ 40 * 2998732 * 2
def baseEnd_2998732 : Nat := 1026527246678977787306059

theorem tailTrace_2998732 : CollatzResearch.WordTrace tailWord_2998732 prefixEnd_2998732 1026527246678977787306059 := by
  unfold tailWord_2998732
  simp only [CollatzResearch.WordTrace]
  refine ⟨54686370686056790748475225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72915160914742387664633633 54686370686056790748475225)
  ·
    refine ⟨41014778014542593061356419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54686370686056790748475225 41014778014542593061356419)
    ·
      refine ⟨61522167021813889592034629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41014778014542593061356419 61522167021813889592034629)
      ·
        refine ⟨11535406316590104298506493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61522167021813889592034629 11535406316590104298506493)
        ·
          refine ⟨4325777368721289111939935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11535406316590104298506493 4325777368721289111939935)
          ·
            refine ⟨6488666053081933667909903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4325777368721289111939935 6488666053081933667909903)
            ·
              refine ⟨9732999079622900501864855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6488666053081933667909903 9732999079622900501864855)
              ·
                refine ⟨14599498619434350752797283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9732999079622900501864855 14599498619434350752797283)
                ·
                  refine ⟨21899247929151526129195925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14599498619434350752797283 21899247929151526129195925)
                  ·
                    refine ⟨1026527246678977787306059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21899247929151526129195925 1026527246678977787306059)
                    ·
                      rfl

theorem cell22_2998732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_2998732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998732 prefixEnd_2998732 := by exact prefixLift 2998732
  have htrace : WordTrace (prefixWord ++ tailWord_2998732) baseStart_2998732 baseEnd_2998732 := by
    simpa [prefixWord, tailWord_2998732, baseEnd_2998732] using wordTrace_append hprefix tailTrace_2998732
  have hstable : (prefixWord ++ tailWord_2998732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998732).length < 2 ^ (prefixWord ++ tailWord_2998732).sum := by decide
  have hdescent : baseEnd_2998732 < baseStart_2998732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998738 : List Nat := [3, 2, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_2998738 : Nat := 118140960795 + 2998738 * 2 ^ 59
def prefixEnd_2998738 : Nat := 4983230072969 + 3 ^ 40 * 2998738 * 2
def baseEnd_2998738 : Nat := 1026529300601595771656041

theorem tailTrace_2998738 : CollatzResearch.WordTrace tailWord_2998738 prefixEnd_2998738 1026529300601595771656041 := by
  unfold tailWord_2998738
  simp only [CollatzResearch.WordTrace]
  refine ⟨27343240052522961130417217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72915306806727896347779245 27343240052522961130417217)
  ·
    refine ⟨20507430039392220847812913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27343240052522961130417217 20507430039392220847812913)
    ·
      refine ⟨15380572529544165635859685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20507430039392220847812913 15380572529544165635859685)
      ·
        refine ⟨2883857349289531056723691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15380572529544165635859685 2883857349289531056723691)
        ·
          refine ⟨4325786023934296585085537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2883857349289531056723691 4325786023934296585085537)
          ·
            refine ⟨3244339517950722438814153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4325786023934296585085537 3244339517950722438814153)
            ·
              refine ⟨2433254638463041829110615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244339517950722438814153 2433254638463041829110615)
              ·
                refine ⟨3649881957694562743665923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433254638463041829110615 3649881957694562743665923)
                ·
                  refine ⟨5474822936541844115498885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3649881957694562743665923 5474822936541844115498885)
                  ·
                    refine ⟨1026529300601595771656041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5474822936541844115498885 1026529300601595771656041)
                    ·
                      rfl

theorem cell22_2998738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_2998738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998738 prefixEnd_2998738 := by exact prefixLift 2998738
  have htrace : WordTrace (prefixWord ++ tailWord_2998738) baseStart_2998738 baseEnd_2998738 := by
    simpa [prefixWord, tailWord_2998738, baseEnd_2998738] using wordTrace_append hprefix tailTrace_2998738
  have hstable : (prefixWord ++ tailWord_2998738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998738).length < 2 ^ (prefixWord ++ tailWord_2998738).sum := by decide
  have hdescent : baseEnd_2998738 < baseStart_2998738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998796 : List Nat := [2, 2, 1, 2, 4, 1, 3, 3, 1, 3]
def baseStart_2998796 : Nat := 118140960795 + 2998796 * 2 ^ 59
def prefixEnd_2998796 : Nat := 4983230072969 + 3 ^ 40 * 2998796 * 2
def baseEnd_2998796 : Nat := 1026549155186902953705863

theorem tailTrace_2998796 : CollatzResearch.WordTrace tailWord_2998796 prefixEnd_2998796 1026549155186902953705863 := by
  unfold tailWord_2998796
  simp only [CollatzResearch.WordTrace]
  refine ⟨54687537821940860213640121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72916717095921146951520161 54687537821940860213640121)
  ·
    refine ⟨41015653366455645160230091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54687537821940860213640121 41015653366455645160230091)
    ·
      refine ⟨61523480049683467740345137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41015653366455645160230091 61523480049683467740345137)
      ·
        refine ⟨46142610037262600805258853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61523480049683467740345137 46142610037262600805258853)
        ·
          refine ⟨8651739381986737650986035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46142610037262600805258853 8651739381986737650986035)
          ·
            refine ⟨12977609072980106476479053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8651739381986737650986035 12977609072980106476479053)
            ·
              refine ⟨4866603402367539928679645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12977609072980106476479053 4866603402367539928679645)
              ·
                refine ⟨1824976275887827473254867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4866603402367539928679645 1824976275887827473254867)
                ·
                  refine ⟨2737464413831741209882301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824976275887827473254867 2737464413831741209882301)
                  ·
                    refine ⟨1026549155186902953705863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737464413831741209882301 1026549155186902953705863)
                    ·
                      rfl

theorem cell22_2998796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_2998796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998796 prefixEnd_2998796 := by exact prefixLift 2998796
  have htrace : WordTrace (prefixWord ++ tailWord_2998796) baseStart_2998796 baseEnd_2998796 := by
    simpa [prefixWord, tailWord_2998796, baseEnd_2998796] using wordTrace_append hprefix tailTrace_2998796
  have hstable : (prefixWord ++ tailWord_2998796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998796).length < 2 ^ (prefixWord ++ tailWord_2998796).sum := by decide
  have hdescent : baseEnd_2998796 < baseStart_2998796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998813 : List Nat := [1, 4, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2998813 : Nat := 118140960795 + 2998813 * 2 ^ 59
def prefixEnd_2998813 : Nat := 4983230072969 + 3 ^ 40 * 2998813 * 2
def baseEnd_2998813 : Nat := 1026554974634320576030811

theorem tailTrace_2998813 : CollatzResearch.WordTrace tailWord_2998813 prefixEnd_2998813 1026554974634320576030811 := by
  unfold tailWord_2998813
  simp only [CollatzResearch.WordTrace]
  refine ⟨109375695684820132330649093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72917130456546754887099395 109375695684820132330649093)
  ·
    refine ⟨20507942940903774811996705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109375695684820132330649093 20507942940903774811996705)
    ·
      refine ⟨15380957205677831108997529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20507942940903774811996705 15380957205677831108997529)
      ·
        refine ⟨11535717904258373331748147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15380957205677831108997529 11535717904258373331748147)
        ·
          refine ⟨17303576856387559997622221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11535717904258373331748147 17303576856387559997622221)
          ·
            refine ⟨6488841321145334999108333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17303576856387559997622221 6488841321145334999108333)
            ·
              refine ⟨2433315495429500624665625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6488841321145334999108333 2433315495429500624665625)
              ·
                refine ⟨1824986621572125468499219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2433315495429500624665625 1824986621572125468499219)
                ·
                  refine ⟨2737479932358188202748829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1824986621572125468499219 2737479932358188202748829)
                  ·
                    refine ⟨1026554974634320576030811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737479932358188202748829 1026554974634320576030811)
                    ·
                      rfl

theorem cell22_2998813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2998813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998813 prefixEnd_2998813 := by exact prefixLift 2998813
  have htrace : WordTrace (prefixWord ++ tailWord_2998813) baseStart_2998813 baseEnd_2998813 := by
    simpa [prefixWord, tailWord_2998813, baseEnd_2998813] using wordTrace_append hprefix tailTrace_2998813
  have hstable : (prefixWord ++ tailWord_2998813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998813).length < 2 ^ (prefixWord ++ tailWord_2998813).sum := by decide
  have hdescent : baseEnd_2998813 < baseStart_2998813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998826 : List Nat := [3, 1, 4, 1, 1, 4, 2, 1, 5]
def baseStart_2998826 : Nat := 118140960795 + 2998826 * 2 ^ 59
def prefixEnd_2998826 : Nat := 4983230072969 + 3 ^ 40 * 2998826 * 2
def baseEnd_2998826 : Nat := 342186474933330958485257

theorem tailTrace_2998826 : CollatzResearch.WordTrace tailWord_2998826 prefixEnd_2998826 342186474933330958485257 := by
  unfold tailWord_2998826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27344042458443258887718083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72917446555848690367248221 27344042458443258887718083)
  ·
    refine ⟨41016063687664888331577125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27344042458443258887718083 41016063687664888331577125)
    ·
      refine ⟨7690511941437166562170711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41016063687664888331577125 7690511941437166562170711)
      ·
        refine ⟨11535767912155749843256067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7690511941437166562170711 11535767912155749843256067)
        ·
          refine ⟨17303651868233624764884101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11535767912155749843256067 17303651868233624764884101)
          ·
            refine ⟨3244434725293804643415769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17303651868233624764884101 3244434725293804643415769)
            ·
              refine ⟨2433326043970353482561827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3244434725293804643415769 2433326043970353482561827)
              ·
                refine ⟨3649989065955530223842741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433326043970353482561827 3649989065955530223842741)
                ·
                  refine ⟨342186474933330958485257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3649989065955530223842741 342186474933330958485257)
                  ·
                    rfl

theorem cell22_2998826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_2998826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998826 prefixEnd_2998826 := by exact prefixLift 2998826
  have htrace : WordTrace (prefixWord ++ tailWord_2998826) baseStart_2998826 baseEnd_2998826 := by
    simpa [prefixWord, tailWord_2998826, baseEnd_2998826] using wordTrace_append hprefix tailTrace_2998826
  have hstable : (prefixWord ++ tailWord_2998826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998826).length < 2 ^ (prefixWord ++ tailWord_2998826).sum := by decide
  have hdescent : baseEnd_2998826 < baseStart_2998826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998865 : List Nat := [1, 2, 2, 1, 3, 13]
def baseStart_2998865 : Nat := 118140960795 + 2998865 * 2 ^ 59
def prefixEnd_2998865 : Nat := 4983230072969 + 3 ^ 40 * 2998865 * 2
def baseEnd_2998865 : Nat := 12673737966629750292971

theorem tailTrace_2998865 : CollatzResearch.WordTrace tailWord_2998865 prefixEnd_2998865 12673737966629750292971 := by
  unfold tailWord_2998865
  simp only [CollatzResearch.WordTrace]
  refine ⟨109377592280631745211542049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72918394853754496807694699 109377592280631745211542049)
  ·
    refine ⟨82033194210473808908656537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109377592280631745211542049 82033194210473808908656537)
    ·
      refine ⟨61524895657855356681492403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82033194210473808908656537 61524895657855356681492403)
      ·
        refine ⟨92287343486783035022238605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61524895657855356681492403 92287343486783035022238605)
        ·
          refine ⟨34607753807543638133339477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92287343486783035022238605 34607753807543638133339477)
          ·
            refine ⟨12673737966629750292971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 34607753807543638133339477 12673737966629750292971)
            ·
              rfl

theorem cell22_2998865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 13].length) (baseStart_2998865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998865 prefixEnd_2998865 := by exact prefixLift 2998865
  have htrace : WordTrace (prefixWord ++ tailWord_2998865) baseStart_2998865 baseEnd_2998865 := by
    simpa [prefixWord, tailWord_2998865, baseEnd_2998865] using wordTrace_append hprefix tailTrace_2998865
  have hstable : (prefixWord ++ tailWord_2998865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998865).length < 2 ^ (prefixWord ++ tailWord_2998865).sum := by decide
  have hdescent : baseEnd_2998865 < baseStart_2998865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998869 : List Nat := [1, 3, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_2998869 : Nat := 118140960795 + 2998869 * 2 ^ 59
def prefixEnd_2998869 : Nat := 4983230072969 + 3 ^ 40 * 2998869 * 2
def baseEnd_2998869 : Nat := 1026574144578755096630639

theorem tailTrace_2998869 : CollatzResearch.WordTrace tailWord_2998869 prefixEnd_2998869 1026574144578755096630639 := by
  unfold tailWord_2998869
  simp only [CollatzResearch.WordTrace]
  refine ⟨109377738172617253894687661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72918492115078169263125107 109377738172617253894687661)
  ·
    refine ⟨41016651814731470210507873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109377738172617253894687661 41016651814731470210507873)
    ·
      refine ⟨30762488861048602657880905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41016651814731470210507873 30762488861048602657880905)
      ·
        refine ⟨23071866645786451993410679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30762488861048602657880905 23071866645786451993410679)
        ·
          refine ⟨34607799968679677990116019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23071866645786451993410679 34607799968679677990116019)
          ·
            refine ⟨51911699953019516985174029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34607799968679677990116019 51911699953019516985174029)
            ·
              refine ⟨19466887482382318869440261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51911699953019516985174029 19466887482382318869440261)
              ·
                refine ⟨3650041402946684788020049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19466887482382318869440261 3650041402946684788020049)
                ·
                  refine ⟨2737531052210013591015037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3650041402946684788020049 2737531052210013591015037)
                  ·
                    refine ⟨1026574144578755096630639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737531052210013591015037 1026574144578755096630639)
                    ·
                      rfl

theorem cell22_2998869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_2998869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998869 prefixEnd_2998869 := by exact prefixLift 2998869
  have htrace : WordTrace (prefixWord ++ tailWord_2998869) baseStart_2998869 baseEnd_2998869 := by
    simpa [prefixWord, tailWord_2998869, baseEnd_2998869] using wordTrace_append hprefix tailTrace_2998869
  have hstable : (prefixWord ++ tailWord_2998869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998869).length < 2 ^ (prefixWord ++ tailWord_2998869).sum := by decide
  have hdescent : baseEnd_2998869 < baseStart_2998869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998965 : List Nat := [1, 3, 3, 3, 1, 3, 1, 3, 1, 3]
def baseStart_2998965 : Nat := 118140960795 + 2998965 * 2 ^ 59
def prefixEnd_2998965 : Nat := 4983230072969 + 3 ^ 40 * 2998965 * 2
def baseEnd_2998965 : Nat := 1026607007340642846230345

theorem tailTrace_2998965 : CollatzResearch.WordTrace tailWord_2998965 prefixEnd_2998965 1026607007340642846230345 := by
  unfold tailWord_2998965
  simp only [CollatzResearch.WordTrace]
  refine ⟨109381239580269462290182349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72920826386846308193454899 109381239580269462290182349)
  ·
    refine ⟨41017964842601048358818381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109381239580269462290182349 41017964842601048358818381)
    ·
      refine ⟨15381736815975393134556893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41017964842601048358818381 15381736815975393134556893)
      ·
        refine ⟨5768151305990772425458835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15381736815975393134556893 5768151305990772425458835)
        ·
          refine ⟨8652226958986158638188253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768151305990772425458835 8652226958986158638188253)
          ·
            refine ⟨3244585109619809489320595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8652226958986158638188253 3244585109619809489320595)
            ·
              refine ⟨4866877664429714233980893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244585109619809489320595 4866877664429714233980893)
              ·
                refine ⟨1825079124161142837742835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4866877664429714233980893 1825079124161142837742835)
                ·
                  refine ⟨2737618686241714256614253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825079124161142837742835 2737618686241714256614253)
                  ·
                    refine ⟨1026607007340642846230345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737618686241714256614253 1026607007340642846230345)
                    ·
                      rfl

theorem cell22_2998965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_2998965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998965 prefixEnd_2998965 := by exact prefixLift 2998965
  have htrace : WordTrace (prefixWord ++ tailWord_2998965) baseStart_2998965 baseEnd_2998965 := by
    simpa [prefixWord, tailWord_2998965, baseEnd_2998965] using wordTrace_append hprefix tailTrace_2998965
  have hstable : (prefixWord ++ tailWord_2998965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998965).length < 2 ^ (prefixWord ++ tailWord_2998965).sum := by decide
  have hdescent : baseEnd_2998965 < baseStart_2998965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2998982 : List Nat := [6, 1, 2, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2998982 : Nat := 118140960795 + 2998982 * 2 ^ 59
def prefixEnd_2998982 : Nat := 4983230072969 + 3 ^ 40 * 2998982 * 2
def baseEnd_2998982 : Nat := 1026612826788060468555293

theorem tailTrace_2998982 : CollatzResearch.WordTrace tailWord_2998982 prefixEnd_2998982 1026612826788060468555293 := by
  unfold tailWord_2998982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3418183113162746068548475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72921239747471916129034133 3418183113162746068548475)
  ·
    refine ⟨5127274669744119102822713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3418183113162746068548475 5127274669744119102822713)
    ·
      refine ⟨3845456002308089327117035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5127274669744119102822713 3845456002308089327117035)
      ·
        refine ⟨5768184003462133990675553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845456002308089327117035 5768184003462133990675553)
        ·
          refine ⟨4326138002596600493006665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5768184003462133990675553 4326138002596600493006665)
          ·
            refine ⟨3244603501947450369754999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4326138002596600493006665 3244603501947450369754999)
            ·
              refine ⟨4866905252921175554632499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244603501947450369754999 4866905252921175554632499)
              ·
                refine ⟨7300357879381763331948749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4866905252921175554632499 7300357879381763331948749)
                ·
                  refine ⟨2737634204768161249480781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7300357879381763331948749 2737634204768161249480781)
                  ·
                    refine ⟨1026612826788060468555293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737634204768161249480781 1026612826788060468555293)
                    ·
                      rfl

theorem cell22_2998982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2998982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2998982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2998982 prefixEnd_2998982 := by exact prefixLift 2998982
  have htrace : WordTrace (prefixWord ++ tailWord_2998982) baseStart_2998982 baseEnd_2998982 := by
    simpa [prefixWord, tailWord_2998982, baseEnd_2998982] using wordTrace_append hprefix tailTrace_2998982
  have hstable : (prefixWord ++ tailWord_2998982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2998982).length < 2 ^ (prefixWord ++ tailWord_2998982).sum := by decide
  have hdescent : baseEnd_2998982 < baseStart_2998982 := by decide
  rcases family_descends (prefixWord ++ tailWord_2998982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999017 : List Nat := [1, 2, 1, 1, 1, 2, 6, 8]
def baseStart_2999017 : Nat := 118140960795 + 2999017 * 2 ^ 59
def prefixEnd_2999017 : Nat := 4983230072969 + 3 ^ 40 * 2999017 * 2
def baseEnd_2999017 : Nat := 114069423111481338214465

theorem tailTrace_2999017 : CollatzResearch.WordTrace tailWord_2999017 prefixEnd_2999017 114069423111481338214465 := by
  unfold tailWord_2999017
  simp only [CollatzResearch.WordTrace]
  refine ⟨109383136176081075171075305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72922090784054050114050203 109383136176081075171075305)
  ·
    refine ⟨82037352132060806378306479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109383136176081075171075305 82037352132060806378306479)
    ·
      refine ⟨123056028198091209567459719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82037352132060806378306479 123056028198091209567459719)
      ·
        refine ⟨184584042297136814351189579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123056028198091209567459719 184584042297136814351189579)
        ·
          refine ⟨276876063445705221526784369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184584042297136814351189579 276876063445705221526784369)
          ·
            refine ⟨207657047584278916145088277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 276876063445705221526784369 207657047584278916145088277)
            ·
              refine ⟨9733924105513074194301013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207657047584278916145088277 9733924105513074194301013)
              ·
                refine ⟨114069423111481338214465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9733924105513074194301013 114069423111481338214465)
                ·
                  rfl

theorem cell22_2999017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6, 8].length) (baseStart_2999017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999017 prefixEnd_2999017 := by exact prefixLift 2999017
  have htrace : WordTrace (prefixWord ++ tailWord_2999017) baseStart_2999017 baseEnd_2999017 := by
    simpa [prefixWord, tailWord_2999017, baseEnd_2999017] using wordTrace_append hprefix tailTrace_2999017
  have hstable : (prefixWord ++ tailWord_2999017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999017).length < 2 ^ (prefixWord ++ tailWord_2999017).sum := by decide
  have hdescent : baseEnd_2999017 < baseStart_2999017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999038 : List Nat := [4, 2, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2999038 : Nat := 118140960795 + 2999038 * 2 ^ 59
def prefixEnd_2999038 : Nat := 4983230072969 + 3 ^ 40 * 2999038 * 2
def baseEnd_2999038 : Nat := 1026631996732494989155121

theorem tailTrace_2999038 : CollatzResearch.WordTrace tailWord_2999038 prefixEnd_2999038 1026631996732494989155121 := by
  unfold tailWord_2999038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13672987763625624469698721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72922601406003330505059845 13672987763625624469698721)
  ·
    refine ⟨10254740822719218352274041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13672987763625624469698721 10254740822719218352274041)
    ·
      refine ⟨7691055617039413764205531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10254740822719218352274041 7691055617039413764205531)
      ·
        refine ⟨11536583425559120646308297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691055617039413764205531 11536583425559120646308297)
        ·
          refine ⟨8652437569169340484731223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11536583425559120646308297 8652437569169340484731223)
          ·
            refine ⟨12978656353754010727096835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652437569169340484731223 12978656353754010727096835)
            ·
              refine ⟨19467984530631016090645253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12978656353754010727096835 19467984530631016090645253)
              ·
                refine ⟨3650247099493315516995985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19467984530631016090645253 3650247099493315516995985)
                ·
                  refine ⟨2737685324619986637746989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3650247099493315516995985 2737685324619986637746989)
                  ·
                    refine ⟨1026631996732494989155121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737685324619986637746989 1026631996732494989155121)
                    ·
                      rfl

theorem cell22_2999038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2999038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999038 prefixEnd_2999038 := by exact prefixLift 2999038
  have htrace : WordTrace (prefixWord ++ tailWord_2999038) baseStart_2999038 baseEnd_2999038 := by
    simpa [prefixWord, tailWord_2999038, baseEnd_2999038] using wordTrace_append hprefix tailTrace_2999038
  have hstable : (prefixWord ++ tailWord_2999038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999038).length < 2 ^ (prefixWord ++ tailWord_2999038).sum := by decide
  have hdescent : baseEnd_2999038 < baseStart_2999038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999066 : List Nat := [3, 1, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_2999066 : Nat := 118140960795 + 2999066 * 2 ^ 59
def prefixEnd_2999066 : Nat := 4983230072969 + 3 ^ 40 * 2999066 * 2
def baseEnd_2999066 : Nat := 1026641581704712249455035

theorem tailTrace_2999066 : CollatzResearch.WordTrace tailWord_2999066 prefixEnd_2999066 1026641581704712249455035 := by
  unfold tailWord_2999066
  simp only [CollatzResearch.WordTrace]
  refine ⟨27346230838225889134902263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72923282235269037693072701 27346230838225889134902263)
  ·
    refine ⟨41019346257338833702353395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27346230838225889134902263 41019346257338833702353395)
    ·
      refine ⟨61529019386008250553530093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41019346257338833702353395 61529019386008250553530093)
      ·
        refine ⟨23073382269753093957573785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61529019386008250553530093 23073382269753093957573785)
        ·
          refine ⟨17305036702314820468180339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23073382269753093957573785 17305036702314820468180339)
          ·
            refine ⟨25957555053472230702270509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17305036702314820468180339 25957555053472230702270509)
            ·
              refine ⟨9734083145052086513351441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25957555053472230702270509 9734083145052086513351441)
              ·
                refine ⟨7300562358789064885013581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9734083145052086513351441 7300562358789064885013581)
                ·
                  refine ⟨2737710884545899331880093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7300562358789064885013581 2737710884545899331880093)
                  ·
                    refine ⟨1026641581704712249455035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737710884545899331880093 1026641581704712249455035)
                    ·
                      rfl

theorem cell22_2999066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_2999066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999066 prefixEnd_2999066 := by exact prefixLift 2999066
  have htrace : WordTrace (prefixWord ++ tailWord_2999066) baseStart_2999066 baseEnd_2999066 := by
    simpa [prefixWord, tailWord_2999066, baseEnd_2999066] using wordTrace_append hprefix tailTrace_2999066
  have hstable : (prefixWord ++ tailWord_2999066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999066).length < 2 ^ (prefixWord ++ tailWord_2999066).sum := by decide
  have hdescent : baseEnd_2999066 < baseStart_2999066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999109 : List Nat := [1, 3, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_2999109 : Nat := 118140960795 + 2999109 * 2 ^ 59
def prefixEnd_2999109 : Nat := 4983230072969 + 3 ^ 40 * 2999109 * 2
def baseEnd_2999109 : Nat := 1026656301483474470629903

theorem tailTrace_2999109 : CollatzResearch.WordTrace tailWord_2999109 prefixEnd_2999109 1026656301483474470629903 := by
  unfold tailWord_2999109
  simp only [CollatzResearch.WordTrace]
  refine ⟨109386491691747774883424381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72924327794498516588949587 109386491691747774883424381)
  ·
    refine ⟨41019934384405415581284143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109386491691747774883424381 41019934384405415581284143)
    ·
      refine ⟨61529901576608123371926215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41019934384405415581284143 61529901576608123371926215)
      ·
        refine ⟨92294852364912185057889323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61529901576608123371926215 92294852364912185057889323)
        ·
          refine ⟨138442278547368277586833985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92294852364912185057889323 138442278547368277586833985)
          ·
            refine ⟨103831708910526208190125489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138442278547368277586833985 103831708910526208190125489)
            ·
              refine ⟨77873781682894656142594117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103831708910526208190125489 77873781682894656142594117)
              ·
                refine ⟨14601334065542748026736397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77873781682894656142594117 14601334065542748026736397)
                ·
                  refine ⟨5475500274578530510026149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14601334065542748026736397 5475500274578530510026149)
                  ·
                    refine ⟨1026656301483474470629903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5475500274578530510026149 1026656301483474470629903)
                    ·
                      rfl

theorem cell22_2999109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_2999109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999109 prefixEnd_2999109 := by exact prefixLift 2999109
  have htrace : WordTrace (prefixWord ++ tailWord_2999109) baseStart_2999109 baseEnd_2999109 := by
    simpa [prefixWord, tailWord_2999109, baseEnd_2999109] using wordTrace_append hprefix tailTrace_2999109
  have hstable : (prefixWord ++ tailWord_2999109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999109).length < 2 ^ (prefixWord ++ tailWord_2999109).sum := by decide
  have hdescent : baseEnd_2999109 < baseStart_2999109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999158 : List Nat := [5, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_2999158 : Nat := 118140960795 + 2999158 * 2 ^ 59
def prefixEnd_2999158 : Nat := 4983230072969 + 3 ^ 40 * 2999158 * 2
def baseEnd_2999158 : Nat := 342224358394951558718251

theorem tailTrace_2999158 : CollatzResearch.WordTrace tailWord_2999158 prefixEnd_2999158 342224358394951558718251 := by
  unfold tailWord_2999158
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836767429285641015747383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72925519245713504167972085 6836767429285641015747383)
  ·
    refine ⟨10255151143928461523621075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6836767429285641015747383 10255151143928461523621075)
    ·
      refine ⟨15382726715892692285431613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10255151143928461523621075 15382726715892692285431613)
      ·
        refine ⟨5768522518459759607036855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15382726715892692285431613 5768522518459759607036855)
        ·
          refine ⟨8652783777689639410555283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768522518459759607036855 8652783777689639410555283)
          ·
            refine ⟨12979175666534459115832925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652783777689639410555283 12979175666534459115832925)
            ·
              refine ⟨4867190874950422168437347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12979175666534459115832925 4867190874950422168437347)
              ·
                refine ⟨7300786312425633252656021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4867190874950422168437347 7300786312425633252656021)
                ·
                  refine ⟨342224358394951558718251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7300786312425633252656021 342224358394951558718251)
                  ·
                    rfl

theorem cell22_2999158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_2999158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999158 prefixEnd_2999158 := by exact prefixLift 2999158
  have htrace : WordTrace (prefixWord ++ tailWord_2999158) baseStart_2999158 baseEnd_2999158 := by
    simpa [prefixWord, tailWord_2999158, baseEnd_2999158] using wordTrace_append hprefix tailTrace_2999158
  have hstable : (prefixWord ++ tailWord_2999158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999158).length < 2 ^ (prefixWord ++ tailWord_2999158).sum := by decide
  have hdescent : baseEnd_2999158 < baseStart_2999158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999173 : List Nat := [1, 3, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_2999173 : Nat := 118140960795 + 2999173 * 2 ^ 59
def prefixEnd_2999173 : Nat := 4983230072969 + 3 ^ 40 * 2999173 * 2
def baseEnd_2999173 : Nat := 1026678209991399637029707

theorem tailTrace_2999173 : CollatzResearch.WordTrace tailWord_2999173 prefixEnd_2999173 1026678209991399637029707 := by
  unfold tailWord_2999173
  simp only [CollatzResearch.WordTrace]
  refine ⟨109388825963515913813754173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72925883975677275875836115 109388825963515913813754173)
  ·
    refine ⟨41020809736318467680157815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109388825963515913813754173 41020809736318467680157815)
    ·
      refine ⟨61531214604477701520236723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41020809736318467680157815 61531214604477701520236723)
      ·
        refine ⟨92296821906716552280355085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61531214604477701520236723 92296821906716552280355085)
        ·
          refine ⟨34611308215018707105133157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92296821906716552280355085 34611308215018707105133157)
          ·
            refine ⟨6489620290316007582212467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34611308215018707105133157 6489620290316007582212467)
            ·
              refine ⟨9734430435474011373318701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6489620290316007582212467 9734430435474011373318701)
              ·
                refine ⟨3650411413302754264994513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9734430435474011373318701 3650411413302754264994513)
                ·
                  refine ⟨2737808559977065698745885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3650411413302754264994513 2737808559977065698745885)
                  ·
                    refine ⟨1026678209991399637029707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737808559977065698745885 1026678209991399637029707)
                    ·
                      rfl

theorem cell22_2999173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_2999173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999173 prefixEnd_2999173 := by exact prefixLift 2999173
  have htrace : WordTrace (prefixWord ++ tailWord_2999173) baseStart_2999173 baseEnd_2999173 := by
    simpa [prefixWord, tailWord_2999173, baseEnd_2999173] using wordTrace_append hprefix tailTrace_2999173
  have hstable : (prefixWord ++ tailWord_2999173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999173).length < 2 ^ (prefixWord ++ tailWord_2999173).sum := by decide
  have hdescent : baseEnd_2999173 < baseStart_2999173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999188 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_2999188 : Nat := 118140960795 + 2999188 * 2 ^ 59
def prefixEnd_2999188 : Nat := 4983230072969 + 3 ^ 40 * 2999188 * 2
def baseEnd_2999188 : Nat := 1026683344797944597904661

theorem tailTrace_2999188 : CollatzResearch.WordTrace tailWord_2999188 prefixEnd_2999188 1026683344797944597904661 := by
  unfold tailWord_2999188
  simp only [CollatzResearch.WordTrace]
  refine ⟨54694686529230785687775109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72926248705641047583700145 54694686529230785687775109)
  ·
    refine ⟨10255253724230772316457833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54694686529230785687775109 10255253724230772316457833)
    ·
      refine ⟨7691440293173079237343375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10255253724230772316457833 7691440293173079237343375)
      ·
        refine ⟨11537160439759618856015063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7691440293173079237343375 11537160439759618856015063)
        ·
          refine ⟨17305740659639428284022595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11537160439759618856015063 17305740659639428284022595)
          ·
            refine ⟨25958610989459142426033893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17305740659639428284022595 25958610989459142426033893)
            ·
              refine ⟨4867239560523589204881355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25958610989459142426033893 4867239560523589204881355)
              ·
                refine ⟨7300859340785383807322033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4867239560523589204881355 7300859340785383807322033)
                ·
                  refine ⟨5475644505589037855491525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7300859340785383807322033 5475644505589037855491525)
                  ·
                    refine ⟨1026683344797944597904661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5475644505589037855491525 1026683344797944597904661)
                    ·
                      rfl

theorem cell22_2999188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_2999188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999188 prefixEnd_2999188 := by exact prefixLift 2999188
  have htrace : WordTrace (prefixWord ++ tailWord_2999188) baseStart_2999188 baseEnd_2999188 := by
    simpa [prefixWord, tailWord_2999188, baseEnd_2999188] using wordTrace_append hprefix tailTrace_2999188
  have hstable : (prefixWord ++ tailWord_2999188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999188).length < 2 ^ (prefixWord ++ tailWord_2999188).sum := by decide
  have hdescent : baseEnd_2999188 < baseStart_2999188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999190 : List Nat := [5, 3, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_2999190 : Nat := 118140960795 + 2999190 * 2 ^ 59
def prefixEnd_2999190 : Nat := 4983230072969 + 3 ^ 40 * 2999190 * 2
def baseEnd_2999190 : Nat := 1026684029438817259354655

theorem tailTrace_2999190 : CollatzResearch.WordTrace tailWord_2999190 prefixEnd_2999190 1026684029438817259354655 := by
  unfold tailWord_2999190
  simp only [CollatzResearch.WordTrace]
  refine ⟨6836840375278395357320189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72926297336302883811415349 6836840375278395357320189)
  ·
    refine ⟨2563815140729398258995071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6836840375278395357320189 2563815140729398258995071)
    ·
      refine ⟨3845722711094097388492607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2563815140729398258995071 3845722711094097388492607)
      ·
        refine ⟨5768584066641146082738911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845722711094097388492607 5768584066641146082738911)
        ·
          refine ⟨8652876099961719124108367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768584066641146082738911 8652876099961719124108367)
          ·
            refine ⟨12979314149942578686162551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8652876099961719124108367 12979314149942578686162551)
            ·
              refine ⟨19468971224913868029243827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12979314149942578686162551 19468971224913868029243827)
              ·
                refine ⟨29203456837370802043865741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19468971224913868029243827 29203456837370802043865741)
                ·
                  refine ⟨10951296314014050766449653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29203456837370802043865741 10951296314014050766449653)
                  ·
                    refine ⟨1026684029438817259354655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10951296314014050766449653 1026684029438817259354655)
                    ·
                      rfl

theorem cell22_2999190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_2999190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999190 prefixEnd_2999190 := by exact prefixLift 2999190
  have htrace : WordTrace (prefixWord ++ tailWord_2999190) baseStart_2999190 baseEnd_2999190 := by
    simpa [prefixWord, tailWord_2999190, baseEnd_2999190] using wordTrace_append hprefix tailTrace_2999190
  have hstable : (prefixWord ++ tailWord_2999190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999190).length < 2 ^ (prefixWord ++ tailWord_2999190).sum := by decide
  have hdescent : baseEnd_2999190 < baseStart_2999190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999220 : List Nat := [2, 5, 2, 1, 1, 3, 1, 7]
def baseStart_2999220 : Nat := 118140960795 + 2999220 * 2 ^ 59
def prefixEnd_2999220 : Nat := 4983230072969 + 3 ^ 40 * 2999220 * 2
def baseEnd_2999220 : Nat := 114077144339100797900507

theorem tailTrace_2999220 : CollatzResearch.WordTrace tailWord_2999220 prefixEnd_2999220 114077144339100797900507 := by
  unfold tailWord_2999220
  simp only [CollatzResearch.WordTrace]
  refine ⟨54695270097172820420357557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72927026796230427227143409 54695270097172820420357557)
  ·
    refine ⟨5127681571609951914408521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 54695270097172820420357557 5127681571609951914408521)
    ·
      refine ⟨3845761178707463935806391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5127681571609951914408521 3845761178707463935806391)
      ·
        refine ⟨5768641768061195903709587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3845761178707463935806391 5768641768061195903709587)
        ·
          refine ⟨8652962652091793855564381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5768641768061195903709587 8652962652091793855564381)
          ·
            refine ⟨3244860994534422695836643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8652962652091793855564381 3244860994534422695836643)
            ·
              refine ⟨4867291491801634043754965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3244860994534422695836643 4867291491801634043754965)
              ·
                refine ⟨114077144339100797900507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4867291491801634043754965 114077144339100797900507)
                ·
                  rfl

theorem cell22_2999220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 1, 7].length) (baseStart_2999220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999220 prefixEnd_2999220 := by exact prefixLift 2999220
  have htrace : WordTrace (prefixWord ++ tailWord_2999220) baseStart_2999220 baseEnd_2999220 := by
    simpa [prefixWord, tailWord_2999220, baseEnd_2999220] using wordTrace_append hprefix tailTrace_2999220
  have hstable : (prefixWord ++ tailWord_2999220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999220).length < 2 ^ (prefixWord ++ tailWord_2999220).sum := by decide
  have hdescent : baseEnd_2999220 < baseStart_2999220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999252 : List Nat := [2, 4, 1, 2, 1, 3, 2, 3, 1, 3]
def baseStart_2999252 : Nat := 118140960795 + 2999252 * 2 ^ 59
def prefixEnd_2999252 : Nat := 4983230072969 + 3 ^ 40 * 2999252 * 2
def baseEnd_2999252 : Nat := 1026705253305869764304465

theorem tailTrace_2999252 : CollatzResearch.WordTrace tailWord_2999252 prefixEnd_2999252 1026705253305869764304465 := by
  unfold tailWord_2999252
  simp only [CollatzResearch.WordTrace]
  refine ⟨54695853665114855152940005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72927804886819806870586673 54695853665114855152940005)
  ·
    refine ⟨10255472562209035341176251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54695853665114855152940005 10255472562209035341176251)
    ·
      refine ⟨15383208843313553011764377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10255472562209035341176251 15383208843313553011764377)
      ·
        refine ⟨11537406632485164758823283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15383208843313553011764377 11537406632485164758823283)
        ·
          refine ⟨17306109948727747138234925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11537406632485164758823283 17306109948727747138234925)
          ·
            refine ⟨6489791230772905176838097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17306109948727747138234925 6489791230772905176838097)
            ·
              refine ⟨4867343423079678882628573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6489791230772905176838097 4867343423079678882628573)
              ·
                refine ⟨1825253783654879580985715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4867343423079678882628573 1825253783654879580985715)
                ·
                  refine ⟨2737880675482319371478573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825253783654879580985715 2737880675482319371478573)
                  ·
                    refine ⟨1026705253305869764304465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737880675482319371478573 1026705253305869764304465)
                    ·
                      rfl

theorem cell22_2999252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 3, 1, 3].length) (baseStart_2999252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999252 prefixEnd_2999252 := by exact prefixLift 2999252
  have htrace : WordTrace (prefixWord ++ tailWord_2999252) baseStart_2999252 baseEnd_2999252 := by
    simpa [prefixWord, tailWord_2999252, baseEnd_2999252] using wordTrace_append hprefix tailTrace_2999252
  have hstable : (prefixWord ++ tailWord_2999252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999252).length < 2 ^ (prefixWord ++ tailWord_2999252).sum := by decide
  have hdescent : baseEnd_2999252 < baseStart_2999252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999282 : List Nat := [3, 2, 1, 5, 1, 1, 3, 1, 5]
def baseStart_2999282 : Nat := 118140960795 + 2999282 * 2 ^ 59
def prefixEnd_2999282 : Nat := 4983230072969 + 3 ^ 40 * 2999282 * 2
def baseEnd_2999282 : Nat := 342238507639653228684791

theorem tailTrace_2999282 : CollatzResearch.WordTrace tailWord_2999282 prefixEnd_2999282 342238507639653228684791 := by
  unfold tailWord_2999282
  simp only [CollatzResearch.WordTrace]
  refine ⟨27348200380030256357368025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72928534346747350286314733 27348200380030256357368025)
  ·
    refine ⟨20511150285022692268026019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27348200380030256357368025 20511150285022692268026019)
    ·
      refine ⟨30766725427534038402039029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20511150285022692268026019 30766725427534038402039029)
      ·
        refine ⟨2884380508831316100191159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30766725427534038402039029 2884380508831316100191159)
        ·
          refine ⟨4326570763246974150286739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2884380508831316100191159 4326570763246974150286739)
          ·
            refine ⟨6489856144870461225430109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326570763246974150286739 6489856144870461225430109)
            ·
              refine ⟨2433696054326422959536291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6489856144870461225430109 2433696054326422959536291)
              ·
                refine ⟨3650544081489634439304437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2433696054326422959536291 3650544081489634439304437)
                ·
                  refine ⟨342238507639653228684791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3650544081489634439304437 342238507639653228684791)
                  ·
                    rfl

theorem cell22_2999282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_2999282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999282 prefixEnd_2999282 := by exact prefixLift 2999282
  have htrace : WordTrace (prefixWord ++ tailWord_2999282) baseStart_2999282 baseEnd_2999282 := by
    simpa [prefixWord, tailWord_2999282, baseEnd_2999282] using wordTrace_append hprefix tailTrace_2999282
  have hstable : (prefixWord ++ tailWord_2999282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999282).length < 2 ^ (prefixWord ++ tailWord_2999282).sum := by decide
  have hdescent : baseEnd_2999282 < baseStart_2999282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999308 : List Nat := [2, 2, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_2999308 : Nat := 118140960795 + 2999308 * 2 ^ 59
def prefixEnd_2999308 : Nat := 4983230072969 + 3 ^ 40 * 2999308 * 2
def baseEnd_2999308 : Nat := 1026724423250304284904293

theorem tailTrace_2999308 : CollatzResearch.WordTrace tailWord_2999308 prefixEnd_2999308 1026724423250304284904293 := by
  unfold tailWord_2999308
  simp only [CollatzResearch.WordTrace]
  refine ⟨54696874909013415934959289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72929166545351221246612385 54696874909013415934959289)
  ·
    refine ⟨41022656181760061951219467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54696874909013415934959289 41022656181760061951219467)
    ·
      refine ⟨61533984272640092926829201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41022656181760061951219467 61533984272640092926829201)
      ·
        refine ⟨46150488204480069695121901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61533984272640092926829201 46150488204480069695121901)
        ·
          refine ⟨17306433076680026135670713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46150488204480069695121901 17306433076680026135670713)
          ·
            refine ⟨12979824807510019601753035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17306433076680026135670713 12979824807510019601753035)
            ·
              refine ⟨19469737211265029402629553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12979824807510019601753035 19469737211265029402629553)
              ·
                refine ⟨14602302908448772051972165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19469737211265029402629553 14602302908448772051972165)
                ·
                  refine ⟨2737931795334144759744781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14602302908448772051972165 2737931795334144759744781)
                  ·
                    refine ⟨1026724423250304284904293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2737931795334144759744781 1026724423250304284904293)
                    ·
                      rfl

theorem cell22_2999308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_2999308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999308 prefixEnd_2999308 := by exact prefixLift 2999308
  have htrace : WordTrace (prefixWord ++ tailWord_2999308) baseStart_2999308 baseEnd_2999308 := by
    simpa [prefixWord, tailWord_2999308, baseEnd_2999308] using wordTrace_append hprefix tailTrace_2999308
  have hstable : (prefixWord ++ tailWord_2999308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999308).length < 2 ^ (prefixWord ++ tailWord_2999308).sum := by decide
  have hdescent : baseEnd_2999308 < baseStart_2999308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999310 : List Nat := [4, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_2999310 : Nat := 118140960795 + 2999310 * 2 ^ 59
def prefixEnd_2999310 : Nat := 4983230072969 + 3 ^ 40 * 2999310 * 2
def baseEnd_2999310 : Nat := 342241702630392315451429

theorem tailTrace_2999310 : CollatzResearch.WordTrace tailWord_2999310 prefixEnd_2999310 342241702630392315451429 := by
  unfold tailWord_2999310
  simp only [CollatzResearch.WordTrace]
  refine ⟨13674227845502448276436423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72929215176013057474327589 13674227845502448276436423)
  ·
    refine ⟨20511341768253672414654635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13674227845502448276436423 20511341768253672414654635)
    ·
      refine ⟨30767012652380508621981953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20511341768253672414654635 30767012652380508621981953)
      ·
        refine ⟨23075259489285381466486465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30767012652380508621981953 23075259489285381466486465)
        ·
          refine ⟨17306444616964036099864849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23075259489285381466486465 17306444616964036099864849)
          ·
            refine ⟨12979833462723027074898637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17306444616964036099864849 12979833462723027074898637)
            ·
              refine ⟨4867437548521135153086989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12979833462723027074898637 4867437548521135153086989)
              ·
                refine ⟨1825289080695425682407621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4867437548521135153086989 1825289080695425682407621)
                ·
                  refine ⟨342241702630392315451429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1825289080695425682407621 342241702630392315451429)
                  ·
                    rfl

theorem cell22_2999310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_2999310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999310 prefixEnd_2999310 := by exact prefixLift 2999310
  have htrace : WordTrace (prefixWord ++ tailWord_2999310) baseStart_2999310 baseEnd_2999310 := by
    simpa [prefixWord, tailWord_2999310, baseEnd_2999310] using wordTrace_append hprefix tailTrace_2999310
  have hstable : (prefixWord ++ tailWord_2999310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999310).length < 2 ^ (prefixWord ++ tailWord_2999310).sum := by decide
  have hdescent : baseEnd_2999310 < baseStart_2999310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999460 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_2999460 : Nat := 118140960795 + 2999460 * 2 ^ 59
def prefixEnd_2999460 : Nat := 4983230072969 + 3 ^ 40 * 2999460 * 2
def baseEnd_2999460 : Nat := 1026776455956626555103827

theorem tailTrace_2999460 : CollatzResearch.WordTrace tailWord_2999460 prefixEnd_2999460 1026776455956626555103827 := by
  unfold tailWord_2999460
  simp only [CollatzResearch.WordTrace]
  refine ⟨54699646856738080914725917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72932862475650774552967889 54699646856738080914725917)
  ·
    refine ⟨20512367571276780343022219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54699646856738080914725917 20512367571276780343022219)
    ·
      refine ⟨30768551356915170514533329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20512367571276780343022219 30768551356915170514533329)
      ·
        refine ⟨23076413517686377885899997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30768551356915170514533329 23076413517686377885899997)
        ·
          refine ⟨8653655069132391707212499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23076413517686377885899997 8653655069132391707212499)
          ·
            refine ⟨12980482603698587560818749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8653655069132391707212499 12980482603698587560818749)
            ·
              refine ⟨4867680976386970335307031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12980482603698587560818749 4867680976386970335307031)
              ·
                refine ⟨7301521464580455502960547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4867680976386970335307031 7301521464580455502960547)
                ·
                  refine ⟨10952282196870683254440821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7301521464580455502960547 10952282196870683254440821)
                  ·
                    refine ⟨1026776455956626555103827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10952282196870683254440821 1026776455956626555103827)
                    ·
                      rfl

theorem cell22_2999460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_2999460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999460 prefixEnd_2999460 := by exact prefixLift 2999460
  have htrace : WordTrace (prefixWord ++ tailWord_2999460) baseStart_2999460 baseEnd_2999460 := by
    simpa [prefixWord, tailWord_2999460, baseEnd_2999460] using wordTrace_append hprefix tailTrace_2999460
  have hstable : (prefixWord ++ tailWord_2999460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999460).length < 2 ^ (prefixWord ++ tailWord_2999460).sum := by decide
  have hdescent : baseEnd_2999460 < baseStart_2999460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999492 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2999492 : Nat := 118140960795 + 2999492 * 2 ^ 59
def prefixEnd_2999492 : Nat := 4983230072969 + 3 ^ 40 * 2999492 * 2
def baseEnd_2999492 : Nat := 1026787410210589138303729

theorem tailTrace_2999492 : CollatzResearch.WordTrace tailWord_2999492 prefixEnd_2999492 1026787410210589138303729 := by
  unfold tailWord_2999492
  simp only [CollatzResearch.WordTrace]
  refine ⟨54700230424680115647308365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72933640566240154196411153 54700230424680115647308365)
  ·
    refine ⟨20512586409255043367740637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54700230424680115647308365 20512586409255043367740637)
    ·
      refine ⟨7692219903470641262902739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20512586409255043367740637 7692219903470641262902739)
      ·
        refine ⟨11538329855205961894354109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7692219903470641262902739 11538329855205961894354109)
        ·
          refine ⟨4326873695702235710382791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11538329855205961894354109 4326873695702235710382791)
          ·
            refine ⟨6490310543553353565574187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4326873695702235710382791 6490310543553353565574187)
            ·
              refine ⟨9735465815330030348361281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490310543553353565574187 9735465815330030348361281)
              ·
                refine ⟨7301599361497522761270961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9735465815330030348361281 7301599361497522761270961)
                ·
                  refine ⟨5476199521123142070953221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7301599361497522761270961 5476199521123142070953221)
                  ·
                    refine ⟨1026787410210589138303729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5476199521123142070953221 1026787410210589138303729)
                    ·
                      rfl

theorem cell22_2999492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2999492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999492 prefixEnd_2999492 := by exact prefixLift 2999492
  have htrace : WordTrace (prefixWord ++ tailWord_2999492) baseStart_2999492 baseEnd_2999492 := by
    simpa [prefixWord, tailWord_2999492, baseEnd_2999492] using wordTrace_append hprefix tailTrace_2999492
  have hstable : (prefixWord ++ tailWord_2999492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999492).length < 2 ^ (prefixWord ++ tailWord_2999492).sum := by decide
  have hdescent : baseEnd_2999492 < baseStart_2999492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999556 : List Nat := [2, 3, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_2999556 : Nat := 118140960795 + 2999556 * 2 ^ 59
def prefixEnd_2999556 : Nat := 4983230072969 + 3 ^ 40 * 2999556 * 2
def baseEnd_2999556 : Nat := 1026809318718514304703533

theorem tailTrace_2999556 : CollatzResearch.WordTrace tailWord_2999556 prefixEnd_2999556 1026809318718514304703533 := by
  unfold tailWord_2999556
  simp only [CollatzResearch.WordTrace]
  refine ⟨54701397560564185112473261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72935196747418913483297681 54701397560564185112473261)
  ·
    refine ⟨20513024085211569417177473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54701397560564185112473261 20513024085211569417177473)
    ·
      refine ⟨15384768063908677062883105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20513024085211569417177473 15384768063908677062883105)
      ·
        refine ⟨11538576047931507797162329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15384768063908677062883105 11538576047931507797162329)
        ·
          refine ⟨8653932035948630847871747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11538576047931507797162329 8653932035948630847871747)
          ·
            refine ⟨12980898053922946271807621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8653932035948630847871747 12980898053922946271807621)
            ·
              refine ⟨2433918385110552425963929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12980898053922946271807621 2433918385110552425963929)
              ·
                refine ⟨1825438788832914319472947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2433918385110552425963929 1825438788832914319472947)
                ·
                  refine ⟨2738158183249371479209421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825438788832914319472947 2738158183249371479209421)
                  ·
                    refine ⟨1026809318718514304703533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738158183249371479209421 1026809318718514304703533)
                    ·
                      rfl

theorem cell22_2999556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_2999556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999556 prefixEnd_2999556 := by exact prefixLift 2999556
  have htrace : WordTrace (prefixWord ++ tailWord_2999556) baseStart_2999556 baseEnd_2999556 := by
    simpa [prefixWord, tailWord_2999556, baseEnd_2999556] using wordTrace_append hprefix tailTrace_2999556
  have hstable : (prefixWord ++ tailWord_2999556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999556).length < 2 ^ (prefixWord ++ tailWord_2999556).sum := by decide
  have hdescent : baseEnd_2999556 < baseStart_2999556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999610 : List Nat := [3, 1, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_2999610 : Nat := 118140960795 + 2999610 * 2 ^ 59
def prefixEnd_2999610 : Nat := 4983230072969 + 3 ^ 40 * 2999610 * 2
def baseEnd_2999610 : Nat := 1026827804022076163853367

theorem tailTrace_2999610 : CollatzResearch.WordTrace tailWord_2999610 prefixEnd_2999610 1026827804022076163853367 := by
  unfold tailWord_2999610
  simp only [CollatzResearch.WordTrace]
  refine ⟨27351191165733184361853071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72936509775288491631608189 27351191165733184361853071)
  ·
    refine ⟨41026786748599776542779607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27351191165733184361853071 41026786748599776542779607)
    ·
      refine ⟨61540180122899664814169411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41026786748599776542779607 61540180122899664814169411)
      ·
        refine ⟨92310270184349497221254117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61540180122899664814169411 92310270184349497221254117)
        ·
          refine ⟨17308175659565530728985147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92310270184349497221254117 17308175659565530728985147)
          ·
            refine ⟨25962263489348296093477721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17308175659565530728985147 25962263489348296093477721)
            ·
              refine ⟨19471697617011222070108291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25962263489348296093477721 19471697617011222070108291)
              ·
                refine ⟨29207546425516833105162437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19471697617011222070108291 29207546425516833105162437)
                ·
                  refine ⟨5476414954784406207217957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29207546425516833105162437 5476414954784406207217957)
                  ·
                    refine ⟨1026827804022076163853367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5476414954784406207217957 1026827804022076163853367)
                    ·
                      rfl

theorem cell22_2999610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_2999610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999610 prefixEnd_2999610 := by exact prefixLift 2999610
  have htrace : WordTrace (prefixWord ++ tailWord_2999610) baseStart_2999610 baseEnd_2999610 := by
    simpa [prefixWord, tailWord_2999610, baseEnd_2999610] using wordTrace_append hprefix tailTrace_2999610
  have hstable : (prefixWord ++ tailWord_2999610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999610).length < 2 ^ (prefixWord ++ tailWord_2999610).sum := by decide
  have hdescent : baseEnd_2999610 < baseStart_2999610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999612 : List Nat := [2, 2, 2, 2, 1, 4, 1, 1, 4, 3]
def baseStart_2999612 : Nat := 118140960795 + 2999612 * 2 ^ 59
def prefixEnd_2999612 : Nat := 4983230072969 + 3 ^ 40 * 2999612 * 2
def baseEnd_2999612 : Nat := 1026828488662948825303361

theorem tailTrace_2999612 : CollatzResearch.WordTrace tailWord_2999612 prefixEnd_2999612 1026828488662948825303361 := by
  unfold tailWord_2999612
  simp only [CollatzResearch.WordTrace]
  refine ⟨54702418804462745894492545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72936558405950327859323393 54702418804462745894492545)
  ·
    refine ⟨41026814103347059420869409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54702418804462745894492545 41026814103347059420869409)
    ·
      refine ⟨30770110577510294565652057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41026814103347059420869409 30770110577510294565652057)
      ·
        refine ⟨23077582933132720924239043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30770110577510294565652057 23077582933132720924239043)
        ·
          refine ⟨34616374399699081386358565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23077582933132720924239043 34616374399699081386358565)
          ·
            refine ⟨6490570199943577759942231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34616374399699081386358565 6490570199943577759942231)
            ·
              refine ⟨9735855299915366639913347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490570199943577759942231 9735855299915366639913347)
              ·
                refine ⟨14603782949873049959870021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9735855299915366639913347 14603782949873049959870021)
                ·
                  refine ⟨2738209303101196867475629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14603782949873049959870021 2738209303101196867475629)
                  ·
                    refine ⟨1026828488662948825303361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738209303101196867475629 1026828488662948825303361)
                    ·
                      rfl

theorem cell22_2999612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_2999612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999612 prefixEnd_2999612 := by exact prefixLift 2999612
  have htrace : WordTrace (prefixWord ++ tailWord_2999612) baseStart_2999612 baseEnd_2999612 := by
    simpa [prefixWord, tailWord_2999612, baseEnd_2999612] using wordTrace_append hprefix tailTrace_2999612
  have hstable : (prefixWord ++ tailWord_2999612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999612).length < 2 ^ (prefixWord ++ tailWord_2999612).sum := by decide
  have hdescent : baseEnd_2999612 < baseStart_2999612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999685 : List Nat := [1, 3, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_2999685 : Nat := 118140960795 + 2999685 * 2 ^ 59
def prefixEnd_2999685 : Nat := 4983230072969 + 3 ^ 40 * 2999685 * 2
def baseEnd_2999685 : Nat := 1026853478054800968228137

theorem tailTrace_2999685 : CollatzResearch.WordTrace tailWord_2999685 prefixEnd_2999685 1026853478054800968228137 := by
  unfold tailWord_2999685
  simp only [CollatzResearch.WordTrace]
  refine ⟨109407500137661025256392509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72938333425107350170928339 109407500137661025256392509)
  ·
    refine ⟨41027812551622884471147191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109407500137661025256392509 41027812551622884471147191)
    ·
      refine ⟨61541718827434326706720787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41027812551622884471147191 61541718827434326706720787)
      ·
        refine ⟨92312578241151490060081181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61541718827434326706720787 92312578241151490060081181)
        ·
          refine ⟨34617216840431808772530443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92312578241151490060081181 34617216840431808772530443)
          ·
            refine ⟨51925825260647713158795665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34617216840431808772530443 51925825260647713158795665)
            ·
              refine ⟨38944368945485784869096749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51925825260647713158795665 38944368945485784869096749)
              ·
                refine ⟨14604138354557169325911281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38944368945485784869096749 14604138354557169325911281)
                ·
                  refine ⟨10953103765917876994433461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14604138354557169325911281 10953103765917876994433461)
                  ·
                    refine ⟨1026853478054800968228137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10953103765917876994433461 1026853478054800968228137)
                    ·
                      rfl

theorem cell22_2999685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_2999685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999685 prefixEnd_2999685 := by exact prefixLift 2999685
  have htrace : WordTrace (prefixWord ++ tailWord_2999685) baseStart_2999685 baseEnd_2999685 := by
    simpa [prefixWord, tailWord_2999685, baseEnd_2999685] using wordTrace_append hprefix tailTrace_2999685
  have hstable : (prefixWord ++ tailWord_2999685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999685).length < 2 ^ (prefixWord ++ tailWord_2999685).sum := by decide
  have hdescent : baseEnd_2999685 < baseStart_2999685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999687 : List Nat := [1, 1, 4, 2, 2, 3, 1, 3, 5]
def baseStart_2999687 : Nat := 118140960795 + 2999687 * 2 ^ 59
def prefixEnd_2999687 : Nat := 4983230072969 + 3 ^ 40 * 2999687 * 2
def baseEnd_2999687 : Nat := 342284720898557876559377

theorem tailTrace_2999687 : CollatzResearch.WordTrace tailWord_2999687 prefixEnd_2999687 342284720898557876559377 := by
  unfold tailWord_2999687
  simp only [CollatzResearch.WordTrace]
  refine ⟨109407573083653779597965315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72938382055769186398643543 109407573083653779597965315)
  ·
    refine ⟨164111359625480669396947973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109407573083653779597965315 164111359625480669396947973)
    ·
      refine ⟨30770879929777625511927745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164111359625480669396947973 30770879929777625511927745)
      ·
        refine ⟨23078159947333219133945809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30770879929777625511927745 23078159947333219133945809)
        ·
          refine ⟨17308619960499914350459357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23078159947333219133945809 17308619960499914350459357)
          ·
            refine ⟨6490732485187467881422259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17308619960499914350459357 6490732485187467881422259)
            ·
              refine ⟨9736098727781201822133389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6490732485187467881422259 9736098727781201822133389)
              ·
                refine ⟨3651037022917950683300021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9736098727781201822133389 3651037022917950683300021)
                ·
                  refine ⟨342284720898557876559377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3651037022917950683300021 342284720898557876559377)
                  ·
                    rfl

theorem cell22_2999687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 5].length) (baseStart_2999687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999687 prefixEnd_2999687 := by exact prefixLift 2999687
  have htrace : WordTrace (prefixWord ++ tailWord_2999687) baseStart_2999687 baseEnd_2999687 := by
    simpa [prefixWord, tailWord_2999687, baseEnd_2999687] using wordTrace_append hprefix tailTrace_2999687
  have hstable : (prefixWord ++ tailWord_2999687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999687).length < 2 ^ (prefixWord ++ tailWord_2999687).sum := by decide
  have hdescent : baseEnd_2999687 < baseStart_2999687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999725 : List Nat := [1, 5, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2999725 : Nat := 118140960795 + 2999725 * 2 ^ 59
def prefixEnd_2999725 : Nat := 4983230072969 + 3 ^ 40 * 2999725 * 2
def baseEnd_2999725 : Nat := 1026867170872254197228015

theorem tailTrace_2999725 : CollatzResearch.WordTrace tailWord_2999725 prefixEnd_2999725 1026867170872254197228015 := by
  unfold tailWord_2999725
  simp only [CollatzResearch.WordTrace]
  refine ⟨109408959057516112087848629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72939306038344074725232419 109408959057516112087848629)
  ·
    refine ⟨10257089911642135508235809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109408959057516112087848629 10257089911642135508235809)
    ·
      refine ⟨7692817433731601631176857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10257089911642135508235809 7692817433731601631176857)
      ·
        refine ⟨5769613075298701223382643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7692817433731601631176857 5769613075298701223382643)
        ·
          refine ⟨8654419612948051835073965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769613075298701223382643 8654419612948051835073965)
          ·
            refine ⟨3245407354855519438152737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8654419612948051835073965 3245407354855519438152737)
            ·
              refine ⟨2434055516141639578614553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3245407354855519438152737 2434055516141639578614553)
              ·
                refine ⟨1825541637106229683960915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434055516141639578614553 1825541637106229683960915)
                ·
                  refine ⟨2738312455659344525941373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825541637106229683960915 2738312455659344525941373)
                  ·
                    refine ⟨1026867170872254197228015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738312455659344525941373 1026867170872254197228015)
                    ·
                      rfl

theorem cell22_2999725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2999725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999725 prefixEnd_2999725 := by exact prefixLift 2999725
  have htrace : WordTrace (prefixWord ++ tailWord_2999725) baseStart_2999725 baseEnd_2999725 := by
    simpa [prefixWord, tailWord_2999725, baseEnd_2999725] using wordTrace_append hprefix tailTrace_2999725
  have hstable : (prefixWord ++ tailWord_2999725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999725).length < 2 ^ (prefixWord ++ tailWord_2999725).sum := by decide
  have hdescent : baseEnd_2999725 < baseStart_2999725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999766 : List Nat := [5, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_2999766 : Nat := 118140960795 + 2999766 * 2 ^ 59
def prefixEnd_2999766 : Nat := 4983230072969 + 3 ^ 40 * 2999766 * 2
def baseEnd_2999766 : Nat := 342293735336714585650963

theorem tailTrace_2999766 : CollatzResearch.WordTrace tailWord_2999766 prefixEnd_2999766 342293735336714585650963 := by
  unfold tailWord_2999766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838153403147973505630697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72940302966911717393394101 6838153403147973505630697)
  ·
    refine ⟨5128615052360980129223023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6838153403147973505630697 5128615052360980129223023)
    ·
      refine ⟨7692922578541470193834535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5128615052360980129223023 7692922578541470193834535)
      ·
        refine ⟨11539383867812205290751803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7692922578541470193834535 11539383867812205290751803)
        ·
          refine ⟨17309075801718307936127705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11539383867812205290751803 17309075801718307936127705)
          ·
            refine ⟨12981806851288730952095779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17309075801718307936127705 12981806851288730952095779)
            ·
              refine ⟨19472710276933096428143669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12981806851288730952095779 19472710276933096428143669)
              ·
                refine ⟨1825566588462477790138469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19472710276933096428143669 1825566588462477790138469)
                ·
                  refine ⟨342293735336714585650963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1825566588462477790138469 342293735336714585650963)
                  ·
                    rfl

theorem cell22_2999766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_2999766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999766 prefixEnd_2999766 := by exact prefixLift 2999766
  have htrace : WordTrace (prefixWord ++ tailWord_2999766) baseStart_2999766 baseEnd_2999766 := by
    simpa [prefixWord, tailWord_2999766, baseEnd_2999766] using wordTrace_append hprefix tailTrace_2999766
  have hstable : (prefixWord ++ tailWord_2999766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999766).length < 2 ^ (prefixWord ++ tailWord_2999766).sum := by decide
  have hdescent : baseEnd_2999766 < baseStart_2999766 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999781 : List Nat := [1, 3, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_2999781 : Nat := 118140960795 + 2999781 * 2 ^ 59
def prefixEnd_2999781 : Nat := 4983230072969 + 3 ^ 40 * 2999781 * 2
def baseEnd_2999781 : Nat := 1026886340816688717827843

theorem tailTrace_2999781 : CollatzResearch.WordTrace tailWord_2999781 prefixEnd_2999781 1026886340816688717827843 := by
  unfold tailWord_2999781
  simp only [CollatzResearch.WordTrace]
  refine ⟨109411001545313233651887197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72940667696875489101258131 109411001545313233651887197)
  ·
    refine ⟨41029125579492462619457699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109411001545313233651887197 41029125579492462619457699)
    ·
      refine ⟨61543688369238693929186549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41029125579492462619457699 61543688369238693929186549)
      ·
        refine ⟨5769720784616127555861239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61543688369238693929186549 5769720784616127555861239)
        ·
          refine ⟨8654581176924191333791859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5769720784616127555861239 8654581176924191333791859)
          ·
            refine ⟨12981871765386287000687789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8654581176924191333791859 12981871765386287000687789)
            ·
              refine ⟨4868201912019857625257921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12981871765386287000687789 4868201912019857625257921)
              ·
                refine ⟨3651151434014893218943441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4868201912019857625257921 3651151434014893218943441)
                ·
                  refine ⟨2738363575511169914207581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651151434014893218943441 2738363575511169914207581)
                  ·
                    refine ⟨1026886340816688717827843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738363575511169914207581 1026886340816688717827843)
                    ·
                      rfl

theorem cell22_2999781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_2999781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999781 prefixEnd_2999781 := by exact prefixLift 2999781
  have htrace : WordTrace (prefixWord ++ tailWord_2999781) baseStart_2999781 baseEnd_2999781 := by
    simpa [prefixWord, tailWord_2999781, baseEnd_2999781] using wordTrace_append hprefix tailTrace_2999781
  have hstable : (prefixWord ++ tailWord_2999781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999781).length < 2 ^ (prefixWord ++ tailWord_2999781).sum := by decide
  have hdescent : baseEnd_2999781 < baseStart_2999781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999798 : List Nat := [5, 1, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_2999798 : Nat := 118140960795 + 2999798 * 2 ^ 59
def prefixEnd_2999798 : Nat := 4983230072969 + 3 ^ 40 * 2999798 * 2
def baseEnd_2999798 : Nat := 1026892160264106340152791

theorem tailTrace_2999798 : CollatzResearch.WordTrace tailWord_2999798 prefixEnd_2999798 1026892160264106340152791 := by
  unfold tailWord_2999798
  simp only [CollatzResearch.WordTrace]
  refine ⟨6838226349140727847203503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72941081057501097036837365 6838226349140727847203503)
  ·
    refine ⟨10257339523711091770805255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6838226349140727847203503 10257339523711091770805255)
    ·
      refine ⟨15386009285566637656207883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10257339523711091770805255 15386009285566637656207883)
      ·
        refine ⟨23079013928349956484311825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15386009285566637656207883 23079013928349956484311825)
        ·
          refine ⟨17309260446262467363233869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23079013928349956484311825 17309260446262467363233869)
          ·
            refine ⟨6490972667348425261212701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17309260446262467363233869 6490972667348425261212701)
            ·
              refine ⟨2434114750255659472954763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6490972667348425261212701 2434114750255659472954763)
              ·
                refine ⟨3651172125383489209432145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434114750255659472954763 3651172125383489209432145)
                ·
                  refine ⟨2738379094037616907074109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651172125383489209432145 2738379094037616907074109)
                  ·
                    refine ⟨1026892160264106340152791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738379094037616907074109 1026892160264106340152791)
                    ·
                      rfl

theorem cell22_2999798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_2999798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999798 prefixEnd_2999798 := by exact prefixLift 2999798
  have htrace : WordTrace (prefixWord ++ tailWord_2999798) baseStart_2999798 baseEnd_2999798 := by
    simpa [prefixWord, tailWord_2999798, baseEnd_2999798] using wordTrace_append hprefix tailTrace_2999798
  have hstable : (prefixWord ++ tailWord_2999798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999798).length < 2 ^ (prefixWord ++ tailWord_2999798).sum := by decide
  have hdescent : baseEnd_2999798 < baseStart_2999798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999843 : List Nat := [1, 1, 1, 4, 6, 1, 1, 1, 3, 3]
def baseStart_2999843 : Nat := 118140960795 + 2999843 * 2 ^ 59
def prefixEnd_2999843 : Nat := 4983230072969 + 3 ^ 40 * 2999843 * 2
def baseEnd_2999843 : Nat := 1026907564683741222777653

theorem tailTrace_2999843 : CollatzResearch.WordTrace tailWord_2999843 prefixEnd_2999843 1026907564683741222777653 := by
  unfold tailWord_2999843
  simp only [CollatzResearch.WordTrace]
  refine ⟨109413262871088618240644183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72942175247392412160429455 109413262871088618240644183)
  ·
    refine ⟨164119894306632927360966275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109413262871088618240644183 164119894306632927360966275)
    ·
      refine ⟨246179841459949391041449413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164119894306632927360966275 246179841459949391041449413)
      ·
        refine ⟨46158720273740510820271765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246179841459949391041449413 46158720273740510820271765)
        ·
          refine ⟨2163690012831586444700239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46158720273740510820271765 2163690012831586444700239)
          ·
            refine ⟨3245535019247379667050359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163690012831586444700239 3245535019247379667050359)
            ·
              refine ⟨4868302528871069500575539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3245535019247379667050359 4868302528871069500575539)
              ·
                refine ⟨7302453793306604250863309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4868302528871069500575539 7302453793306604250863309)
                ·
                  refine ⟨2738420172489976594073741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7302453793306604250863309 2738420172489976594073741)
                  ·
                    refine ⟨1026907564683741222777653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738420172489976594073741 1026907564683741222777653)
                    ·
                      rfl

theorem cell22_2999843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 1, 3, 3].length) (baseStart_2999843 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999843 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999843 prefixEnd_2999843 := by exact prefixLift 2999843
  have htrace : WordTrace (prefixWord ++ tailWord_2999843) baseStart_2999843 baseEnd_2999843 := by
    simpa [prefixWord, tailWord_2999843, baseEnd_2999843] using wordTrace_append hprefix tailTrace_2999843
  have hstable : (prefixWord ++ tailWord_2999843).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999843).length < 2 ^ (prefixWord ++ tailWord_2999843).sum := by decide
  have hdescent : baseEnd_2999843 < baseStart_2999843 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2999929 : List Nat := [1, 2, 1, 3, 3, 1, 5, 6]
def baseStart_2999929 : Nat := 118140960795 + 2999929 * 2 ^ 59
def prefixEnd_2999929 : Nat := 4983230072969 + 3 ^ 40 * 2999929 * 2
def baseEnd_2999929 : Nat := 114104111582362851680821

theorem tailTrace_2999929 : CollatzResearch.WordTrace tailWord_2999929 prefixEnd_2999929 114104111582362851680821 := by
  unfold tailWord_2999929
  simp only [CollatzResearch.WordTrace]
  refine ⟨109416399548777054928274841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72944266365851369952183227 109416399548777054928274841)
  ·
    refine ⟨82062299661582791196206131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109416399548777054928274841 82062299661582791196206131)
    ·
      refine ⟨123093449492374186794309197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82062299661582791196206131 123093449492374186794309197)
      ·
        refine ⟨46160043559640320047865949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123093449492374186794309197 46160043559640320047865949)
        ·
          refine ⟨17310016334865120017949731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46160043559640320047865949 17310016334865120017949731)
          ·
            refine ⟨25965024502297680026924597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17310016334865120017949731 25965024502297680026924597)
            ·
              refine ⟨2434221047090407502524181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25965024502297680026924597 2434221047090407502524181)
              ·
                refine ⟨114104111582362851680821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2434221047090407502524181 114104111582362851680821)
                ·
                  rfl

theorem cell22_2999929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5, 6].length) (baseStart_2999929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2999929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2999929 prefixEnd_2999929 := by exact prefixLift 2999929
  have htrace : WordTrace (prefixWord ++ tailWord_2999929) baseStart_2999929 baseEnd_2999929 := by
    simpa [prefixWord, tailWord_2999929, baseEnd_2999929] using wordTrace_append hprefix tailTrace_2999929
  have hstable : (prefixWord ++ tailWord_2999929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2999929).length < 2 ^ (prefixWord ++ tailWord_2999929).sum := by decide
  have hdescent : baseEnd_2999929 < baseStart_2999929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2999929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000012 : List Nat := [2, 2, 1, 5, 2, 1, 3, 2, 1, 3]
def baseStart_3000012 : Nat := 118140960795 + 3000012 * 2 ^ 59
def prefixEnd_3000012 : Nat := 4983230072969 + 3 ^ 40 * 3000012 * 2
def baseEnd_3000012 : Nat := 1026965416837481115302135

theorem tailTrace_3000012 : CollatzResearch.WordTrace tailWord_3000012 prefixEnd_3000012 1026965416837481115302135 := by
  unfold tailWord_3000012
  simp only [CollatzResearch.WordTrace]
  refine ⟨54709713403738180051773145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72946284538317573402364193 54709713403738180051773145)
  ·
    refine ⟨41032285052803635038829859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54709713403738180051773145 41032285052803635038829859)
    ·
      refine ⟨61548427579205452558244789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41032285052803635038829859 61548427579205452558244789)
      ·
        refine ⟨5770165085550511177335449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61548427579205452558244789 5770165085550511177335449)
        ·
          refine ⟨4327623814162883383001587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5770165085550511177335449 4327623814162883383001587)
          ·
            refine ⟨6491435721244325074502381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4327623814162883383001587 6491435721244325074502381)
            ·
              refine ⟨2434288395466621902938393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6491435721244325074502381 2434288395466621902938393)
              ·
                refine ⟨1825716296599966427203795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434288395466621902938393 1825716296599966427203795)
                ·
                  refine ⟨2738574444899949640805693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825716296599966427203795 2738574444899949640805693)
                  ·
                    refine ⟨1026965416837481115302135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738574444899949640805693 1026965416837481115302135)
                    ·
                      rfl

theorem cell22_3000012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_3000012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000012 prefixEnd_3000012 := by exact prefixLift 3000012
  have htrace : WordTrace (prefixWord ++ tailWord_3000012) baseStart_3000012 baseEnd_3000012 := by
    simpa [prefixWord, tailWord_3000012, baseEnd_3000012] using wordTrace_append hprefix tailTrace_3000012
  have hstable : (prefixWord ++ tailWord_3000012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000012).length < 2 ^ (prefixWord ++ tailWord_3000012).sum := by decide
  have hdescent : baseEnd_3000012 < baseStart_3000012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000068 : List Nat := [2, 3, 2, 2, 1, 2, 1, 4, 2, 3]
def baseStart_3000068 : Nat := 118140960795 + 3000068 * 2 ^ 59
def prefixEnd_3000068 : Nat := 4983230072969 + 3 ^ 40 * 3000068 * 2
def baseEnd_3000068 : Nat := 1026984586781915635901963

theorem tailTrace_3000068 : CollatzResearch.WordTrace tailWord_3000068 prefixEnd_3000068 1026984586781915635901963 := by
  unfold tailWord_3000068
  simp only [CollatzResearch.WordTrace]
  refine ⟨54710734647636740833792429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72947646196848987778389905 54710734647636740833792429)
  ·
    refine ⟨20516525492863777812672161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54710734647636740833792429 20516525492863777812672161)
    ·
      refine ⟨15387394119647833359504121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20516525492863777812672161 15387394119647833359504121)
      ·
        refine ⟨11540545589735875019628091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15387394119647833359504121 11540545589735875019628091)
        ·
          refine ⟨17310818384603812529442137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11540545589735875019628091 17310818384603812529442137)
          ·
            refine ⟨12983113788452859397081603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17310818384603812529442137 12983113788452859397081603)
            ·
              refine ⟨19474670682679289095622405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12983113788452859397081603 19474670682679289095622405)
              ·
                refine ⟨3651500753002366705429201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19474670682679289095622405 3651500753002366705429201)
                ·
                  refine ⟨2738625564751775029071901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651500753002366705429201 2738625564751775029071901)
                  ·
                    refine ⟨1026984586781915635901963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738625564751775029071901 1026984586781915635901963)
                    ·
                      rfl

theorem cell22_3000068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_3000068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000068 prefixEnd_3000068 := by exact prefixLift 3000068
  have htrace : WordTrace (prefixWord ++ tailWord_3000068) baseStart_3000068 baseEnd_3000068 := by
    simpa [prefixWord, tailWord_3000068, baseEnd_3000068] using wordTrace_append hprefix tailTrace_3000068
  have hstable : (prefixWord ++ tailWord_3000068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000068).length < 2 ^ (prefixWord ++ tailWord_3000068).sum := by decide
  have hdescent : baseEnd_3000068 < baseStart_3000068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000164 : List Nat := [2, 3, 1, 1, 6, 1, 1, 3, 1, 3]
def baseStart_3000164 : Nat := 118140960795 + 3000164 * 2 ^ 59
def prefixEnd_3000164 : Nat := 4983230072969 + 3 ^ 40 * 3000164 * 2
def baseEnd_3000164 : Nat := 1027017449543803385501669

theorem tailTrace_3000164 : CollatzResearch.WordTrace tailWord_3000164 prefixEnd_3000164 1027017449543803385501669 := by
  unfold tailWord_3000164
  simp only [CollatzResearch.WordTrace]
  refine ⟨54712485351462845031539773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72949980468617126708719697 54712485351462845031539773)
  ·
    refine ⟨20517182006798566886827415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54712485351462845031539773 20517182006798566886827415)
    ·
      refine ⟨30775773010197850330241123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20517182006798566886827415 30775773010197850330241123)
      ·
        refine ⟨46163659515296775495361685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30775773010197850330241123 46163659515296775495361685)
        ·
          refine ⟨2163921539779536351345079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 46163659515296775495361685 2163921539779536351345079)
          ·
            refine ⟨3245882309669304527017619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2163921539779536351345079 3245882309669304527017619)
            ·
              refine ⟨4868823464503956790526429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3245882309669304527017619 4868823464503956790526429)
              ·
                refine ⟨1825808799188983796447411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4868823464503956790526429 1825808799188983796447411)
                ·
                  refine ⟨2738713198783475694671117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1825808799188983796447411 2738713198783475694671117)
                  ·
                    refine ⟨1027017449543803385501669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738713198783475694671117 1027017449543803385501669)
                    ·
                      rfl

theorem cell22_3000164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_3000164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000164 prefixEnd_3000164 := by exact prefixLift 3000164
  have htrace : WordTrace (prefixWord ++ tailWord_3000164) baseStart_3000164 baseEnd_3000164 := by
    simpa [prefixWord, tailWord_3000164, baseEnd_3000164] using wordTrace_append hprefix tailTrace_3000164
  have hstable : (prefixWord ++ tailWord_3000164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000164).length < 2 ^ (prefixWord ++ tailWord_3000164).sum := by decide
  have hdescent : baseEnd_3000164 < baseStart_3000164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000173 : List Nat := [1, 5, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3000173 : Nat := 118140960795 + 3000173 * 2 ^ 59
def prefixEnd_3000173 : Nat := 4983230072969 + 3 ^ 40 * 3000173 * 2
def baseEnd_3000173 : Nat := 1027020530427730362026641

theorem tailTrace_3000173 : CollatzResearch.WordTrace tailWord_3000173 prefixEnd_3000173 1027020530427730362026641 := by
  unfold tailWord_3000173
  simp only [CollatzResearch.WordTrace]
  refine ⟨109425298959893084600157173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72950199306595389733438115 109425298959893084600157173)
  ·
    refine ⟨10258621777489976681264735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109425298959893084600157173 10258621777489976681264735)
    ·
      refine ⟨15387932666234965021897103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10258621777489976681264735 15387932666234965021897103)
      ·
        refine ⟨23081898999352447532845655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15387932666234965021897103 23081898999352447532845655)
        ·
          refine ⟨34622848499028671299268483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23081898999352447532845655 34622848499028671299268483)
          ·
            refine ⟨51934272748543006948902725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34622848499028671299268483 51934272748543006948902725)
            ·
              refine ⟨9737676140351813802919261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51934272748543006948902725 9737676140351813802919261)
              ·
                refine ⟨3651628552631930176094723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9737676140351813802919261 3651628552631930176094723)
                ·
                  refine ⟨5477442828947895264142085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651628552631930176094723 5477442828947895264142085)
                  ·
                    refine ⟨1027020530427730362026641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5477442828947895264142085 1027020530427730362026641)
                    ·
                      rfl

theorem cell22_3000173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3000173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000173 prefixEnd_3000173 := by exact prefixLift 3000173
  have htrace : WordTrace (prefixWord ++ tailWord_3000173) baseStart_3000173 baseEnd_3000173 := by
    simpa [prefixWord, tailWord_3000173, baseEnd_3000173] using wordTrace_append hprefix tailTrace_3000173
  have hstable : (prefixWord ++ tailWord_3000173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000173).length < 2 ^ (prefixWord ++ tailWord_3000173).sum := by decide
  have hdescent : baseEnd_3000173 < baseStart_3000173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000201 : List Nat := [1, 2, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_3000201 : Nat := 118140960795 + 3000201 * 2 ^ 59
def prefixEnd_3000201 : Nat := 4983230072969 + 3 ^ 40 * 3000201 * 2
def baseEnd_3000201 : Nat := 1027030115399947622326555

theorem tailTrace_3000201 : CollatzResearch.WordTrace tailWord_3000201 prefixEnd_3000201 1027030115399947622326555 := by
  unfold tailWord_3000201
  simp only [CollatzResearch.WordTrace]
  refine ⟨109426320203791645382176457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72950880135861096921450971 109426320203791645382176457)
  ·
    refine ⟨82069740152843734036632343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109426320203791645382176457 82069740152843734036632343)
    ·
      refine ⟨123104610229265601054948515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82069740152843734036632343 123104610229265601054948515)
      ·
        refine ⟨184656915343898401582422773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123104610229265601054948515 184656915343898401582422773)
        ·
          refine ⟨17311585813490475148352135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184656915343898401582422773 17311585813490475148352135)
          ·
            refine ⟨25967378720235712722528203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17311585813490475148352135 25967378720235712722528203)
            ·
              refine ⟨38951068080353569083792305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25967378720235712722528203 38951068080353569083792305)
              ·
                refine ⟨29213301060265176812844229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38951068080353569083792305 29213301060265176812844229)
                ·
                  refine ⟨5477493948799720652408293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29213301060265176812844229 5477493948799720652408293)
                  ·
                    refine ⟨1027030115399947622326555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5477493948799720652408293 1027030115399947622326555)
                    ·
                      rfl

theorem cell22_3000201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_3000201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000201 prefixEnd_3000201 := by exact prefixLift 3000201
  have htrace : WordTrace (prefixWord ++ tailWord_3000201) baseStart_3000201 baseEnd_3000201 := by
    simpa [prefixWord, tailWord_3000201, baseEnd_3000201] using wordTrace_append hprefix tailTrace_3000201
  have hstable : (prefixWord ++ tailWord_3000201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000201).length < 2 ^ (prefixWord ++ tailWord_3000201).sum := by decide
  have hdescent : baseEnd_3000201 < baseStart_3000201 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000218 : List Nat := [3, 1, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_3000218 : Nat := 118140960795 + 3000218 * 2 ^ 59
def prefixEnd_3000218 : Nat := 4983230072969 + 3 ^ 40 * 3000218 * 2
def baseEnd_3000218 : Nat := 1027035934847365244651503

theorem tailTrace_3000218 : CollatzResearch.WordTrace tailWord_3000218 prefixEnd_3000218 1027035934847365244651503 := by
  unfold tailWord_3000218
  simp only [CollatzResearch.WordTrace]
  refine ⟨27356735061182514321386327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72951293496486704857030205 27356735061182514321386327)
  ·
    refine ⟨41035102591773771482079491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27356735061182514321386327 41035102591773771482079491)
    ·
      refine ⟨61552653887660657223119237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41035102591773771482079491 61552653887660657223119237)
      ·
        refine ⟨11541122603936373229334857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61552653887660657223119237 11541122603936373229334857)
        ·
          refine ⟨8655841952952279922001143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11541122603936373229334857 8655841952952279922001143)
          ·
            refine ⟨12983762929428419883001715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8655841952952279922001143 12983762929428419883001715)
            ·
              refine ⟨19475644394142629824502573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12983762929428419883001715 19475644394142629824502573)
              ·
                refine ⟨7303366647803486184188465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19475644394142629824502573 7303366647803486184188465)
                ·
                  refine ⟨5477524985852614638141349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7303366647803486184188465 5477524985852614638141349)
                  ·
                    refine ⟨1027035934847365244651503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5477524985852614638141349 1027035934847365244651503)
                    ·
                      rfl

theorem cell22_3000218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_3000218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000218 prefixEnd_3000218 := by exact prefixLift 3000218
  have htrace : WordTrace (prefixWord ++ tailWord_3000218) baseStart_3000218 baseEnd_3000218 := by
    simpa [prefixWord, tailWord_3000218, baseEnd_3000218] using wordTrace_append hprefix tailTrace_3000218
  have hstable : (prefixWord ++ tailWord_3000218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000218).length < 2 ^ (prefixWord ++ tailWord_3000218).sum := by decide
  have hdescent : baseEnd_3000218 < baseStart_3000218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000248 : List Nat := [2, 1, 2, 1, 2, 3, 2, 3, 3, 3]
def baseStart_3000248 : Nat := 118140960795 + 3000248 * 2 ^ 59
def prefixEnd_3000248 : Nat := 4983230072969 + 3 ^ 40 * 3000248 * 2
def baseEnd_3000248 : Nat := 1027046204460455166401411

theorem tailTrace_3000248 : CollatzResearch.WordTrace tailWord_3000248 prefixEnd_3000248 1027046204460455166401411 := by
  unfold tailWord_3000248
  simp only [CollatzResearch.WordTrace]
  refine ⟨54714017217310686204568699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72952022956414248272758265 54714017217310686204568699)
  ·
    refine ⟨82071025825966029306853049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54714017217310686204568699 82071025825966029306853049)
    ·
      refine ⟨61553269369474521980139787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82071025825966029306853049 61553269369474521980139787)
      ·
        refine ⟨92329904054211782970209681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61553269369474521980139787 92329904054211782970209681)
        ·
          refine ⟨69247428040658837227657261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92329904054211782970209681 69247428040658837227657261)
          ·
            refine ⟨25967785515247063960371473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69247428040658837227657261 25967785515247063960371473)
            ·
              refine ⟨19475839136435297970278605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25967785515247063960371473 19475839136435297970278605)
              ·
                refine ⟨7303439676163236738854477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19475839136435297970278605 7303439676163236738854477)
                ·
                  refine ⟨2738789878561213777070429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7303439676163236738854477 2738789878561213777070429)
                  ·
                    refine ⟨1027046204460455166401411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738789878561213777070429 1027046204460455166401411)
                    ·
                      rfl

theorem cell22_3000248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 3, 3, 3].length) (baseStart_3000248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000248 prefixEnd_3000248 := by exact prefixLift 3000248
  have htrace : WordTrace (prefixWord ++ tailWord_3000248) baseStart_3000248 baseEnd_3000248 := by
    simpa [prefixWord, tailWord_3000248, baseEnd_3000248] using wordTrace_append hprefix tailTrace_3000248
  have hstable : (prefixWord ++ tailWord_3000248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000248).length < 2 ^ (prefixWord ++ tailWord_3000248).sum := by decide
  have hdescent : baseEnd_3000248 < baseStart_3000248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000325 : List Nat := [1, 3, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_3000325 : Nat := 118140960795 + 3000325 * 2 ^ 59
def prefixEnd_3000325 : Nat := 4983230072969 + 3 ^ 40 * 3000325 * 2
def baseEnd_3000325 : Nat := 1027072563134052632226175

theorem tailTrace_3000325 : CollatzResearch.WordTrace tailWord_3000325 prefixEnd_3000325 1027072563134052632226175 := by
  unfold tailWord_3000325
  simp only [CollatzResearch.WordTrace]
  refine ⟨109430842855342414559690429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72953895236894943039793619 109430842855342414559690429)
  ·
    refine ⟨41036566070753405459883911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109430842855342414559690429 41036566070753405459883911)
    ·
      refine ⟨61554849106130108189825867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41036566070753405459883911 61554849106130108189825867)
      ·
        refine ⟨92332273659195162284738801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61554849106130108189825867 92332273659195162284738801)
        ·
          refine ⟨69249205244396371713554101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92332273659195162284738801 69249205244396371713554101)
          ·
            refine ⟨6492112991662159848145697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69249205244396371713554101 6492112991662159848145697)
            ·
              refine ⟨4869084743746619886109273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492112991662159848145697 4869084743746619886109273)
              ·
                refine ⟨3651813557809964914581955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4869084743746619886109273 3651813557809964914581955)
                ·
                  refine ⟨5477720336714947371872933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3651813557809964914581955 5477720336714947371872933)
                  ·
                    refine ⟨1027072563134052632226175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5477720336714947371872933 1027072563134052632226175)
                    ·
                      rfl

theorem cell22_3000325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_3000325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000325 prefixEnd_3000325 := by exact prefixLift 3000325
  have htrace : WordTrace (prefixWord ++ tailWord_3000325) baseStart_3000325 baseEnd_3000325 := by
    simpa [prefixWord, tailWord_3000325, baseEnd_3000325] using wordTrace_append hprefix tailTrace_3000325
  have hstable : (prefixWord ++ tailWord_3000325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000325).length < 2 ^ (prefixWord ++ tailWord_3000325).sum := by decide
  have hdescent : baseEnd_3000325 < baseStart_3000325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000355 : List Nat := [1, 1, 1, 4, 3, 1, 2, 4, 2, 3]
def baseStart_3000355 : Nat := 118140960795 + 3000355 * 2 ^ 59
def prefixEnd_3000355 : Nat := 4983230072969 + 3 ^ 40 * 3000355 * 2
def baseEnd_3000355 : Nat := 1027082832747142553976083

theorem tailTrace_3000355 : CollatzResearch.WordTrace tailWord_3000355 prefixEnd_3000355 1027082832747142553976083 := by
  unfold tailWord_3000355
  simp only [CollatzResearch.WordTrace]
  refine ⟨109431937045233729683282519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72954624696822486455521679 109431937045233729683282519)
  ·
    refine ⟨164147905567850594524923779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109431937045233729683282519 164147905567850594524923779)
    ·
      refine ⟨246221858351775891787385669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164147905567850594524923779 246221858351775891787385669)
      ·
        refine ⟨46166598440957979710134813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246221858351775891787385669 46166598440957979710134813)
        ·
          refine ⟨17312474415359242391300555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46166598440957979710134813 17312474415359242391300555)
          ·
            refine ⟨25968711623038863586950833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17312474415359242391300555 25968711623038863586950833)
            ·
              refine ⟨19476533717279147690213125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25968711623038863586950833 19476533717279147690213125)
              ·
                refine ⟨3651850071989840191914961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19476533717279147690213125 3651850071989840191914961)
                ·
                  refine ⟨2738887553992380143936221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651850071989840191914961 2738887553992380143936221)
                  ·
                    refine ⟨1027082832747142553976083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738887553992380143936221 1027082832747142553976083)
                    ·
                      rfl

theorem cell22_3000355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 3].length) (baseStart_3000355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000355 prefixEnd_3000355 := by exact prefixLift 3000355
  have htrace : WordTrace (prefixWord ++ tailWord_3000355) baseStart_3000355 baseEnd_3000355 := by
    simpa [prefixWord, tailWord_3000355, baseEnd_3000355] using wordTrace_append hprefix tailTrace_3000355
  have hstable : (prefixWord ++ tailWord_3000355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000355).length < 2 ^ (prefixWord ++ tailWord_3000355).sum := by decide
  have hdescent : baseEnd_3000355 < baseStart_3000355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000357 : List Nat := [1, 3, 1, 2, 2, 4, 3, 2, 4]
def baseStart_3000357 : Nat := 118140960795 + 3000357 * 2 ^ 59
def prefixEnd_3000357 : Nat := 4983230072969 + 3 ^ 40 * 3000357 * 2
def baseEnd_3000357 : Nat := 342361172462671738475359

theorem tailTrace_3000357 : CollatzResearch.WordTrace tailWord_3000357 prefixEnd_3000357 342361172462671738475359 := by
  unfold tailWord_3000357
  simp only [CollatzResearch.WordTrace]
  refine ⟨109432009991226484024855325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72954673327484322683236883 109432009991226484024855325)
  ·
    refine ⟨41037003746709931509320747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109432009991226484024855325 41037003746709931509320747)
    ·
      refine ⟨61555505620064897263981121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41037003746709931509320747 61555505620064897263981121)
      ·
        refine ⟨46166629215048672947985841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61555505620064897263981121 46166629215048672947985841)
        ·
          refine ⟨34624971911286504710989381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46166629215048672947985841 34624971911286504710989381)
          ·
            refine ⟨6492182233366219633310509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34624971911286504710989381 6492182233366219633310509)
            ·
              refine ⟨2434568337512332362491441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6492182233366219633310509 2434568337512332362491441)
              ·
                refine ⟨1825926253134249271868581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434568337512332362491441 1825926253134249271868581)
                ·
                  refine ⟨342361172462671738475359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1825926253134249271868581 342361172462671738475359)
                  ·
                    rfl

theorem cell22_3000357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_3000357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000357 prefixEnd_3000357 := by exact prefixLift 3000357
  have htrace : WordTrace (prefixWord ++ tailWord_3000357) baseStart_3000357 baseEnd_3000357 := by
    simpa [prefixWord, tailWord_3000357, baseEnd_3000357] using wordTrace_append hprefix tailTrace_3000357
  have hstable : (prefixWord ++ tailWord_3000357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000357).length < 2 ^ (prefixWord ++ tailWord_3000357).sum := by decide
  have hdescent : baseEnd_3000357 < baseStart_3000357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000368 : List Nat := [2, 1, 1, 1, 2, 6, 2, 7]
def baseStart_3000368 : Nat := 118140960795 + 3000368 * 2 ^ 59
def prefixEnd_3000368 : Nat := 4983230072969 + 3 ^ 40 * 3000368 * 2
def baseEnd_3000368 : Nat := 114120809212534983711227

theorem tailTrace_3000368 : CollatzResearch.WordTrace tailWord_3000368 prefixEnd_3000368 114120809212534983711227 := by
  unfold tailWord_3000368
  simp only [CollatzResearch.WordTrace]
  refine ⟨54716205597093316451752879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72954940796124421935670505 54716205597093316451752879)
  ·
    refine ⟨82074308395639974677629319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54716205597093316451752879 82074308395639974677629319)
    ·
      refine ⟨123111462593459962016443979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82074308395639974677629319 123111462593459962016443979)
      ·
        refine ⟨184667193890189943024665969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123111462593459962016443979 184667193890189943024665969)
        ·
          refine ⟨138500395417642457268499477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184667193890189943024665969 138500395417642457268499477)
          ·
            refine ⟨6492206035201990184460913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 138500395417642457268499477 6492206035201990184460913)
            ·
              refine ⟨4869154526401492638345685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492206035201990184460913 4869154526401492638345685)
              ·
                refine ⟨114120809212534983711227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4869154526401492638345685 114120809212534983711227)
                ·
                  rfl

theorem cell22_3000368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 7].length) (baseStart_3000368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000368 prefixEnd_3000368 := by exact prefixLift 3000368
  have htrace : WordTrace (prefixWord ++ tailWord_3000368) baseStart_3000368 baseEnd_3000368 := by
    simpa [prefixWord, tailWord_3000368, baseEnd_3000368] using wordTrace_append hprefix tailTrace_3000368
  have hstable : (prefixWord ++ tailWord_3000368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000368).length < 2 ^ (prefixWord ++ tailWord_3000368).sum := by decide
  have hdescent : baseEnd_3000368 < baseStart_3000368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000406 : List Nat := [5, 2, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3000406 : Nat := 118140960795 + 3000406 * 2 ^ 59
def prefixEnd_3000406 : Nat := 4983230072969 + 3 ^ 40 * 3000406 * 2
def baseEnd_3000406 : Nat := 1027100291089395420950927

theorem tailTrace_3000406 : CollatzResearch.WordTrace tailWord_3000406 prefixEnd_3000406 1027100291089395420950927 := by
  unfold tailWord_3000406
  simp only [CollatzResearch.WordTrace]
  refine ⟨6839612323003060337086817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72955864778699310262259381 6839612323003060337086817)
  ·
    refine ⟨5129709242252295252815113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6839612323003060337086817 5129709242252295252815113)
    ·
      refine ⟨3847281931689221439611335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5129709242252295252815113 3847281931689221439611335)
      ·
        refine ⟨5770922897533832159417003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3847281931689221439611335 5770922897533832159417003)
        ·
          refine ⟨8656384346300748239125505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5770922897533832159417003 8656384346300748239125505)
          ·
            refine ⟨6492288259725561179344129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8656384346300748239125505 6492288259725561179344129)
            ·
              refine ⟨4869216194794170884508097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492288259725561179344129 4869216194794170884508097)
              ·
                refine ⟨3651912146095628163381073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4869216194794170884508097 3651912146095628163381073)
                ·
                  refine ⟨2738934109571721122535805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3651912146095628163381073 2738934109571721122535805)
                  ·
                    refine ⟨1027100291089395420950927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2738934109571721122535805 1027100291089395420950927)
                    ·
                      rfl

theorem cell22_3000406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3000406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000406 prefixEnd_3000406 := by exact prefixLift 3000406
  have htrace : WordTrace (prefixWord ++ tailWord_3000406) baseStart_3000406 baseEnd_3000406 := by
    simpa [prefixWord, tailWord_3000406, baseEnd_3000406] using wordTrace_append hprefix tailTrace_3000406
  have hstable : (prefixWord ++ tailWord_3000406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000406).length < 2 ^ (prefixWord ++ tailWord_3000406).sum := by decide
  have hdescent : baseEnd_3000406 < baseStart_3000406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000428 : List Nat := [2, 2, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_3000428 : Nat := 118140960795 + 3000428 * 2 ^ 59
def prefixEnd_3000428 : Nat := 4983230072969 + 3 ^ 40 * 3000428 * 2
def baseEnd_3000428 : Nat := 1027107822138994696900859

theorem tailTrace_3000428 : CollatzResearch.WordTrace tailWord_3000428 prefixEnd_3000428 1027107822138994696900859 := by
  unfold tailWord_3000428
  simp only [CollatzResearch.WordTrace]
  refine ⟨54717299786984631575344969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72956399715979508767126625 54717299786984631575344969)
  ·
    refine ⟨41037974840238473681508727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54717299786984631575344969 41037974840238473681508727)
    ·
      refine ⟨61556962260357710522263091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41037974840238473681508727 61556962260357710522263091)
      ·
        refine ⟨92335443390536565783394637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61556962260357710522263091 92335443390536565783394637)
        ·
          refine ⟨34625791271451212168772989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92335443390536565783394637 34625791271451212168772989)
          ·
            refine ⟨12984671726794204563289871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34625791271451212168772989 12984671726794204563289871)
            ·
              refine ⟨19477007590191306844934807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12984671726794204563289871 19477007590191306844934807)
              ·
                refine ⟨29215511385286960267402211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19477007590191306844934807 29215511385286960267402211)
                ·
                  refine ⟨43823267077930440401103317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29215511385286960267402211 43823267077930440401103317)
                  ·
                    refine ⟨1027107822138994696900859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43823267077930440401103317 1027107822138994696900859)
                    ·
                      rfl

theorem cell22_3000428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_3000428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000428 prefixEnd_3000428 := by exact prefixLift 3000428
  have htrace : WordTrace (prefixWord ++ tailWord_3000428) baseStart_3000428 baseEnd_3000428 := by
    simpa [prefixWord, tailWord_3000428, baseEnd_3000428] using wordTrace_append hprefix tailTrace_3000428
  have hstable : (prefixWord ++ tailWord_3000428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000428).length < 2 ^ (prefixWord ++ tailWord_3000428).sum := by decide
  have hdescent : baseEnd_3000428 < baseStart_3000428 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000430 : List Nat := [4, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_3000430 : Nat := 118140960795 + 3000430 * 2 ^ 59
def prefixEnd_3000430 : Nat := 4983230072969 + 3 ^ 40 * 3000430 * 2
def baseEnd_3000430 : Nat := 342369502259955786116951

theorem tailTrace_3000430 : CollatzResearch.WordTrace tailWord_3000430 prefixEnd_3000430 342369502259955786116951 := by
  unfold tailWord_3000430
  simp only [CollatzResearch.WordTrace]
  refine ⟨13679334064995252186532843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72956448346641344994841829 13679334064995252186532843)
  ·
    refine ⟨20519001097492878279799265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13679334064995252186532843 20519001097492878279799265)
    ·
      refine ⟨15389250823119658709849449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20519001097492878279799265 15389250823119658709849449)
      ·
        refine ⟨11541938117339744032387087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15389250823119658709849449 11541938117339744032387087)
        ·
          refine ⟨17312907176009616048580631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11541938117339744032387087 17312907176009616048580631)
          ·
            refine ⟨25969360764014424072870947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17312907176009616048580631 25969360764014424072870947)
            ·
              refine ⟨38954041146021636109306421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25969360764014424072870947 38954041146021636109306421)
              ·
                refine ⟨3651941357439528385247477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38954041146021636109306421 3651941357439528385247477)
                ·
                  refine ⟨342369502259955786116951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3651941357439528385247477 342369502259955786116951)
                  ·
                    rfl

theorem cell22_3000430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_3000430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000430 prefixEnd_3000430 := by exact prefixLift 3000430
  have htrace : WordTrace (prefixWord ++ tailWord_3000430) baseStart_3000430 baseEnd_3000430 := by
    simpa [prefixWord, tailWord_3000430, baseEnd_3000430] using wordTrace_append hprefix tailTrace_3000430
  have hstable : (prefixWord ++ tailWord_3000430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000430).length < 2 ^ (prefixWord ++ tailWord_3000430).sum := by decide
  have hdescent : baseEnd_3000430 < baseStart_3000430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000473 : List Nat := [1, 2, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_3000473 : Nat := 118140960795 + 3000473 * 2 ^ 59
def prefixEnd_3000473 : Nat := 4983230072969 + 3 ^ 40 * 3000473 * 2
def baseEnd_3000473 : Nat := 1027123226558629579525721

theorem tailTrace_3000473 : CollatzResearch.WordTrace tailWord_3000473 prefixEnd_3000473 1027123226558629579525721 := by
  unfold tailWord_3000473
  simp only [CollatzResearch.WordTrace]
  refine ⟨109436240858806235836078073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72957493905870823890718715 109436240858806235836078073)
  ·
    refine ⟨82077180644104676877058555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109436240858806235836078073 82077180644104676877058555)
    ·
      refine ⟨123115770966157015315587833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82077180644104676877058555 123115770966157015315587833)
      ·
        refine ⟨92336828224617761486690875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123115770966157015315587833 92336828224617761486690875)
        ·
          refine ⟨138505242336926642230036313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92336828224617761486690875 138505242336926642230036313)
          ·
            refine ⟨103878931752694981672527235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138505242336926642230036313 103878931752694981672527235)
            ·
              refine ⟨155818397629042472508790853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103878931752694981672527235 155818397629042472508790853)
              ·
                refine ⟨29215949555445463595398285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 155818397629042472508790853 29215949555445463595398285)
                ·
                  refine ⟨10955981083292048848274357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29215949555445463595398285 10955981083292048848274357)
                  ·
                    refine ⟨1027123226558629579525721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10955981083292048848274357 1027123226558629579525721)
                    ·
                      rfl

theorem cell22_3000473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_3000473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000473 prefixEnd_3000473 := by exact prefixLift 3000473
  have htrace : WordTrace (prefixWord ++ tailWord_3000473) baseStart_3000473 baseEnd_3000473 := by
    simpa [prefixWord, tailWord_3000473, baseEnd_3000473] using wordTrace_append hprefix tailTrace_3000473
  have hstable : (prefixWord ++ tailWord_3000473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000473).length < 2 ^ (prefixWord ++ tailWord_3000473).sum := by decide
  have hdescent : baseEnd_3000473 < baseStart_3000473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000475 : List Nat := [1, 1, 1, 1, 1, 1, 2, 10, 4]
def baseStart_3000475 : Nat := 118140960795 + 3000475 * 2 ^ 59
def prefixEnd_3000475 : Nat := 4983230072969 + 3 ^ 40 * 3000475 * 2
def baseEnd_3000475 : Nat := 342374637066500746991905

theorem tailTrace_3000475 : CollatzResearch.WordTrace tailWord_3000475 prefixEnd_3000475 342374637066500746991905 := by
  unfold tailWord_3000475
  simp only [CollatzResearch.WordTrace]
  refine ⟨109436313804798990177650879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72957542536532660118433919 109436313804798990177650879)
  ·
    refine ⟨164154470707198485266476319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109436313804798990177650879 164154470707198485266476319)
    ·
      refine ⟨246231706060797727899714479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164154470707198485266476319 246231706060797727899714479)
      ·
        refine ⟨369347559091196591849571719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246231706060797727899714479 369347559091196591849571719)
        ·
          refine ⟨554021338636794887774357579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 369347559091196591849571719 554021338636794887774357579)
          ·
            refine ⟨831032007955192331661536369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 554021338636794887774357579 831032007955192331661536369)
            ·
              refine ⟨623274005966394248746152277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 831032007955192331661536369 623274005966394248746152277)
              ·
                refine ⟨1825998064354670650623493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 623274005966394248746152277 1825998064354670650623493)
                ·
                  refine ⟨342374637066500746991905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1825998064354670650623493 342374637066500746991905)
                  ·
                    rfl

theorem cell22_3000475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 4].length) (baseStart_3000475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000475 prefixEnd_3000475 := by exact prefixLift 3000475
  have htrace : WordTrace (prefixWord ++ tailWord_3000475) baseStart_3000475 baseEnd_3000475 := by
    simpa [prefixWord, tailWord_3000475, baseEnd_3000475] using wordTrace_append hprefix tailTrace_3000475
  have hstable : (prefixWord ++ tailWord_3000475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000475).length < 2 ^ (prefixWord ++ tailWord_3000475).sum := by decide
  have hdescent : baseEnd_3000475 < baseStart_3000475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000505 : List Nat := [1, 2, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_3000505 : Nat := 118140960795 + 3000505 * 2 ^ 59
def prefixEnd_3000505 : Nat := 4983230072969 + 3 ^ 40 * 3000505 * 2
def baseEnd_3000505 : Nat := 1027134180812592162725623

theorem tailTrace_3000505 : CollatzResearch.WordTrace tailWord_3000505 prefixEnd_3000505 1027134180812592162725623 := by
  unfold tailWord_3000505
  simp only [CollatzResearch.WordTrace]
  refine ⟨109437407994690305301242969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72958271996460203534161979 109437407994690305301242969)
  ·
    refine ⟨82078055996017728975932227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109437407994690305301242969 82078055996017728975932227)
    ·
      refine ⟨123117083994026593463898341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82078055996017728975932227 123117083994026593463898341)
      ·
        refine ⟨23084453248879986274480939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123117083994026593463898341 23084453248879986274480939)
        ·
          refine ⟨34626679873319979411721409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23084453248879986274480939 34626679873319979411721409)
          ·
            refine ⟨25970009904989984558791057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34626679873319979411721409 25970009904989984558791057)
            ·
              refine ⟨19477507428742488419093293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25970009904989984558791057 19477507428742488419093293)
              ·
                refine ⟨7304065285778433157159985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19477507428742488419093293 7304065285778433157159985)
                ·
                  refine ⟨5478048964333824867869989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7304065285778433157159985 5478048964333824867869989)
                  ·
                    refine ⟨1027134180812592162725623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5478048964333824867869989 1027134180812592162725623)
                    ·
                      rfl

theorem cell22_3000505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_3000505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000505 prefixEnd_3000505 := by exact prefixLift 3000505
  have htrace : WordTrace (prefixWord ++ tailWord_3000505) baseStart_3000505 baseEnd_3000505 := by
    simpa [prefixWord, tailWord_3000505, baseEnd_3000505] using wordTrace_append hprefix tailTrace_3000505
  have hstable : (prefixWord ++ tailWord_3000505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000505).length < 2 ^ (prefixWord ++ tailWord_3000505).sum := by decide
  have hdescent : baseEnd_3000505 < baseStart_3000505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000541 : List Nat := [1, 4, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_3000541 : Nat := 118140960795 + 3000541 * 2 ^ 59
def prefixEnd_3000541 : Nat := 4983230072969 + 3 ^ 40 * 3000541 * 2
def baseEnd_3000541 : Nat := 1027146504348300068825513

theorem tailTrace_3000541 : CollatzResearch.WordTrace tailWord_3000541 prefixEnd_3000541 1027146504348300068825513 := by
  unfold tailWord_3000541
  simp only [CollatzResearch.WordTrace]
  refine ⟨109438721022559883449553477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72959147348373255633035651 109438721022559883449553477)
  ·
    refine ⟨20519760191729978146791277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109438721022559883449553477 20519760191729978146791277)
    ·
      refine ⟨7694910071898741805046729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20519760191729978146791277 7694910071898741805046729)
      ·
        refine ⟨5771182553924056353785047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7694910071898741805046729 5771182553924056353785047)
        ·
          refine ⟨8656773830886084530677571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5771182553924056353785047 8656773830886084530677571)
          ·
            refine ⟨12985160746329126796016357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8656773830886084530677571 12985160746329126796016357)
            ·
              refine ⟨2434717639936711274253067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12985160746329126796016357 2434717639936711274253067)
              ·
                refine ⟨3652076459905066911379601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2434717639936711274253067 3652076459905066911379601)
                ·
                  refine ⟨2739057344928800183534701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3652076459905066911379601 2739057344928800183534701)
                  ·
                    refine ⟨1027146504348300068825513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739057344928800183534701 1027146504348300068825513)
                    ·
                      rfl

theorem cell22_3000541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_3000541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000541 prefixEnd_3000541 := by exact prefixLift 3000541
  have htrace : WordTrace (prefixWord ++ tailWord_3000541) baseStart_3000541 baseEnd_3000541 := by
    simpa [prefixWord, tailWord_3000541, baseEnd_3000541] using wordTrace_append hprefix tailTrace_3000541
  have hstable : (prefixWord ++ tailWord_3000541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000541).length < 2 ^ (prefixWord ++ tailWord_3000541).sum := by decide
  have hdescent : baseEnd_3000541 < baseStart_3000541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000586 : List Nat := [3, 1, 2, 2, 1, 1, 6, 2, 1, 3]
def baseStart_3000586 : Nat := 118140960795 + 3000586 * 2 ^ 59
def prefixEnd_3000586 : Nat := 4983230072969 + 3 ^ 40 * 3000586 * 2
def baseEnd_3000586 : Nat := 1027161908767934951450375

theorem tailTrace_3000586 : CollatzResearch.WordTrace tailWord_3000586 prefixEnd_3000586 1027161908767934951450375 := by
  unfold tailWord_3000586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27360090576849214033735403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72960241538264570756627741 27360090576849214033735403)
  ·
    refine ⟨41040135865273821050603105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27360090576849214033735403 41040135865273821050603105)
    ·
      refine ⟨30780101898955365787952329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41040135865273821050603105 30780101898955365787952329)
      ·
        refine ⟨23085076424216524340964247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30780101898955365787952329 23085076424216524340964247)
        ·
          refine ⟨34627614636324786511446371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23085076424216524340964247 34627614636324786511446371)
          ·
            refine ⟨51941421954487179767169557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34627614636324786511446371 51941421954487179767169557)
            ·
              refine ⟨2434754154116586551586073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51941421954487179767169557 2434754154116586551586073)
              ·
                refine ⟨1826065615587439913689555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2434754154116586551586073 1826065615587439913689555)
                ·
                  refine ⟨2739098423381159870534333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826065615587439913689555 2739098423381159870534333)
                  ·
                    refine ⟨1027161908767934951450375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739098423381159870534333 1027161908767934951450375)
                    ·
                      rfl

theorem cell22_3000586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_3000586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000586 prefixEnd_3000586 := by exact prefixLift 3000586
  have htrace : WordTrace (prefixWord ++ tailWord_3000586) baseStart_3000586 baseEnd_3000586 := by
    simpa [prefixWord, tailWord_3000586, baseEnd_3000586] using wordTrace_append hprefix tailTrace_3000586
  have hstable : (prefixWord ++ tailWord_3000586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000586).length < 2 ^ (prefixWord ++ tailWord_3000586).sum := by decide
  have hdescent : baseEnd_3000586 < baseStart_3000586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000612 : List Nat := [2, 3, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_3000612 : Nat := 118140960795 + 3000612 * 2 ^ 59
def prefixEnd_3000612 : Nat := 4983230072969 + 3 ^ 40 * 3000612 * 2
def baseEnd_3000612 : Nat := 1027170809099279550300295

theorem tailTrace_3000612 : CollatzResearch.WordTrace tailWord_3000612 prefixEnd_3000612 1027170809099279550300295 := by
  unfold tailWord_3000612
  simp only [CollatzResearch.WordTrace]
  refine ⟨54720655302651331287694045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72960873736868441716925393 54720655302651331287694045)
  ·
    refine ⟨20520245738494249232885267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54720655302651331287694045 20520245738494249232885267)
    ·
      refine ⟨30780368607741373849327901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20520245738494249232885267 30780368607741373849327901)
      ·
        refine ⟨11542638227903015193497963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30780368607741373849327901 11542638227903015193497963)
        ·
          refine ⟨17313957341854522790246945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11542638227903015193497963 17313957341854522790246945)
          ·
            refine ⟨12985468006390892092685209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17313957341854522790246945 12985468006390892092685209)
            ·
              refine ⟨9739101004793169069513907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12985468006390892092685209 9739101004793169069513907)
              ·
                refine ⟨14608651507189753604270861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9739101004793169069513907 14608651507189753604270861)
                ·
                  refine ⟨5478244315196157601601573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14608651507189753604270861 5478244315196157601601573)
                  ·
                    refine ⟨1027170809099279550300295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5478244315196157601601573 1027170809099279550300295)
                    ·
                      rfl

theorem cell22_3000612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_3000612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000612 prefixEnd_3000612 := by exact prefixLift 3000612
  have htrace : WordTrace (prefixWord ++ tailWord_3000612) baseStart_3000612 baseEnd_3000612 := by
    simpa [prefixWord, tailWord_3000612, baseEnd_3000612] using wordTrace_append hprefix tailTrace_3000612
  have hstable : (prefixWord ++ tailWord_3000612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000612).length < 2 ^ (prefixWord ++ tailWord_3000612).sum := by decide
  have hdescent : baseEnd_3000612 < baseStart_3000612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000672 : List Nat := [2, 1, 1, 3, 5, 1, 1, 8]
def baseStart_3000672 : Nat := 118140960795 + 3000672 * 2 ^ 59
def prefixEnd_3000672 : Nat := 4983230072969 + 3 ^ 40 * 3000672 * 2
def baseEnd_3000672 : Nat := 114132372036162154866679

theorem tailTrace_3000672 : CollatzResearch.WordTrace tailWord_3000672 prefixEnd_3000672 114132372036162154866679 := by
  unfold tailWord_3000672
  simp only [CollatzResearch.WordTrace]
  refine ⟨54721749492542646411286135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72962332656723528548381513 54721749492542646411286135)
  ·
    refine ⟨82082624238813969616929203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54721749492542646411286135 82082624238813969616929203)
    ·
      refine ⟨123123936358220954425393805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82082624238813969616929203 123123936358220954425393805)
      ·
        refine ⟨46171476134332857909522677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123123936358220954425393805 46171476134332857909522677)
        ·
          refine ⟨4328575887593705429017751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46171476134332857909522677 4328575887593705429017751)
          ·
            refine ⟨6492863831390558143526627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328575887593705429017751 6492863831390558143526627)
            ·
              refine ⟨9739295747085837215289941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6492863831390558143526627 9739295747085837215289941)
              ·
                refine ⟨114132372036162154866679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9739295747085837215289941 114132372036162154866679)
                ·
                  rfl

theorem cell22_3000672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 8].length) (baseStart_3000672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000672 prefixEnd_3000672 := by exact prefixLift 3000672
  have htrace : WordTrace (prefixWord ++ tailWord_3000672) baseStart_3000672 baseEnd_3000672 := by
    simpa [prefixWord, tailWord_3000672, baseEnd_3000672] using wordTrace_append hprefix tailTrace_3000672
  have hstable : (prefixWord ++ tailWord_3000672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000672).length < 2 ^ (prefixWord ++ tailWord_3000672).sum := by decide
  have hdescent : baseEnd_3000672 < baseStart_3000672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000706 : List Nat := [3, 4, 2, 1, 2, 1, 2, 7]
def baseStart_3000706 : Nat := 118140960795 + 3000706 * 2 ^ 59
def prefixEnd_3000706 : Nat := 4983230072969 + 3 ^ 40 * 3000706 * 2
def baseEnd_3000706 : Nat := 114133665246699404272223

theorem tailTrace_3000706 : CollatzResearch.WordTrace tailWord_3000706 prefixEnd_3000706 114133665246699404272223 := by
  unfold tailWord_3000706
  simp only [CollatzResearch.WordTrace]
  refine ⟨27361184766740529157327493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72963159377974744419539981 27361184766740529157327493)
  ·
    refine ⟨5130222143763849216998905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27361184766740529157327493 5130222143763849216998905)
    ·
      refine ⟨3847666607822886912749179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5130222143763849216998905 3847666607822886912749179)
      ·
        refine ⟨5771499911734330369123769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3847666607822886912749179 5771499911734330369123769)
        ·
          refine ⟨4328624933800747776842827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5771499911734330369123769 4328624933800747776842827)
          ·
            refine ⟨6492937400701121665264241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4328624933800747776842827 6492937400701121665264241)
            ·
              refine ⟨4869703050525841248948181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6492937400701121665264241 4869703050525841248948181)
              ·
                refine ⟨114133665246699404272223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4869703050525841248948181 114133665246699404272223)
                ·
                  rfl

theorem cell22_3000706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_3000706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000706 prefixEnd_3000706 := by exact prefixLift 3000706
  have htrace : WordTrace (prefixWord ++ tailWord_3000706) baseStart_3000706 baseEnd_3000706 := by
    simpa [prefixWord, tailWord_3000706, baseEnd_3000706] using wordTrace_append hprefix tailTrace_3000706
  have hstable : (prefixWord ++ tailWord_3000706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000706).length < 2 ^ (prefixWord ++ tailWord_3000706).sum := by decide
  have hdescent : baseEnd_3000706 < baseStart_3000706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000764 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_3000764 : Nat := 118140960795 + 3000764 * 2 ^ 59
def prefixEnd_3000764 : Nat := 4983230072969 + 3 ^ 40 * 3000764 * 2
def baseEnd_3000764 : Nat := 1027222841805601820499829

theorem tailTrace_3000764 : CollatzResearch.WordTrace tailWord_3000764 prefixEnd_3000764 1027222841805601820499829 := by
  unfold tailWord_3000764
  simp only [CollatzResearch.WordTrace]
  refine ⟨54723427250375996267460673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72964569667167995023280897 54723427250375996267460673)
  ·
    refine ⟨41042570437781997200595505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54723427250375996267460673 41042570437781997200595505)
    ·
      refine ⟨30781927828336497900446629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41042570437781997200595505 30781927828336497900446629)
      ·
        refine ⟨5771611467813093356333743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30781927828336497900446629 5771611467813093356333743)
        ·
          refine ⟨8657417201719640034500615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5771611467813093356333743 8657417201719640034500615)
          ·
            refine ⟨12986125802579460051750923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8657417201719640034500615 12986125802579460051750923)
            ·
              refine ⟨19479188703869190077626385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12986125802579460051750923 19479188703869190077626385)
              ·
                refine ⟨14609391527901892558219789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19479188703869190077626385 14609391527901892558219789)
                ·
                  refine ⟨5478521822963209709332421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14609391527901892558219789 5478521822963209709332421)
                  ·
                    refine ⟨1027222841805601820499829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5478521822963209709332421 1027222841805601820499829)
                    ·
                      rfl

theorem cell22_3000764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_3000764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000764 prefixEnd_3000764 := by exact prefixLift 3000764
  have htrace : WordTrace (prefixWord ++ tailWord_3000764) baseStart_3000764 baseEnd_3000764 := by
    simpa [prefixWord, tailWord_3000764, baseEnd_3000764] using wordTrace_append hprefix tailTrace_3000764
  have hstable : (prefixWord ++ tailWord_3000764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000764).length < 2 ^ (prefixWord ++ tailWord_3000764).sum := by decide
  have hdescent : baseEnd_3000764 < baseStart_3000764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000777 : List Nat := [1, 2, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_3000777 : Nat := 118140960795 + 3000777 * 2 ^ 59
def prefixEnd_3000777 : Nat := 4983230072969 + 3 ^ 40 * 3000777 * 2
def baseEnd_3000777 : Nat := 1027227291971274119924789

theorem tailTrace_3000777 : CollatzResearch.WordTrace tailWord_3000777 prefixEnd_3000777 1027227291971274119924789 := by
  unfold tailWord_3000777
  simp only [CollatzResearch.WordTrace]
  refine ⟨109447328649704895755144585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72964885766469930503429723 109447328649704895755144585)
  ·
    refine ⟨82085496487278671816358439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109447328649704895755144585 82085496487278671816358439)
    ·
      refine ⟨123128244730918007724537659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82085496487278671816358439 123128244730918007724537659)
      ·
        refine ⟨184692367096377011586806489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123128244730918007724537659 184692367096377011586806489)
        ·
          refine ⟨138519275322282758690104867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184692367096377011586806489 138519275322282758690104867)
          ·
            refine ⟨207778912983424138035157301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138519275322282758690104867 207778912983424138035157301)
            ·
              refine ⟨19479273092196012940795997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 207778912983424138035157301 19479273092196012940795997)
              ·
                refine ⟨7304727409573504852798499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19479273092196012940795997 7304727409573504852798499)
                ·
                  refine ⟨10957091114360257279197749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7304727409573504852798499 10957091114360257279197749)
                  ·
                    refine ⟨1027227291971274119924789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10957091114360257279197749 1027227291971274119924789)
                    ·
                      rfl

theorem cell22_3000777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_3000777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000777 prefixEnd_3000777 := by exact prefixLift 3000777
  have htrace : WordTrace (prefixWord ++ tailWord_3000777) baseStart_3000777 baseEnd_3000777 := by
    simpa [prefixWord, tailWord_3000777, baseEnd_3000777] using wordTrace_append hprefix tailTrace_3000777
  have hstable : (prefixWord ++ tailWord_3000777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000777).length < 2 ^ (prefixWord ++ tailWord_3000777).sum := by decide
  have hdescent : baseEnd_3000777 < baseStart_3000777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000794 : List Nat := [3, 1, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_3000794 : Nat := 118140960795 + 3000794 * 2 ^ 59
def prefixEnd_3000794 : Nat := 4983230072969 + 3 ^ 40 * 3000794 * 2
def baseEnd_3000794 : Nat := 1027233111418691742249737

theorem tailTrace_3000794 : CollatzResearch.WordTrace tailWord_3000794 prefixEnd_3000794 1027233111418691742249737 := by
  unfold tailWord_3000794
  simp only [CollatzResearch.WordTrace]
  refine ⟨27361987172660826914628359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72965299127095538439008957 27361987172660826914628359)
  ·
    refine ⟨41042980758991240371942539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27361987172660826914628359 41042980758991240371942539)
    ·
      refine ⟨61564471138486860557913809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41042980758991240371942539 61564471138486860557913809)
      ·
        refine ⟨46173353353865145418435357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61564471138486860557913809 46173353353865145418435357)
        ·
          refine ⟨17315007507699429531913259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46173353353865145418435357 17315007507699429531913259)
          ·
            refine ⟨25972511261549144297869889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17315007507699429531913259 25972511261549144297869889)
            ·
              refine ⟨19479383446161858223402417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25972511261549144297869889 19479383446161858223402417)
              ·
                refine ⟨14609537584621393667551813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19479383446161858223402417 14609537584621393667551813)
                ·
                  refine ⟨2739288297116511312665965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14609537584621393667551813 2739288297116511312665965)
                  ·
                    refine ⟨1027233111418691742249737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739288297116511312665965 1027233111418691742249737)
                    ·
                      rfl

theorem cell22_3000794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_3000794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000794 prefixEnd_3000794 := by exact prefixLift 3000794
  have htrace : WordTrace (prefixWord ++ tailWord_3000794) baseStart_3000794 baseEnd_3000794 := by
    simpa [prefixWord, tailWord_3000794, baseEnd_3000794] using wordTrace_append hprefix tailTrace_3000794
  have hstable : (prefixWord ++ tailWord_3000794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000794).length < 2 ^ (prefixWord ++ tailWord_3000794).sum := by decide
  have hdescent : baseEnd_3000794 < baseStart_3000794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000807 : List Nat := [1, 1, 5, 2, 1, 1, 11]
def baseStart_3000807 : Nat := 118140960795 + 3000807 * 2 ^ 59
def prefixEnd_3000807 : Nat := 4983230072969 + 3 ^ 40 * 3000807 * 2
def baseEnd_3000807 : Nat := 38045835614235705247211

theorem tailTrace_3000807 : CollatzResearch.WordTrace tailWord_3000807 prefixEnd_3000807 38045835614235705247211 := by
  unfold tailWord_3000807
  simp only [CollatzResearch.WordTrace]
  refine ⟨109448422839596210878736675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72965615226397473919157783 109448422839596210878736675)
  ·
    refine ⟨164172634259394316318105013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109448422839596210878736675 164172634259394316318105013)
    ·
      refine ⟨15391184461818217154822345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164172634259394316318105013 15391184461818217154822345)
      ·
        refine ⟨11543388346363662866116759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15391184461818217154822345 11543388346363662866116759)
        ·
          refine ⟨17315082519545494299175139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11543388346363662866116759 17315082519545494299175139)
          ·
            refine ⟨25972623779318241448762709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17315082519545494299175139 25972623779318241448762709)
            ·
              refine ⟨38045835614235705247211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 25972623779318241448762709 38045835614235705247211)
              ·
                rfl

theorem cell22_3000807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 11].length) (baseStart_3000807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000807 prefixEnd_3000807 := by exact prefixLift 3000807
  have htrace : WordTrace (prefixWord ++ tailWord_3000807) baseStart_3000807 baseEnd_3000807 := by
    simpa [prefixWord, tailWord_3000807, baseEnd_3000807] using wordTrace_append hprefix tailTrace_3000807
  have hstable : (prefixWord ++ tailWord_3000807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000807).length < 2 ^ (prefixWord ++ tailWord_3000807).sum := by decide
  have hdescent : baseEnd_3000807 < baseStart_3000807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000837 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_3000837 : Nat := 118140960795 + 3000837 * 2 ^ 59
def prefixEnd_3000837 : Nat := 4983230072969 + 3 ^ 40 * 3000837 * 2
def baseEnd_3000837 : Nat := 1027247831197453963424605

theorem tailTrace_3000837 : CollatzResearch.WordTrace tailWord_3000837 prefixEnd_3000837 1027247831197453963424605 := by
  unfold tailWord_3000837
  simp only [CollatzResearch.WordTrace]
  refine ⟨109449517029487526002328765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72966344686325017334885843 109449517029487526002328765)
  ·
    refine ⟨41043568886057822250873287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109449517029487526002328765 41043568886057822250873287)
    ·
      refine ⟨61565353329086733376309931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41043568886057822250873287 61565353329086733376309931)
      ·
        refine ⟨92348029993630100064464897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61565353329086733376309931 92348029993630100064464897)
        ·
          refine ⟨69261022495222575048348673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92348029993630100064464897 69261022495222575048348673)
          ·
            refine ⟨51945766871416931286261505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69261022495222575048348673 51945766871416931286261505)
            ·
              refine ⟨38959325153562698464696129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51945766871416931286261505 38959325153562698464696129)
              ·
                refine ⟨29219493865172023848522097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38959325153562698464696129 29219493865172023848522097)
                ·
                  refine ⟨21914620398879017886391573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29219493865172023848522097 21914620398879017886391573)
                  ·
                    refine ⟨1027247831197453963424605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21914620398879017886391573 1027247831197453963424605)
                    ·
                      rfl

theorem cell22_3000837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_3000837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000837 prefixEnd_3000837 := by exact prefixLift 3000837
  have htrace : WordTrace (prefixWord ++ tailWord_3000837) baseStart_3000837 baseEnd_3000837 := by
    simpa [prefixWord, tailWord_3000837, baseEnd_3000837] using wordTrace_append hprefix tailTrace_3000837
  have hstable : (prefixWord ++ tailWord_3000837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000837).length < 2 ^ (prefixWord ++ tailWord_3000837).sum := by decide
  have hdescent : baseEnd_3000837 < baseStart_3000837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000924 : List Nat := [2, 2, 4, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3000924 : Nat := 118140960795 + 3000924 * 2 ^ 59
def prefixEnd_3000924 : Nat := 4983230072969 + 3 ^ 40 * 3000924 * 2
def baseEnd_3000924 : Nat := 1027277613075414736499339

theorem tailTrace_3000924 : CollatzResearch.WordTrace tailWord_3000924 prefixEnd_3000924 1027277613075414736499339 := by
  unfold tailWord_3000924
  simp only [CollatzResearch.WordTrace]
  refine ⟨54726345090086169930372913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72968460120114893240497217 54726345090086169930372913)
  ·
    refine ⟨41044758817564627447779685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54726345090086169930372913 41044758817564627447779685)
    ·
      refine ⟨7695892278293367646458691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41044758817564627447779685 7695892278293367646458691)
      ·
        refine ⟨11543838417440051469688037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7695892278293367646458691 11543838417440051469688037)
        ·
          refine ⟨2164469703270009650566507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11543838417440051469688037 2164469703270009650566507)
          ·
            refine ⟨3246704554905014475849761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164469703270009650566507 3246704554905014475849761)
            ·
              refine ⟨2435028416178760856887321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3246704554905014475849761 2435028416178760856887321)
              ·
                refine ⟨1826271312134070642665491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435028416178760856887321 1826271312134070642665491)
                ·
                  refine ⟨2739406968201105963998237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826271312134070642665491 2739406968201105963998237)
                  ·
                    refine ⟨1027277613075414736499339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739406968201105963998237 1027277613075414736499339)
                    ·
                      rfl

theorem cell22_3000924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3000924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000924 prefixEnd_3000924 := by exact prefixLift 3000924
  have htrace : WordTrace (prefixWord ++ tailWord_3000924) baseStart_3000924 baseEnd_3000924 := by
    simpa [prefixWord, tailWord_3000924, baseEnd_3000924] using wordTrace_append hprefix tailTrace_3000924
  have hstable : (prefixWord ++ tailWord_3000924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000924).length < 2 ^ (prefixWord ++ tailWord_3000924).sum := by decide
  have hdescent : baseEnd_3000924 < baseStart_3000924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000931 : List Nat := [1, 1, 1, 5, 1, 2, 3, 4, 4]
def baseStart_3000931 : Nat := 118140960795 + 3000931 * 2 ^ 59
def prefixEnd_3000931 : Nat := 4983230072969 + 3 ^ 40 * 3000931 * 2
def baseEnd_3000931 : Nat := 342426669772823017191439

theorem tailTrace_3000931 : CollatzResearch.WordTrace tailWord_3000931 prefixEnd_3000931 342426669772823017191439 := by
  unfold tailWord_3000931
  simp only [CollatzResearch.WordTrace]
  refine ⟨109452945491146980056250647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72968630327431320037500431 109452945491146980056250647)
  ·
    refine ⟨164179418236720470084375971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109452945491146980056250647 164179418236720470084375971)
    ·
      refine ⟨246269127355080705126563957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164179418236720470084375971 246269127355080705126563957)
      ·
        refine ⟨23087730689538816105615371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246269127355080705126563957 23087730689538816105615371)
        ·
          refine ⟨34631596034308224158423057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23087730689538816105615371 34631596034308224158423057)
          ·
            refine ⟨25973697025731168118817293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34631596034308224158423057 25973697025731168118817293)
            ·
              refine ⟨9740136384649188044556485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25973697025731168118817293 9740136384649188044556485)
              ·
                refine ⟨1826275572121722758354341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9740136384649188044556485 1826275572121722758354341)
                ·
                  refine ⟨342426669772823017191439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826275572121722758354341 342426669772823017191439)
                  ·
                    rfl

theorem cell22_3000931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 4].length) (baseStart_3000931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000931 prefixEnd_3000931 := by exact prefixLift 3000931
  have htrace : WordTrace (prefixWord ++ tailWord_3000931) baseStart_3000931 baseEnd_3000931 := by
    simpa [prefixWord, tailWord_3000931, baseEnd_3000931] using wordTrace_append hprefix tailTrace_3000931
  have hstable : (prefixWord ++ tailWord_3000931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000931).length < 2 ^ (prefixWord ++ tailWord_3000931).sum := by decide
  have hdescent : baseEnd_3000931 < baseStart_3000931 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000980 : List Nat := [2, 4, 2, 2, 1, 1, 3, 2, 2, 3]
def baseStart_3000980 : Nat := 118140960795 + 3000980 * 2 ^ 59
def prefixEnd_3000980 : Nat := 4983230072969 + 3 ^ 40 * 3000980 * 2
def baseEnd_3000980 : Nat := 1027296783019849257099167

theorem tailTrace_3000980 : CollatzResearch.WordTrace tailWord_3000980 prefixEnd_3000980 1027296783019849257099167 := by
  unfold tailWord_3000980
  simp only [CollatzResearch.WordTrace]
  refine ⟨54727366333984730712392197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72969821778646307616522929 54727366333984730712392197)
  ·
    refine ⟨10261381187622137008573537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54727366333984730712392197 10261381187622137008573537)
    ·
      refine ⟨7696035890716602756430153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10261381187622137008573537 7696035890716602756430153)
      ·
        refine ⟨5772026918037452067322615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7696035890716602756430153 5772026918037452067322615)
        ·
          refine ⟨8658040377056178100983923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772026918037452067322615 8658040377056178100983923)
          ·
            refine ⟨12987060565584267151475885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8658040377056178100983923 12987060565584267151475885)
            ·
              refine ⟨4870147712094100181803457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12987060565584267151475885 4870147712094100181803457)
              ·
                refine ⟨3652610784070575136352593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4870147712094100181803457 3652610784070575136352593)
                ·
                  refine ⟨2739458088052931352264445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3652610784070575136352593 2739458088052931352264445)
                  ·
                    refine ⟨1027296783019849257099167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739458088052931352264445 1027296783019849257099167)
                    ·
                      rfl

theorem cell22_3000980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_3000980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000980 prefixEnd_3000980 := by exact prefixLift 3000980
  have htrace : WordTrace (prefixWord ++ tailWord_3000980) baseStart_3000980 baseEnd_3000980 := by
    simpa [prefixWord, tailWord_3000980, baseEnd_3000980] using wordTrace_append hprefix tailTrace_3000980
  have hstable : (prefixWord ++ tailWord_3000980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000980).length < 2 ^ (prefixWord ++ tailWord_3000980).sum := by decide
  have hdescent : baseEnd_3000980 < baseStart_3000980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3000989 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 1, 8]
def baseStart_3000989 : Nat := 118140960795 + 3000989 * 2 ^ 59
def prefixEnd_3000989 : Nat := 4983230072969 + 3 ^ 40 * 3000989 * 2
def baseEnd_3000989 : Nat := 1027299863903776233624139

theorem tailTrace_3000989 : CollatzResearch.WordTrace tailWord_3000989 prefixEnd_3000989 1027299863903776233624139 := by
  unfold tailWord_3000989
  simp only [CollatzResearch.WordTrace]
  refine ⟨109455060924936855961862021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72970040616624570641241347 109455060924936855961862021)
  ·
    refine ⟨20522823923425660492849129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109455060924936855961862021 20522823923425660492849129)
    ·
      refine ⟨15392117942569245369636847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20522823923425660492849129 15392117942569245369636847)
      ·
        refine ⟨23088176913853868054455271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15392117942569245369636847 23088176913853868054455271)
        ·
          refine ⟨34632265370780802081682907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23088176913853868054455271 34632265370780802081682907)
          ·
            refine ⟨51948398056171203122524361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34632265370780802081682907 51948398056171203122524361)
            ·
              refine ⟨38961298542128402341893271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51948398056171203122524361 38961298542128402341893271)
              ·
                refine ⟨58441947813192603512839907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38961298542128402341893271 58441947813192603512839907)
                ·
                  refine ⟨87662921719788905269259861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58441947813192603512839907 87662921719788905269259861)
                  ·
                    refine ⟨1027299863903776233624139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87662921719788905269259861 1027299863903776233624139)
                    ·
                      rfl

theorem cell22_3000989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_3000989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3000989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3000989 prefixEnd_3000989 := by exact prefixLift 3000989
  have htrace : WordTrace (prefixWord ++ tailWord_3000989) baseStart_3000989 baseEnd_3000989 := by
    simpa [prefixWord, tailWord_3000989, baseEnd_3000989] using wordTrace_append hprefix tailTrace_3000989
  have hstable : (prefixWord ++ tailWord_3000989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3000989).length < 2 ^ (prefixWord ++ tailWord_3000989).sum := by decide
  have hdescent : baseEnd_3000989 < baseStart_3000989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3000989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001042 : List Nat := [3, 2, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_3001042 : Nat := 118140960795 + 3001042 * 2 ^ 59
def prefixEnd_3001042 : Nat := 4983230072969 + 3 ^ 40 * 3001042 * 2
def baseEnd_3001042 : Nat := 1027318006886901762048977

theorem tailTrace_3001042 : CollatzResearch.WordTrace tailWord_3001042 prefixEnd_3001042 1027318006886901762048977 := by
  unfold tailWord_3001042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27364248498436211503385345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72971329329163230675694253 27364248498436211503385345)
  ·
    refine ⟨20523186373827158627539009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27364248498436211503385345 20523186373827158627539009)
    ·
      refine ⟨15392389780370368970654257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20523186373827158627539009 15392389780370368970654257)
      ·
        refine ⟨11544292335277776727990693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15392389780370368970654257 11544292335277776727990693)
        ·
          refine ⟨2164554812864583136498255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11544292335277776727990693 2164554812864583136498255)
          ·
            refine ⟨3246832219296874704747383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164554812864583136498255 3246832219296874704747383)
            ·
              refine ⟨4870248328945312057121075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3246832219296874704747383 4870248328945312057121075)
              ·
                refine ⟨7305372493417968085681613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4870248328945312057121075 7305372493417968085681613)
                ·
                  refine ⟨2739514685031738032130605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7305372493417968085681613 2739514685031738032130605)
                  ·
                    refine ⟨1027318006886901762048977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739514685031738032130605 1027318006886901762048977)
                    ·
                      rfl

theorem cell22_3001042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_3001042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001042 prefixEnd_3001042 := by exact prefixLift 3001042
  have htrace : WordTrace (prefixWord ++ tailWord_3001042) baseStart_3001042 baseEnd_3001042 := by
    simpa [prefixWord, tailWord_3001042, baseEnd_3001042] using wordTrace_append hprefix tailTrace_3001042
  have hstable : (prefixWord ++ tailWord_3001042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001042).length < 2 ^ (prefixWord ++ tailWord_3001042).sum := by decide
  have hdescent : baseEnd_3001042 < baseStart_3001042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001081 : List Nat := [1, 2, 1, 3, 1, 1, 1, 3, 6, 3]
def baseStart_3001081 : Nat := 118140960795 + 3001081 * 2 ^ 59
def prefixEnd_3001081 : Nat := 4983230072969 + 3 ^ 40 * 3001081 * 2
def baseEnd_3001081 : Nat := 1027331357383918660323857

theorem tailTrace_3001081 : CollatzResearch.WordTrace tailWord_3001081 prefixEnd_3001081 1027331357383918660323857 := by
  unfold tailWord_3001081
  simp only [CollatzResearch.WordTrace]
  refine ⟨109458416440603555674211097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72972277627069037116140731 109458416440603555674211097)
  ·
    refine ⟨82093812330452666755658323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109458416440603555674211097 82093812330452666755658323)
    ·
      refine ⟨123140718495679000133487485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82093812330452666755658323 123140718495679000133487485)
      ·
        refine ⟨46177769435879625050057807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123140718495679000133487485 46177769435879625050057807)
        ·
          refine ⟨69266654153819437575086711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46177769435879625050057807 69266654153819437575086711)
          ·
            refine ⟨103899981230729156362630067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69266654153819437575086711 103899981230729156362630067)
            ·
              refine ⟨155849971846093734543945101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103899981230729156362630067 155849971846093734543945101)
              ·
                refine ⟨58443739442285150453979413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155849971846093734543945101 58443739442285150453979413)
                ·
                  refine ⟨2739550286357116427530285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 58443739442285150453979413 2739550286357116427530285)
                  ·
                    refine ⟨1027331357383918660323857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739550286357116427530285 1027331357383918660323857)
                    ·
                      rfl

theorem cell22_3001081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_3001081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001081 prefixEnd_3001081 := by exact prefixLift 3001081
  have htrace : WordTrace (prefixWord ++ tailWord_3001081) baseStart_3001081 baseEnd_3001081 := by
    simpa [prefixWord, tailWord_3001081, baseEnd_3001081] using wordTrace_append hprefix tailTrace_3001081
  have hstable : (prefixWord ++ tailWord_3001081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001081).length < 2 ^ (prefixWord ++ tailWord_3001081).sum := by decide
  have hdescent : baseEnd_3001081 < baseStart_3001081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001128 : List Nat := [2, 1, 5, 1, 1, 1, 5, 6]
def baseStart_3001128 : Nat := 118140960795 + 3001128 * 2 ^ 59
def prefixEnd_3001128 : Nat := 4983230072969 + 3 ^ 40 * 3001128 * 2
def baseEnd_3001128 : Nat := 114149716271602911599857

theorem tailTrace_3001128 : CollatzResearch.WordTrace tailWord_3001128 prefixEnd_3001128 114149716271602911599857 := by
  unfold tailWord_3001128
  simp only [CollatzResearch.WordTrace]
  refine ⟨54730065335716641350586019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72973420447622188467448025 54730065335716641350586019)
  ·
    refine ⟨82095098003574962025879029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54730065335716641350586019 82095098003574962025879029)
    ·
      refine ⟨7696415437835152689926159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82095098003574962025879029 7696415437835152689926159)
      ·
        refine ⟨11544623156752729034889239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7696415437835152689926159 11544623156752729034889239)
        ·
          refine ⟨17316934735129093552333859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11544623156752729034889239 17316934735129093552333859)
          ·
            refine ⟨25975402102693640328500789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17316934735129093552333859 25975402102693640328500789)
            ·
              refine ⟨2435193947127528780796949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25975402102693640328500789 2435193947127528780796949)
              ·
                refine ⟨114149716271602911599857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2435193947127528780796949 114149716271602911599857)
                ·
                  rfl

theorem cell22_3001128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 5, 6].length) (baseStart_3001128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001128 prefixEnd_3001128 := by exact prefixLift 3001128
  have htrace : WordTrace (prefixWord ++ tailWord_3001128) baseStart_3001128 baseEnd_3001128 := by
    simpa [prefixWord, tailWord_3001128, baseEnd_3001128] using wordTrace_append hprefix tailTrace_3001128
  have hstable : (prefixWord ++ tailWord_3001128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001128).length < 2 ^ (prefixWord ++ tailWord_3001128).sum := by decide
  have hdescent : baseEnd_3001128 < baseStart_3001128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001130 : List Nat := [3, 1, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_3001130 : Nat := 118140960795 + 3001130 * 2 ^ 59
def prefixEnd_3001130 : Nat := 4983230072969 + 3 ^ 40 * 3001130 * 2
def baseEnd_3001130 : Nat := 1027348131085298865848707

theorem tailTrace_3001130 : CollatzResearch.WordTrace tailWord_3001130 prefixEnd_3001130 1027348131085298865848707 := by
  unfold tailWord_3001130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27365050904356509260686211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72973469078284024695163229 27365050904356509260686211)
  ·
    refine ⟨41047576356534763891029317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27365050904356509260686211 41047576356534763891029317)
    ·
      refine ⟨7696420566850268229567997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41047576356534763891029317 7696420566850268229567997)
      ·
        refine ⟨2886157712568850586087999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7696420566850268229567997 2886157712568850586087999)
        ·
          refine ⟨4329236568853275879131999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2886157712568850586087999 4329236568853275879131999)
          ·
            refine ⟨6493854853279913818697999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329236568853275879131999 6493854853279913818697999)
            ·
              refine ⟨9740782279919870728046999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6493854853279913818697999 9740782279919870728046999)
              ·
                refine ⟨14611173419879806092070499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9740782279919870728046999 14611173419879806092070499)
                ·
                  refine ⟨21916760129819709138105749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14611173419879806092070499 21916760129819709138105749)
                  ·
                    refine ⟨1027348131085298865848707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21916760129819709138105749 1027348131085298865848707)
                    ·
                      rfl

theorem cell22_3001130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_3001130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001130 prefixEnd_3001130 := by exact prefixLift 3001130
  have htrace : WordTrace (prefixWord ++ tailWord_3001130) baseStart_3001130 baseEnd_3001130 := by
    simpa [prefixWord, tailWord_3001130, baseEnd_3001130] using wordTrace_append hprefix tailTrace_3001130
  have hstable : (prefixWord ++ tailWord_3001130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001130).length < 2 ^ (prefixWord ++ tailWord_3001130).sum := by decide
  have hdescent : baseEnd_3001130 < baseStart_3001130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001149 : List Nat := [1, 4, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_3001149 : Nat := 118140960795 + 3001149 * 2 ^ 59
def prefixEnd_3001149 : Nat := 4983230072969 + 3 ^ 40 * 3001149 * 2
def baseEnd_3001149 : Nat := 1027354635173589149623649

theorem tailTrace_3001149 : CollatzResearch.WordTrace tailWord_3001149 prefixEnd_3001149 1027354635173589149623649 := by
  unfold tailWord_3001149
  simp only [CollatzResearch.WordTrace]
  refine ⟨109460896604357203287686501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72973931069571468858457667 109460896604357203287686501)
  ·
    refine ⟨20523918113316975616441219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109460896604357203287686501 20523918113316975616441219)
    ·
      refine ⟨30785877169975463424661829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20523918113316975616441219 30785877169975463424661829)
      ·
        refine ⟨5772351969370399392124093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30785877169975463424661829 5772351969370399392124093)
        ·
          refine ⟨2164631988513899772046535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5772351969370399392124093 2164631988513899772046535)
          ·
            refine ⟨3246947982770849658069803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164631988513899772046535 3246947982770849658069803)
            ·
              refine ⟨4870421974156274487104705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3246947982770849658069803 4870421974156274487104705)
              ·
                refine ⟨3652816480617205865328529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4870421974156274487104705 3652816480617205865328529)
                ·
                  refine ⟨2739612360462904398996397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3652816480617205865328529 2739612360462904398996397)
                  ·
                    refine ⟨1027354635173589149623649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739612360462904398996397 1027354635173589149623649)
                    ·
                      rfl

theorem cell22_3001149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_3001149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001149 prefixEnd_3001149 := by exact prefixLift 3001149
  have htrace : WordTrace (prefixWord ++ tailWord_3001149) baseStart_3001149 baseEnd_3001149 := by
    simpa [prefixWord, tailWord_3001149, baseEnd_3001149] using wordTrace_append hprefix tailTrace_3001149
  have hstable : (prefixWord ++ tailWord_3001149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001149).length < 2 ^ (prefixWord ++ tailWord_3001149).sum := by decide
  have hdescent : baseEnd_3001149 < baseStart_3001149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001160 : List Nat := [2, 1, 3, 1, 1, 3, 1, 6, 1, 3]
def baseStart_3001160 : Nat := 118140960795 + 3001160 * 2 ^ 59
def prefixEnd_3001160 : Nat := 4983230072969 + 3 ^ 40 * 3001160 * 2
def baseEnd_3001160 : Nat := 1027358400698388787598615

theorem tailTrace_3001160 : CollatzResearch.WordTrace tailWord_3001160 prefixEnd_3001160 1027358400698388787598615 := by
  unfold tailWord_3001160
  simp only [CollatzResearch.WordTrace]
  refine ⟨54730648903658676083168467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72974198538211568110891289 54730648903658676083168467)
  ·
    refine ⟨82095973355488014124752701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54730648903658676083168467 82095973355488014124752701)
    ·
      refine ⟨30785990008308005296782263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82095973355488014124752701 30785990008308005296782263)
      ·
        refine ⟨46178985012462007945173395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30785990008308005296782263 46178985012462007945173395)
        ·
          refine ⟨69268477518693011917760093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46178985012462007945173395 69268477518693011917760093)
          ·
            refine ⟨25975679069509879469160035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69268477518693011917760093 25975679069509879469160035)
            ·
              refine ⟨38963518604264819203740053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25975679069509879469160035 38963518604264819203740053)
              ·
                refine ⟨1826414934574913400175315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38963518604264819203740053 1826414934574913400175315)
                ·
                  refine ⟨2739622401862370100262973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826414934574913400175315 2739622401862370100262973)
                  ·
                    refine ⟨1027358400698388787598615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739622401862370100262973 1027358400698388787598615)
                    ·
                      rfl

theorem cell22_3001160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 6, 1, 3].length) (baseStart_3001160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001160 prefixEnd_3001160 := by exact prefixLift 3001160
  have htrace : WordTrace (prefixWord ++ tailWord_3001160) baseStart_3001160 baseEnd_3001160 := by
    simpa [prefixWord, tailWord_3001160, baseEnd_3001160] using wordTrace_append hprefix tailTrace_3001160
  have hstable : (prefixWord ++ tailWord_3001160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001160).length < 2 ^ (prefixWord ++ tailWord_3001160).sum := by decide
  have hdescent : baseEnd_3001160 < baseStart_3001160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001203 : List Nat := [1, 1, 1, 2, 2, 1, 6, 3, 1, 4]
def baseStart_3001203 : Nat := 118140960795 + 3001203 * 2 ^ 59
def prefixEnd_3001203 : Nat := 4983230072969 + 3 ^ 40 * 3001203 * 2
def baseEnd_3001203 : Nat := 1027373120477151008773483

theorem tailTrace_3001203 : CollatzResearch.WordTrace tailWord_3001203 prefixEnd_3001203 1027373120477151008773483 := by
  unfold tailWord_3001203
  simp only [CollatzResearch.WordTrace]
  refine ⟨109462866146161570510152263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72975244097441047006768175 109462866146161570510152263)
  ·
    refine ⟨164194299219242355765228395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109462866146161570510152263 164194299219242355765228395)
    ·
      refine ⟨246291448828863533647842593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164194299219242355765228395 246291448828863533647842593)
      ·
        refine ⟨184718586621647650235881945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246291448828863533647842593 184718586621647650235881945)
        ·
          refine ⟨138538939966235737676911459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184718586621647650235881945 138538939966235737676911459)
          ·
            refine ⟨207808409949353606515367189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138538939966235737676911459 207808409949353606515367189)
            ·
              refine ⟨9741019216375950305407837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 207808409949353606515367189 9741019216375950305407837)
              ·
                refine ⟨3652882206140981364527939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9741019216375950305407837 3652882206140981364527939)
                ·
                  refine ⟨5479323309211472046791909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3652882206140981364527939 5479323309211472046791909)
                  ·
                    refine ⟨1027373120477151008773483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5479323309211472046791909 1027373120477151008773483)
                    ·
                      rfl

theorem cell22_3001203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 4].length) (baseStart_3001203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001203 prefixEnd_3001203 := by exact prefixLift 3001203
  have htrace : WordTrace (prefixWord ++ tailWord_3001203) baseStart_3001203 baseEnd_3001203 := by
    simpa [prefixWord, tailWord_3001203, baseEnd_3001203] using wordTrace_append hprefix tailTrace_3001203
  have hstable : (prefixWord ++ tailWord_3001203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001203).length < 2 ^ (prefixWord ++ tailWord_3001203).sum := by decide
  have hdescent : baseEnd_3001203 < baseStart_3001203 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001216 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_3001216 : Nat := 118140960795 + 3001216 * 2 ^ 59
def prefixEnd_3001216 : Nat := 4983230072969 + 3 ^ 40 * 3001216 * 2
def baseEnd_3001216 : Nat := 1027377570642823308198443

theorem tailTrace_3001216 : CollatzResearch.WordTrace tailWord_3001216 prefixEnd_3001216 1027377570642823308198443 := by
  unfold tailWord_3001216
  simp only [CollatzResearch.WordTrace]
  refine ⟨54731670147557236865187751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72975560196742982486917001 54731670147557236865187751)
  ·
    refine ⟨82097505221335855297781627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54731670147557236865187751 82097505221335855297781627)
    ·
      refine ⟨123146257832003782946672441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82097505221335855297781627 123146257832003782946672441)
      ·
        refine ⟨92359693374002837210004331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123146257832003782946672441 92359693374002837210004331)
        ·
          refine ⟨138539540061004255815006497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92359693374002837210004331 138539540061004255815006497)
          ·
            refine ⟨103904655045753191861254873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138539540061004255815006497 103904655045753191861254873)
            ·
              refine ⟨77928491284314893895941155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103904655045753191861254873 77928491284314893895941155)
              ·
                refine ⟨116892736926472340843911733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77928491284314893895941155 116892736926472340843911733)
                ·
                  refine ⟨10958694086856781954116725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 116892736926472340843911733 10958694086856781954116725)
                  ·
                    refine ⟨1027377570642823308198443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10958694086856781954116725 1027377570642823308198443)
                    ·
                      rfl

theorem cell22_3001216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_3001216 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001216 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001216 prefixEnd_3001216 := by exact prefixLift 3001216
  have htrace : WordTrace (prefixWord ++ tailWord_3001216) baseStart_3001216 baseEnd_3001216 := by
    simpa [prefixWord, tailWord_3001216, baseEnd_3001216] using wordTrace_append hprefix tailTrace_3001216
  have hstable : (prefixWord ++ tailWord_3001216).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001216).length < 2 ^ (prefixWord ++ tailWord_3001216).sum := by decide
  have hdescent : baseEnd_3001216 < baseStart_3001216 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001248 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_3001248 : Nat := 118140960795 + 3001248 * 2 ^ 59
def prefixEnd_3001248 : Nat := 4983230072969 + 3 ^ 40 * 3001248 * 2
def baseEnd_3001248 : Nat := 1027388524896785891398345

theorem tailTrace_3001248 : CollatzResearch.WordTrace tailWord_3001248 prefixEnd_3001248 1027388524896785891398345 := by
  unfold tailWord_3001248
  simp only [CollatzResearch.WordTrace]
  refine ⟨54732253715499271597770199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72976338287332362130360265 54732253715499271597770199)
  ·
    refine ⟨82098380573248907396655299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54732253715499271597770199 82098380573248907396655299)
    ·
      refine ⟨123147570859873361094982949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82098380573248907396655299 123147570859873361094982949)
      ·
        refine ⟨23090169536226255205309303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123147570859873361094982949 23090169536226255205309303)
        ·
          refine ⟨34635254304339382807963955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23090169536226255205309303 34635254304339382807963955)
          ·
            refine ⟨51952881456509074211945933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34635254304339382807963955 51952881456509074211945933)
            ·
              refine ⟨19482330546190902829479725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51952881456509074211945933 19482330546190902829479725)
              ·
                refine ⟨7305873954821588561054897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19482330546190902829479725 7305873954821588561054897)
                ·
                  refine ⟨5479405466116191420791173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7305873954821588561054897 5479405466116191420791173)
                  ·
                    refine ⟨1027388524896785891398345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5479405466116191420791173 1027388524896785891398345)
                    ·
                      rfl

theorem cell22_3001248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_3001248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001248 prefixEnd_3001248 := by exact prefixLift 3001248
  have htrace : WordTrace (prefixWord ++ tailWord_3001248) baseStart_3001248 baseEnd_3001248 := by
    simpa [prefixWord, tailWord_3001248, baseEnd_3001248] using wordTrace_append hprefix tailTrace_3001248
  have hstable : (prefixWord ++ tailWord_3001248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001248).length < 2 ^ (prefixWord ++ tailWord_3001248).sum := by decide
  have hdescent : baseEnd_3001248 < baseStart_3001248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001250 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_3001250 : Nat := 118140960795 + 3001250 * 2 ^ 59
def prefixEnd_3001250 : Nat := 4983230072969 + 3 ^ 40 * 3001250 * 2
def baseEnd_3001250 : Nat := 1027389209537658552848339

theorem tailTrace_3001250 : CollatzResearch.WordTrace tailWord_3001250 prefixEnd_3001250 1027389209537658552848339 := by
  unfold tailWord_3001250
  simp only [CollatzResearch.WordTrace]
  refine ⟨27366145094247824384278301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72976386917994198358075469 27366145094247824384278301)
  ·
    refine ⟨10262304410342934144104363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27366145094247824384278301 10262304410342934144104363)
    ·
      refine ⟨15393456615514401216156545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10262304410342934144104363 15393456615514401216156545)
      ·
        refine ⟨11545092461635800912117409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15393456615514401216156545 11545092461635800912117409)
        ·
          refine ⟨8658819346226850684088057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11545092461635800912117409 8658819346226850684088057)
          ·
            refine ⟨6494114509670138013066043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8658819346226850684088057 6494114509670138013066043)
            ·
              refine ⟨9741171764505207019599065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494114509670138013066043 9741171764505207019599065)
              ·
                refine ⟨7305878823378905264699299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9741171764505207019599065 7305878823378905264699299)
                ·
                  refine ⟨10958818235068357897048949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7305878823378905264699299 10958818235068357897048949)
                  ·
                    refine ⟨1027389209537658552848339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10958818235068357897048949 1027389209537658552848339)
                    ·
                      rfl

theorem cell22_3001250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_3001250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001250 prefixEnd_3001250 := by exact prefixLift 3001250
  have htrace : WordTrace (prefixWord ++ tailWord_3001250) baseStart_3001250 baseEnd_3001250 := by
    simpa [prefixWord, tailWord_3001250, baseEnd_3001250] using wordTrace_append hprefix tailTrace_3001250
  have hstable : (prefixWord ++ tailWord_3001250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001250).length < 2 ^ (prefixWord ++ tailWord_3001250).sum := by decide
  have hdescent : baseEnd_3001250 < baseStart_3001250 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001286 : List Nat := [6, 1, 3, 1, 1, 1, 1, 2, 6]
def baseStart_3001286 : Nat := 118140960795 + 3001286 * 2 ^ 59
def prefixEnd_3001286 : Nat := 4983230072969 + 3 ^ 40 * 3001286 * 2
def baseEnd_3001286 : Nat := 342467177691122152982743

theorem tailTrace_3001286 : CollatzResearch.WordTrace tailWord_3001286 prefixEnd_3001286 342467177691122152982743 := by
  unfold tailWord_3001286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3420809168901902365169491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72977262269907250456949141 3420809168901902365169491)
  ·
    refine ⟨5131213753352853547754237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3420809168901902365169491 5131213753352853547754237)
    ·
      refine ⟨1924205157507320080407839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5131213753352853547754237 1924205157507320080407839)
      ·
        refine ⟨2886307736260980120611759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1924205157507320080407839 2886307736260980120611759)
        ·
          refine ⟨4329461604391470180917639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2886307736260980120611759 4329461604391470180917639)
          ·
            refine ⟨6494192406587205271376459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329461604391470180917639 6494192406587205271376459)
            ·
              refine ⟨9741288609880807907064689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494192406587205271376459 9741288609880807907064689)
              ·
                refine ⟨7305966457410605930298517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9741288609880807907064689 7305966457410605930298517)
                ·
                  refine ⟨342467177691122152982743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7305966457410605930298517 342467177691122152982743)
                  ·
                    rfl

theorem cell22_3001286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_3001286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001286 prefixEnd_3001286 := by exact prefixLift 3001286
  have htrace : WordTrace (prefixWord ++ tailWord_3001286) baseStart_3001286 baseEnd_3001286 := by
    simpa [prefixWord, tailWord_3001286, baseEnd_3001286] using wordTrace_append hprefix tailTrace_3001286
  have hstable : (prefixWord ++ tailWord_3001286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001286).length < 2 ^ (prefixWord ++ tailWord_3001286).sum := by decide
  have hdescent : baseEnd_3001286 < baseStart_3001286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001295 : List Nat := [1, 1, 2, 1, 1, 7, 1, 2, 3, 3]
def baseStart_3001295 : Nat := 118140960795 + 3001295 * 2 ^ 59
def prefixEnd_3001295 : Nat := 4983230072969 + 3 ^ 40 * 3001295 * 2
def baseEnd_3001295 : Nat := 1027404613957293435473201

theorem tailTrace_3001295 : CollatzResearch.WordTrace tailWord_3001295 prefixEnd_3001295 1027404613957293435473201 := by
  unfold tailWord_3001295
  simp only [CollatzResearch.WordTrace]
  refine ⟨109466221661828270222501339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72977481107885513481667559 109466221661828270222501339)
  ·
    refine ⟨164199332492742405333752009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109466221661828270222501339 164199332492742405333752009)
    ·
      refine ⟨123149499369556804000314007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164199332492742405333752009 123149499369556804000314007)
      ·
        refine ⟨184724249054335206000471011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123149499369556804000314007 184724249054335206000471011)
        ·
          refine ⟨277086373581502809000706517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184724249054335206000471011 277086373581502809000706517)
          ·
            refine ⟨6494211880816472085954059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 277086373581502809000706517 6494211880816472085954059)
            ·
              refine ⟨9741317821224708128931089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494211880816472085954059 9741317821224708128931089)
              ·
                refine ⟨7305988365918531096698317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9741317821224708128931089 7305988365918531096698317)
                ·
                  refine ⟨2739745637219449161261869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7305988365918531096698317 2739745637219449161261869)
                  ·
                    refine ⟨1027404613957293435473201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739745637219449161261869 1027404613957293435473201)
                    ·
                      rfl

theorem cell22_3001295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 2, 3, 3].length) (baseStart_3001295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001295 prefixEnd_3001295 := by exact prefixLift 3001295
  have htrace : WordTrace (prefixWord ++ tailWord_3001295) baseStart_3001295 baseEnd_3001295 := by
    simpa [prefixWord, tailWord_3001295, baseEnd_3001295] using wordTrace_append hprefix tailTrace_3001295
  have hstable : (prefixWord ++ tailWord_3001295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001295).length < 2 ^ (prefixWord ++ tailWord_3001295).sum := by decide
  have hdescent : baseEnd_3001295 < baseStart_3001295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001338 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_3001338 : Nat := 118140960795 + 3001338 * 2 ^ 59
def prefixEnd_3001338 : Nat := 4983230072969 + 3 ^ 40 * 3001338 * 2
def baseEnd_3001338 : Nat := 1027419333736055656648069

theorem tailTrace_3001338 : CollatzResearch.WordTrace tailWord_3001338 prefixEnd_3001338 1027419333736055656648069 := by
  unfold tailWord_3001338
  simp only [CollatzResearch.WordTrace]
  refine ⟨27366947500168122141579167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72978526667114992377544445 27366947500168122141579167)
  ·
    refine ⟨41050421250252183212368751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27366947500168122141579167 41050421250252183212368751)
    ·
      refine ⟨61575631875378274818553127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41050421250252183212368751 61575631875378274818553127)
      ·
        refine ⟨92363447813067412227829691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61575631875378274818553127 92363447813067412227829691)
        ·
          refine ⟨138545171719601118341744537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92363447813067412227829691 138545171719601118341744537)
          ·
            refine ⟨103908878789700838756308403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138545171719601118341744537 103908878789700838756308403)
            ·
              refine ⟨155863318184551258134462605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103908878789700838756308403 155863318184551258134462605)
              ·
                refine ⟨58448744319206721800423477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 155863318184551258134462605 58448744319206721800423477)
                ·
                  refine ⟨5479569779925630168789701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58448744319206721800423477 5479569779925630168789701)
                  ·
                    refine ⟨1027419333736055656648069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5479569779925630168789701 1027419333736055656648069)
                    ·
                      rfl

theorem cell22_3001338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_3001338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001338 prefixEnd_3001338 := by exact prefixLift 3001338
  have htrace : WordTrace (prefixWord ++ tailWord_3001338) baseStart_3001338 baseEnd_3001338 := by
    simpa [prefixWord, tailWord_3001338, baseEnd_3001338] using wordTrace_append hprefix tailTrace_3001338
  have hstable : (prefixWord ++ tailWord_3001338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001338).length < 2 ^ (prefixWord ++ tailWord_3001338).sum := by decide
  have hdescent : baseEnd_3001338 < baseStart_3001338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001355 : List Nat := [1, 1, 1, 1, 6, 2, 1, 4, 1, 4]
def baseStart_3001355 : Nat := 118140960795 + 3001355 * 2 ^ 59
def prefixEnd_3001355 : Nat := 4983230072969 + 3 ^ 40 * 3001355 * 2
def baseEnd_3001355 : Nat := 1027425153183473278973017

theorem tailTrace_3001355 : CollatzResearch.WordTrace tailWord_3001355 prefixEnd_3001355 1027425153183473278973017 := by
  unfold tailWord_3001355
  simp only [CollatzResearch.WordTrace]
  refine ⟨109468410041610900469685519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72978940027740600313123679 109468410041610900469685519)
  ·
    refine ⟨164202615062416350704528279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109468410041610900469685519 164202615062416350704528279)
    ·
      refine ⟨246303922593624526056792419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164202615062416350704528279 246303922593624526056792419)
      ·
        refine ⟨369455883890436789085188629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246303922593624526056792419 369455883890436789085188629)
        ·
          refine ⟨17318244557364224488368217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 369455883890436789085188629 17318244557364224488368217)
          ·
            refine ⟨12988683418023168366276163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17318244557364224488368217 12988683418023168366276163)
            ·
              refine ⟨19483025127034752549414245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12988683418023168366276163 19483025127034752549414245)
              ·
                refine ⟨3653067211319016103015171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19483025127034752549414245 3653067211319016103015171)
                ·
                  refine ⟨5479600816978524154522757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653067211319016103015171 5479600816978524154522757)
                  ·
                    refine ⟨1027425153183473278973017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5479600816978524154522757 1027425153183473278973017)
                    ·
                      rfl

theorem cell22_3001355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 4].length) (baseStart_3001355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001355 prefixEnd_3001355 := by exact prefixLift 3001355
  have htrace : WordTrace (prefixWord ++ tailWord_3001355) baseStart_3001355 baseEnd_3001355 := by
    simpa [prefixWord, tailWord_3001355, baseEnd_3001355] using wordTrace_append hprefix tailTrace_3001355
  have hstable : (prefixWord ++ tailWord_3001355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001355).length < 2 ^ (prefixWord ++ tailWord_3001355).sum := by decide
  have hdescent : baseEnd_3001355 < baseStart_3001355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001387 : List Nat := [1, 1, 1, 1, 2, 1, 9, 2, 4]
def baseStart_3001387 : Nat := 118140960795 + 3001387 * 2 ^ 59
def prefixEnd_3001387 : Nat := 4983230072969 + 3 ^ 40 * 3001387 * 2
def baseEnd_3001387 : Nat := 342478702479145287390973

theorem tailTrace_3001387 : CollatzResearch.WordTrace tailWord_3001387 prefixEnd_3001387 342478702479145287390973 := by
  unfold tailWord_3001387
  simp only [CollatzResearch.WordTrace]
  refine ⟨109469577177494969934850415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72979718118329979956566943 109469577177494969934850415)
  ·
    refine ⟨164204365766242454902275623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109469577177494969934850415 164204365766242454902275623)
    ·
      refine ⟨246306548649363682353413435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164204365766242454902275623 246306548649363682353413435)
      ·
        refine ⟨369459822974045523530120153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246306548649363682353413435 369459822974045523530120153)
        ·
          refine ⟨277094867230534142647590115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369459822974045523530120153 277094867230534142647590115)
          ·
            refine ⟨415642300845801213971385173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 277094867230534142647590115 415642300845801213971385173)
            ·
              refine ⟨2435404106518366488113585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 415642300845801213971385173 2435404106518366488113585)
              ·
                refine ⟨1826553079888774866085189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435404106518366488113585 1826553079888774866085189)
                ·
                  refine ⟨342478702479145287390973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826553079888774866085189 342478702479145287390973)
                  ·
                    rfl

theorem cell22_3001387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 4].length) (baseStart_3001387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001387 prefixEnd_3001387 := by exact prefixLift 3001387
  have htrace : WordTrace (prefixWord ++ tailWord_3001387) baseStart_3001387 baseEnd_3001387 := by
    simpa [prefixWord, tailWord_3001387, baseEnd_3001387] using wordTrace_append hprefix tailTrace_3001387
  have hstable : (prefixWord ++ tailWord_3001387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001387).length < 2 ^ (prefixWord ++ tailWord_3001387).sum := by decide
  have hdescent : baseEnd_3001387 < baseStart_3001387 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001413 : List Nat := [1, 3, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_3001413 : Nat := 118140960795 + 3001413 * 2 ^ 59
def prefixEnd_3001413 : Nat := 4983230072969 + 3 ^ 40 * 3001413 * 2
def baseEnd_3001413 : Nat := 1027445007768780461022839

theorem tailTrace_3001413 : CollatzResearch.WordTrace tailWord_3001413 prefixEnd_3001413 1027445007768780461022839 := by
  unfold tailWord_3001413
  simp only [CollatzResearch.WordTrace]
  refine ⟨109470525475400776375296893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72980350316933850916864595 109470525475400776375296893)
  ·
    refine ⟨41051447053275291140736335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109470525475400776375296893 41051447053275291140736335)
    ·
      refine ⟨61577170579912936711104503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41051447053275291140736335 61577170579912936711104503)
      ·
        refine ⟨92365755869869405066656755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61577170579912936711104503 92365755869869405066656755)
        ·
          refine ⟨138548633804804107599985133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92365755869869405066656755 138548633804804107599985133)
          ·
            refine ⟨51955737676801540349994425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138548633804804107599985133 51955737676801540349994425)
            ·
              refine ⟨38966803257601155262495819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51955737676801540349994425 38966803257601155262495819)
              ·
                refine ⟨58450204886401732893743729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38966803257601155262495819 58450204886401732893743729)
                ·
                  refine ⟨43837653664801299670307797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58450204886401732893743729 43837653664801299670307797)
                  ·
                    refine ⟨1027445007768780461022839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43837653664801299670307797 1027445007768780461022839)
                    ·
                      rfl

theorem cell22_3001413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_3001413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001413 prefixEnd_3001413 := by exact prefixLift 3001413
  have htrace : WordTrace (prefixWord ++ tailWord_3001413) baseStart_3001413 baseEnd_3001413 := by
    simpa [prefixWord, tailWord_3001413, baseEnd_3001413] using wordTrace_append hprefix tailTrace_3001413
  have hstable : (prefixWord ++ tailWord_3001413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001413).length < 2 ^ (prefixWord ++ tailWord_3001413).sum := by decide
  have hdescent : baseEnd_3001413 < baseStart_3001413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001438 : List Nat := [4, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3001438 : Nat := 118140960795 + 3001438 * 2 ^ 59
def prefixEnd_3001438 : Nat := 4983230072969 + 3 ^ 40 * 3001438 * 2
def baseEnd_3001438 : Nat := 342484521926562909715921

theorem tailTrace_3001438 : CollatzResearch.WordTrace tailWord_3001438 prefixEnd_3001438 342484521926562909715921 := by
  unfold tailWord_3001438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13683929662538775705619621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72980958200206803763304645 13683929662538775705619621)
  ·
    refine ⟨2565736811726020444803679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13683929662538775705619621 2565736811726020444803679)
    ·
      refine ⟨3848605217589030667205519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2565736811726020444803679 3848605217589030667205519)
      ·
        refine ⟨5772907826383546000808279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3848605217589030667205519 5772907826383546000808279)
        ·
          refine ⟨8659361739575319001212419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5772907826383546000808279 8659361739575319001212419)
          ·
            refine ⟨12989042609362978501818629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8659361739575319001212419 12989042609362978501818629)
            ·
              refine ⟨2435445489255558469090993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12989042609362978501818629 2435445489255558469090993)
              ·
                refine ⟨1826584116941668851818245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435445489255558469090993 1826584116941668851818245)
                ·
                  refine ⟨342484521926562909715921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826584116941668851818245 342484521926562909715921)
                  ·
                    rfl

theorem cell22_3001438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3001438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001438 prefixEnd_3001438 := by exact prefixLift 3001438
  have htrace : WordTrace (prefixWord ++ tailWord_3001438) baseStart_3001438 baseEnd_3001438 := by
    simpa [prefixWord, tailWord_3001438, baseEnd_3001438] using wordTrace_append hprefix tailTrace_3001438
  have hstable : (prefixWord ++ tailWord_3001438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001438).length < 2 ^ (prefixWord ++ tailWord_3001438).sum := by decide
  have hdescent : baseEnd_3001438 < baseStart_3001438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001535 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 1, 6]
def baseStart_3001535 : Nat := 118140960795 + 3001535 * 2 ^ 59
def prefixEnd_3001535 : Nat := 4983230072969 + 3 ^ 40 * 3001535 * 2
def baseEnd_3001535 : Nat := 1027486770862012809472465

theorem tailTrace_3001535 : CollatzResearch.WordTrace tailWord_3001535 prefixEnd_3001535 1027486770862012809472465 := by
  unfold tailWord_3001535
  simp only [CollatzResearch.WordTrace]
  refine ⟨109474975180958791211238059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72983316787305860807492039 109474975180958791211238059)
  ·
    refine ⟨164212462771438186816857089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109474975180958791211238059 164212462771438186816857089)
    ·
      refine ⟨123159347078578640112642817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164212462771438186816857089 123159347078578640112642817)
      ·
        refine ⟨92369510308933980084482113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123159347078578640112642817 92369510308933980084482113)
        ·
          refine ⟨69277132731700485063361585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92369510308933980084482113 69277132731700485063361585)
          ·
            refine ⟨51957849548775363797521189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69277132731700485063361585 51957849548775363797521189)
            ·
              refine ⟨9742096790395380712035223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51957849548775363797521189 9742096790395380712035223)
              ·
                refine ⟨14613145185593071068052835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9742096790395380712035223 14613145185593071068052835)
                ·
                  refine ⟨21919717778389606602079253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14613145185593071068052835 21919717778389606602079253)
                  ·
                    refine ⟨1027486770862012809472465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21919717778389606602079253 1027486770862012809472465)
                    ·
                      rfl

theorem cell22_3001535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 6].length) (baseStart_3001535 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001535 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001535 prefixEnd_3001535 := by exact prefixLift 3001535
  have htrace : WordTrace (prefixWord ++ tailWord_3001535) baseStart_3001535 baseEnd_3001535 := by
    simpa [prefixWord, tailWord_3001535, baseEnd_3001535] using wordTrace_append hprefix tailTrace_3001535
  have hstable : (prefixWord ++ tailWord_3001535).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001535).length < 2 ^ (prefixWord ++ tailWord_3001535).sum := by decide
  have hdescent : baseEnd_3001535 < baseStart_3001535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001554 : List Nat := [3, 2, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_3001554 : Nat := 118140960795 + 3001554 * 2 ^ 59
def prefixEnd_3001554 : Nat := 4983230072969 + 3 ^ 40 * 3001554 * 2
def baseEnd_3001554 : Nat := 1027493274950303093247407

theorem tailTrace_3001554 : CollatzResearch.WordTrace tailWord_3001554 prefixEnd_3001554 1027493274950303093247407 := by
  unfold tailWord_3001554
  simp only [CollatzResearch.WordTrace]
  refine ⟨27368917041972489364044929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72983778778593304970786477 27368917041972489364044929)
  ·
    refine ⟨20526687781479367023033697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27368917041972489364044929 20526687781479367023033697)
    ·
      refine ⟨15395015836109525267275273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20526687781479367023033697 15395015836109525267275273)
      ·
        refine ⟨11546261877082143950456455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15395015836109525267275273 11546261877082143950456455)
        ·
          refine ⟨17319392815623215925684683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11546261877082143950456455 17319392815623215925684683)
          ·
            refine ⟨25979089223434823888527025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17319392815623215925684683 25979089223434823888527025)
            ·
              refine ⟨19484316917576117916395269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25979089223434823888527025 19484316917576117916395269)
              ·
                refine ⟨3653309422045522109324113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19484316917576117916395269 3653309422045522109324113)
                ·
                  refine ⟨2739982066534141581993085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3653309422045522109324113 2739982066534141581993085)
                  ·
                    refine ⟨1027493274950303093247407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2739982066534141581993085 1027493274950303093247407)
                    ·
                      rfl

theorem cell22_3001554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_3001554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001554 prefixEnd_3001554 := by exact prefixLift 3001554
  have htrace : WordTrace (prefixWord ++ tailWord_3001554) baseStart_3001554 baseEnd_3001554 := by
    simpa [prefixWord, tailWord_3001554, baseEnd_3001554] using wordTrace_append hprefix tailTrace_3001554
  have hstable : (prefixWord ++ tailWord_3001554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001554).length < 2 ^ (prefixWord ++ tailWord_3001554).sum := by decide
  have hdescent : baseEnd_3001554 < baseStart_3001554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001556 : List Nat := [2, 4, 1, 4, 1, 2, 1, 1, 6]
def baseStart_3001556 : Nat := 118140960795 + 3001556 * 2 ^ 59
def prefixEnd_3001556 : Nat := 4983230072969 + 3 ^ 40 * 3001556 * 2
def baseEnd_3001556 : Nat := 342497986530391918232467

theorem tailTrace_3001556 : CollatzResearch.WordTrace tailWord_3001556 prefixEnd_3001556 342497986530391918232467 := by
  unfold tailWord_3001556
  simp only [CollatzResearch.WordTrace]
  refine ⟨54737870556941355898876261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72983827409255141198501681 54737870556941355898876261)
  ·
    refine ⟨10263350729426504231039299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54737870556941355898876261 10263350729426504231039299)
    ·
      refine ⟨15395026094139756346558949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10263350729426504231039299 15395026094139756346558949)
      ·
        refine ⟨2886567392651204314979803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15395026094139756346558949 2886567392651204314979803)
        ·
          refine ⟨4329851088976806472469705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2886567392651204314979803 4329851088976806472469705)
          ·
            refine ⟨3247388316732604854352279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4329851088976806472469705 3247388316732604854352279)
            ·
              refine ⟨4871082475098907281528419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247388316732604854352279 4871082475098907281528419)
              ·
                refine ⟨7306623712648360922292629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871082475098907281528419 7306623712648360922292629)
                ·
                  refine ⟨342497986530391918232467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7306623712648360922292629 342497986530391918232467)
                  ·
                    rfl

theorem cell22_3001556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_3001556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001556 prefixEnd_3001556 := by exact prefixLift 3001556
  have htrace : WordTrace (prefixWord ++ tailWord_3001556) baseStart_3001556 baseEnd_3001556 := by
    simpa [prefixWord, tailWord_3001556, baseEnd_3001556] using wordTrace_append hprefix tailTrace_3001556
  have hstable : (prefixWord ++ tailWord_3001556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001556).length < 2 ^ (prefixWord ++ tailWord_3001556).sum := by decide
  have hdescent : baseEnd_3001556 < baseStart_3001556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001588 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_3001588 : Nat := 118140960795 + 3001588 * 2 ^ 59
def prefixEnd_3001588 : Nat := 4983230072969 + 3 ^ 40 * 3001588 * 2
def baseEnd_3001588 : Nat := 1027504913845138337897303

theorem tailTrace_3001588 : CollatzResearch.WordTrace tailWord_3001588 prefixEnd_3001588 1027504913845138337897303 := by
  unfold tailWord_3001588
  simp only [CollatzResearch.WordTrace]
  refine ⟨54738454124883390631458709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72984605499844520841944945 54738454124883390631458709)
  ·
    refine ⟨2565865037103908935849627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 54738454124883390631458709 2565865037103908935849627)
    ·
      refine ⟨3848797555655863403774441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2565865037103908935849627 3848797555655863403774441)
      ·
        refine ⟨2886598166741897552830831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3848797555655863403774441 2886598166741897552830831)
        ·
          refine ⟨4329897250112846329246247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2886598166741897552830831 4329897250112846329246247)
          ·
            refine ⟨6494845875169269493869371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4329897250112846329246247 6494845875169269493869371)
            ·
              refine ⟨9742268812753904240804057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6494845875169269493869371 9742268812753904240804057)
              ·
                refine ⟨7306701609565428180603043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9742268812753904240804057 7306701609565428180603043)
                ·
                  refine ⟨10960052414348142270904565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7306701609565428180603043 10960052414348142270904565)
                  ·
                    refine ⟨1027504913845138337897303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10960052414348142270904565 1027504913845138337897303)
                    ·
                      rfl

theorem cell22_3001588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_3001588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001588 prefixEnd_3001588 := by exact prefixLift 3001588
  have htrace : WordTrace (prefixWord ++ tailWord_3001588) baseStart_3001588 baseEnd_3001588 := by
    simpa [prefixWord, tailWord_3001588, baseEnd_3001588] using wordTrace_append hprefix tailTrace_3001588
  have hstable : (prefixWord ++ tailWord_3001588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001588).length < 2 ^ (prefixWord ++ tailWord_3001588).sum := by decide
  have hdescent : baseEnd_3001588 < baseStart_3001588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001612 : List Nat := [2, 2, 1, 2, 2, 3, 1, 4, 5]
def baseStart_3001612 : Nat := 118140960795 + 3001612 * 2 ^ 59
def prefixEnd_3001612 : Nat := 4983230072969 + 3 ^ 40 * 3001612 * 2
def baseEnd_3001612 : Nat := 342504376511870091765743

theorem tailTrace_3001612 : CollatzResearch.WordTrace tailWord_3001612 prefixEnd_3001612 342504376511870091765743 := by
  unfold tailWord_3001612
  simp only [CollatzResearch.WordTrace]
  refine ⟨54738891800839916680895545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72985189067786555574527393 54738891800839916680895545)
  ·
    refine ⟨41054168850629937510671659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54738891800839916680895545 41054168850629937510671659)
    ·
      refine ⟨61581253275944906266007489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41054168850629937510671659 61581253275944906266007489)
      ·
        refine ⟨46185939956958679699505617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61581253275944906266007489 46185939956958679699505617)
        ·
          refine ⟨34639454967719009774629213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46185939956958679699505617 34639454967719009774629213)
          ·
            refine ⟨12989795612894628665485955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34639454967719009774629213 12989795612894628665485955)
            ·
              refine ⟨19484693419341942998228933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12989795612894628665485955 19484693419341942998228933)
              ·
                refine ⟨3653380016126614312167925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19484693419341942998228933 3653380016126614312167925)
                ·
                  refine ⟨342504376511870091765743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3653380016126614312167925 342504376511870091765743)
                  ·
                    rfl

theorem cell22_3001612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_3001612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001612 prefixEnd_3001612 := by exact prefixLift 3001612
  have htrace : WordTrace (prefixWord ++ tailWord_3001612) baseStart_3001612 baseEnd_3001612 := by
    simpa [prefixWord, tailWord_3001612, baseEnd_3001612] using wordTrace_append hprefix tailTrace_3001612
  have hstable : (prefixWord ++ tailWord_3001612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001612).length < 2 ^ (prefixWord ++ tailWord_3001612).sum := by decide
  have hdescent : baseEnd_3001612 < baseStart_3001612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001618 : List Nat := [3, 2, 4, 2, 2, 1, 1, 7]
def baseStart_3001618 : Nat := 118140960795 + 3001618 * 2 ^ 59
def prefixEnd_3001618 : Nat := 4983230072969 + 3 ^ 40 * 3001618 * 2
def baseEnd_3001618 : Nat := 114168353717580917738579

theorem tailTrace_3001618 : CollatzResearch.WordTrace tailWord_3001618 prefixEnd_3001618 114168353717580917738579 := by
  unfold tailWord_3001618
  simp only [CollatzResearch.WordTrace]
  refine ⟨27369500609914524096627377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72985334959772064257673005 27369500609914524096627377)
  ·
    refine ⟨20527125457435893072470533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27369500609914524096627377 20527125457435893072470533)
    ·
      refine ⟨3848836023269229951088225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20527125457435893072470533 3848836023269229951088225)
      ·
        refine ⟨2886627017451922463316169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3848836023269229951088225 2886627017451922463316169)
        ·
          refine ⟨2164970263088941847487127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2886627017451922463316169 2164970263088941847487127)
          ·
            refine ⟨3247455394633412771230691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2164970263088941847487127 3247455394633412771230691)
            ·
              refine ⟨4871183091950119156846037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3247455394633412771230691 4871183091950119156846037)
              ·
                refine ⟨114168353717580917738579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4871183091950119156846037 114168353717580917738579)
                ·
                  rfl

theorem cell22_3001618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_3001618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001618 prefixEnd_3001618 := by exact prefixLift 3001618
  have htrace : WordTrace (prefixWord ++ tailWord_3001618) baseStart_3001618 baseEnd_3001618 := by
    simpa [prefixWord, tailWord_3001618, baseEnd_3001618] using wordTrace_append hprefix tailTrace_3001618
  have hstable : (prefixWord ++ tailWord_3001618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001618).length < 2 ^ (prefixWord ++ tailWord_3001618).sum := by decide
  have hdescent : baseEnd_3001618 < baseStart_3001618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001629 : List Nat := [1, 4, 2, 3, 1, 1, 2, 3, 5]
def baseStart_3001629 : Nat := 118140960795 + 3001629 * 2 ^ 59
def prefixEnd_3001629 : Nat := 4983230072969 + 3 ^ 40 * 3001629 * 2
def baseEnd_3001629 : Nat := 342506316327675965874059

theorem tailTrace_3001629 : CollatzResearch.WordTrace tailWord_3001629 prefixEnd_3001629 342506316327675965874059 := by
  unfold tailWord_3001629
  simp only [CollatzResearch.WordTrace]
  refine ⟨109478403642618245265159941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72985602428412163510106627 109478403642618245265159941)
  ·
    refine ⟨20527200682990920987217489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109478403642618245265159941 20527200682990920987217489)
    ·
      refine ⟨15395400512243190740413117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20527200682990920987217489 15395400512243190740413117)
      ·
        refine ⟨5773275192091196527654919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15395400512243190740413117 5773275192091196527654919)
        ·
          refine ⟨8659912788136794791482379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5773275192091196527654919 8659912788136794791482379)
          ·
            refine ⟨12989869182205192187223569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8659912788136794791482379 12989869182205192187223569)
            ·
              refine ⟨9742401886653894140417677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12989869182205192187223569 9742401886653894140417677)
              ·
                refine ⟨3653400707495210302656629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9742401886653894140417677 3653400707495210302656629)
                ·
                  refine ⟨342506316327675965874059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3653400707495210302656629 342506316327675965874059)
                  ·
                    rfl

theorem cell22_3001629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_3001629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001629 prefixEnd_3001629 := by exact prefixLift 3001629
  have htrace : WordTrace (prefixWord ++ tailWord_3001629) baseStart_3001629 baseEnd_3001629 := by
    simpa [prefixWord, tailWord_3001629, baseEnd_3001629] using wordTrace_append hprefix tailTrace_3001629
  have hstable : (prefixWord ++ tailWord_3001629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001629).length < 2 ^ (prefixWord ++ tailWord_3001629).sum := by decide
  have hdescent : baseEnd_3001629 < baseStart_3001629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001687 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 1, 6]
def baseStart_3001687 : Nat := 118140960795 + 3001687 * 2 ^ 59
def prefixEnd_3001687 : Nat := 4983230072969 + 3 ^ 40 * 3001687 * 2
def baseEnd_3001687 : Nat := 1027538803568335079671999

theorem tailTrace_3001687 : CollatzResearch.WordTrace tailWord_3001687 prefixEnd_3001687 1027538803568335079671999 := by
  unfold tailWord_3001687
  simp only [CollatzResearch.WordTrace]
  refine ⟨109480519076408121170771315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72987012717605414113847543 109480519076408121170771315)
  ·
    refine ⟨164220778614612181756156973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109480519076408121170771315 164220778614612181756156973)
    ·
      refine ⟨61582791980479568158558865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164220778614612181756156973 61582791980479568158558865)
      ·
        refine ⟨46187093985359676118919149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61582791980479568158558865 46187093985359676118919149)
        ·
          refine ⟨17320160244509878544594681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46187093985359676118919149 17320160244509878544594681)
          ·
            refine ⟨12990120183382408908446011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17320160244509878544594681 12990120183382408908446011)
            ·
              refine ⟨19485180275073613362669017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12990120183382408908446011 19485180275073613362669017)
              ·
                refine ⟨14613885206305210022001763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19485180275073613362669017 14613885206305210022001763)
                ·
                  refine ⟨21920827809457815033002645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14613885206305210022001763 21920827809457815033002645)
                  ·
                    refine ⟨1027538803568335079671999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21920827809457815033002645 1027538803568335079671999)
                    ·
                      rfl

theorem cell22_3001687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_3001687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001687 prefixEnd_3001687 := by exact prefixLift 3001687
  have htrace : WordTrace (prefixWord ++ tailWord_3001687) baseStart_3001687 baseEnd_3001687 := by
    simpa [prefixWord, tailWord_3001687, baseEnd_3001687] using wordTrace_append hprefix tailTrace_3001687
  have hstable : (prefixWord ++ tailWord_3001687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001687).length < 2 ^ (prefixWord ++ tailWord_3001687).sum := by decide
  have hdescent : baseEnd_3001687 < baseStart_3001687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001689 : List Nat := [1, 2, 1, 2, 2, 2, 2, 5, 2, 3]
def baseStart_3001689 : Nat := 118140960795 + 3001689 * 2 ^ 59
def prefixEnd_3001689 : Nat := 4983230072969 + 3 ^ 40 * 3001689 * 2
def baseEnd_3001689 : Nat := 1027539488209207741121993

theorem tailTrace_3001689 : CollatzResearch.WordTrace tailWord_3001689 prefixEnd_3001689 1027539488209207741121993 := by
  unfold tailWord_3001689
  simp only [CollatzResearch.WordTrace]
  refine ⟨109480592022400875512344121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72987061348267250341562747 109480592022400875512344121)
  ·
    refine ⟨82110444016800656634258091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109480592022400875512344121 82110444016800656634258091)
    ·
      refine ⟨123165666025200984951387137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82110444016800656634258091 123165666025200984951387137)
      ·
        refine ⟨92374249518900738713540353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123165666025200984951387137 92374249518900738713540353)
        ·
          refine ⟨69280687139175554035155265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92374249518900738713540353 69280687139175554035155265)
          ·
            refine ⟨51960515354381665526366449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69280687139175554035155265 51960515354381665526366449)
            ·
              refine ⟨38970386515786249144774837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51960515354381665526366449 38970386515786249144774837)
              ·
                refine ⟨3653473735854960857322641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38970386515786249144774837 3653473735854960857322641)
                ·
                  refine ⟨2740105301891220642991981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3653473735854960857322641 2740105301891220642991981)
                  ·
                    refine ⟨1027539488209207741121993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2740105301891220642991981 1027539488209207741121993)
                    ·
                      rfl

theorem cell22_3001689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_3001689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001689 prefixEnd_3001689 := by exact prefixLift 3001689
  have htrace : WordTrace (prefixWord ++ tailWord_3001689) baseStart_3001689 baseEnd_3001689 := by
    simpa [prefixWord, tailWord_3001689, baseEnd_3001689] using wordTrace_append hprefix tailTrace_3001689
  have hstable : (prefixWord ++ tailWord_3001689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001689).length < 2 ^ (prefixWord ++ tailWord_3001689).sum := by decide
  have hdescent : baseEnd_3001689 < baseStart_3001689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001781 : List Nat := [1, 3, 3, 2, 2, 2, 2, 2, 5]
def baseStart_3001781 : Nat := 118140960795 + 3001781 * 2 ^ 59
def prefixEnd_3001781 : Nat := 4983230072969 + 3 ^ 40 * 3001781 * 2
def baseEnd_3001781 : Nat := 342523660563116722607237

theorem tailTrace_3001781 : CollatzResearch.WordTrace tailWord_3001781 prefixEnd_3001781 342523660563116722607237 := by
  unfold tailWord_3001781
  simp only [CollatzResearch.WordTrace]
  refine ⟨109483947538067575224693197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72989298358711716816462131 109483947538067575224693197)
  ·
    refine ⟨41056480326775340709259949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109483947538067575224693197 41056480326775340709259949)
    ·
      refine ⟨15396180122540752765972481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41056480326775340709259949 15396180122540752765972481)
      ·
        refine ⟨11547135091905564574479361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15396180122540752765972481 11547135091905564574479361)
        ·
          refine ⟨8660351318929173430859521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11547135091905564574479361 8660351318929173430859521)
          ·
            refine ⟨6495263489196880073144641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8660351318929173430859521 6495263489196880073144641)
            ·
              refine ⟨4871447616897660054858481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6495263489196880073144641 4871447616897660054858481)
              ·
                refine ⟨3653585712673245041143861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4871447616897660054858481 3653585712673245041143861)
                ·
                  refine ⟨342523660563116722607237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3653585712673245041143861 342523660563116722607237)
                  ·
                    rfl

theorem cell22_3001781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 5].length) (baseStart_3001781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001781 prefixEnd_3001781 := by exact prefixLift 3001781
  have htrace : WordTrace (prefixWord ++ tailWord_3001781) baseStart_3001781 baseEnd_3001781 := by
    simpa [prefixWord, tailWord_3001781, baseEnd_3001781] using wordTrace_append hprefix tailTrace_3001781
  have hstable : (prefixWord ++ tailWord_3001781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001781).length < 2 ^ (prefixWord ++ tailWord_3001781).sum := by decide
  have hdescent : baseEnd_3001781 < baseStart_3001781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001796 : List Nat := [2, 3, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_3001796 : Nat := 118140960795 + 3001796 * 2 ^ 59
def prefixEnd_3001796 : Nat := 4983230072969 + 3 ^ 40 * 3001796 * 2
def baseEnd_3001796 : Nat := 1027576116495895128696665

theorem tailTrace_3001796 : CollatzResearch.WordTrace tailWord_3001796 prefixEnd_3001796 1027576116495895128696665 := by
  unfold tailWord_3001796
  simp only [CollatzResearch.WordTrace]
  refine ⟨54742247316506616393244621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72989663088675488524326161 54742247316506616393244621)
  ·
    refine ⟨20528342743689981147466733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54742247316506616393244621 20528342743689981147466733)
    ·
      refine ⟨7698128528883742930300025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20528342743689981147466733 7698128528883742930300025)
      ·
        refine ⟨5773596396662807197725019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7698128528883742930300025 5773596396662807197725019)
        ·
          refine ⟨8660394594994210796587529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5773596396662807197725019 8660394594994210796587529)
          ·
            refine ⟨6495295946245658097440647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8660394594994210796587529 6495295946245658097440647)
            ·
              refine ⟨9742943919368487146160971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495295946245658097440647 9742943919368487146160971)
              ·
                refine ⟨14614415879052730719241457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9742943919368487146160971 14614415879052730719241457)
                ·
                  refine ⟨10960811909289548039431093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14614415879052730719241457 10960811909289548039431093)
                  ·
                    refine ⟨1027576116495895128696665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10960811909289548039431093 1027576116495895128696665)
                    ·
                      rfl

theorem cell22_3001796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_3001796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001796 prefixEnd_3001796 := by exact prefixLift 3001796
  have htrace : WordTrace (prefixWord ++ tailWord_3001796) baseStart_3001796 baseEnd_3001796 := by
    simpa [prefixWord, tailWord_3001796, baseEnd_3001796] using wordTrace_append hprefix tailTrace_3001796
  have hstable : (prefixWord ++ tailWord_3001796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001796).length < 2 ^ (prefixWord ++ tailWord_3001796).sum := by decide
  have hdescent : baseEnd_3001796 < baseStart_3001796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001839 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 2, 4]
def baseStart_3001839 : Nat := 118140960795 + 3001839 * 2 ^ 59
def prefixEnd_3001839 : Nat := 4983230072969 + 3 ^ 40 * 3001839 * 2
def baseEnd_3001839 : Nat := 1027590836274657349871533

theorem tailTrace_3001839 : CollatzResearch.WordTrace tailWord_3001839 prefixEnd_3001839 1027590836274657349871533 := by
  unfold tailWord_3001839
  simp only [CollatzResearch.WordTrace]
  refine ⟨109486062971857451130304571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72990708647904967420203047 109486062971857451130304571)
  ·
    refine ⟨164229094457786176695456857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109486062971857451130304571 164229094457786176695456857)
    ·
      refine ⟨123171820843339632521592643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164229094457786176695456857 123171820843339632521592643)
      ·
        refine ⟨184757731265009448782388965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123171820843339632521592643 184757731265009448782388965)
        ·
          refine ⟨34642074612189271646697931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184757731265009448782388965 34642074612189271646697931)
          ·
            refine ⟨51963111918283907470046897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34642074612189271646697931 51963111918283907470046897)
            ·
              refine ⟨38972333938712930602535173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51963111918283907470046897 38972333938712930602535173)
              ·
                refine ⟨7307312613508674487975345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38972333938712930602535173 7307312613508674487975345)
                ·
                  refine ⟨5480484460131505865981509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7307312613508674487975345 5480484460131505865981509)
                  ·
                    refine ⟨1027590836274657349871533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5480484460131505865981509 1027590836274657349871533)
                    ·
                      rfl

theorem cell22_3001839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_3001839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001839 prefixEnd_3001839 := by exact prefixLift 3001839
  have htrace : WordTrace (prefixWord ++ tailWord_3001839) baseStart_3001839 baseEnd_3001839 := by
    simpa [prefixWord, tailWord_3001839, baseEnd_3001839] using wordTrace_append hprefix tailTrace_3001839
  have hstable : (prefixWord ++ tailWord_3001839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001839).length < 2 ^ (prefixWord ++ tailWord_3001839).sum := by decide
  have hdescent : baseEnd_3001839 < baseStart_3001839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001841 : List Nat := [1, 2, 2, 2, 3, 3, 1, 1, 4, 3]
def baseStart_3001841 : Nat := 118140960795 + 3001841 * 2 ^ 59
def prefixEnd_3001841 : Nat := 4983230072969 + 3 ^ 40 * 3001841 * 2
def baseEnd_3001841 : Nat := 1027591520915530011321527

theorem tailTrace_3001841 : CollatzResearch.WordTrace tailWord_3001841 prefixEnd_3001841 1027591520915530011321527 := by
  unfold tailWord_3001841
  simp only [CollatzResearch.WordTrace]
  refine ⟨109486135917850205471877377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72990757278566803647918251 109486135917850205471877377)
  ·
    refine ⟨82114601938387654103908033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109486135917850205471877377 82114601938387654103908033)
    ·
      refine ⟨61585951453790740577931025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82114601938387654103908033 61585951453790740577931025)
      ·
        refine ⟨46189463590343055433448269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61585951453790740577931025 46189463590343055433448269)
        ·
          refine ⟨17321048846378645787543101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46189463590343055433448269 17321048846378645787543101)
          ·
            refine ⟨6495393317391992170328663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17321048846378645787543101 6495393317391992170328663)
            ·
              refine ⟨9743089976087988255492995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495393317391992170328663 9743089976087988255492995)
              ·
                refine ⟨14614634964131982383239493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9743089976087988255492995 14614634964131982383239493)
                ·
                  refine ⟨2740244055774746696857405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14614634964131982383239493 2740244055774746696857405)
                  ·
                    refine ⟨1027591520915530011321527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2740244055774746696857405 1027591520915530011321527)
                    ·
                      rfl

theorem cell22_3001841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 3].length) (baseStart_3001841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001841 prefixEnd_3001841 := by exact prefixLift 3001841
  have htrace : WordTrace (prefixWord ++ tailWord_3001841) baseStart_3001841 baseEnd_3001841 := by
    simpa [prefixWord, tailWord_3001841, baseEnd_3001841] using wordTrace_append hprefix tailTrace_3001841
  have hstable : (prefixWord ++ tailWord_3001841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001841).length < 2 ^ (prefixWord ++ tailWord_3001841).sum := by decide
  have hdescent : baseEnd_3001841 < baseStart_3001841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001858 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_3001858 : Nat := 118140960795 + 3001858 * 2 ^ 59
def prefixEnd_3001858 : Nat := 4983230072969 + 3 ^ 40 * 3001858 * 2
def baseEnd_3001858 : Nat := 1027597340362947633646475

theorem tailTrace_3001858 : CollatzResearch.WordTrace tailWord_3001858 prefixEnd_3001858 1027597340362947633646475 := by
  unfold tailWord_3001858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27371688989697154343811557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72991170639192411583497485 27371688989697154343811557)
  ·
    refine ⟨5132191685568216439464667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27371688989697154343811557 5132191685568216439464667)
    ·
      refine ⟨7698287528352324659197001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5132191685568216439464667 7698287528352324659197001)
      ·
        refine ⟨5773715646264243494397751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7698287528352324659197001 5773715646264243494397751)
        ·
          refine ⟨8660573469396365241596627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5773715646264243494397751 8660573469396365241596627)
          ·
            refine ⟨12990860204094547862394941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8660573469396365241596627 12990860204094547862394941)
            ·
              refine ⟨4871572576535455448398103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12990860204094547862394941 4871572576535455448398103)
              ·
                refine ⟨7307358864803183172597155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4871572576535455448398103 7307358864803183172597155)
                ·
                  refine ⟨10961038297204774758895733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7307358864803183172597155 10961038297204774758895733)
                  ·
                    refine ⟨1027597340362947633646475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10961038297204774758895733 1027597340362947633646475)
                    ·
                      rfl

theorem cell22_3001858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_3001858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001858 prefixEnd_3001858 := by exact prefixLift 3001858
  have htrace : WordTrace (prefixWord ++ tailWord_3001858) baseStart_3001858 baseEnd_3001858 := by
    simpa [prefixWord, tailWord_3001858, baseEnd_3001858] using wordTrace_append hprefix tailTrace_3001858
  have hstable : (prefixWord ++ tailWord_3001858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001858).length < 2 ^ (prefixWord ++ tailWord_3001858).sum := by decide
  have hdescent : baseEnd_3001858 < baseStart_3001858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001914 : List Nat := [3, 1, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_3001914 : Nat := 118140960795 + 3001914 * 2 ^ 59
def prefixEnd_3001914 : Nat := 4983230072969 + 3 ^ 40 * 3001914 * 2
def baseEnd_3001914 : Nat := 1027616510307382154246303

theorem tailTrace_3001914 : CollatzResearch.WordTrace tailWord_3001914 prefixEnd_3001914 1027616510307382154246303 := by
  unfold tailWord_3001914
  simp only [CollatzResearch.WordTrace]
  refine ⟨27372199611646434734821199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72992532297723825959523197 27372199611646434734821199)
  ·
    refine ⟨41058299417469652102231799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27372199611646434734821199 41058299417469652102231799)
    ·
      refine ⟨61587449126204478153347699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41058299417469652102231799 61587449126204478153347699)
      ·
        refine ⟨92381173689306717230021549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61587449126204478153347699 92381173689306717230021549)
        ·
          refine ⟨34642940133490018961258081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92381173689306717230021549 34642940133490018961258081)
          ·
            refine ⟨25982205100117514220943561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34642940133490018961258081 25982205100117514220943561)
            ·
              refine ⟨19486653825088135665707671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25982205100117514220943561 19486653825088135665707671)
              ·
                refine ⟨29229980737632203498561507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19486653825088135665707671 29229980737632203498561507)
                ·
                  refine ⟨43844971106448305247842261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29229980737632203498561507 43844971106448305247842261)
                  ·
                    refine ⟨1027616510307382154246303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43844971106448305247842261 1027616510307382154246303)
                    ·
                      rfl

theorem cell22_3001914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_3001914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001914 prefixEnd_3001914 := by exact prefixLift 3001914
  have htrace : WordTrace (prefixWord ++ tailWord_3001914) baseStart_3001914 baseEnd_3001914 := by
    simpa [prefixWord, tailWord_3001914, baseEnd_3001914] using wordTrace_append hprefix tailTrace_3001914
  have hstable : (prefixWord ++ tailWord_3001914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001914).length < 2 ^ (prefixWord ++ tailWord_3001914).sum := by decide
  have hdescent : baseEnd_3001914 < baseStart_3001914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001946 : List Nat := [3, 1, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_3001946 : Nat := 118140960795 + 3001946 * 2 ^ 59
def prefixEnd_3001946 : Nat := 4983230072969 + 3 ^ 40 * 3001946 * 2
def baseEnd_3001946 : Nat := 1027627464561344737446205

theorem tailTrace_3001946 : CollatzResearch.WordTrace tailWord_3001946 prefixEnd_3001946 1027627464561344737446205 := by
  unfold tailWord_3001946
  simp only [CollatzResearch.WordTrace]
  refine ⟨27372491395617452101112423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72993310388313205602966461 27372491395617452101112423)
  ·
    refine ⟨41058737093426178151668635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27372491395617452101112423 41058737093426178151668635)
    ·
      refine ⟨61588105640139267227502953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41058737093426178151668635 61588105640139267227502953)
      ·
        refine ⟨46191079230104450420627215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61588105640139267227502953 46191079230104450420627215)
        ·
          refine ⟨69286618845156675630940823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46191079230104450420627215 69286618845156675630940823)
          ·
            refine ⟨103929928267735013446411235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69286618845156675630940823 103929928267735013446411235)
            ·
              refine ⟨155894892401602520169616853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103929928267735013446411235 155894892401602520169616853)
              ·
                refine ⟨3653786540662559066475395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 155894892401602520169616853 3653786540662559066475395)
                ·
                  refine ⟨5480679810993838599713093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3653786540662559066475395 5480679810993838599713093)
                  ·
                    refine ⟨1027627464561344737446205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5480679810993838599713093 1027627464561344737446205)
                    ·
                      rfl

theorem cell22_3001946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_3001946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001946 prefixEnd_3001946 := by exact prefixLift 3001946
  have htrace : WordTrace (prefixWord ++ tailWord_3001946) baseStart_3001946 baseEnd_3001946 := by
    simpa [prefixWord, tailWord_3001946, baseEnd_3001946] using wordTrace_append hprefix tailTrace_3001946
  have hstable : (prefixWord ++ tailWord_3001946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001946).length < 2 ^ (prefixWord ++ tailWord_3001946).sum := by decide
  have hdescent : baseEnd_3001946 < baseStart_3001946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3001991 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3001991 : Nat := 118140960795 + 3001991 * 2 ^ 59
def prefixEnd_3001991 : Nat := 4983230072969 + 3 ^ 40 * 3001991 * 2
def baseEnd_3001991 : Nat := 1027642868980979620071067

theorem tailTrace_3001991 : CollatzResearch.WordTrace tailWord_3001991 prefixEnd_3001991 1027642868980979620071067 := by
  unfold tailWord_3001991
  simp only [CollatzResearch.WordTrace]
  refine ⟨109491606867306781089837827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72994404578204520726558551 109491606867306781089837827)
  ·
    refine ⟨164237410300960171634756741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109491606867306781089837827 164237410300960171634756741)
    ·
      refine ⟨30794514431430032181516889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164237410300960171634756741 30794514431430032181516889)
      ·
        refine ⟨23095885823572524136137667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30794514431430032181516889 23095885823572524136137667)
        ·
          refine ⟨34643828735358786204206501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23095885823572524136137667 34643828735358786204206501)
          ·
            refine ⟨6495717887879772413288719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34643828735358786204206501 6495717887879772413288719)
            ·
              refine ⟨9743576831819658619933079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6495717887879772413288719 9743576831819658619933079)
              ·
                refine ⟨14615365247729487929899619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9743576831819658619933079 14615365247729487929899619)
                ·
                  refine ⟨21923047871594231894849429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14615365247729487929899619 21923047871594231894849429)
                  ·
                    refine ⟨1027642868980979620071067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21923047871594231894849429 1027642868980979620071067)
                    ·
                      rfl

theorem cell22_3001991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3001991 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3001991 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3001991 prefixEnd_3001991 := by exact prefixLift 3001991
  have htrace : WordTrace (prefixWord ++ tailWord_3001991) baseStart_3001991 baseEnd_3001991 := by
    simpa [prefixWord, tailWord_3001991, baseEnd_3001991] using wordTrace_append hprefix tailTrace_3001991
  have hstable : (prefixWord ++ tailWord_3001991).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3001991).length < 2 ^ (prefixWord ++ tailWord_3001991).sum := by decide
  have hdescent : baseEnd_3001991 < baseStart_3001991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3001991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002068 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 7]
def baseStart_3002068 : Nat := 118140960795 + 3002068 * 2 ^ 59
def prefixEnd_3002068 : Nat := 4983230072969 + 3 ^ 40 * 3002068 * 2
def baseEnd_3002068 : Nat := 342556409218192361965277

theorem tailTrace_3002068 : CollatzResearch.WordTrace tailWord_3002068 prefixEnd_3002068 342556409218192361965277 := by
  unfold tailWord_3002068
  simp only [CollatzResearch.WordTrace]
  refine ⟨54747207644013911620195429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72996276858685215493593905 54747207644013911620195429)
  ·
    refine ⟨10265101433252608428786643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54747207644013911620195429 10265101433252608428786643)
    ·
      refine ⟨15397652149878912643179965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10265101433252608428786643 15397652149878912643179965)
      ·
        refine ⟨5774119556204592241192487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15397652149878912643179965 5774119556204592241192487)
        ·
          refine ⟨8661179334306888361788731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5774119556204592241192487 8661179334306888361788731)
          ·
            refine ⟨12991769001460332542683097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8661179334306888361788731 12991769001460332542683097)
            ·
              refine ⟨9743826751095249407012323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12991769001460332542683097 9743826751095249407012323)
              ·
                refine ⟨14615740126642874110518485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9743826751095249407012323 14615740126642874110518485)
                ·
                  refine ⟨342556409218192361965277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14615740126642874110518485 342556409218192361965277)
                  ·
                    rfl

theorem cell22_3002068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_3002068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002068 prefixEnd_3002068 := by exact prefixLift 3002068
  have htrace : WordTrace (prefixWord ++ tailWord_3002068) baseStart_3002068 baseEnd_3002068 := by
    simpa [prefixWord, tailWord_3002068, baseEnd_3002068] using wordTrace_append hprefix tailTrace_3002068
  have hstable : (prefixWord ++ tailWord_3002068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002068).length < 2 ^ (prefixWord ++ tailWord_3002068).sum := by decide
  have hdescent : baseEnd_3002068 < baseStart_3002068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002072 : List Nat := [2, 1, 2, 2, 3, 1, 5, 2, 1, 3]
def baseStart_3002072 : Nat := 118140960795 + 3002072 * 2 ^ 59
def prefixEnd_3002072 : Nat := 4983230072969 + 3 ^ 40 * 3002072 * 2
def baseEnd_3002072 : Nat := 1027670596936322408795819

theorem tailTrace_3002072 : CollatzResearch.WordTrace tailWord_3002072 prefixEnd_3002072 1027670596936322408795819 := by
  unfold tailWord_3002072
  simp only [CollatzResearch.WordTrace]
  refine ⟨54747280590006665961768235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72996374120008887949024313 54747280590006665961768235)
  ·
    refine ⟨82120920885009998942652353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54747280590006665961768235 82120920885009998942652353)
    ·
      refine ⟨61590690663757499206989265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82120920885009998942652353 61590690663757499206989265)
      ·
        refine ⟨46193017997818124405241949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61590690663757499206989265 46193017997818124405241949)
        ·
          refine ⟨17322381749181796651965731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46193017997818124405241949 17322381749181796651965731)
          ·
            refine ⟨25983572623772694977948597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17322381749181796651965731 25983572623772694977948597)
            ·
              refine ⟨2435959933478690154182681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25983572623772694977948597 2435959933478690154182681)
              ·
                refine ⟨1826969950109017615637011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2435959933478690154182681 1826969950109017615637011)
                ·
                  refine ⟨2740454925163526423455517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1826969950109017615637011 2740454925163526423455517)
                  ·
                    refine ⟨1027670596936322408795819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2740454925163526423455517 1027670596936322408795819)
                    ·
                      rfl

theorem cell22_3002072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 2, 1, 3].length) (baseStart_3002072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002072 prefixEnd_3002072 := by exact prefixLift 3002072
  have htrace : WordTrace (prefixWord ++ tailWord_3002072) baseStart_3002072 baseEnd_3002072 := by
    simpa [prefixWord, tailWord_3002072, baseEnd_3002072] using wordTrace_append hprefix tailTrace_3002072
  have hstable : (prefixWord ++ tailWord_3002072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002072).length < 2 ^ (prefixWord ++ tailWord_3002072).sum := by decide
  have hdescent : baseEnd_3002072 < baseStart_3002072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002098 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_3002098 : Nat := 118140960795 + 3002098 * 2 ^ 59
def prefixEnd_3002098 : Nat := 4983230072969 + 3 ^ 40 * 3002098 * 2
def baseEnd_3002098 : Nat := 1027679497267667007645739

theorem tailTrace_3002098 : CollatzResearch.WordTrace tailWord_3002098 prefixEnd_3002098 1027679497267667007645739 := by
  unfold tailWord_3002098
  simp only [CollatzResearch.WordTrace]
  refine ⟨27373877369479784590995737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72997006318612758909321965 27373877369479784590995737)
  ·
    refine ⟨20530408027109838443246803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27373877369479784590995737 20530408027109838443246803)
    ·
      refine ⟨30795612040664757664870205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20530408027109838443246803 30795612040664757664870205)
      ·
        refine ⟨11548354515249284124326327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30795612040664757664870205 11548354515249284124326327)
        ·
          refine ⟨17322531772873926186489491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11548354515249284124326327 17322531772873926186489491)
          ·
            refine ⟨25983797659310889279734237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17322531772873926186489491 25983797659310889279734237)
            ·
              refine ⟨9743924122241583479900339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25983797659310889279734237 9743924122241583479900339)
              ·
                refine ⟨14615886183362375219850509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9743924122241583479900339 14615886183362375219850509)
                ·
                  refine ⟨5480957318760890707443941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14615886183362375219850509 5480957318760890707443941)
                  ·
                    refine ⟨1027679497267667007645739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5480957318760890707443941 1027679497267667007645739)
                    ·
                      rfl

theorem cell22_3002098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_3002098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002098 prefixEnd_3002098 := by exact prefixLift 3002098
  have htrace : WordTrace (prefixWord ++ tailWord_3002098) baseStart_3002098 baseEnd_3002098 := by
    simpa [prefixWord, tailWord_3002098, baseEnd_3002098] using wordTrace_append hprefix tailTrace_3002098
  have hstable : (prefixWord ++ tailWord_3002098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002098).length < 2 ^ (prefixWord ++ tailWord_3002098).sum := by decide
  have hdescent : baseEnd_3002098 < baseStart_3002098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002111 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 3, 5]
def baseStart_3002111 : Nat := 118140960795 + 3002111 * 2 ^ 59
def prefixEnd_3002111 : Nat := 4983230072969 + 3 ^ 40 * 3002111 * 2
def baseEnd_3002111 : Nat := 1027683947433339307070699

theorem tailTrace_3002111 : CollatzResearch.WordTrace tailWord_3002111 prefixEnd_3002111 1027683947433339307070699 := by
  unfold tailWord_3002111
  simp only [CollatzResearch.WordTrace]
  refine ⟨109495983626872041584206187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72997322417914694389470791 109495983626872041584206187)
  ·
    refine ⟨164243975440308062376309281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109495983626872041584206187 164243975440308062376309281)
    ·
      refine ⟨123182981580231046782231961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164243975440308062376309281 123182981580231046782231961)
      ·
        refine ⟨92387236185173285086673971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123182981580231046782231961 92387236185173285086673971)
        ·
          refine ⟨138580854277759927630010957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92387236185173285086673971 138580854277759927630010957)
          ·
            refine ⟨51967820354159972861254109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138580854277759927630010957 51967820354159972861254109)
            ·
              refine ⟨19487932632809989822970291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51967820354159972861254109 19487932632809989822970291)
              ·
                refine ⟨29231898949214984734455437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19487932632809989822970291 29231898949214984734455437)
                ·
                  refine ⟨10961962105955619275420789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29231898949214984734455437 10961962105955619275420789)
                  ·
                    refine ⟨1027683947433339307070699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10961962105955619275420789 1027683947433339307070699)
                    ·
                      rfl

theorem cell22_3002111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 5].length) (baseStart_3002111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002111 prefixEnd_3002111 := by exact prefixLift 3002111
  have htrace : WordTrace (prefixWord ++ tailWord_3002111) baseStart_3002111 baseEnd_3002111 := by
    simpa [prefixWord, tailWord_3002111, baseEnd_3002111] using wordTrace_append hprefix tailTrace_3002111
  have hstable : (prefixWord ++ tailWord_3002111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002111).length < 2 ^ (prefixWord ++ tailWord_3002111).sum := by decide
  have hdescent : baseEnd_3002111 < baseStart_3002111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002145 : List Nat := [1, 2, 3, 2, 1, 3, 2, 3, 2, 3]
def baseStart_3002145 : Nat := 118140960795 + 3002145 * 2 ^ 59
def prefixEnd_3002145 : Nat := 4983230072969 + 3 ^ 40 * 3002145 * 2
def baseEnd_3002145 : Nat := 1027695586328174551720595

theorem tailTrace_3002145 : CollatzResearch.WordTrace tailWord_3002145 prefixEnd_3002145 1027695586328174551720595 := by
  unfold tailWord_3002145
  simp only [CollatzResearch.WordTrace]
  refine ⟨109497223708748865390943889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72998149139165910260629259 109497223708748865390943889)
  ·
    refine ⟨82122917781561649043207917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109497223708748865390943889 82122917781561649043207917)
    ·
      refine ⟨30796094168085618391202969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82122917781561649043207917 30796094168085618391202969)
      ·
        refine ⟨23097070626064213793402227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30796094168085618391202969 23097070626064213793402227)
        ·
          refine ⟨34645605939096320690103341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23097070626064213793402227 34645605939096320690103341)
          ·
            refine ⟨12992102227161120258788753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34645605939096320690103341 12992102227161120258788753)
            ·
              refine ⟨9744076670370840194091565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12992102227161120258788753 9744076670370840194091565)
              ·
                refine ⟨3654028751389065072784337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9744076670370840194091565 3654028751389065072784337)
                ·
                  refine ⟨2740521563541798804588253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3654028751389065072784337 2740521563541798804588253)
                  ·
                    refine ⟨1027695586328174551720595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2740521563541798804588253 1027695586328174551720595)
                    ·
                      rfl

theorem cell22_3002145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_3002145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002145 prefixEnd_3002145 := by exact prefixLift 3002145
  have htrace : WordTrace (prefixWord ++ tailWord_3002145) baseStart_3002145 baseEnd_3002145 := by
    simpa [prefixWord, tailWord_3002145, baseEnd_3002145] using wordTrace_append hprefix tailTrace_3002145
  have hstable : (prefixWord ++ tailWord_3002145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002145).length < 2 ^ (prefixWord ++ tailWord_3002145).sum := by decide
  have hdescent : baseEnd_3002145 < baseStart_3002145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002241 : List Nat := [1, 2, 4, 4, 2, 1, 1, 1, 3, 3]
def baseStart_3002241 : Nat := 118140960795 + 3002241 * 2 ^ 59
def prefixEnd_3002241 : Nat := 4983230072969 + 3 ^ 40 * 3002241 * 2
def baseEnd_3002241 : Nat := 1027728449090062301320301

theorem tailTrace_3002241 : CollatzResearch.WordTrace tailWord_3002241 prefixEnd_3002241 1027728449090062301320301 := by
  unfold tailWord_3002241
  simp only [CollatzResearch.WordTrace]
  refine ⟨109500725116401073786438577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73000483410934049190959051 109500725116401073786438577)
  ·
    refine ⟨82125543837300805339828933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109500725116401073786438577 82125543837300805339828933)
    ·
      refine ⟨15398539469493901001217925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82125543837300805339828933 15398539469493901001217925)
      ·
        refine ⟨2887226150530106437728361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15398539469493901001217925 2887226150530106437728361)
        ·
          refine ⟨2165419612897579828296271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2887226150530106437728361 2165419612897579828296271)
          ·
            refine ⟨3248129419346369742444407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165419612897579828296271 3248129419346369742444407)
            ·
              refine ⟨4872194129019554613666611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248129419346369742444407 4872194129019554613666611)
              ·
                refine ⟨7308291193529331920499917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872194129019554613666611 7308291193529331920499917)
                ·
                  refine ⟨2740609197573499470187469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7308291193529331920499917 2740609197573499470187469)
                  ·
                    refine ⟨1027728449090062301320301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2740609197573499470187469 1027728449090062301320301)
                    ·
                      rfl

theorem cell22_3002241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_3002241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002241 prefixEnd_3002241 := by exact prefixLift 3002241
  have htrace : WordTrace (prefixWord ++ tailWord_3002241) baseStart_3002241 baseEnd_3002241 := by
    simpa [prefixWord, tailWord_3002241, baseEnd_3002241] using wordTrace_append hprefix tailTrace_3002241
  have hstable : (prefixWord ++ tailWord_3002241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002241).length < 2 ^ (prefixWord ++ tailWord_3002241).sum := by decide
  have hdescent : baseEnd_3002241 < baseStart_3002241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002293 : List Nat := [1, 3, 3, 2, 1, 12]
def baseStart_3002293 : Nat := 118140960795 + 3002293 * 2 ^ 59
def prefixEnd_3002293 : Nat := 4983230072969 + 3 ^ 40 * 3002293 * 2
def baseEnd_3002293 : Nat := 12688225305589524679261

theorem tailTrace_3002293 : CollatzResearch.WordTrace tailWord_3002293 prefixEnd_3002293 12688225305589524679261 := by
  unfold tailWord_3002293
  simp only [CollatzResearch.WordTrace]
  refine ⟨109502621712212686667331533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73001747808141791111554355 109502621712212686667331533)
  ·
    refine ⟨41063483142079757500249325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109502621712212686667331533 41063483142079757500249325)
    ·
      refine ⟨15398806178279909062593497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41063483142079757500249325 15398806178279909062593497)
      ·
        refine ⟨11549104633709931796945123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15398806178279909062593497 11549104633709931796945123)
        ·
          refine ⟨17323656950564897695417685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11549104633709931796945123 17323656950564897695417685)
          ·
            refine ⟨12688225305589524679261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 17323656950564897695417685 12688225305589524679261)
            ·
              rfl

theorem cell22_3002293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 12].length) (baseStart_3002293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002293 prefixEnd_3002293 := by exact prefixLift 3002293
  have htrace : WordTrace (prefixWord ++ tailWord_3002293) baseStart_3002293 baseEnd_3002293 := by
    simpa [prefixWord, tailWord_3002293, baseEnd_3002293] using wordTrace_append hprefix tailTrace_3002293
  have hstable : (prefixWord ++ tailWord_3002293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002293).length < 2 ^ (prefixWord ++ tailWord_3002293).sum := by decide
  have hdescent : baseEnd_3002293 < baseStart_3002293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002297 : List Nat := [1, 2, 1, 4, 2, 1, 4, 2, 2, 3]
def baseStart_3002297 : Nat := 118140960795 + 3002297 * 2 ^ 59
def prefixEnd_3002297 : Nat := 4983230072969 + 3 ^ 40 * 3002297 * 2
def baseEnd_3002297 : Nat := 1027747619034496821920129

theorem tailTrace_3002297 : CollatzResearch.WordTrace tailWord_3002297 prefixEnd_3002297 1027747619034496821920129 := by
  unfold tailWord_3002297
  simp only [CollatzResearch.WordTrace]
  refine ⟨109502767604198195350477145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73001845069465463566984763 109502767604198195350477145)
  ·
    refine ⟨82127075703148646512857859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109502767604198195350477145 82127075703148646512857859)
    ·
      refine ⟨123190613554722969769286789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82127075703148646512857859 123190613554722969769286789)
      ·
        refine ⟨23098240041510556831741273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123190613554722969769286789 23098240041510556831741273)
        ·
          refine ⟨17323680031132917623805955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23098240041510556831741273 17323680031132917623805955)
          ·
            refine ⟨25985520046699376435708933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17323680031132917623805955 25985520046699376435708933)
            ·
              refine ⟨4872285008756133081695425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25985520046699376435708933 4872285008756133081695425)
              ·
                refine ⟨3654213756567099811271569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4872285008756133081695425 3654213756567099811271569)
                ·
                  refine ⟨2740660317425324858453677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3654213756567099811271569 2740660317425324858453677)
                  ·
                    refine ⟨1027747619034496821920129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2740660317425324858453677 1027747619034496821920129)
                    ·
                      rfl

theorem cell22_3002297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 2, 2, 3].length) (baseStart_3002297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002297 prefixEnd_3002297 := by exact prefixLift 3002297
  have htrace : WordTrace (prefixWord ++ tailWord_3002297) baseStart_3002297 baseEnd_3002297 := by
    simpa [prefixWord, tailWord_3002297, baseEnd_3002297] using wordTrace_append hprefix tailTrace_3002297
  have hstable : (prefixWord ++ tailWord_3002297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002297).length < 2 ^ (prefixWord ++ tailWord_3002297).sum := by decide
  have hdescent : baseEnd_3002297 < baseStart_3002297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002329 : List Nat := [1, 2, 1, 2, 7, 1, 1, 1, 2, 4]
def baseStart_3002329 : Nat := 118140960795 + 3002329 * 2 ^ 59
def prefixEnd_3002329 : Nat := 4983230072969 + 3 ^ 40 * 3002329 * 2
def baseEnd_3002329 : Nat := 1027758573288459405120031

theorem tailTrace_3002329 : CollatzResearch.WordTrace tailWord_3002329 prefixEnd_3002329 1027758573288459405120031 := by
  unfold tailWord_3002329
  simp only [CollatzResearch.WordTrace]
  refine ⟨109503934740082264815642041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73002623160054843210428027 109503934740082264815642041)
  ·
    refine ⟨82127951055061698611731531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109503934740082264815642041 82127951055061698611731531)
    ·
      refine ⟨123191926582592547917597297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82127951055061698611731531 123191926582592547917597297)
      ·
        refine ⟨92393944936944410938197973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123191926582592547917597297 92393944936944410938197973)
        ·
          refine ⟨2165483084459634631364015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 92393944936944410938197973 2165483084459634631364015)
          ·
            refine ⟨3248224626689451947046023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165483084459634631364015 3248224626689451947046023)
            ·
              refine ⟨4872336940034177920569035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248224626689451947046023 4872336940034177920569035)
              ·
                refine ⟨7308505410051266880853553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872336940034177920569035 7308505410051266880853553)
                ·
                  refine ⟨5481379057538450160640165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7308505410051266880853553 5481379057538450160640165)
                  ·
                    refine ⟨1027758573288459405120031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5481379057538450160640165 1027758573288459405120031)
                    ·
                      rfl

theorem cell22_3002329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 1, 2, 4].length) (baseStart_3002329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002329 prefixEnd_3002329 := by exact prefixLift 3002329
  have htrace : WordTrace (prefixWord ++ tailWord_3002329) baseStart_3002329 baseEnd_3002329 := by
    simpa [prefixWord, tailWord_3002329, baseEnd_3002329] using wordTrace_append hprefix tailTrace_3002329
  have hstable : (prefixWord ++ tailWord_3002329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002329).length < 2 ^ (prefixWord ++ tailWord_3002329).sum := by decide
  have hdescent : baseEnd_3002329 < baseStart_3002329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002368 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 2, 8]
def baseStart_3002368 : Nat := 118140960795 + 3002368 * 2 ^ 59
def prefixEnd_3002368 : Nat := 4983230072969 + 3 ^ 40 * 3002368 * 2
def baseEnd_3002368 : Nat := 1027771923785476303394911

theorem tailTrace_3002368 : CollatzResearch.WordTrace tailWord_3002368 prefixEnd_3002368 1027771923785476303394911 := by
  unfold tailWord_3002368
  simp only [CollatzResearch.WordTrace]
  refine ⟨54752678593470487238155879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73003571457960649650874505 54752678593470487238155879)
  ·
    refine ⟨82129017890205730857233819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54752678593470487238155879 82129017890205730857233819)
    ·
      refine ⟨123193526835308596285850729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82129017890205730857233819 123193526835308596285850729)
      ·
        refine ⟨92395145126481447214388047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123193526835308596285850729 92395145126481447214388047)
        ·
          refine ⟨138592717689722170821582071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92395145126481447214388047 138592717689722170821582071)
          ·
            refine ⟨207889076534583256232373107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138592717689722170821582071 207889076534583256232373107)
            ·
              refine ⟨311833614801874884348559661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207889076534583256232373107 311833614801874884348559661)
              ·
                refine ⟨116937605550703081630709873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 311833614801874884348559661 116937605550703081630709873)
                ·
                  refine ⟨87703204163027311223032405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 116937605550703081630709873 87703204163027311223032405)
                  ·
                    refine ⟨1027771923785476303394911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 87703204163027311223032405 1027771923785476303394911)
                    ·
                      rfl

theorem cell22_3002368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 2, 8].length) (baseStart_3002368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002368 prefixEnd_3002368 := by exact prefixLift 3002368
  have htrace : WordTrace (prefixWord ++ tailWord_3002368) baseStart_3002368 baseEnd_3002368 := by
    simpa [prefixWord, tailWord_3002368, baseEnd_3002368] using wordTrace_append hprefix tailTrace_3002368
  have hstable : (prefixWord ++ tailWord_3002368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002368).length < 2 ^ (prefixWord ++ tailWord_3002368).sum := by decide
  have hdescent : baseEnd_3002368 < baseStart_3002368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002402 : List Nat := [3, 3, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_3002402 : Nat := 118140960795 + 3002402 * 2 ^ 59
def prefixEnd_3002402 : Nat := 4983230072969 + 3 ^ 40 * 3002402 * 2
def baseEnd_3002402 : Nat := 1027783562680311548044807

theorem tailTrace_3002402 : CollatzResearch.WordTrace tailWord_3002402 prefixEnd_3002402 1027783562680311548044807 := by
  unfold tailWord_3002402
  simp only [CollatzResearch.WordTrace]
  refine ⟨27376649317204449570762365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73004398179211865522032973 27376649317204449570762365)
  ·
    refine ⟨10266243493951668589035887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27376649317204449570762365 10266243493951668589035887)
    ·
      refine ⟨15399365240927502883553831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10266243493951668589035887 15399365240927502883553831)
      ·
        refine ⟨23099047861391254325330747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15399365240927502883553831 23099047861391254325330747)
        ·
          refine ⟨34648571792086881487996121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23099047861391254325330747 34648571792086881487996121)
          ·
            refine ⟨25986428844065161115997091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34648571792086881487996121 25986428844065161115997091)
            ·
              refine ⟨38979643266097741673995637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25986428844065161115997091 38979643266097741673995637)
              ·
                refine ⟨3654341556196663281937091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38979643266097741673995637 3654341556196663281937091)
                ·
                  refine ⟨5481512334294994922905637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654341556196663281937091 5481512334294994922905637)
                  ·
                    refine ⟨1027783562680311548044807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5481512334294994922905637 1027783562680311548044807)
                    ·
                      rfl

theorem cell22_3002402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_3002402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002402 prefixEnd_3002402 := by exact prefixLift 3002402
  have htrace : WordTrace (prefixWord ++ tailWord_3002402) baseStart_3002402 baseEnd_3002402 := by
    simpa [prefixWord, tailWord_3002402, baseEnd_3002402] using wordTrace_append hprefix tailTrace_3002402
  have hstable : (prefixWord ++ tailWord_3002402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002402).length < 2 ^ (prefixWord ++ tailWord_3002402).sum := by decide
  have hdescent : baseEnd_3002402 < baseStart_3002402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002417 : List Nat := [1, 2, 2, 3, 1, 5, 1, 1, 6]
def baseStart_3002417 : Nat := 118140960795 + 3002417 * 2 ^ 59
def prefixEnd_3002417 : Nat := 4983230072969 + 3 ^ 40 * 3002417 * 2
def baseEnd_3002417 : Nat := 342596232495618836306587

theorem tailTrace_3002417 : CollatzResearch.WordTrace tailWord_3002417 prefixEnd_3002417 342596232495618836306587 := by
  unfold tailWord_3002417
  simp only [CollatzResearch.WordTrace]
  refine ⟨109507144363763455844845505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73004762909175637229897003 109507144363763455844845505)
  ·
    refine ⟨82130358272822591883634129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109507144363763455844845505 82130358272822591883634129)
    ·
      refine ⟨61597768704616943912725597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82130358272822591883634129 61597768704616943912725597)
      ·
        refine ⟨23099163264231353967272099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61597768704616943912725597 23099163264231353967272099)
        ·
          refine ⟨34648744896347030950908149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23099163264231353967272099 34648744896347030950908149)
          ·
            refine ⟨3248319834032534151647639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34648744896347030950908149 3248319834032534151647639)
            ·
              refine ⟨4872479751048801227471459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248319834032534151647639 4872479751048801227471459)
              ·
                refine ⟨7308719626573201841207189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872479751048801227471459 7308719626573201841207189)
                ·
                  refine ⟨342596232495618836306587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7308719626573201841207189 342596232495618836306587)
                  ·
                    rfl

theorem cell22_3002417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 6].length) (baseStart_3002417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002417 prefixEnd_3002417 := by exact prefixLift 3002417
  have htrace : WordTrace (prefixWord ++ tailWord_3002417) baseStart_3002417 baseEnd_3002417 := by
    simpa [prefixWord, tailWord_3002417, baseEnd_3002417] using wordTrace_append hprefix tailTrace_3002417
  have hstable : (prefixWord ++ tailWord_3002417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002417).length < 2 ^ (prefixWord ++ tailWord_3002417).sum := by decide
  have hdescent : baseEnd_3002417 < baseStart_3002417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002505 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_3002505 : Nat := 118140960795 + 3002505 * 2 ^ 59
def prefixEnd_3002505 : Nat := 4983230072969 + 3 ^ 40 * 3002505 * 2
def baseEnd_3002505 : Nat := 1027818821685253612719491

theorem tailTrace_3002505 : CollatzResearch.WordTrace tailWord_3002505 prefixEnd_3002505 1027818821685253612719491 := by
  unfold tailWord_3002505
  simp only [CollatzResearch.WordTrace]
  refine ⟨109510353987444646874048969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73006902658296431249365979 109510353987444646874048969)
  ·
    refine ⟨82132765490583485155536727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109510353987444646874048969 82132765490583485155536727)
    ·
      refine ⟨123199148235875227733305091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82132765490583485155536727 123199148235875227733305091)
      ·
        refine ⟨184798722353812841599957637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123199148235875227733305091 184798722353812841599957637)
        ·
          refine ⟨34649760441339907799992057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184798722353812841599957637 34649760441339907799992057)
          ·
            refine ⟨25987320331004930849994043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34649760441339907799992057 25987320331004930849994043)
            ·
              refine ⟨38980980496507396274991065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25987320331004930849994043 38980980496507396274991065)
              ·
                refine ⟨29235735372380547206243299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38980980496507396274991065 29235735372380547206243299)
                ·
                  refine ⟨43853603058570820809364949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29235735372380547206243299 43853603058570820809364949)
                  ·
                    refine ⟨1027818821685253612719491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43853603058570820809364949 1027818821685253612719491)
                    ·
                      rfl

theorem cell22_3002505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_3002505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002505 prefixEnd_3002505 := by exact prefixLift 3002505
  have htrace : WordTrace (prefixWord ++ tailWord_3002505) baseStart_3002505 baseEnd_3002505 := by
    simpa [prefixWord, tailWord_3002505, baseEnd_3002505] using wordTrace_append hprefix tailTrace_3002505
  have hstable : (prefixWord ++ tailWord_3002505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002505).length < 2 ^ (prefixWord ++ tailWord_3002505).sum := by decide
  have hdescent : baseEnd_3002505 < baseStart_3002505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002541 : List Nat := [1, 5, 2, 1, 2, 2, 3, 1, 5]
def baseStart_3002541 : Nat := 118140960795 + 3002541 * 2 ^ 59
def prefixEnd_3002541 : Nat := 4983230072969 + 3 ^ 40 * 3002541 * 2
def baseEnd_3002541 : Nat := 342610381740320506273127

theorem tailTrace_3002541 : CollatzResearch.WordTrace tailWord_3002541 prefixEnd_3002541 342610381740320506273127 := by
  unfold tailWord_3002541
  simp only [CollatzResearch.WordTrace]
  refine ⟨109511667015314225022359477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73007778010209483348239651 109511667015314225022359477)
  ·
    refine ⟨10266718782685708595846201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109511667015314225022359477 10266718782685708595846201)
    ·
      refine ⟨7700039087014281446884651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10266718782685708595846201 7700039087014281446884651)
      ·
        refine ⟨11550058630521422170326977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7700039087014281446884651 11550058630521422170326977)
        ·
          refine ⟨8662543972891066627745233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11550058630521422170326977 8662543972891066627745233)
          ·
            refine ⟨6496907979668299970808925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8662543972891066627745233 6496907979668299970808925)
            ·
              refine ⟨2436340492375612489053347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6496907979668299970808925 2436340492375612489053347)
              ·
                refine ⟨3654510738563418733580021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2436340492375612489053347 3654510738563418733580021)
                ·
                  refine ⟨342610381740320506273127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3654510738563418733580021 342610381740320506273127)
                  ·
                    rfl

theorem cell22_3002541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_3002541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002541 prefixEnd_3002541 := by exact prefixLift 3002541
  have htrace : WordTrace (prefixWord ++ tailWord_3002541) baseStart_3002541 baseEnd_3002541 := by
    simpa [prefixWord, tailWord_3002541, baseEnd_3002541] using wordTrace_append hprefix tailTrace_3002541
  have hstable : (prefixWord ++ tailWord_3002541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002541).length < 2 ^ (prefixWord ++ tailWord_3002541).sum := by decide
  have hdescent : baseEnd_3002541 < baseStart_3002541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002562 : List Nat := [3, 5, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_3002562 : Nat := 118140960795 + 3002562 * 2 ^ 59
def prefixEnd_3002562 : Nat := 4983230072969 + 3 ^ 40 * 3002562 * 2
def baseEnd_3002562 : Nat := 1027838333950124464044317

theorem tailTrace_3002562 : CollatzResearch.WordTrace tailWord_3002562 prefixEnd_3002562 1027838333950124464044317 := by
  unfold tailWord_3002562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27378108237059536402218485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73008288632158763739249293 27378108237059536402218485)
  ·
    refine ⟨2566697647224331537707983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 27378108237059536402218485 2566697647224331537707983)
    ·
      refine ⟨3850046470836497306561975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2566697647224331537707983 3850046470836497306561975)
      ·
        refine ⟨5775069706254745959842963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3850046470836497306561975 5775069706254745959842963)
        ·
          refine ⟨8662604559382118939764445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5775069706254745959842963 8662604559382118939764445)
          ·
            refine ⟨3248476709768294602411667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8662604559382118939764445 3248476709768294602411667)
            ·
              refine ⟨4872715064652441903617501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248476709768294602411667 4872715064652441903617501)
              ·
                refine ⟨1827268149244665713856563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4872715064652441903617501 1827268149244665713856563)
                ·
                  refine ⟨2740902223866998570784845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827268149244665713856563 2740902223866998570784845)
                  ·
                    refine ⟨1027838333950124464044317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2740902223866998570784845 1027838333950124464044317)
                    ·
                      rfl

theorem cell22_3002562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_3002562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002562 prefixEnd_3002562 := by exact prefixLift 3002562
  have htrace : WordTrace (prefixWord ++ tailWord_3002562) baseStart_3002562 baseEnd_3002562 := by
    simpa [prefixWord, tailWord_3002562, baseEnd_3002562] using wordTrace_append hprefix tailTrace_3002562
  have hstable : (prefixWord ++ tailWord_3002562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002562).length < 2 ^ (prefixWord ++ tailWord_3002562).sum := by decide
  have hdescent : baseEnd_3002562 < baseStart_3002562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002584 : List Nat := [2, 1, 2, 2, 4, 1, 2, 1, 4, 3]
def baseStart_3002584 : Nat := 118140960795 + 3002584 * 2 ^ 59
def prefixEnd_3002584 : Nat := 4983230072969 + 3 ^ 40 * 3002584 * 2
def baseEnd_3002584 : Nat := 1027845864999723739994249

theorem tailTrace_3002584 : CollatzResearch.WordTrace tailWord_3002584 prefixEnd_3002584 1027845864999723739994249 := by
  unfold tailWord_3002584
  simp only [CollatzResearch.WordTrace]
  refine ⟨54756617677079221683087403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73008823569438962244116537 54756617677079221683087403)
  ·
    refine ⟨82134926515618832524631105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54756617677079221683087403 82134926515618832524631105)
    ·
      refine ⟨61601194886714124393473329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82134926515618832524631105 61601194886714124393473329)
      ·
        refine ⟨46200896165035593295104997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61601194886714124393473329 46200896165035593295104997)
        ·
          refine ⟨8662668030944173742832187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46200896165035593295104997 8662668030944173742832187)
          ·
            refine ⟨12994002046416260614248281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8662668030944173742832187 12994002046416260614248281)
            ·
              refine ⟨9745501534812195460686211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12994002046416260614248281 9745501534812195460686211)
              ·
                refine ⟨14618252302218293191029317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9745501534812195460686211 14618252302218293191029317)
                ·
                  refine ⟨2740922306665929973317997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14618252302218293191029317 2740922306665929973317997)
                  ·
                    refine ⟨1027845864999723739994249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2740922306665929973317997 1027845864999723739994249)
                    ·
                      rfl

theorem cell22_3002584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 1, 4, 3].length) (baseStart_3002584 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002584 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002584 prefixEnd_3002584 := by exact prefixLift 3002584
  have htrace : WordTrace (prefixWord ++ tailWord_3002584) baseStart_3002584 baseEnd_3002584 := by
    simpa [prefixWord, tailWord_3002584, baseEnd_3002584] using wordTrace_append hprefix tailTrace_3002584
  have hstable : (prefixWord ++ tailWord_3002584).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002584).length < 2 ^ (prefixWord ++ tailWord_3002584).sum := by decide
  have hdescent : baseEnd_3002584 < baseStart_3002584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002597 : List Nat := [1, 3, 1, 4, 2, 1, 1, 9]
def baseStart_3002597 : Nat := 118140960795 + 3002597 * 2 ^ 59
def prefixEnd_3002597 : Nat := 4983230072969 + 3 ^ 40 * 3002597 * 2
def baseEnd_3002597 : Nat := 114205590573932893268801

theorem tailTrace_3002597 : CollatzResearch.WordTrace tailWord_3002597 prefixEnd_3002597 114205590573932893268801 := by
  unfold tailWord_3002597
  simp only [CollatzResearch.WordTrace]
  refine ⟨109513709503111346586398045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73009139668740897724265363 109513709503111346586398045)
  ·
    refine ⟨41067641063666754969899267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109513709503111346586398045 41067641063666754969899267)
    ·
      refine ⟨61601461595500132454848901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41067641063666754969899267 61601461595500132454848901)
      ·
        refine ⟨11550274049156274835284169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61601461595500132454848901 11550274049156274835284169)
        ·
          refine ⟨8662705536867206126463127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11550274049156274835284169 8662705536867206126463127)
          ·
            refine ⟨12994058305300809189694691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8662705536867206126463127 12994058305300809189694691)
            ·
              refine ⟨19491087457951213784542037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12994058305300809189694691 19491087457951213784542037)
              ·
                refine ⟨114205590573932893268801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19491087457951213784542037 114205590573932893268801)
                ·
                  rfl

theorem cell22_3002597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 9].length) (baseStart_3002597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002597 prefixEnd_3002597 := by exact prefixLift 3002597
  have htrace : WordTrace (prefixWord ++ tailWord_3002597) baseStart_3002597 baseEnd_3002597 := by
    simpa [prefixWord, tailWord_3002597, baseEnd_3002597] using wordTrace_append hprefix tailTrace_3002597
  have hstable : (prefixWord ++ tailWord_3002597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002597).length < 2 ^ (prefixWord ++ tailWord_3002597).sum := by decide
  have hdescent : baseEnd_3002597 < baseStart_3002597 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002657 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 1, 7]
def baseStart_3002657 : Nat := 118140960795 + 3002657 * 2 ^ 59
def prefixEnd_3002657 : Nat := 4983230072969 + 3 ^ 40 * 3002657 * 2
def baseEnd_3002657 : Nat := 1027870854391575882919025

theorem tailTrace_3002657 : CollatzResearch.WordTrace tailWord_3002657 prefixEnd_3002657 1027870854391575882919025 := by
  unfold tailWord_3002657
  simp only [CollatzResearch.WordTrace]
  refine ⟨109515897882893976833582225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73010598588595984555721483 109515897882893976833582225)
  ·
    refine ⟨82136923412170482625186669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109515897882893976833582225 82136923412170482625186669)
    ·
      refine ⟨30801346279563930984445001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82136923412170482625186669 30801346279563930984445001)
      ·
        refine ⟨23101009709672948238333751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30801346279563930984445001 23101009709672948238333751)
        ·
          refine ⟨34651514564509422357500627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23101009709672948238333751 34651514564509422357500627)
          ·
            refine ⟨51977271846764133536250941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34651514564509422357500627 51977271846764133536250941)
            ·
              refine ⟨19491476942536550076094103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51977271846764133536250941 19491476942536550076094103)
              ·
                refine ⟨29237215413804825114141155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19491476942536550076094103 29237215413804825114141155)
                ·
                  refine ⟨43855823120707237671211733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29237215413804825114141155 43855823120707237671211733)
                  ·
                    refine ⟨1027870854391575882919025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43855823120707237671211733 1027870854391575882919025)
                    ·
                      rfl

theorem cell22_3002657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_3002657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002657 prefixEnd_3002657 := by exact prefixLift 3002657
  have htrace : WordTrace (prefixWord ++ tailWord_3002657) baseStart_3002657 baseEnd_3002657 := by
    simpa [prefixWord, tailWord_3002657, baseEnd_3002657] using wordTrace_append hprefix tailTrace_3002657
  have hstable : (prefixWord ++ tailWord_3002657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002657).length < 2 ^ (prefixWord ++ tailWord_3002657).sum := by decide
  have hdescent : baseEnd_3002657 < baseStart_3002657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002687 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 8]
def baseStart_3002687 : Nat := 118140960795 + 3002687 * 2 ^ 59
def prefixEnd_3002687 : Nat := 4983230072969 + 3 ^ 40 * 3002687 * 2
def baseEnd_3002687 : Nat := 342627041334888601556311

theorem tailTrace_3002687 : CollatzResearch.WordTrace tailWord_3002687 prefixEnd_3002687 342627041334888601556311 := by
  unfold tailWord_3002687
  simp only [CollatzResearch.WordTrace]
  refine ⟨109516992072785291957174315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73011328048523527971449543 109516992072785291957174315)
  ·
    refine ⟨164275488109177937935761473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109516992072785291957174315 164275488109177937935761473)
    ·
      refine ⟨123206616081883453451821105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164275488109177937935761473 123206616081883453451821105)
      ·
        refine ⟨92404962061412590088865829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123206616081883453451821105 92404962061412590088865829)
        ·
          refine ⟨17325930386514860641662343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92404962061412590088865829 17325930386514860641662343)
          ·
            refine ⟨25988895579772290962493515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17325930386514860641662343 25988895579772290962493515)
            ·
              refine ⟨38983343369658436443740273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25988895579772290962493515 38983343369658436443740273)
              ·
                refine ⟨29237507527243827332805205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38983343369658436443740273 29237507527243827332805205)
                ·
                  refine ⟨342627041334888601556311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29237507527243827332805205 342627041334888601556311)
                  ·
                    rfl

theorem cell22_3002687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 8].length) (baseStart_3002687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002687 prefixEnd_3002687 := by exact prefixLift 3002687
  have htrace : WordTrace (prefixWord ++ tailWord_3002687) baseStart_3002687 baseEnd_3002687 := by
    simpa [prefixWord, tailWord_3002687, baseEnd_3002687] using wordTrace_append hprefix tailTrace_3002687
  have hstable : (prefixWord ++ tailWord_3002687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002687).length < 2 ^ (prefixWord ++ tailWord_3002687).sum := by decide
  have hdescent : baseEnd_3002687 < baseStart_3002687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002704 : List Nat := [2, 1, 1, 1, 1, 7, 2, 1, 6]
def baseStart_3002704 : Nat := 118140960795 + 3002704 * 2 ^ 59
def prefixEnd_3002704 : Nat := 4983230072969 + 3 ^ 40 * 3002704 * 2
def baseEnd_3002704 : Nat := 342628981150694475664627

theorem tailTrace_3002704 : CollatzResearch.WordTrace tailWord_3002704 prefixEnd_3002704 342628981150694475664627 := by
  unfold tailWord_3002704
  simp only [CollatzResearch.WordTrace]
  refine ⟨54758806056861851930271583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73011741409149135907028777 54758806056861851930271583)
  ·
    refine ⟨82138209085292777895407375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54758806056861851930271583 82138209085292777895407375)
    ·
      refine ⟨123207313627939166843111063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82138209085292777895407375 123207313627939166843111063)
      ·
        refine ⟨184810970441908750264666595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123207313627939166843111063 184810970441908750264666595)
        ·
          refine ⟨277216455662863125396999893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184810970441908750264666595 277216455662863125396999893)
          ·
            refine ⟨6497260679598354501492185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 277216455662863125396999893 6497260679598354501492185)
            ·
              refine ⟨4872945509698765876119139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6497260679598354501492185 4872945509698765876119139)
              ·
                refine ⟨7309418264548148814178709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872945509698765876119139 7309418264548148814178709)
                ·
                  refine ⟨342628981150694475664627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7309418264548148814178709 342628981150694475664627)
                  ·
                    rfl

theorem cell22_3002704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 6].length) (baseStart_3002704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002704 prefixEnd_3002704 := by exact prefixLift 3002704
  have htrace : WordTrace (prefixWord ++ tailWord_3002704) baseStart_3002704 baseEnd_3002704 := by
    simpa [prefixWord, tailWord_3002704, baseEnd_3002704] using wordTrace_append hprefix tailTrace_3002704
  have hstable : (prefixWord ++ tailWord_3002704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002704).length < 2 ^ (prefixWord ++ tailWord_3002704).sum := by decide
  have hdescent : baseEnd_3002704 < baseStart_3002704 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002719 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 1, 5]
def baseStart_3002719 : Nat := 118140960795 + 3002719 * 2 ^ 59
def prefixEnd_3002719 : Nat := 4983230072969 + 3 ^ 40 * 3002719 * 2
def baseEnd_3002719 : Nat := 1027892078258628387868835

theorem tailTrace_3002719 : CollatzResearch.WordTrace tailWord_3002719 prefixEnd_3002719 1027892078258628387868835 := by
  unfold tailWord_3002719
  simp only [CollatzResearch.WordTrace]
  refine ⟨109518159208669361422339211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73012106139112907614892807 109518159208669361422339211)
  ·
    refine ⟨164277238813004042133508817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109518159208669361422339211 164277238813004042133508817)
    ·
      refine ⟨123207929109753031600131613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164277238813004042133508817 123207929109753031600131613)
      ·
        refine ⟨46202973416157386850049355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123207929109753031600131613 46202973416157386850049355)
        ·
          refine ⟨69304460124236080275074033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46202973416157386850049355 69304460124236080275074033)
          ·
            refine ⟨51978345093177060206305525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69304460124236080275074033 51978345093177060206305525)
            ·
              refine ⟨4872969852485349394341143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51978345093177060206305525 4872969852485349394341143)
              ·
                refine ⟨7309454778728024091511715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4872969852485349394341143 7309454778728024091511715)
                ·
                  refine ⟨10964182168092036137267573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7309454778728024091511715 10964182168092036137267573)
                  ·
                    refine ⟨1027892078258628387868835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10964182168092036137267573 1027892078258628387868835)
                    ·
                      rfl

theorem cell22_3002719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_3002719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002719 prefixEnd_3002719 := by exact prefixLift 3002719
  have htrace : WordTrace (prefixWord ++ tailWord_3002719) baseStart_3002719 baseEnd_3002719 := by
    simpa [prefixWord, tailWord_3002719, baseEnd_3002719] using wordTrace_append hprefix tailTrace_3002719
  have hstable : (prefixWord ++ tailWord_3002719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002719).length < 2 ^ (prefixWord ++ tailWord_3002719).sum := by decide
  have hdescent : baseEnd_3002719 < baseStart_3002719 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002738 : List Nat := [3, 2, 1, 2, 1, 5, 1, 3, 4]
def baseStart_3002738 : Nat := 118140960795 + 3002738 * 2 ^ 59
def prefixEnd_3002738 : Nat := 4983230072969 + 3 ^ 40 * 3002738 * 2
def baseEnd_3002738 : Nat := 342632860782306223881259

theorem tailTrace_3002738 : CollatzResearch.WordTrace tailWord_3002738 prefixEnd_3002738 342632860782306223881259 := by
  unfold tailWord_3002738
  simp only [CollatzResearch.WordTrace]
  refine ⟨27379713048900131916820217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73012568130400351778187245 27379713048900131916820217)
  ·
    refine ⟨20534784786675098937615163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27379713048900131916820217 20534784786675098937615163)
    ·
      refine ⟨30802177180012648406422745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20534784786675098937615163 30802177180012648406422745)
      ·
        refine ⟨23101632885009486304817059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30802177180012648406422745 23101632885009486304817059)
        ·
          refine ⟨34652449327514229457225589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23101632885009486304817059 34652449327514229457225589)
          ·
            refine ⟨3248667124454459011614899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34652449327514229457225589 3248667124454459011614899)
            ·
              refine ⟨4873000686681688517422349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248667124454459011614899 4873000686681688517422349)
              ·
                refine ⟨1827375257505633194033381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4873000686681688517422349 1827375257505633194033381)
                ·
                  refine ⟨342632860782306223881259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1827375257505633194033381 342632860782306223881259)
                  ·
                    rfl

theorem cell22_3002738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_3002738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002738 prefixEnd_3002738 := by exact prefixLift 3002738
  have htrace : WordTrace (prefixWord ++ tailWord_3002738) baseStart_3002738 baseEnd_3002738 := by
    simpa [prefixWord, tailWord_3002738, baseEnd_3002738] using wordTrace_append hprefix tailTrace_3002738
  have hstable : (prefixWord ++ tailWord_3002738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002738).length < 2 ^ (prefixWord ++ tailWord_3002738).sum := by decide
  have hdescent : baseEnd_3002738 < baseStart_3002738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002749 : List Nat := [1, 4, 1, 1, 2, 5, 8]
def baseStart_3002749 : Nat := 118140960795 + 3002749 * 2 ^ 59
def prefixEnd_3002749 : Nat := 4983230072969 + 3 ^ 40 * 3002749 * 2
def baseEnd_3002749 : Nat := 38070457328582159615509

theorem tailTrace_3002749 : CollatzResearch.WordTrace tailWord_3002749 prefixEnd_3002749 38070457328582159615509 := by
  unfold tailWord_3002749
  simp only [CollatzResearch.WordTrace]
  refine ⟨109519253398560676545931301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73012835599040451030620867 109519253398560676545931301)
  ·
    refine ⟨20534860012230126852362119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109519253398560676545931301 20534860012230126852362119)
    ·
      refine ⟨30802290018345190278543179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20534860012230126852362119 30802290018345190278543179)
      ·
        refine ⟨46203435027517785417814769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30802290018345190278543179 46203435027517785417814769)
        ·
          refine ⟨34652576270638339063361077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46203435027517785417814769 34652576270638339063361077)
          ·
            refine ⟨3248679025372344287190101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34652576270638339063361077 3248679025372344287190101)
            ·
              refine ⟨38070457328582159615509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3248679025372344287190101 38070457328582159615509)
              ·
                rfl

theorem cell22_3002749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 8].length) (baseStart_3002749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002749 prefixEnd_3002749 := by exact prefixLift 3002749
  have htrace : WordTrace (prefixWord ++ tailWord_3002749) baseStart_3002749 baseEnd_3002749 := by
    simpa [prefixWord, tailWord_3002749, baseEnd_3002749] using wordTrace_append hprefix tailTrace_3002749
  have hstable : (prefixWord ++ tailWord_3002749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002749).length < 2 ^ (prefixWord ++ tailWord_3002749).sum := by decide
  have hdescent : baseEnd_3002749 < baseStart_3002749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002766 : List Nat := [4, 1, 1, 4, 1, 2, 2, 7]
def baseStart_3002766 : Nat := 118140960795 + 3002766 * 2 ^ 59
def prefixEnd_3002766 : Nat := 4983230072969 + 3 ^ 40 * 3002766 * 2
def baseEnd_3002766 : Nat := 114212018591015103549299

theorem tailTrace_3002766 : CollatzResearch.WordTrace tailWord_3002766 prefixEnd_3002766 114212018591015103549299 := by
  unfold tailWord_3002766
  simp only [CollatzResearch.WordTrace]
  refine ⟨13689984179937386056162519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73013248959666058966200101 13689984179937386056162519)
  ·
    refine ⟨20534976269906079084243779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13689984179937386056162519 20534976269906079084243779)
    ·
      refine ⟨30802464404859118626365669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20534976269906079084243779 30802464404859118626365669)
      ·
        refine ⟨5775462075911084742443563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30802464404859118626365669 5775462075911084742443563)
        ·
          refine ⟨8663193113866627113665345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5775462075911084742443563 8663193113866627113665345)
          ·
            refine ⟨6497394835399970335249009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8663193113866627113665345 6497394835399970335249009)
            ·
              refine ⟨4873046126549977751436757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6497394835399970335249009 4873046126549977751436757)
              ·
                refine ⟨114212018591015103549299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4873046126549977751436757 114212018591015103549299)
                ·
                  rfl

theorem cell22_3002766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_3002766 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002766 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002766 prefixEnd_3002766 := by exact prefixLift 3002766
  have htrace : WordTrace (prefixWord ++ tailWord_3002766) baseStart_3002766 baseEnd_3002766 := by
    simpa [prefixWord, tailWord_3002766, baseEnd_3002766] using wordTrace_append hprefix tailTrace_3002766
  have hstable : (prefixWord ++ tailWord_3002766).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002766).length < 2 ^ (prefixWord ++ tailWord_3002766).sum := by decide
  have hdescent : baseEnd_3002766 < baseStart_3002766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002774 : List Nat := [5, 3, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_3002774 : Nat := 118140960795 + 3002774 * 2 ^ 59
def prefixEnd_3002774 : Nat := 4983230072969 + 3 ^ 40 * 3002774 * 2
def baseEnd_3002774 : Nat := 1027910905882626577743667

theorem tailTrace_3002774 : CollatzResearch.WordTrace tailWord_3002774 prefixEnd_3002774 1027910905882626577743667 := by
  unfold tailWord_3002774
  simp only [CollatzResearch.WordTrace]
  refine ⟨6845010326466881613474461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73013443482313403877060917 6845010326466881613474461)
  ·
    refine ⟨2566878872425080605052923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6845010326466881613474461 2566878872425080605052923)
    ·
      refine ⟨3850318308637620907579385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2566878872425080605052923 3850318308637620907579385)
      ·
        refine ⟨2887738731478215680684539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3850318308637620907579385 2887738731478215680684539)
        ·
          refine ⟨4331608097217323521026809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2887738731478215680684539 4331608097217323521026809)
          ·
            refine ⟨3248706072912992640770107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4331608097217323521026809 3248706072912992640770107)
            ·
              refine ⟨4873059109369488961155161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248706072912992640770107 4873059109369488961155161)
              ·
                refine ⟨3654794332027116720866371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873059109369488961155161 3654794332027116720866371)
                ·
                  refine ⟨5482191498040675081299557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654794332027116720866371 5482191498040675081299557)
                  ·
                    refine ⟨1027910905882626577743667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5482191498040675081299557 1027910905882626577743667)
                    ·
                      rfl

theorem cell22_3002774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_3002774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002774 prefixEnd_3002774 := by exact prefixLift 3002774
  have htrace : WordTrace (prefixWord ++ tailWord_3002774) baseStart_3002774 baseEnd_3002774 := by
    simpa [prefixWord, tailWord_3002774, baseEnd_3002774] using wordTrace_append hprefix tailTrace_3002774
  have hstable : (prefixWord ++ tailWord_3002774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002774).length < 2 ^ (prefixWord ++ tailWord_3002774).sum := by decide
  have hdescent : baseEnd_3002774 < baseStart_3002774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002817 : List Nat := [1, 2, 7, 1, 2, 1, 1, 7]
def baseStart_3002817 : Nat := 118140960795 + 3002817 * 2 ^ 59
def prefixEnd_3002817 : Nat := 4983230072969 + 3 ^ 40 * 3002817 * 2
def baseEnd_3002817 : Nat := 114213958406820977657615

theorem tailTrace_3002817 : CollatzResearch.WordTrace tailWord_3002817 prefixEnd_3002817 114213958406820977657615 := by
  unfold tailWord_3002817
  simp only [CollatzResearch.WordTrace]
  refine ⟨109521733562314324159406705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73014489041542882772937803 109521733562314324159406705)
  ·
    refine ⟨82141300171735743119555029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109521733562314324159406705 82141300171735743119555029)
    ·
      refine ⟨1925186722775056479364571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 82141300171735743119555029 1925186722775056479364571)
      ·
        refine ⟨2887780084162584719046857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925186722775056479364571 2887780084162584719046857)
        ·
          refine ⟨2165835063121938539285143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2887780084162584719046857 2165835063121938539285143)
          ·
            refine ⟨3248752594682907808927715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2165835063121938539285143 3248752594682907808927715)
            ·
              refine ⟨4873128892024361713391573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3248752594682907808927715 4873128892024361713391573)
              ·
                refine ⟨114213958406820977657615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4873128892024361713391573 114213958406820977657615)
                ·
                  rfl

theorem cell22_3002817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 7].length) (baseStart_3002817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002817 prefixEnd_3002817 := by exact prefixLift 3002817
  have htrace : WordTrace (prefixWord ++ tailWord_3002817) baseStart_3002817 baseEnd_3002817 := by
    simpa [prefixWord, tailWord_3002817, baseEnd_3002817] using wordTrace_append hprefix tailTrace_3002817
  have hstable : (prefixWord ++ tailWord_3002817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002817).length < 2 ^ (prefixWord ++ tailWord_3002817).sum := by decide
  have hdescent : baseEnd_3002817 < baseStart_3002817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002841 : List Nat := [1, 2, 1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_3002841 : Nat := 118140960795 + 3002841 * 2 ^ 59
def prefixEnd_3002841 : Nat := 4983230072969 + 3 ^ 40 * 3002841 * 2
def baseEnd_3002841 : Nat := 1027933841351860736318461

theorem tailTrace_3002841 : CollatzResearch.WordTrace tailWord_3002841 prefixEnd_3002841 1027933841351860736318461 := by
  unfold tailWord_3002841
  simp only [CollatzResearch.WordTrace]
  refine ⟨109522608914227376258280377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73015072609484917505520251 109522608914227376258280377)
  ·
    refine ⟨82141956685670532193710283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109522608914227376258280377 82141956685670532193710283)
    ·
      refine ⟨123212935028505798290565425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82141956685670532193710283 123212935028505798290565425)
      ·
        refine ⟨92409701271379348717924069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123212935028505798290565425 92409701271379348717924069)
        ·
          refine ⟨17326818988383627884610763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92409701271379348717924069 17326818988383627884610763)
          ·
            refine ⟨25990228482575441826916145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17326818988383627884610763 25990228482575441826916145)
            ·
              refine ⟨19492671361931581370187109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25990228482575441826916145 19492671361931581370187109)
              ·
                refine ⟨3654875880362171506910083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19492671361931581370187109 3654875880362171506910083)
                ·
                  refine ⟨5482313820543257260365125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654875880362171506910083 5482313820543257260365125)
                  ·
                    refine ⟨1027933841351860736318461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5482313820543257260365125 1027933841351860736318461)
                    ·
                      rfl

theorem cell22_3002841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_3002841 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002841 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002841 prefixEnd_3002841 := by exact prefixLift 3002841
  have htrace : WordTrace (prefixWord ++ tailWord_3002841) baseStart_3002841 baseEnd_3002841 := by
    simpa [prefixWord, tailWord_3002841, baseEnd_3002841] using wordTrace_append hprefix tailTrace_3002841
  have hstable : (prefixWord ++ tailWord_3002841).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002841).length < 2 ^ (prefixWord ++ tailWord_3002841).sum := by decide
  have hdescent : baseEnd_3002841 < baseStart_3002841 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002858 : List Nat := [3, 1, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_3002858 : Nat := 118140960795 + 3002858 * 2 ^ 59
def prefixEnd_3002858 : Nat := 4983230072969 + 3 ^ 40 * 3002858 * 2
def baseEnd_3002858 : Nat := 1027939660799278358643409

theorem tailTrace_3002858 : CollatzResearch.WordTrace tailWord_3002858 prefixEnd_3002858 1027939660799278358643409 := by
  unfold tailWord_3002858
  simp only [CollatzResearch.WordTrace]
  refine ⟨27380807238791447040412307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73015485970110525441099485 27380807238791447040412307)
  ·
    refine ⟨41071210858187170560618461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27380807238791447040412307 41071210858187170560618461)
    ·
      refine ⟨15401704071820188960231923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41071210858187170560618461 15401704071820188960231923)
      ·
        refine ⟨23102556107730283440347885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15401704071820188960231923 23102556107730283440347885)
        ·
          refine ⟨8663458540398856290130457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23102556107730283440347885 8663458540398856290130457)
          ·
            refine ⟨6497593905299142217597843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8663458540398856290130457 6497593905299142217597843)
            ·
              refine ⟨9746390857948713326396765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497593905299142217597843 9746390857948713326396765)
              ·
                refine ⟨3654896571730767497398787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9746390857948713326396765 3654896571730767497398787)
                ·
                  refine ⟨5482344857596151246098181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3654896571730767497398787 5482344857596151246098181)
                  ·
                    refine ⟨1027939660799278358643409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5482344857596151246098181 1027939660799278358643409)
                    ·
                      rfl

theorem cell22_3002858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_3002858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002858 prefixEnd_3002858 := by exact prefixLift 3002858
  have htrace : WordTrace (prefixWord ++ tailWord_3002858) baseStart_3002858 baseEnd_3002858 := by
    simpa [prefixWord, tailWord_3002858, baseEnd_3002858] using wordTrace_append hprefix tailTrace_3002858
  have hstable : (prefixWord ++ tailWord_3002858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002858).length < 2 ^ (prefixWord ++ tailWord_3002858).sum := by decide
  have hdescent : baseEnd_3002858 < baseStart_3002858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3002899 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 2, 7]
def baseStart_3002899 : Nat := 118140960795 + 3002899 * 2 ^ 59
def prefixEnd_3002899 : Nat := 4983230072969 + 3 ^ 40 * 3002899 * 2
def baseEnd_3002899 : Nat := 1027953695937167918368283

theorem tailTrace_3002899 : CollatzResearch.WordTrace tailWord_3002899 prefixEnd_3002899 1027953695937167918368283 := by
  unfold tailWord_3002899
  simp only [CollatzResearch.WordTrace]
  refine ⟨109524724348017252163891751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73016482898678168109261167 109524724348017252163891751)
  ·
    refine ⟨164287086522025878245837627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109524724348017252163891751 164287086522025878245837627)
    ·
      refine ⟨246430629783038817368756441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164287086522025878245837627 246430629783038817368756441)
      ·
        refine ⟨184822972337279113026567331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246430629783038817368756441 184822972337279113026567331)
        ·
          refine ⟨277234458505918669539850997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184822972337279113026567331 277234458505918669539850997)
          ·
            refine ⟨25990730484929875269361031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 277234458505918669539850997 25990730484929875269361031)
            ·
              refine ⟨38986095727394812904041547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25990730484929875269361031 38986095727394812904041547)
              ·
                refine ⟨58479143591092219356062321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38986095727394812904041547 58479143591092219356062321)
                ·
                  refine ⟨43859357693319164517046741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58479143591092219356062321 43859357693319164517046741)
                  ·
                    refine ⟨1027953695937167918368283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43859357693319164517046741 1027953695937167918368283)
                    ·
                      rfl

theorem cell22_3002899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 7].length) (baseStart_3002899 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3002899 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3002899 prefixEnd_3002899 := by exact prefixLift 3002899
  have htrace : WordTrace (prefixWord ++ tailWord_3002899) baseStart_3002899 baseEnd_3002899 := by
    simpa [prefixWord, tailWord_3002899, baseEnd_3002899] using wordTrace_append hprefix tailTrace_3002899
  have hstable : (prefixWord ++ tailWord_3002899).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3002899).length < 2 ^ (prefixWord ++ tailWord_3002899).sum := by decide
  have hdescent : baseEnd_3002899 < baseStart_3002899 := by decide
  rcases family_descends (prefixWord ++ tailWord_3002899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003040 : List Nat := [2, 1, 1, 4, 4, 1, 1, 1, 4, 3]
def baseStart_3003040 : Nat := 118140960795 + 3003040 * 2 ^ 59
def prefixEnd_3003040 : Nat := 4983230072969 + 3 ^ 40 * 3003040 * 2
def baseEnd_3003040 : Nat := 1028001963118690550592851

theorem tailTrace_3003040 : CollatzResearch.WordTrace tailWord_3003040 prefixEnd_3003040 1028001963118690550592851 := by
  unfold tailWord_3003040
  simp only [CollatzResearch.WordTrace]
  refine ⟨54764933520253216622387287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73019911360337622163183049 54764933520253216622387287)
  ·
    refine ⟨82147400280379824933580931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54764933520253216622387287 82147400280379824933580931)
    ·
      refine ⟨123221100420569737400371397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82147400280379824933580931 123221100420569737400371397)
      ·
        refine ⟨23103956328856825762569637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123221100420569737400371397 23103956328856825762569637)
        ·
          refine ⟨4331991811660654830481807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23103956328856825762569637 4331991811660654830481807)
          ·
            refine ⟨6497987717490982245722711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4331991811660654830481807 6497987717490982245722711)
            ·
              refine ⟨9746981576236473368584067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6497987717490982245722711 9746981576236473368584067)
              ·
                refine ⟨14620472364354710052876101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9746981576236473368584067 14620472364354710052876101)
                ·
                  refine ⟨2741338568316508134914269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14620472364354710052876101 2741338568316508134914269)
                  ·
                    refine ⟨1028001963118690550592851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2741338568316508134914269 1028001963118690550592851)
                    ·
                      rfl

theorem cell22_3003040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 1, 4, 3].length) (baseStart_3003040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003040 prefixEnd_3003040 := by exact prefixLift 3003040
  have htrace : WordTrace (prefixWord ++ tailWord_3003040) baseStart_3003040 baseEnd_3003040 := by
    simpa [prefixWord, tailWord_3003040, baseEnd_3003040] using wordTrace_append hprefix tailTrace_3003040
  have hstable : (prefixWord ++ tailWord_3003040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003040).length < 2 ^ (prefixWord ++ tailWord_3003040).sum := by decide
  have hdescent : baseEnd_3003040 < baseStart_3003040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003057 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 1, 5]
def baseStart_3003057 : Nat := 118140960795 + 3003057 * 2 ^ 59
def prefixEnd_3003057 : Nat := 4983230072969 + 3 ^ 40 * 3003057 * 2
def baseEnd_3003057 : Nat := 1028007782566108172917799

theorem tailTrace_3003057 : CollatzResearch.WordTrace tailWord_3003057 prefixEnd_3003057 1028007782566108172917799 := by
  unfold tailWord_3003057
  simp only [CollatzResearch.WordTrace]
  refine ⟨109530487081444845148143425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73020324720963230098762283 109530487081444845148143425)
  ·
    refine ⟨82147865311083633861107569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109530487081444845148143425 82147865311083633861107569)
    ·
      refine ⟨61610898983312725395830677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82147865311083633861107569 61610898983312725395830677)
      ·
        refine ⟨2888010889842784002929563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61610898983312725395830677 2888010889842784002929563)
        ·
          refine ⟨4332016334764176004394345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2888010889842784002929563 4332016334764176004394345)
          ·
            refine ⟨3249012251073132003295759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4332016334764176004394345 3249012251073132003295759)
            ·
              refine ⟨4873518376609698004943639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249012251073132003295759 4873518376609698004943639)
              ·
                refine ⟨7310277564914547007415459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4873518376609698004943639 7310277564914547007415459)
                ·
                  refine ⟨10965416347371820511123189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7310277564914547007415459 10965416347371820511123189)
                  ·
                    refine ⟨1028007782566108172917799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10965416347371820511123189 1028007782566108172917799)
                    ·
                      rfl

theorem cell22_3003057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_3003057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003057 prefixEnd_3003057 := by exact prefixLift 3003057
  have htrace : WordTrace (prefixWord ++ tailWord_3003057) baseStart_3003057 baseEnd_3003057 := by
    simpa [prefixWord, tailWord_3003057, baseEnd_3003057] using wordTrace_append hprefix tailTrace_3003057
  have hstable : (prefixWord ++ tailWord_3003057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003057).length < 2 ^ (prefixWord ++ tailWord_3003057).sum := by decide
  have hdescent : baseEnd_3003057 < baseStart_3003057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003098 : List Nat := [3, 1, 1, 2, 2, 2, 2, 4, 5]
def baseStart_3003098 : Nat := 118140960795 + 3003098 * 2 ^ 59
def prefixEnd_3003098 : Nat := 4983230072969 + 3 ^ 40 * 3003098 * 2
def baseEnd_3003098 : Nat := 342673939234665910880891

theorem tailTrace_3003098 : CollatzResearch.WordTrace tailWord_3003098 prefixEnd_3003098 342673939234665910880891 := by
  unfold tailWord_3003098
  simp only [CollatzResearch.WordTrace]
  refine ⟨27382995618574077287596487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73021321649530872766923965 27382995618574077287596487)
  ·
    refine ⟨41074493427861115931394731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27382995618574077287596487 41074493427861115931394731)
    ·
      refine ⟨61611740141791673897092097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41074493427861115931394731 61611740141791673897092097)
      ·
        refine ⟨46208805106343755422819073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61611740141791673897092097 46208805106343755422819073)
        ·
          refine ⟨34656603829757816567114305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46208805106343755422819073 34656603829757816567114305)
          ·
            refine ⟨25992452872318362425335729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34656603829757816567114305 25992452872318362425335729)
            ·
              refine ⟨19494339654238771819001797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25992452872318362425335729 19494339654238771819001797)
              ·
                refine ⟨3655188685169769716062837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19494339654238771819001797 3655188685169769716062837)
                ·
                  refine ⟨342673939234665910880891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3655188685169769716062837 342673939234665910880891)
                  ·
                    rfl

theorem cell22_3003098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_3003098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003098 prefixEnd_3003098 := by exact prefixLift 3003098
  have htrace : WordTrace (prefixWord ++ tailWord_3003098) baseStart_3003098 baseEnd_3003098 := by
    simpa [prefixWord, tailWord_3003098, baseEnd_3003098] using wordTrace_append hprefix tailTrace_3003098
  have hstable : (prefixWord ++ tailWord_3003098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003098).length < 2 ^ (prefixWord ++ tailWord_3003098).sum := by decide
  have hdescent : baseEnd_3003098 < baseStart_3003098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003128 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 3, 4]
def baseStart_3003128 : Nat := 118140960795 + 3003128 * 2 ^ 59
def prefixEnd_3003128 : Nat := 4983230072969 + 3 ^ 40 * 3003128 * 2
def baseEnd_3003128 : Nat := 1028032087317087654392581

theorem tailTrace_3003128 : CollatzResearch.WordTrace tailWord_3003128 prefixEnd_3003128 1028032087317087654392581 := by
  unfold tailWord_3003128
  simp only [CollatzResearch.WordTrace]
  refine ⟨54766538332093812136989019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73022051109458416182652025 54766538332093812136989019)
  ·
    refine ⟨82149807498140718205483529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54766538332093812136989019 82149807498140718205483529)
    ·
      refine ⟨61612355623605538654112647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82149807498140718205483529 61612355623605538654112647)
      ·
        refine ⟨92418533435408307981168971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61612355623605538654112647 92418533435408307981168971)
        ·
          refine ⟨138627800153112461971753457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92418533435408307981168971 138627800153112461971753457)
          ·
            refine ⟨103970850114834346478815093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138627800153112461971753457 103970850114834346478815093)
            ·
              refine ⟨9747267198265719982388915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 103970850114834346478815093 9747267198265719982388915)
              ·
                refine ⟨14620900797398579973583373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9747267198265719982388915 14620900797398579973583373)
                ·
                  refine ⟨5482837799024467490093765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14620900797398579973583373 5482837799024467490093765)
                  ·
                    refine ⟨1028032087317087654392581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5482837799024467490093765 1028032087317087654392581)
                    ·
                      rfl

theorem cell22_3003128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 3, 4].length) (baseStart_3003128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003128 prefixEnd_3003128 := by exact prefixLift 3003128
  have htrace : WordTrace (prefixWord ++ tailWord_3003128) baseStart_3003128 baseEnd_3003128 := by
    simpa [prefixWord, tailWord_3003128, baseEnd_3003128] using wordTrace_append hprefix tailTrace_3003128
  have hstable : (prefixWord ++ tailWord_3003128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003128).length < 2 ^ (prefixWord ++ tailWord_3003128).sum := by decide
  have hdescent : baseEnd_3003128 < baseStart_3003128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003173 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 1, 6]
def baseStart_3003173 : Nat := 118140960795 + 3003173 * 2 ^ 59
def prefixEnd_3003173 : Nat := 4983230072969 + 3 ^ 40 * 3003173 * 2
def baseEnd_3003173 : Nat := 1028047491736722537017443

theorem tailTrace_3003173 : CollatzResearch.WordTrace tailWord_3003173 prefixEnd_3003173 1028047491736722537017443 := by
  unfold tailWord_3003173
  simp only [CollatzResearch.WordTrace]
  refine ⟨109534717949024596959366173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73023145299349731306244115 109534717949024596959366173)
  ·
    refine ⟨41075519230884223859762315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109534717949024596959366173 41075519230884223859762315)
    ·
      refine ⟨61613278846326335789643473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41075519230884223859762315 61613278846326335789643473)
      ·
        refine ⟨46209959134744751842232605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61613278846326335789643473 46209959134744751842232605)
        ·
          refine ⟨17328734675529281940837227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46209959134744751842232605 17328734675529281940837227)
          ·
            refine ⟨25993102013293922911255841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17328734675529281940837227 25993102013293922911255841)
            ·
              refine ⟨19494826509970442183441881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25993102013293922911255841 19494826509970442183441881)
              ·
                refine ⟨14621119882477831637581411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19494826509970442183441881 14621119882477831637581411)
                ·
                  refine ⟨21931679823716747456372117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14621119882477831637581411 21931679823716747456372117)
                  ·
                    refine ⟨1028047491736722537017443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21931679823716747456372117 1028047491736722537017443)
                    ·
                      rfl

theorem cell22_3003173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 6].length) (baseStart_3003173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003173 prefixEnd_3003173 := by exact prefixLift 3003173
  have htrace : WordTrace (prefixWord ++ tailWord_3003173) baseStart_3003173 baseEnd_3003173 := by
    simpa [prefixWord, tailWord_3003173, baseEnd_3003173] using wordTrace_append hprefix tailTrace_3003173
  have hstable : (prefixWord ++ tailWord_3003173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003173).length < 2 ^ (prefixWord ++ tailWord_3003173).sum := by decide
  have hdescent : baseEnd_3003173 < baseStart_3003173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003248 : List Nat := [2, 1, 1, 1, 4, 1, 2, 2, 1, 7]
def baseStart_3003248 : Nat := 118140960795 + 3003248 * 2 ^ 59
def prefixEnd_3003248 : Nat := 4983230072969 + 3 ^ 40 * 3003248 * 2
def baseEnd_3003248 : Nat := 1028073165769447341392213

theorem tailTrace_3003248 : CollatzResearch.WordTrace tailWord_3003248 prefixEnd_3003248 1028073165769447341392213 := by
  unfold tailWord_3003248
  simp only [CollatzResearch.WordTrace]
  refine ⟨54768726711876442384173199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73024968949168589845564265 54768726711876442384173199)
  ·
    refine ⟨82153090067814663576259799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54768726711876442384173199 82153090067814663576259799)
    ·
      refine ⟨123229635101721995364389699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82153090067814663576259799 123229635101721995364389699)
      ·
        refine ⟨184844452652582993046584549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123229635101721995364389699 184844452652582993046584549)
        ·
          refine ⟨34658334872359311196234603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 184844452652582993046584549 34658334872359311196234603)
          ·
            refine ⟨51987502308538966794351905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34658334872359311196234603 51987502308538966794351905)
            ·
              refine ⟨38990626731404225095763929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51987502308538966794351905 38990626731404225095763929)
              ·
                refine ⟨29242970048553168821822947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38990626731404225095763929 29242970048553168821822947)
                ·
                  refine ⟨43864455072829753232734421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29242970048553168821822947 43864455072829753232734421)
                  ·
                    refine ⟨1028073165769447341392213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43864455072829753232734421 1028073165769447341392213)
                    ·
                      rfl

theorem cell22_3003248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 2, 1, 7].length) (baseStart_3003248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003248 prefixEnd_3003248 := by exact prefixLift 3003248
  have htrace : WordTrace (prefixWord ++ tailWord_3003248) baseStart_3003248 baseEnd_3003248 := by
    simpa [prefixWord, tailWord_3003248, baseEnd_3003248] using wordTrace_append hprefix tailTrace_3003248
  have hstable : (prefixWord ++ tailWord_3003248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003248).length < 2 ^ (prefixWord ++ tailWord_3003248).sum := by decide
  have hdescent : baseEnd_3003248 < baseStart_3003248 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003271 : List Nat := [1, 1, 4, 2, 3, 2, 3, 2, 1, 3]
def baseStart_3003271 : Nat := 118140960795 + 3003271 * 2 ^ 59
def prefixEnd_3003271 : Nat := 4983230072969 + 3 ^ 40 * 3003271 * 2
def baseEnd_3003271 : Nat := 1028081039139482948067143

theorem tailTrace_3003271 : CollatzResearch.WordTrace tailWord_3003271 prefixEnd_3003271 1028081039139482948067143 := by
  unfold tailWord_3003271
  simp only [CollatzResearch.WordTrace]
  refine ⟨109538292302669559696433667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73025528201779706464289111 109538292302669559696433667)
  ·
    refine ⟨164307438454004339544650501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109538292302669559696433667 164307438454004339544650501)
    ·
      refine ⟨30807644710125813664621969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164307438454004339544650501 30807644710125813664621969)
      ·
        refine ⟨23105733532594360248466477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30807644710125813664621969 23105733532594360248466477)
        ·
          refine ⟨8664650074722885093174929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23105733532594360248466477 8664650074722885093174929)
          ·
            refine ⟨6498487556042163819881197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8664650074722885093174929 6498487556042163819881197)
            ·
              refine ⟨2436932833515811432455449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6498487556042163819881197 2436932833515811432455449)
              ·
                refine ⟨1827699625136858574341587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2436932833515811432455449 1827699625136858574341587)
                ·
                  refine ⟨2741549437705287861512381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827699625136858574341587 2741549437705287861512381)
                  ·
                    refine ⟨1028081039139482948067143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2741549437705287861512381 1028081039139482948067143)
                    ·
                      rfl

theorem cell22_3003271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_3003271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003271 prefixEnd_3003271 := by exact prefixLift 3003271
  have htrace : WordTrace (prefixWord ++ tailWord_3003271) baseStart_3003271 baseEnd_3003271 := by
    simpa [prefixWord, tailWord_3003271, baseEnd_3003271] using wordTrace_append hprefix tailTrace_3003271
  have hstable : (prefixWord ++ tailWord_3003271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003271).length < 2 ^ (prefixWord ++ tailWord_3003271).sum := by decide
  have hdescent : baseEnd_3003271 < baseStart_3003271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003297 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_3003297 : Nat := 118140960795 + 3003297 * 2 ^ 59
def prefixEnd_3003297 : Nat := 4983230072969 + 3 ^ 40 * 3003297 * 2
def baseEnd_3003297 : Nat := 1028089939470827546917063

theorem tailTrace_3003297 : CollatzResearch.WordTrace tailWord_3003297 prefixEnd_3003297 1028089939470827546917063 := by
  unfold tailWord_3003297
  simp only [CollatzResearch.WordTrace]
  refine ⟨109539240600575366136880145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73026160400383577424586763 109539240600575366136880145)
  ·
    refine ⟨82154430450431524602660109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109539240600575366136880145 82154430450431524602660109)
    ·
      refine ⟨30807911418911821725997541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82154430450431524602660109 30807911418911821725997541)
      ·
        refine ⟨5776483391045966573624539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30807911418911821725997541 5776483391045966573624539)
        ·
          refine ⟨8664725086568949860436809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5776483391045966573624539 8664725086568949860436809)
          ·
            refine ⟨6498543814926712395327607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8664725086568949860436809 6498543814926712395327607)
            ·
              refine ⟨9747815722390068592991411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6498543814926712395327607 9747815722390068592991411)
              ·
                refine ⟨14621723583585102889487117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9747815722390068592991411 14621723583585102889487117)
                ·
                  refine ⟨5483146343844413583557669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14621723583585102889487117 5483146343844413583557669)
                  ·
                    refine ⟨1028089939470827546917063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5483146343844413583557669 1028089939470827546917063)
                    ·
                      rfl

theorem cell22_3003297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_3003297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003297 prefixEnd_3003297 := by exact prefixLift 3003297
  have htrace : WordTrace (prefixWord ++ tailWord_3003297) baseStart_3003297 baseEnd_3003297 := by
    simpa [prefixWord, tailWord_3003297, baseEnd_3003297] using wordTrace_append hprefix tailTrace_3003297
  have hstable : (prefixWord ++ tailWord_3003297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003297).length < 2 ^ (prefixWord ++ tailWord_3003297).sum := by decide
  have hdescent : baseEnd_3003297 < baseStart_3003297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003318 : List Nat := [5, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_3003318 : Nat := 118140960795 + 3003318 * 2 ^ 59
def prefixEnd_3003318 : Nat := 4983230072969 + 3 ^ 40 * 3003318 * 2
def baseEnd_3003318 : Nat := 342699042733330164047333

theorem tailTrace_3003318 : CollatzResearch.WordTrace tailWord_3003318 prefixEnd_3003318 342699042733330164047333 := by
  unfold tailWord_3003318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6846250408343705420212163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73026671022332857815596405 6846250408343705420212163)
  ·
    refine ⟨10269375612515558130318245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6846250408343705420212163 10269375612515558130318245)
    ·
      refine ⟨1925507927346667149434671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10269375612515558130318245 1925507927346667149434671)
      ·
        refine ⟨2888261891020000724152007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1925507927346667149434671 2888261891020000724152007)
        ·
          refine ⟨4332392836530001086228011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2888261891020000724152007 4332392836530001086228011)
          ·
            refine ⟨6498589254795001629342017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4332392836530001086228011 6498589254795001629342017)
            ·
              refine ⟨4873941941096251222006513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6498589254795001629342017 4873941941096251222006513)
              ·
                refine ⟨3655456455822188416504885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4873941941096251222006513 3655456455822188416504885)
                ·
                  refine ⟨342699042733330164047333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3655456455822188416504885 342699042733330164047333)
                  ·
                    rfl

theorem cell22_3003318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_3003318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003318 prefixEnd_3003318 := by exact prefixLift 3003318
  have htrace : WordTrace (prefixWord ++ tailWord_3003318) baseStart_3003318 baseEnd_3003318 := by
    simpa [prefixWord, tailWord_3003318, baseEnd_3003318] using wordTrace_append hprefix tailTrace_3003318
  have hstable : (prefixWord ++ tailWord_3003318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003318).length < 2 ^ (prefixWord ++ tailWord_3003318).sum := by decide
  have hdescent : baseEnd_3003318 < baseStart_3003318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003359 : List Nat := [1, 1, 2, 3, 5, 2, 1, 1, 2, 4]
def baseStart_3003359 : Nat := 118140960795 + 3003359 * 2 ^ 59
def prefixEnd_3003359 : Nat := 4983230072969 + 3 ^ 40 * 3003359 * 2
def baseEnd_3003359 : Nat := 1028111163337880051866873

theorem tailTrace_3003359 : CollatzResearch.WordTrace tailWord_3003359 prefixEnd_3003359 1028111163337880051866873 := by
  unfold tailWord_3003359
  simp only [CollatzResearch.WordTrace]
  refine ⟨109541501926350750725637131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73027667950900500483758087 109541501926350750725637131)
  ·
    refine ⟨164312252889526126088455697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109541501926350750725637131 164312252889526126088455697)
    ·
      refine ⟨123234189667144594566341773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164312252889526126088455697 123234189667144594566341773)
      ·
        refine ⟨46212821125179222962378165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123234189667144594566341773 46212821125179222962378165)
        ·
          refine ⟨4332451980485552152722953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 46212821125179222962378165 4332451980485552152722953)
          ·
            refine ⟨3249338985364164114542215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4332451980485552152722953 3249338985364164114542215)
            ·
              refine ⟨4874008478046246171813323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249338985364164114542215 4874008478046246171813323)
              ·
                refine ⟨7311012717069369257719985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874008478046246171813323 7311012717069369257719985)
                ·
                  refine ⟨5483259537802026943289989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7311012717069369257719985 5483259537802026943289989)
                  ·
                    refine ⟨1028111163337880051866873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5483259537802026943289989 1028111163337880051866873)
                    ·
                      rfl

theorem cell22_3003359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 4].length) (baseStart_3003359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003359 prefixEnd_3003359 := by exact prefixLift 3003359
  have htrace : WordTrace (prefixWord ++ tailWord_3003359) baseStart_3003359 baseEnd_3003359 := by
    simpa [prefixWord, tailWord_3003359, baseEnd_3003359] using wordTrace_append hprefix tailTrace_3003359
  have hstable : (prefixWord ++ tailWord_3003359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003359).length < 2 ^ (prefixWord ++ tailWord_3003359).sum := by decide
  have hdescent : baseEnd_3003359 < baseStart_3003359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003378 : List Nat := [3, 2, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_3003378 : Nat := 118140960795 + 3003378 * 2 ^ 59
def prefixEnd_3003378 : Nat := 4983230072969 + 3 ^ 40 * 3003378 * 2
def baseEnd_3003378 : Nat := 1028117667426170335641815

theorem tailTrace_3003378 : CollatzResearch.WordTrace tailWord_3003378 prefixEnd_3003378 1028117667426170335641815 := by
  unfold tailWord_3003378
  simp only [CollatzResearch.WordTrace]
  refine ⟨27385548728320479242644697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73028129942187944647052525 27385548728320479242644697)
  ·
    refine ⟨20539161546240359431983523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27385548728320479242644697 20539161546240359431983523)
    ·
      refine ⟨30808742319360539147975285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20539161546240359431983523 30808742319360539147975285)
      ·
        refine ⟨2888319592440050545122683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30808742319360539147975285 2888319592440050545122683)
        ·
          refine ⟨4332479388660075817684025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2888319592440050545122683 4332479388660075817684025)
          ·
            refine ⟨3249359541495056863263019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4332479388660075817684025 3249359541495056863263019)
            ·
              refine ⟨4874039312242585294894529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249359541495056863263019 4874039312242585294894529)
              ·
                refine ⟨3655529484181938971170897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4874039312242585294894529 3655529484181938971170897)
                ·
                  refine ⟨2741647113136454228378173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3655529484181938971170897 2741647113136454228378173)
                  ·
                    refine ⟨1028117667426170335641815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2741647113136454228378173 1028117667426170335641815)
                    ·
                      rfl

theorem cell22_3003378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_3003378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003378 prefixEnd_3003378 := by exact prefixLift 3003378
  have htrace : WordTrace (prefixWord ++ tailWord_3003378) baseStart_3003378 baseEnd_3003378 := by
    simpa [prefixWord, tailWord_3003378, baseEnd_3003378] using wordTrace_append hprefix tailTrace_3003378
  have hstable : (prefixWord ++ tailWord_3003378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003378).length < 2 ^ (prefixWord ++ tailWord_3003378).sum := by decide
  have hdescent : baseEnd_3003378 < baseStart_3003378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003385 : List Nat := [1, 2, 1, 3, 1, 3, 3, 1, 7]
def baseStart_3003385 : Nat := 118140960795 + 3003385 * 2 ^ 59
def prefixEnd_3003385 : Nat := 4983230072969 + 3 ^ 40 * 3003385 * 2
def baseEnd_3003385 : Nat := 342706687889741550238931

theorem tailTrace_3003385 : CollatzResearch.WordTrace tailWord_3003385 prefixEnd_3003385 342706687889741550238931 := by
  unfold tailWord_3003385
  simp only [CollatzResearch.WordTrace]
  refine ⟨109542450224256557166083609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73028300149504371444055739 109542450224256557166083609)
  ·
    refine ⟨82156837668192417874562707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109542450224256557166083609 82156837668192417874562707)
    ·
      refine ⟨123235256502288626811844061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82156837668192417874562707 123235256502288626811844061)
      ·
        refine ⟨46213221188358235054441523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123235256502288626811844061 46213221188358235054441523)
        ·
          refine ⟨69319831782537352581662285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46213221188358235054441523 69319831782537352581662285)
          ·
            refine ⟨25994936918451507218123357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69319831782537352581662285 25994936918451507218123357)
            ·
              refine ⟨9748101344419315206796259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25994936918451507218123357 9748101344419315206796259)
              ·
                refine ⟨14622152016628972810194389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9748101344419315206796259 14622152016628972810194389)
                ·
                  refine ⟨342706687889741550238931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14622152016628972810194389 342706687889741550238931)
                  ·
                    rfl

theorem cell22_3003385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 7].length) (baseStart_3003385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003385 prefixEnd_3003385 := by exact prefixLift 3003385
  have htrace : WordTrace (prefixWord ++ tailWord_3003385) baseStart_3003385 baseEnd_3003385 := by
    simpa [prefixWord, tailWord_3003385, baseEnd_3003385] using wordTrace_append hprefix tailTrace_3003385
  have hstable : (prefixWord ++ tailWord_3003385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003385).length < 2 ^ (prefixWord ++ tailWord_3003385).sum := by decide
  have hdescent : baseEnd_3003385 < baseStart_3003385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003498 : List Nat := [3, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_3003498 : Nat := 118140960795 + 3003498 * 2 ^ 59
def prefixEnd_3003498 : Nat := 4983230072969 + 3 ^ 40 * 3003498 * 2
def baseEnd_3003498 : Nat := 342719581959510007547149

theorem tailTrace_3003498 : CollatzResearch.WordTrace tailWord_3003498 prefixEnd_3003498 342719581959510007547149 := by
  unfold tailWord_3003498
  simp only [CollatzResearch.WordTrace]
  refine ⟨27386642918211794366236787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73031047781898118309964765 27386642918211794366236787)
  ·
    refine ⟨41079964377317691549355181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27386642918211794366236787 41079964377317691549355181)
    ·
      refine ⟨15404986641494134331008193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41079964377317691549355181 15404986641494134331008193)
      ·
        refine ⟨11553739981120600748256145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15404986641494134331008193 11553739981120600748256145)
        ·
          refine ⟨8665304985840450561192109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11553739981120600748256145 8665304985840450561192109)
          ·
            refine ⟨3249489369690168960447041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8665304985840450561192109 3249489369690168960447041)
            ·
              refine ⟨2437117027267626720335281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3249489369690168960447041 2437117027267626720335281)
              ·
                refine ⟨1827837770450720040251461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2437117027267626720335281 1827837770450720040251461)
                ·
                  refine ⟨342719581959510007547149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1827837770450720040251461 342719581959510007547149)
                  ·
                    rfl

theorem cell22_3003498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_3003498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003498 prefixEnd_3003498 := by exact prefixLift 3003498
  have htrace : WordTrace (prefixWord ++ tailWord_3003498) baseStart_3003498 baseEnd_3003498 := by
    simpa [prefixWord, tailWord_3003498, baseEnd_3003498] using wordTrace_append hprefix tailTrace_3003498
  have hstable : (prefixWord ++ tailWord_3003498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003498).length < 2 ^ (prefixWord ++ tailWord_3003498).sum := by decide
  have hdescent : baseEnd_3003498 < baseStart_3003498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003507 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 9, 3]
def baseStart_3003507 : Nat := 118140960795 + 3003507 * 2 ^ 59
def prefixEnd_3003507 : Nat := 4983230072969 + 3 ^ 40 * 3003507 * 2
def baseEnd_3003507 : Nat := 1028161826762456999166419

theorem tailTrace_3003507 : CollatzResearch.WordTrace tailWord_3003507 prefixEnd_3003507 1028161826762456999166419 := by
  unfold tailWord_3003507
  simp only [CollatzResearch.WordTrace]
  refine ⟨109546899929814572002024775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73031266619876381334683183 109546899929814572002024775)
  ·
    refine ⟨164320349894721858003037163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109546899929814572002024775 164320349894721858003037163)
    ·
      refine ⟨246480524842082787004555745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164320349894721858003037163 246480524842082787004555745)
      ·
        refine ⟨184860393631562090253416809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246480524842082787004555745 184860393631562090253416809)
        ·
          refine ⟨138645295223671567690062607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184860393631562090253416809 138645295223671567690062607)
          ·
            refine ⟨207967942835507351535093911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138645295223671567690062607 207967942835507351535093911)
            ·
              refine ⟨311951914253261027302640867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207967942835507351535093911 311951914253261027302640867)
              ·
                refine ⟨467927871379891540953961301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 311951914253261027302640867 467927871379891540953961301)
                ·
                  refine ⟨2741764871366551997777117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 467927871379891540953961301 2741764871366551997777117)
                  ·
                    refine ⟨1028161826762456999166419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2741764871366551997777117 1028161826762456999166419)
                    ·
                      rfl

theorem cell22_3003507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 3].length) (baseStart_3003507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003507 prefixEnd_3003507 := by exact prefixLift 3003507
  have htrace : WordTrace (prefixWord ++ tailWord_3003507) baseStart_3003507 baseEnd_3003507 := by
    simpa [prefixWord, tailWord_3003507, baseEnd_3003507] using wordTrace_append hprefix tailTrace_3003507
  have hstable : (prefixWord ++ tailWord_3003507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003507).length < 2 ^ (prefixWord ++ tailWord_3003507).sum := by decide
  have hdescent : baseEnd_3003507 < baseStart_3003507 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003524 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 5, 3]
def baseStart_3003524 : Nat := 118140960795 + 3003524 * 2 ^ 59
def prefixEnd_3003524 : Nat := 4983230072969 + 3 ^ 40 * 3003524 * 2
def baseEnd_3003524 : Nat := 1028167646209874621491367

theorem tailTrace_3003524 : CollatzResearch.WordTrace tailWord_3003524 prefixEnd_3003524 1028167646209874621491367 := by
  unfold tailWord_3003524
  simp only [CollatzResearch.WordTrace]
  refine ⟨54773759985376491952696813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73031679980501989270262417 54773759985376491952696813)
  ·
    refine ⟨20540159994516184482261305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54773759985376491952696813 20540159994516184482261305)
    ·
      refine ⟨15405119995887138361695979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20540159994516184482261305 15405119995887138361695979)
      ·
        refine ⟨23107679993830707542543969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15405119995887138361695979 23107679993830707542543969)
        ·
          refine ⟨17330759995373030656907977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23107679993830707542543969 17330759995373030656907977)
          ·
            refine ⟨12998069996529772992680983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17330759995373030656907977 12998069996529772992680983)
            ·
              refine ⟨19497104994794659489021475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12998069996529772992680983 19497104994794659489021475)
              ·
                refine ⟨29245657492191989233532213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19497104994794659489021475 29245657492191989233532213)
                ·
                  refine ⟨2741780389892998990643645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29245657492191989233532213 2741780389892998990643645)
                  ·
                    refine ⟨1028167646209874621491367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2741780389892998990643645 1028167646209874621491367)
                    ·
                      rfl

theorem cell22_3003524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 5, 3].length) (baseStart_3003524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003524 prefixEnd_3003524 := by exact prefixLift 3003524
  have htrace : WordTrace (prefixWord ++ tailWord_3003524) baseStart_3003524 baseEnd_3003524 := by
    simpa [prefixWord, tailWord_3003524, baseEnd_3003524] using wordTrace_append hprefix tailTrace_3003524
  have hstable : (prefixWord ++ tailWord_3003524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003524).length < 2 ^ (prefixWord ++ tailWord_3003524).sum := by decide
  have hdescent : baseEnd_3003524 < baseStart_3003524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003528 : List Nat := [2, 1, 3, 4, 3, 1, 1, 1, 2, 4]
def baseStart_3003528 : Nat := 118140960795 + 3003528 * 2 ^ 59
def prefixEnd_3003528 : Nat := 4983230072969 + 3 ^ 40 * 3003528 * 2
def baseEnd_3003528 : Nat := 1028169015491619944391355

theorem tailTrace_3003528 : CollatzResearch.WordTrace tailWord_3003528 prefixEnd_3003528 1028169015491619944391355 := by
  unfold tailWord_3003528
  simp only [CollatzResearch.WordTrace]
  refine ⟨54773832931369246294269619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73031777241825661725692825 54773832931369246294269619)
  ·
    refine ⟨82160749397053869441404429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54773832931369246294269619 82160749397053869441404429)
    ·
      refine ⟨30810281023895201040526661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82160749397053869441404429 30810281023895201040526661)
      ·
        refine ⟨5776927691980350195098749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30810281023895201040526661 5776927691980350195098749)
        ·
          refine ⟨2166347884492631323162031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5776927691980350195098749 2166347884492631323162031)
          ·
            refine ⟨3249521826738946984743047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2166347884492631323162031 3249521826738946984743047)
            ·
              refine ⟨4874282740108420477114571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3249521826738946984743047 4874282740108420477114571)
              ·
                refine ⟨7311424110162630715671857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4874282740108420477114571 7311424110162630715671857)
                ·
                  refine ⟨5483568082621973036753893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7311424110162630715671857 5483568082621973036753893)
                  ·
                    refine ⟨1028169015491619944391355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5483568082621973036753893 1028169015491619944391355)
                    ·
                      rfl

theorem cell22_3003528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_3003528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003528 prefixEnd_3003528 := by exact prefixLift 3003528
  have htrace : WordTrace (prefixWord ++ tailWord_3003528) baseStart_3003528 baseEnd_3003528 := by
    simpa [prefixWord, tailWord_3003528, baseEnd_3003528] using wordTrace_append hprefix tailTrace_3003528
  have hstable : (prefixWord ++ tailWord_3003528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003528).length < 2 ^ (prefixWord ++ tailWord_3003528).sum := by decide
  have hdescent : baseEnd_3003528 < baseStart_3003528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003552 : List Nat := [2, 1, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_3003552 : Nat := 118140960795 + 3003552 * 2 ^ 59
def prefixEnd_3003552 : Nat := 4983230072969 + 3 ^ 40 * 3003552 * 2
def baseEnd_3003552 : Nat := 1028177231182091881791281

theorem tailTrace_3003552 : CollatzResearch.WordTrace tailWord_3003552 prefixEnd_3003552 1028177231182091881791281 := by
  unfold tailWord_3003552
  simp only [CollatzResearch.WordTrace]
  refine ⟨54774270607325772343706455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73032360809767696458275273 54774270607325772343706455)
  ·
    refine ⟨82161405910988658515559683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54774270607325772343706455 82161405910988658515559683)
    ·
      refine ⟨123242108866482987773339525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82161405910988658515559683 123242108866482987773339525)
      ·
        refine ⟨23107895412465560207501161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123242108866482987773339525 23107895412465560207501161)
        ·
          refine ⟨17330921559349170155625871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23107895412465560207501161 17330921559349170155625871)
          ·
            refine ⟨25996382339023755233438807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17330921559349170155625871 25996382339023755233438807)
            ·
              refine ⟨38994573508535632850158211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25996382339023755233438807 38994573508535632850158211)
              ·
                refine ⟨58491860262803449275237317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38994573508535632850158211 58491860262803449275237317)
                ·
                  refine ⟨10967223799275646739106997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58491860262803449275237317 10967223799275646739106997)
                  ·
                    refine ⟨1028177231182091881791281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10967223799275646739106997 1028177231182091881791281)
                    ·
                      rfl

theorem cell22_3003552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_3003552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003552 prefixEnd_3003552 := by exact prefixLift 3003552
  have htrace : WordTrace (prefixWord ++ tailWord_3003552) baseStart_3003552 baseEnd_3003552 := by
    simpa [prefixWord, tailWord_3003552, baseEnd_3003552] using wordTrace_append hprefix tailTrace_3003552
  have hstable : (prefixWord ++ tailWord_3003552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003552).length < 2 ^ (prefixWord ++ tailWord_3003552).sum := by decide
  have hdescent : baseEnd_3003552 < baseStart_3003552 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003567 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 5, 4]
def baseStart_3003567 : Nat := 118140960795 + 3003567 * 2 ^ 59
def prefixEnd_3003567 : Nat := 4983230072969 + 3 ^ 40 * 3003567 * 2
def baseEnd_3003567 : Nat := 1028182365988636842666235

theorem tailTrace_3003567 : CollatzResearch.WordTrace tailWord_3003567 prefixEnd_3003567 1028182365988636842666235 := by
  unfold tailWord_3003567
  simp only [CollatzResearch.WordTrace]
  refine ⟨109549088309597202249208955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73032725539731468166139303 109549088309597202249208955)
  ·
    refine ⟨164323632464395803373813433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109549088309597202249208955 164323632464395803373813433)
    ·
      refine ⟨123242724348296852530360075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164323632464395803373813433 123242724348296852530360075)
      ·
        refine ⟨184864086522445278795540113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123242724348296852530360075 184864086522445278795540113)
        ·
          refine ⟨138648064891833959096655085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184864086522445278795540113 138648064891833959096655085)
          ·
            refine ⟨51993024334437734661245657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 138648064891833959096655085 51993024334437734661245657)
            ·
              refine ⟨38994768250828300995934243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51993024334437734661245657 38994768250828300995934243)
              ·
                refine ⟨58492152376242451493901365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38994768250828300995934243 58492152376242451493901365)
                ·
                  refine ⟨5483639285272729827553253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58492152376242451493901365 5483639285272729827553253)
                  ·
                    refine ⟨1028182365988636842666235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5483639285272729827553253 1028182365988636842666235)
                    ·
                      rfl

theorem cell22_3003567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_3003567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003567 prefixEnd_3003567 := by exact prefixLift 3003567
  have htrace : WordTrace (prefixWord ++ tailWord_3003567) baseStart_3003567 baseEnd_3003567 := by
    simpa [prefixWord, tailWord_3003567, baseEnd_3003567] using wordTrace_append hprefix tailTrace_3003567
  have hstable : (prefixWord ++ tailWord_3003567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003567).length < 2 ^ (prefixWord ++ tailWord_3003567).sum := by decide
  have hdescent : baseEnd_3003567 < baseStart_3003567 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003569 : List Nat := [1, 2, 2, 5, 1, 1, 2, 1, 2, 5]
def baseStart_3003569 : Nat := 118140960795 + 3003569 * 2 ^ 59
def prefixEnd_3003569 : Nat := 4983230072969 + 3 ^ 40 * 3003569 * 2
def baseEnd_3003569 : Nat := 1028183050629509504116229

theorem tailTrace_3003569 : CollatzResearch.WordTrace tailWord_3003569 prefixEnd_3003569 1028183050629509504116229 := by
  unfold tailWord_3003569
  simp only [CollatzResearch.WordTrace]
  refine ⟨109549161255589956590781761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73032774170393304393854507 109549161255589956590781761)
  ·
    refine ⟨82161870941692467443086321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109549161255589956590781761 82161870941692467443086321)
    ·
      refine ⟨61621403206269350582314741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82161870941692467443086321 61621403206269350582314741)
      ·
        refine ⟨5777006550587751617092007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61621403206269350582314741 5777006550587751617092007)
        ·
          refine ⟨8665509825881627425638011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5777006550587751617092007 8665509825881627425638011)
          ·
            refine ⟨12998264738822441138457017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665509825881627425638011 12998264738822441138457017)
            ·
              refine ⟨9748698554116830853842763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12998264738822441138457017 9748698554116830853842763)
              ·
                refine ⟨14623047831175246280764145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9748698554116830853842763 14623047831175246280764145)
                ·
                  refine ⟨10967285873381434710573109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14623047831175246280764145 10967285873381434710573109)
                  ·
                    refine ⟨1028183050629509504116229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10967285873381434710573109 1028183050629509504116229)
                    ·
                      rfl

theorem cell22_3003569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 5].length) (baseStart_3003569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003569 prefixEnd_3003569 := by exact prefixLift 3003569
  have htrace : WordTrace (prefixWord ++ tailWord_3003569) baseStart_3003569 baseEnd_3003569 := by
    simpa [prefixWord, tailWord_3003569, baseEnd_3003569] using wordTrace_append hprefix tailTrace_3003569
  have hstable : (prefixWord ++ tailWord_3003569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003569).length < 2 ^ (prefixWord ++ tailWord_3003569).sum := by decide
  have hdescent : baseEnd_3003569 < baseStart_3003569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003599 : List Nat := [1, 1, 2, 1, 1, 3, 2, 7, 4]
def baseStart_3003599 : Nat := 118140960795 + 3003599 * 2 ^ 59
def prefixEnd_3003599 : Nat := 4983230072969 + 3 ^ 40 * 3003599 * 2
def baseEnd_3003599 : Nat := 342731106747533141955379

theorem tailTrace_3003599 : CollatzResearch.WordTrace tailWord_3003599 prefixEnd_3003599 342731106747533141955379 := by
  unfold tailWord_3003599
  simp only [CollatzResearch.WordTrace]
  refine ⟨109550255445481271714373851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73033503630320847809582567 109550255445481271714373851)
  ·
    refine ⟨164325383168221907571560777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109550255445481271714373851 164325383168221907571560777)
    ·
      refine ⟨123244037376166430678670583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164325383168221907571560777 123244037376166430678670583)
      ·
        refine ⟨184866056064249646018005875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123244037376166430678670583 184866056064249646018005875)
        ·
          refine ⟨277299084096374469027008813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 184866056064249646018005875 277299084096374469027008813)
          ·
            refine ⟨103987156536140425885128305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 277299084096374469027008813 103987156536140425885128305)
            ·
              refine ⟨77990367402105319413846229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 103987156536140425885128305 77990367402105319413846229)
              ·
                refine ⟨1827899235986843423762021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 77990367402105319413846229 1827899235986843423762021)
                ·
                  refine ⟨342731106747533141955379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1827899235986843423762021 342731106747533141955379)
                  ·
                    rfl

theorem cell22_3003599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 4].length) (baseStart_3003599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003599 prefixEnd_3003599 := by exact prefixLift 3003599
  have htrace : WordTrace (prefixWord ++ tailWord_3003599) baseStart_3003599 baseEnd_3003599 := by
    simpa [prefixWord, tailWord_3003599, baseEnd_3003599] using wordTrace_append hprefix tailTrace_3003599
  have hstable : (prefixWord ++ tailWord_3003599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003599).length < 2 ^ (prefixWord ++ tailWord_3003599).sum := by decide
  have hdescent : baseEnd_3003599 < baseStart_3003599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003627 : List Nat := [1, 1, 1, 1, 2, 6, 1, 9]
def baseStart_3003627 : Nat := 118140960795 + 3003627 * 2 ^ 59
def prefixEnd_3003627 : Nat := 4983230072969 + 3 ^ 40 * 3003627 * 2
def baseEnd_3003627 : Nat := 114244767246090742907339

theorem tailTrace_3003627 : CollatzResearch.WordTrace tailWord_3003627 prefixEnd_3003627 114244767246090742907339 := by
  unfold tailWord_3003627
  simp only [CollatzResearch.WordTrace]
  refine ⟨109551276689379832496393135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73034184459586554997595423 109551276689379832496393135)
  ·
    refine ⟨164326915034069748744589703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109551276689379832496393135 164326915034069748744589703)
    ·
      refine ⟨246490372551104623116884555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164326915034069748744589703 246490372551104623116884555)
      ·
        refine ⟨369735558826656934675326833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246490372551104623116884555 369735558826656934675326833)
        ·
          refine ⟨277301669119992701006495125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 369735558826656934675326833 277301669119992701006495125)
          ·
            refine ⟨12998515739999657859679459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 277301669119992701006495125 12998515739999657859679459)
            ·
              refine ⟨19497773609999486789519189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12998515739999657859679459 19497773609999486789519189)
              ·
                refine ⟨114244767246090742907339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19497773609999486789519189 114244767246090742907339)
                ·
                  rfl

theorem cell22_3003627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 9].length) (baseStart_3003627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003627 prefixEnd_3003627 := by exact prefixLift 3003627
  have htrace : WordTrace (prefixWord ++ tailWord_3003627) baseStart_3003627 baseEnd_3003627 := by
    simpa [prefixWord, tailWord_3003627, baseEnd_3003627] using wordTrace_append hprefix tailTrace_3003627
  have hstable : (prefixWord ++ tailWord_3003627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003627).length < 2 ^ (prefixWord ++ tailWord_3003627).sum := by decide
  have hdescent : baseEnd_3003627 < baseStart_3003627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003646 : List Nat := [4, 2, 2, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3003646 : Nat := 118140960795 + 3003646 * 2 ^ 59
def prefixEnd_3003646 : Nat := 4983230072969 + 3 ^ 40 * 3003646 * 2
def baseEnd_3003646 : Nat := 1028209409303106969940993

theorem tailTrace_3003646 : CollatzResearch.WordTrace tailWord_3003646 prefixEnd_3003646 1028209409303106969940993 := by
  unfold tailWord_3003646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13693996209538874842666849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73034646450873999160889861 13693996209538874842666849)
  ·
    refine ⟨10270497157154156132000137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13693996209538874842666849 10270497157154156132000137)
    ·
      refine ⟨7702872867865617099000103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10270497157154156132000137 7702872867865617099000103)
      ·
        refine ⟨11554309301798425648500155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7702872867865617099000103 11554309301798425648500155)
        ·
          refine ⟨17331463952697638472750233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11554309301798425648500155 17331463952697638472750233)
          ·
            refine ⟨12998597964523228854562675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17331463952697638472750233 12998597964523228854562675)
            ·
              refine ⟨19497896946784843281844013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12998597964523228854562675 19497896946784843281844013)
              ·
                refine ⟨7311711355044316230691505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19497896946784843281844013 7311711355044316230691505)
                ·
                  refine ⟨5483783516283237173018629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7311711355044316230691505 5483783516283237173018629)
                  ·
                    refine ⟨1028209409303106969940993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5483783516283237173018629 1028209409303106969940993)
                    ·
                      rfl

theorem cell22_3003646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3003646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003646 prefixEnd_3003646 := by exact prefixLift 3003646
  have htrace : WordTrace (prefixWord ++ tailWord_3003646) baseStart_3003646 baseEnd_3003646 := by
    simpa [prefixWord, tailWord_3003646, baseEnd_3003646] using wordTrace_append hprefix tailTrace_3003646
  have hstable : (prefixWord ++ tailWord_3003646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003646).length < 2 ^ (prefixWord ++ tailWord_3003646).sum := by decide
  have hdescent : baseEnd_3003646 < baseStart_3003646 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003674 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_3003674 : Nat := 118140960795 + 3003674 * 2 ^ 59
def prefixEnd_3003674 : Nat := 4983230072969 + 3 ^ 40 * 3003674 * 2
def baseEnd_3003674 : Nat := 1028218994275324230240907

theorem tailTrace_3003674 : CollatzResearch.WordTrace tailWord_3003674 prefixEnd_3003674 1028218994275324230240907 := by
  unfold tailWord_3003674
  simp only [CollatzResearch.WordTrace]
  refine ⟨27388247730052389880838519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73035327280139706348902717 27388247730052389880838519)
  ·
    refine ⟨41082371595078584821257779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27388247730052389880838519 41082371595078584821257779)
    ·
      refine ⟨61623557392617877231886669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41082371595078584821257779 61623557392617877231886669)
      ·
        refine ⟨23108834022231703961957501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61623557392617877231886669 23108834022231703961957501)
        ·
          refine ⟨8665812758336888985734063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23108834022231703961957501 8665812758336888985734063)
          ·
            refine ⟨12998719137505333478601095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665812758336888985734063 12998719137505333478601095)
            ·
              refine ⟨19498078706258000217901643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12998719137505333478601095 19498078706258000217901643)
              ·
                refine ⟨29247118059387000326852465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19498078706258000217901643 29247118059387000326852465)
                ·
                  refine ⟨21935338544540250245139349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29247118059387000326852465 21935338544540250245139349)
                  ·
                    refine ⟨1028218994275324230240907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21935338544540250245139349 1028218994275324230240907)
                    ·
                      rfl

theorem cell22_3003674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_3003674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003674 prefixEnd_3003674 := by exact prefixLift 3003674
  have htrace : WordTrace (prefixWord ++ tailWord_3003674) baseStart_3003674 baseEnd_3003674 := by
    simpa [prefixWord, tailWord_3003674, baseEnd_3003674] using wordTrace_append hprefix tailTrace_3003674
  have hstable : (prefixWord ++ tailWord_3003674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003674).length < 2 ^ (prefixWord ++ tailWord_3003674).sum := by decide
  have hdescent : baseEnd_3003674 < baseStart_3003674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003693 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_3003693 : Nat := 118140960795 + 3003693 * 2 ^ 59
def prefixEnd_3003693 : Nat := 4983230072969 + 3 ^ 40 * 3003693 * 2
def baseEnd_3003693 : Nat := 1028225498363614514015849

theorem tailTrace_3003693 : CollatzResearch.WordTrace tailWord_3003693 prefixEnd_3003693 1028225498363614514015849 := by
  unfold tailWord_3003693
  simp only [CollatzResearch.WordTrace]
  refine ⟨109553683907140725768295733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73035789271427150512197155 109553683907140725768295733)
  ·
    refine ⟨10270657866294443040777725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109553683907140725768295733 10270657866294443040777725)
    ·
      refine ⟨3851496699860416140291647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10270657866294443040777725 3851496699860416140291647)
      ·
        refine ⟨5777245049790624210437471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3851496699860416140291647 5777245049790624210437471)
        ·
          refine ⟨8665867574685936315656207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5777245049790624210437471 8665867574685936315656207)
          ·
            refine ⟨12998801362028904473484311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8665867574685936315656207 12998801362028904473484311)
            ·
              refine ⟨19498202043043356710226467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12998801362028904473484311 19498202043043356710226467)
              ·
                refine ⟨29247303064565035065339701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19498202043043356710226467 29247303064565035065339701)
                ·
                  refine ⟨2741934662302972037375597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29247303064565035065339701 2741934662302972037375597)
                  ·
                    refine ⟨1028225498363614514015849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2741934662302972037375597 1028225498363614514015849)
                    ·
                      rfl

theorem cell22_3003693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_3003693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003693 prefixEnd_3003693 := by exact prefixLift 3003693
  have htrace : WordTrace (prefixWord ++ tailWord_3003693) baseStart_3003693 baseEnd_3003693 := by
    simpa [prefixWord, tailWord_3003693, baseEnd_3003693] using wordTrace_append hprefix tailTrace_3003693
  have hstable : (prefixWord ++ tailWord_3003693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003693).length < 2 ^ (prefixWord ++ tailWord_3003693).sum := by decide
  have hdescent : baseEnd_3003693 < baseStart_3003693 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003710 : List Nat := [4, 2, 1, 2, 1, 1, 4, 3, 1, 3]
def baseStart_3003710 : Nat := 118140960795 + 3003710 * 2 ^ 59
def prefixEnd_3003710 : Nat := 4983230072969 + 3 ^ 40 * 3003710 * 2
def baseEnd_3003710 : Nat := 1028231317811032136340797

theorem tailTrace_3003710 : CollatzResearch.WordTrace tailWord_3003710 prefixEnd_3003710 1028231317811032136340797 := by
  unfold tailWord_3003710
  simp only [CollatzResearch.WordTrace]
  refine ⟨13694287993509892208958073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73036202632052758447776389 13694287993509892208958073)
  ·
    refine ⟨10270715995132419156718555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13694287993509892208958073 10270715995132419156718555)
    ·
      refine ⟨15406073992698628735077833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10270715995132419156718555 15406073992698628735077833)
      ·
        refine ⟨11554555494523971551308375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15406073992698628735077833 11554555494523971551308375)
        ·
          refine ⟨17331833241785957326962563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11554555494523971551308375 17331833241785957326962563)
          ·
            refine ⟨25997749862678935990443845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17331833241785957326962563 25997749862678935990443845)
            ·
              refine ⟨4874578099252300498208221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25997749862678935990443845 4874578099252300498208221)
              ·
                refine ⟨1827966787219612686828083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4874578099252300498208221 1827966787219612686828083)
                ·
                  refine ⟨2741950180829419030242125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1827966787219612686828083 2741950180829419030242125)
                  ·
                    refine ⟨1028231317811032136340797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2741950180829419030242125 1028231317811032136340797)
                    ·
                      rfl

theorem cell22_3003710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_3003710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003710 prefixEnd_3003710 := by exact prefixLift 3003710
  have htrace : WordTrace (prefixWord ++ tailWord_3003710) baseStart_3003710 baseEnd_3003710 := by
    simpa [prefixWord, tailWord_3003710, baseEnd_3003710] using wordTrace_append hprefix tailTrace_3003710
  have hstable : (prefixWord ++ tailWord_3003710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003710).length < 2 ^ (prefixWord ++ tailWord_3003710).sum := by decide
  have hdescent : baseEnd_3003710 < baseStart_3003710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003779 : List Nat := [1, 1, 1, 3, 5, 1, 10]
def baseStart_3003779 : Nat := 118140960795 + 3003779 * 2 ^ 59
def prefixEnd_3003779 : Nat := 4983230072969 + 3 ^ 40 * 3003779 * 2
def baseEnd_3003779 : Nat := 38083516219301442828355

theorem tailTrace_3003779 : CollatzResearch.WordTrace tailWord_3003779 prefixEnd_3003779 38083516219301442828355 := by
  unfold tailWord_3003779
  simp only [CollatzResearch.WordTrace]
  refine ⟨109556820584829162455926391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73037880389886108303950927 109556820584829162455926391)
  ·
    refine ⟨164335230877243743683889587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109556820584829162455926391 164335230877243743683889587)
    ·
      refine ⟨246502846315865615525834381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164335230877243743683889587 246502846315865615525834381)
      ·
        refine ⟨92438567368449605822187893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 246502846315865615525834381 92438567368449605822187893)
        ·
          refine ⟨8666115690792150545830115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92438567368449605822187893 8666115690792150545830115)
          ·
            refine ⟨12999173536188225818745173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8666115690792150545830115 12999173536188225818745173)
            ·
              refine ⟨38083516219301442828355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12999173536188225818745173 38083516219301442828355)
              ·
                rfl

theorem cell22_3003779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 10].length) (baseStart_3003779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003779 prefixEnd_3003779 := by exact prefixLift 3003779
  have htrace : WordTrace (prefixWord ++ tailWord_3003779) baseStart_3003779 baseEnd_3003779 := by
    simpa [prefixWord, tailWord_3003779, baseEnd_3003779] using wordTrace_append hprefix tailTrace_3003779
  have hstable : (prefixWord ++ tailWord_3003779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003779).length < 2 ^ (prefixWord ++ tailWord_3003779).sum := by decide
  have hdescent : baseEnd_3003779 < baseStart_3003779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003785 : List Nat := [1, 2, 1, 1, 7, 1, 3, 2, 4]
def baseStart_3003785 : Nat := 118140960795 + 3003785 * 2 ^ 59
def prefixEnd_3003785 : Nat := 4983230072969 + 3 ^ 40 * 3003785 * 2
def baseEnd_3003785 : Nat := 342752330614585646905189

theorem tailTrace_3003785 : CollatzResearch.WordTrace tailWord_3003785 prefixEnd_3003785 342752330614585646905189 := by
  unfold tailWord_3003785
  simp only [CollatzResearch.WordTrace]
  refine ⟨109557039422807425480644809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73038026281871616987096539 109557039422807425480644809)
  ·
    refine ⟨82167779567105569110483607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109557039422807425480644809 82167779567105569110483607)
    ·
      refine ⟨123251669350658353665725411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82167779567105569110483607 123251669350658353665725411)
      ·
        refine ⟨184877504025987530498588117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123251669350658353665725411 184877504025987530498588117)
        ·
          refine ⟨4333066500609082746060659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 184877504025987530498588117 4333066500609082746060659)
          ·
            refine ⟨6499599750913624119090989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4333066500609082746060659 6499599750913624119090989)
            ·
              refine ⟨2437349906592609044659121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6499599750913624119090989 2437349906592609044659121)
              ·
                refine ⟨1828012429944456783494341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2437349906592609044659121 1828012429944456783494341)
                ·
                  refine ⟨342752330614585646905189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1828012429944456783494341 342752330614585646905189)
                  ·
                    rfl

theorem cell22_3003785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 4].length) (baseStart_3003785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003785 prefixEnd_3003785 := by exact prefixLift 3003785
  have htrace : WordTrace (prefixWord ++ tailWord_3003785) baseStart_3003785 baseEnd_3003785 := by
    simpa [prefixWord, tailWord_3003785, baseEnd_3003785] using wordTrace_append hprefix tailTrace_3003785
  have hstable : (prefixWord ++ tailWord_3003785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003785).length < 2 ^ (prefixWord ++ tailWord_3003785).sum := by decide
  have hdescent : baseEnd_3003785 < baseStart_3003785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003796 : List Nat := [2, 4, 2, 1, 2, 1, 1, 9]
def baseStart_3003796 : Nat := 118140960795 + 3003796 * 2 ^ 59
def prefixEnd_3003796 : Nat := 4983230072969 + 3 ^ 40 * 3003796 * 2
def baseEnd_3003796 : Nat := 114251195263172953187837

theorem tailTrace_3003796 : CollatzResearch.WordTrace tailWord_3003796 prefixEnd_3003796 114251195263172953187837 := by
  unfold tailWord_3003796
  simp only [CollatzResearch.WordTrace]
  refine ⟨54778720312883787179647621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73038293750511716239530161 54778720312883787179647621)
  ·
    refine ⟨10271010058665710096183929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54778720312883787179647621 10271010058665710096183929)
    ·
      refine ⟨7703257543999282572137947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10271010058665710096183929 7703257543999282572137947)
      ·
        refine ⟨11554886315998923858206921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7703257543999282572137947 11554886315998923858206921)
        ·
          refine ⟨8666164736999192893655191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11554886315998923858206921 8666164736999192893655191)
          ·
            refine ⟨12999247105498789340482787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8666164736999192893655191 12999247105498789340482787)
            ·
              refine ⟨19498870658248184010724181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12999247105498789340482787 19498870658248184010724181)
              ·
                refine ⟨114251195263172953187837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19498870658248184010724181 114251195263172953187837)
                ·
                  rfl

theorem cell22_3003796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 9].length) (baseStart_3003796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003796 prefixEnd_3003796 := by exact prefixLift 3003796
  have htrace : WordTrace (prefixWord ++ tailWord_3003796) baseStart_3003796 baseEnd_3003796 := by
    simpa [prefixWord, tailWord_3003796, baseEnd_3003796] using wordTrace_append hprefix tailTrace_3003796
  have hstable : (prefixWord ++ tailWord_3003796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003796).length < 2 ^ (prefixWord ++ tailWord_3003796).sum := by decide
  have hdescent : baseEnd_3003796 < baseStart_3003796 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003800 : List Nat := [2, 1, 2, 5, 2, 1, 1, 3, 2, 3]
def baseStart_3003800 : Nat := 118140960795 + 3003800 * 2 ^ 59
def prefixEnd_3003800 : Nat := 4983230072969 + 3 ^ 40 * 3003800 * 2
def baseEnd_3003800 : Nat := 1028262126650301901590521

theorem tailTrace_3003800 : CollatzResearch.WordTrace tailWord_3003800 prefixEnd_3003800 1028262126650301901590521 := by
  unfold tailWord_3003800
  simp only [CollatzResearch.WordTrace]
  refine ⟨54778793258876541521220427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73038391011835388694960569 54778793258876541521220427)
  ·
    refine ⟨82168189888314812281830641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54778793258876541521220427 82168189888314812281830641)
    ·
      refine ⟨61626142416236109211372981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82168189888314812281830641 61626142416236109211372981)
      ·
        refine ⟨5777450851522135238566217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61626142416236109211372981 5777450851522135238566217)
        ·
          refine ⟨4333088138641601428924663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5777450851522135238566217 4333088138641601428924663)
          ·
            refine ⟨6499632207962402143386995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4333088138641601428924663 6499632207962402143386995)
            ·
              refine ⟨9749448311943603215080493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6499632207962402143386995 9749448311943603215080493)
              ·
                refine ⟨3656043116978851205655185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9749448311943603215080493 3656043116978851205655185)
                ·
                  refine ⟨2742032337734138404241389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3656043116978851205655185 2742032337734138404241389)
                  ·
                    refine ⟨1028262126650301901590521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2742032337734138404241389 1028262126650301901590521)
                    ·
                      rfl

theorem cell22_3003800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 3, 2, 3].length) (baseStart_3003800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003800 prefixEnd_3003800 := by exact prefixLift 3003800
  have htrace : WordTrace (prefixWord ++ tailWord_3003800) baseStart_3003800 baseEnd_3003800 := by
    simpa [prefixWord, tailWord_3003800, baseEnd_3003800] using wordTrace_append hprefix tailTrace_3003800
  have hstable : (prefixWord ++ tailWord_3003800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003800).length < 2 ^ (prefixWord ++ tailWord_3003800).sum := by decide
  have hdescent : baseEnd_3003800 < baseStart_3003800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003811 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 5, 3]
def baseStart_3003811 : Nat := 118140960795 + 3003811 * 2 ^ 59
def prefixEnd_3003811 : Nat := 4983230072969 + 3 ^ 40 * 3003811 * 2
def baseEnd_3003811 : Nat := 1028265892175101539565487

theorem tailTrace_3003811 : CollatzResearch.WordTrace tailWord_3003811 prefixEnd_3003811 1028265892175101539565487 := by
  unfold tailWord_3003811
  simp only [CollatzResearch.WordTrace]
  refine ⟨109557987720713231921091287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73038658480475487947394191 109557987720713231921091287)
  ·
    refine ⟨164336981581069847881636931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109557987720713231921091287 164336981581069847881636931)
    ·
      refine ⟨246505472371604771822455397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164336981581069847881636931 246505472371604771822455397)
      ·
        refine ⟨46219776069675894716710387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246505472371604771822455397 46219776069675894716710387)
        ·
          refine ⟨69329664104513842075065581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46219776069675894716710387 69329664104513842075065581)
          ·
            refine ⟨25998624039192690778149593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69329664104513842075065581 25998624039192690778149593)
            ·
              refine ⟨19498968029394518083612195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25998624039192690778149593 19498968029394518083612195)
              ·
                refine ⟨29248452044091777125418293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19498968029394518083612195 29248452044091777125418293)
                ·
                  refine ⟨2742042379133604105507965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29248452044091777125418293 2742042379133604105507965)
                  ·
                    refine ⟨1028265892175101539565487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2742042379133604105507965 1028265892175101539565487)
                    ·
                      rfl

theorem cell22_3003811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 3].length) (baseStart_3003811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003811 prefixEnd_3003811 := by exact prefixLift 3003811
  have htrace : WordTrace (prefixWord ++ tailWord_3003811) baseStart_3003811 baseEnd_3003811 := by
    simpa [prefixWord, tailWord_3003811, baseEnd_3003811] using wordTrace_append hprefix tailTrace_3003811
  have hstable : (prefixWord ++ tailWord_3003811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003811).length < 2 ^ (prefixWord ++ tailWord_3003811).sum := by decide
  have hdescent : baseEnd_3003811 < baseStart_3003811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003824 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 7]
def baseStart_3003824 : Nat := 118140960795 + 3003824 * 2 ^ 59
def prefixEnd_3003824 : Nat := 4983230072969 + 3 ^ 40 * 3003824 * 2
def baseEnd_3003824 : Nat := 342756780780257946330149

theorem tailTrace_3003824 : CollatzResearch.WordTrace tailWord_3003824 prefixEnd_3003824 342756780780257946330149 := by
  unfold tailWord_3003824
  simp only [CollatzResearch.WordTrace]
  refine ⟨54779230934833067570657263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73038974579777423427543017 54779230934833067570657263)
  ·
    refine ⟨82168846402249601355985895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54779230934833067570657263 82168846402249601355985895)
    ·
      refine ⟨123253269603374402033978843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82168846402249601355985895 123253269603374402033978843)
      ·
        refine ⟨184879904405061603050968265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123253269603374402033978843 184879904405061603050968265)
        ·
          refine ⟨138659928303796202288226199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184879904405061603050968265 138659928303796202288226199)
          ·
            refine ⟨207989892455694303432339299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 138659928303796202288226199 207989892455694303432339299)
            ·
              refine ⟨311984838683541455148508949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 207989892455694303432339299 311984838683541455148508949)
              ·
                refine ⟨14624289313291005710086357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 311984838683541455148508949 14624289313291005710086357)
                ·
                  refine ⟨342756780780257946330149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14624289313291005710086357 342756780780257946330149)
                  ·
                    rfl

theorem cell22_3003824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 7].length) (baseStart_3003824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003824 prefixEnd_3003824 := by exact prefixLift 3003824
  have htrace : WordTrace (prefixWord ++ tailWord_3003824) baseStart_3003824 baseEnd_3003824 := by
    simpa [prefixWord, tailWord_3003824, baseEnd_3003824] using wordTrace_append hprefix tailTrace_3003824
  have hstable : (prefixWord ++ tailWord_3003824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003824).length < 2 ^ (prefixWord ++ tailWord_3003824).sum := by decide
  have hdescent : baseEnd_3003824 < baseStart_3003824 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003839 : List Nat := [1, 1, 2, 2, 2, 1, 1, 2, 3, 7]
def baseStart_3003839 : Nat := 118140960795 + 3003839 * 2 ^ 59
def prefixEnd_3003839 : Nat := 4983230072969 + 3 ^ 40 * 3003839 * 2
def baseEnd_3003839 : Nat := 1028275477147318799865401

theorem tailTrace_3003839 : CollatzResearch.WordTrace tailWord_3003839 prefixEnd_3003839 1028275477147318799865401 := by
  unfold tailWord_3003839
  simp only [CollatzResearch.WordTrace]
  refine ⟨109559008964611792703110571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73039339309741195135407047 109559008964611792703110571)
  ·
    refine ⟨164338513446917689054665857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109559008964611792703110571 164338513446917689054665857)
    ·
      refine ⟨123253885085188266790999393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164338513446917689054665857 123253885085188266790999393)
      ·
        refine ⟨92440413813891200093249545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123253885085188266790999393 92440413813891200093249545)
        ·
          refine ⟨69330310360418400069937159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92440413813891200093249545 69330310360418400069937159)
          ·
            refine ⟨103995465540627600104905739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69330310360418400069937159 103995465540627600104905739)
            ·
              refine ⟨155993198310941400157358609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 103995465540627600104905739 155993198310941400157358609)
              ·
                refine ⟨116994898733206050118018957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 155993198310941400157358609 116994898733206050118018957)
                ·
                  refine ⟨43873087024952268794257109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 116994898733206050118018957 43873087024952268794257109)
                  ·
                    refine ⟨1028275477147318799865401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43873087024952268794257109 1028275477147318799865401)
                    ·
                      rfl

theorem cell22_3003839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 7].length) (baseStart_3003839 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003839 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003839 prefixEnd_3003839 := by exact prefixLift 3003839
  have htrace : WordTrace (prefixWord ++ tailWord_3003839) baseStart_3003839 baseEnd_3003839 := by
    simpa [prefixWord, tailWord_3003839, baseEnd_3003839] using wordTrace_append hprefix tailTrace_3003839
  have hstable : (prefixWord ++ tailWord_3003839).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003839).length < 2 ^ (prefixWord ++ tailWord_3003839).sum := by decide
  have hdescent : baseEnd_3003839 < baseStart_3003839 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003871 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 3, 4]
def baseStart_3003871 : Nat := 118140960795 + 3003871 * 2 ^ 59
def prefixEnd_3003871 : Nat := 4983230072969 + 3 ^ 40 * 3003871 * 2
def baseEnd_3003871 : Nat := 1028286431401281383065303

theorem tailTrace_3003871 : CollatzResearch.WordTrace tailWord_3003871 prefixEnd_3003871 1028286431401281383065303 := by
  unfold tailWord_3003871
  simp only [CollatzResearch.WordTrace]
  refine ⟨109560176100495862168275467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73040117400330574778850311 109560176100495862168275467)
  ·
    refine ⟨164340264150743793252413201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109560176100495862168275467 164340264150743793252413201)
    ·
      refine ⟨123255198113057844939309901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164340264150743793252413201 123255198113057844939309901)
      ·
        refine ⟨46220699292396691852241213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123255198113057844939309901 46220699292396691852241213)
        ·
          refine ⟨17332762234648759444590455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46220699292396691852241213 17332762234648759444590455)
          ·
            refine ⟨25999143351973139166885683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17332762234648759444590455 25999143351973139166885683)
            ·
              refine ⟨38998715027959708750328525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25999143351973139166885683 38998715027959708750328525)
              ·
                refine ⟨14624518135484890781373197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38998715027959708750328525 14624518135484890781373197)
                ·
                  refine ⟨5484194300806834043014949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14624518135484890781373197 5484194300806834043014949)
                  ·
                    refine ⟨1028286431401281383065303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484194300806834043014949 1028286431401281383065303)
                    ·
                      rfl

theorem cell22_3003871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_3003871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003871 prefixEnd_3003871 := by exact prefixLift 3003871
  have htrace : WordTrace (prefixWord ++ tailWord_3003871) baseStart_3003871 baseEnd_3003871 := by
    simpa [prefixWord, tailWord_3003871, baseEnd_3003871] using wordTrace_append hprefix tailTrace_3003871
  have hstable : (prefixWord ++ tailWord_3003871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003871).length < 2 ^ (prefixWord ++ tailWord_3003871).sum := by decide
  have hdescent : baseEnd_3003871 < baseStart_3003871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003886 : List Nat := [4, 1, 2, 1, 2, 1, 1, 2, 8]
def baseStart_3003886 : Nat := 118140960795 + 3003886 * 2 ^ 59
def prefixEnd_3003886 : Nat := 4983230072969 + 3 ^ 40 * 3003886 * 2
def baseEnd_3003886 : Nat := 342763855402608781313419

theorem tailTrace_3003886 : CollatzResearch.WordTrace tailWord_3003886 prefixEnd_3003886 342763855402608781313419 := by
  unfold tailWord_3003886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13695090399430189966258939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73040482130294346486714341 13695090399430189966258939)
  ·
    refine ⟨20542635599145284949388409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13695090399430189966258939 20542635599145284949388409)
    ·
      refine ⟨15406976699358963712041307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20542635599145284949388409 15406976699358963712041307)
      ·
        refine ⟨23110465049038445568061961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15406976699358963712041307 23110465049038445568061961)
        ·
          refine ⟨17332848786778834176046471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23110465049038445568061961 17332848786778834176046471)
          ·
            refine ⟨25999273180168251264069707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17332848786778834176046471 25999273180168251264069707)
            ·
              refine ⟨38998909770252376896104561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25999273180168251264069707 38998909770252376896104561)
              ·
                refine ⟨29249182327689282672078421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38998909770252376896104561 29249182327689282672078421)
                ·
                  refine ⟨342763855402608781313419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29249182327689282672078421 342763855402608781313419)
                  ·
                    rfl

theorem cell22_3003886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 8].length) (baseStart_3003886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003886 prefixEnd_3003886 := by exact prefixLift 3003886
  have htrace : WordTrace (prefixWord ++ tailWord_3003886) baseStart_3003886 baseEnd_3003886 := by
    simpa [prefixWord, tailWord_3003886, baseEnd_3003886] using wordTrace_append hprefix tailTrace_3003886
  have hstable : (prefixWord ++ tailWord_3003886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003886).length < 2 ^ (prefixWord ++ tailWord_3003886).sum := by decide
  have hdescent : baseEnd_3003886 < baseStart_3003886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003888 : List Nat := [2, 1, 1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_3003888 : Nat := 118140960795 + 3003888 * 2 ^ 59
def prefixEnd_3003888 : Nat := 4983230072969 + 3 ^ 40 * 3003888 * 2
def baseEnd_3003888 : Nat := 1028292250848699005390251

theorem tailTrace_3003888 : CollatzResearch.WordTrace tailWord_3003888 prefixEnd_3003888 1028292250848699005390251 := by
  unfold tailWord_3003888
  simp only [CollatzResearch.WordTrace]
  refine ⟨54780398070717137035822159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73040530760956182714429545 54780398070717137035822159)
  ·
    refine ⟨82170597106075705553733239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54780398070717137035822159 82170597106075705553733239)
    ·
      refine ⟨123255895659113558330599859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82170597106075705553733239 123255895659113558330599859)
      ·
        refine ⟨184883843488670337495899789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123255895659113558330599859 184883843488670337495899789)
        ·
          refine ⟨69331441308251376560962421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184883843488670337495899789 69331441308251376560962421)
          ·
            refine ⟨6499822622648566552590227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69331441308251376560962421 6499822622648566552590227)
            ·
              refine ⟨9749733933972849828885341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6499822622648566552590227 9749733933972849828885341)
              ·
                refine ⟨3656150225239818685832003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9749733933972849828885341 3656150225239818685832003)
                ·
                  refine ⟨5484225337859728028748005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656150225239818685832003 5484225337859728028748005)
                  ·
                    refine ⟨1028292250848699005390251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484225337859728028748005 1028292250848699005390251)
                    ·
                      rfl

theorem cell22_3003888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_3003888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003888 prefixEnd_3003888 := by exact prefixLift 3003888
  have htrace : WordTrace (prefixWord ++ tailWord_3003888) baseStart_3003888 baseEnd_3003888 := by
    simpa [prefixWord, tailWord_3003888, baseEnd_3003888] using wordTrace_append hprefix tailTrace_3003888
  have hstable : (prefixWord ++ tailWord_3003888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003888).length < 2 ^ (prefixWord ++ tailWord_3003888).sum := by decide
  have hdescent : baseEnd_3003888 < baseStart_3003888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003933 : List Nat := [1, 4, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3003933 : Nat := 118140960795 + 3003933 * 2 ^ 59
def prefixEnd_3003933 : Nat := 4983230072969 + 3 ^ 40 * 3003933 * 2
def baseEnd_3003933 : Nat := 1028307655268333888015113

theorem tailTrace_3003933 : CollatzResearch.WordTrace tailWord_3003933 prefixEnd_3003933 1028307655268333888015113 := by
  unfold tailWord_3003933
  simp only [CollatzResearch.WordTrace]
  refine ⟨109562437426271246757032453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73041624950847497838021635 109562437426271246757032453)
  ·
    refine ⟨20542957017425858766943585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109562437426271246757032453 20542957017425858766943585)
    ·
      refine ⟨15407217763069394075207689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20542957017425858766943585 15407217763069394075207689)
      ·
        refine ⟨11555413322302045556405767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15407217763069394075207689 11555413322302045556405767)
        ·
          refine ⟨17333119983453068334608651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11555413322302045556405767 17333119983453068334608651)
          ·
            refine ⟨25999679975179602501912977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17333119983453068334608651 25999679975179602501912977)
            ·
              refine ⟨19499759981384701876434733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25999679975179602501912977 19499759981384701876434733)
              ·
                refine ⟨7312409993019263203663025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19499759981384701876434733 7312409993019263203663025)
                ·
                  refine ⟨5484307494764447402747269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7312409993019263203663025 5484307494764447402747269)
                  ·
                    refine ⟨1028307655268333888015113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484307494764447402747269 1028307655268333888015113)
                    ·
                      rfl

theorem cell22_3003933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3003933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003933 prefixEnd_3003933 := by exact prefixLift 3003933
  have htrace : WordTrace (prefixWord ++ tailWord_3003933) baseStart_3003933 baseEnd_3003933 := by
    simpa [prefixWord, tailWord_3003933, baseEnd_3003933] using wordTrace_append hprefix tailTrace_3003933
  have hstable : (prefixWord ++ tailWord_3003933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003933).length < 2 ^ (prefixWord ++ tailWord_3003933).sum := by decide
  have hdescent : baseEnd_3003933 < baseStart_3003933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3003950 : List Nat := [4, 1, 3, 1, 2, 2, 1, 2, 2, 4]
def baseStart_3003950 : Nat := 118140960795 + 3003950 * 2 ^ 59
def prefixEnd_3003950 : Nat := 4983230072969 + 3 ^ 40 * 3003950 * 2
def baseEnd_3003950 : Nat := 1028313474715751510340061

theorem tailTrace_3003950 : CollatzResearch.WordTrace tailWord_3003950 prefixEnd_3003950 1028313474715751510340061 := by
  unfold tailWord_3003950
  simp only [CollatzResearch.WordTrace]
  refine ⟨13695382183401207332550163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73042038311473105773600869 13695382183401207332550163)
  ·
    refine ⟨20543073275101810998825245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13695382183401207332550163 20543073275101810998825245)
    ·
      refine ⟨7703652478163179124559467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20543073275101810998825245 7703652478163179124559467)
      ·
        refine ⟨11555478717244768686839201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7703652478163179124559467 11555478717244768686839201)
        ·
          refine ⟨8666609037933576515129401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11555478717244768686839201 8666609037933576515129401)
          ·
            refine ⟨6499956778450182386347051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8666609037933576515129401 6499956778450182386347051)
            ·
              refine ⟨9749935167675273579520577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6499956778450182386347051 9749935167675273579520577)
              ·
                refine ⟨7312451375756455184640433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9749935167675273579520577 7312451375756455184640433)
                ·
                  refine ⟨5484338531817341388480325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7312451375756455184640433 5484338531817341388480325)
                  ·
                    refine ⟨1028313474715751510340061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5484338531817341388480325 1028313474715751510340061)
                    ·
                      rfl

theorem cell22_3003950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_3003950 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3003950 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3003950 prefixEnd_3003950 := by exact prefixLift 3003950
  have htrace : WordTrace (prefixWord ++ tailWord_3003950) baseStart_3003950 baseEnd_3003950 := by
    simpa [prefixWord, tailWord_3003950, baseEnd_3003950] using wordTrace_append hprefix tailTrace_3003950
  have hstable : (prefixWord ++ tailWord_3003950).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3003950).length < 2 ^ (prefixWord ++ tailWord_3003950).sum := by decide
  have hdescent : baseEnd_3003950 < baseStart_3003950 := by decide
  rcases family_descends (prefixWord ++ tailWord_3003950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004010 : List Nat := [3, 1, 3, 2, 1, 3, 2, 2, 5]
def baseStart_3004010 : Nat := 118140960795 + 3004010 * 2 ^ 59
def prefixEnd_3004010 : Nat := 4983230072969 + 3 ^ 40 * 3004010 * 2
def baseEnd_3004010 : Nat := 342778004647310451279959

theorem tailTrace_3004010 : CollatzResearch.WordTrace tailWord_3004010 prefixEnd_3004010 342778004647310451279959 := by
  unfold tailWord_3004010
  simp only [CollatzResearch.WordTrace]
  refine ⟨27391311461748072226896371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73043497231328192605056989 27391311461748072226896371)
  ·
    refine ⟨41086967192622108340344557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27391311461748072226896371 41086967192622108340344557)
    ·
      refine ⟨15407612697233290627629209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41086967192622108340344557 15407612697233290627629209)
      ·
        refine ⟨11555709522924967970721907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15407612697233290627629209 11555709522924967970721907)
        ·
          refine ⟨17333564284387451956082861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11555709522924967970721907 17333564284387451956082861)
          ·
            refine ⟨6500086606645294483531073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17333564284387451956082861 6500086606645294483531073)
            ·
              refine ⟨4875064954983970862648305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6500086606645294483531073 4875064954983970862648305)
              ·
                refine ⟨3656298716237978146986229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4875064954983970862648305 3656298716237978146986229)
                ·
                  refine ⟨342778004647310451279959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3656298716237978146986229 342778004647310451279959)
                  ·
                    rfl

theorem cell22_3004010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_3004010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004010 prefixEnd_3004010 := by exact prefixLift 3004010
  have htrace : WordTrace (prefixWord ++ tailWord_3004010) baseStart_3004010 baseEnd_3004010 := by
    simpa [prefixWord, tailWord_3004010, baseEnd_3004010] using wordTrace_append hprefix tailTrace_3004010
  have hstable : (prefixWord ++ tailWord_3004010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004010).length < 2 ^ (prefixWord ++ tailWord_3004010).sum := by decide
  have hdescent : baseEnd_3004010 < baseStart_3004010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004014 : List Nat := [4, 1, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_3004014 : Nat := 118140960795 + 3004014 * 2 ^ 59
def prefixEnd_3004014 : Nat := 4983230072969 + 3 ^ 40 * 3004014 * 2
def baseEnd_3004014 : Nat := 1028335383223676676739865

theorem tailTrace_3004014 : CollatzResearch.WordTrace tailWord_3004014 prefixEnd_3004014 1028335383223676676739865 := by
  unfold tailWord_3004014
  simp only [CollatzResearch.WordTrace]
  refine ⟨13695673967372224698841387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73043594492651865060487397 13695673967372224698841387)
  ·
    refine ⟨20543510951058337048262081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13695673967372224698841387 20543510951058337048262081)
    ·
      refine ⟨15407633213293752786196561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20543510951058337048262081 15407633213293752786196561)
      ·
        refine ⟨11555724909970314589647421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15407633213293752786196561 11555724909970314589647421)
        ·
          refine ⟨4333396841238867971117783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11555724909970314589647421 4333396841238867971117783)
          ·
            refine ⟨6500095261858301956676675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4333396841238867971117783 6500095261858301956676675)
            ·
              refine ⟨9750142892787452935015013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6500095261858301956676675 9750142892787452935015013)
              ·
                refine ⟨1828151792397647425315315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9750142892787452935015013 1828151792397647425315315)
                ·
                  refine ⟨2742227688596471137972973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828151792397647425315315 2742227688596471137972973)
                  ·
                    refine ⟨1028335383223676676739865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2742227688596471137972973 1028335383223676676739865)
                    ·
                      rfl

theorem cell22_3004014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_3004014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004014 prefixEnd_3004014 := by exact prefixLift 3004014
  have htrace : WordTrace (prefixWord ++ tailWord_3004014) baseStart_3004014 baseEnd_3004014 := by
    simpa [prefixWord, tailWord_3004014, baseEnd_3004014] using wordTrace_append hprefix tailTrace_3004014
  have hstable : (prefixWord ++ tailWord_3004014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004014).length < 2 ^ (prefixWord ++ tailWord_3004014).sum := by decide
  have hdescent : baseEnd_3004014 < baseStart_3004014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004055 : List Nat := [1, 1, 3, 3, 2, 2, 1, 5, 4]
def baseStart_3004055 : Nat := 118140960795 + 3004055 * 2 ^ 59
def prefixEnd_3004055 : Nat := 4983230072969 + 3 ^ 40 * 3004055 * 2
def baseEnd_3004055 : Nat := 342783139453855412154913

theorem tailTrace_3004055 : CollatzResearch.WordTrace tailWord_3004055 prefixEnd_3004055 342783139453855412154913 := by
  unfold tailWord_3004055
  simp only [CollatzResearch.WordTrace]
  refine ⟨109566887131829261592973619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73044591421219507728649079 109566887131829261592973619)
  ·
    refine ⟨164350330697743892389460429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109566887131829261592973619 164350330697743892389460429)
    ·
      refine ⟨61631374011653959646047661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164350330697743892389460429 61631374011653959646047661)
      ·
        refine ⟨23111765254370234867267873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61631374011653959646047661 23111765254370234867267873)
        ·
          refine ⟨17333823940777676150450905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23111765254370234867267873 17333823940777676150450905)
          ·
            refine ⟨13000367955583257112838179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17333823940777676150450905 13000367955583257112838179)
            ·
              refine ⟨19500551933374885669257269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13000367955583257112838179 19500551933374885669257269)
              ·
                refine ⟨1828176743753895531492869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19500551933374885669257269 1828176743753895531492869)
                ·
                  refine ⟨342783139453855412154913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1828176743753895531492869 342783139453855412154913)
                  ·
                    rfl

theorem cell22_3004055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 4].length) (baseStart_3004055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004055 prefixEnd_3004055 := by exact prefixLift 3004055
  have htrace : WordTrace (prefixWord ++ tailWord_3004055) baseStart_3004055 baseEnd_3004055 := by
    simpa [prefixWord, tailWord_3004055, baseEnd_3004055] using wordTrace_append hprefix tailTrace_3004055
  have hstable : (prefixWord ++ tailWord_3004055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004055).length < 2 ^ (prefixWord ++ tailWord_3004055).sum := by decide
  have hdescent : baseEnd_3004055 < baseStart_3004055 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004128 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 7]
def baseStart_3004128 : Nat := 118140960795 + 3004128 * 2 ^ 59
def prefixEnd_3004128 : Nat := 4983230072969 + 3 ^ 40 * 3004128 * 2
def baseEnd_3004128 : Nat := 342791469251139459796505

theorem tailTrace_3004128 : CollatzResearch.WordTrace tailWord_3004128 prefixEnd_3004128 342791469251139459796505 := by
  unfold tailWord_3004128
  simp only [CollatzResearch.WordTrace]
  refine ⟨54784774830282397530190519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73046366440376530040254025 54784774830282397530190519)
  ·
    refine ⟨82177162245423596295285779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54784774830282397530190519 82177162245423596295285779)
    ·
      refine ⟨123265743368135394442928669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82177162245423596295285779 123265743368135394442928669)
      ·
        refine ⟨46224653763050772916098251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123265743368135394442928669 46224653763050772916098251)
        ·
          refine ⟨69336980644576159374147377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46224653763050772916098251 69336980644576159374147377)
          ·
            refine ⟨52002735483432119530610533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69336980644576159374147377 52002735483432119530610533)
            ·
              refine ⟨9750512903143522411989475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52002735483432119530610533 9750512903143522411989475)
              ·
                refine ⟨14625769354715283617984213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9750512903143522411989475 14625769354715283617984213)
                ·
                  refine ⟨342791469251139459796505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14625769354715283617984213 342791469251139459796505)
                  ·
                    rfl

theorem cell22_3004128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_3004128 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004128 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004128 prefixEnd_3004128 := by exact prefixLift 3004128
  have htrace : WordTrace (prefixWord ++ tailWord_3004128) baseStart_3004128 baseEnd_3004128 := by
    simpa [prefixWord, tailWord_3004128, baseEnd_3004128] using wordTrace_append hprefix tailTrace_3004128
  have hstable : (prefixWord ++ tailWord_3004128).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004128).length < 2 ^ (prefixWord ++ tailWord_3004128).sum := by decide
  have hdescent : baseEnd_3004128 < baseStart_3004128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004143 : List Nat := [1, 1, 2, 1, 5, 1, 2, 1, 1, 7]
def baseStart_3004143 : Nat := 118140960795 + 3004143 * 2 ^ 59
def prefixEnd_3004143 : Nat := 4983230072969 + 3 ^ 40 * 3004143 * 2
def baseEnd_3004143 : Nat := 1028379542559963340264469

theorem tailTrace_3004143 : CollatzResearch.WordTrace tailWord_3004143 prefixEnd_3004143 1028379542559963340264469 := by
  unfold tailWord_3004143
  simp only [CollatzResearch.WordTrace]
  refine ⟨109570096755510452622177083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73046731170340301748118055 109570096755510452622177083)
  ·
    refine ⟨164355145133265678933265625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109570096755510452622177083 164355145133265678933265625)
    ·
      refine ⟨123266358849949259199949219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164355145133265678933265625 123266358849949259199949219)
      ·
        refine ⟨184899538274923888799923829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123266358849949259199949219 184899538274923888799923829)
        ·
          refine ⟨17334331713274114574992859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184899538274923888799923829 17334331713274114574992859)
          ·
            refine ⟨26001497569911171862489289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17334331713274114574992859 26001497569911171862489289)
            ·
              refine ⟨19501123177433378896866967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26001497569911171862489289 19501123177433378896866967)
              ·
                refine ⟨29251684766150068345300451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19501123177433378896866967 29251684766150068345300451)
                ·
                  refine ⟨43877527149225102517950677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29251684766150068345300451 43877527149225102517950677)
                  ·
                    refine ⟨1028379542559963340264469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43877527149225102517950677 1028379542559963340264469)
                    ·
                      rfl

theorem cell22_3004143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_3004143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004143 prefixEnd_3004143 := by exact prefixLift 3004143
  have htrace : WordTrace (prefixWord ++ tailWord_3004143) baseStart_3004143 baseEnd_3004143 := by
    simpa [prefixWord, tailWord_3004143, baseEnd_3004143] using wordTrace_append hprefix tailTrace_3004143
  have hstable : (prefixWord ++ tailWord_3004143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004143).length < 2 ^ (prefixWord ++ tailWord_3004143).sum := by decide
  have hdescent : baseEnd_3004143 < baseStart_3004143 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004145 : List Nat := [1, 2, 2, 2, 2, 4, 1, 3, 5]
def baseStart_3004145 : Nat := 118140960795 + 3004145 * 2 ^ 59
def prefixEnd_3004145 : Nat := 4983230072969 + 3 ^ 40 * 3004145 * 2
def baseEnd_3004145 : Nat := 342793409066945333904821

theorem tailTrace_3004145 : CollatzResearch.WordTrace tailWord_3004145 prefixEnd_3004145 342793409066945333904821 := by
  unfold tailWord_3004145
  simp only [CollatzResearch.WordTrace]
  refine ⟨109570169701503206963749889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73046779801002137975833259 109570169701503206963749889)
  ·
    refine ⟨82177627276127405222812417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109570169701503206963749889 82177627276127405222812417)
    ·
      refine ⟨61633220457095553917109313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82177627276127405222812417 61633220457095553917109313)
      ·
        refine ⟨46224915342821665437831985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61633220457095553917109313 46224915342821665437831985)
        ·
          refine ⟨34668686507116249078373989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46224915342821665437831985 34668686507116249078373989)
          ·
            refine ⟨6500378720084296702195123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34668686507116249078373989 6500378720084296702195123)
            ·
              refine ⟨9750568080126445053292685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6500378720084296702195123 9750568080126445053292685)
              ·
                refine ⟨3656463030047416894984757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9750568080126445053292685 3656463030047416894984757)
                ·
                  refine ⟨342793409066945333904821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3656463030047416894984757 342793409066945333904821)
                  ·
                    rfl

theorem cell22_3004145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 5].length) (baseStart_3004145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004145 prefixEnd_3004145 := by exact prefixLift 3004145
  have htrace : WordTrace (prefixWord ++ tailWord_3004145) baseStart_3004145 baseEnd_3004145 := by
    simpa [prefixWord, tailWord_3004145, baseEnd_3004145] using wordTrace_append hprefix tailTrace_3004145
  have hstable : (prefixWord ++ tailWord_3004145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004145).length < 2 ^ (prefixWord ++ tailWord_3004145).sum := by decide
  have hdescent : baseEnd_3004145 < baseStart_3004145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004222 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 1, 5]
def baseStart_3004222 : Nat := 118140960795 + 3004222 * 2 ^ 59
def prefixEnd_3004222 : Nat := 4983230072969 + 3 ^ 40 * 3004222 * 2
def baseEnd_3004222 : Nat := 1028406585874433467539227

theorem tailTrace_3004222 : CollatzResearch.WordTrace tailWord_3004222 prefixEnd_3004222 1028406585874433467539227 := by
  unfold tailWord_3004222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13696622265278031139287865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73048652081482832742868613 13696622265278031139287865)
  ·
    refine ⟨10272466698958523354465899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13696622265278031139287865 10272466698958523354465899)
    ·
      refine ⟨15408700048437785031698849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10272466698958523354465899 15408700048437785031698849)
      ·
        refine ⟨11556525036328338773774137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15408700048437785031698849 11556525036328338773774137)
        ·
          refine ⟨8667393777246254080330603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11556525036328338773774137 8667393777246254080330603)
          ·
            refine ⟨13001090665869381120495905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667393777246254080330603 13001090665869381120495905)
            ·
              refine ⟨9750817999402035840371929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13001090665869381120495905 9750817999402035840371929)
              ·
                refine ⟨7313113499551526880278947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9750817999402035840371929 7313113499551526880278947)
                ·
                  refine ⟨10969670249327290320418421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7313113499551526880278947 10969670249327290320418421)
                  ·
                    refine ⟨1028406585874433467539227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10969670249327290320418421 1028406585874433467539227)
                    ·
                      rfl

theorem cell22_3004222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_3004222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004222 prefixEnd_3004222 := by exact prefixLift 3004222
  have htrace : WordTrace (prefixWord ++ tailWord_3004222) baseStart_3004222 baseEnd_3004222 := by
    simpa [prefixWord, tailWord_3004222, baseEnd_3004222] using wordTrace_append hprefix tailTrace_3004222
  have hstable : (prefixWord ++ tailWord_3004222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004222).length < 2 ^ (prefixWord ++ tailWord_3004222).sum := by decide
  have hdescent : baseEnd_3004222 < baseStart_3004222 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004314 : List Nat := [3, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_3004314 : Nat := 118140960795 + 3004314 * 2 ^ 59
def prefixEnd_3004314 : Nat := 4983230072969 + 3 ^ 40 * 3004314 * 2
def baseEnd_3004314 : Nat := 342812693118191964746315

theorem tailTrace_3004314 : CollatzResearch.WordTrace tailWord_3004314 prefixEnd_3004314 342812693118191964746315 := by
  unfold tailWord_3004314
  simp only [CollatzResearch.WordTrace]
  refine ⟨27394083409472737206662999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73050889091927299217767997 27394083409472737206662999)
  ·
    refine ⟨41091125114209105809994499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27394083409472737206662999 41091125114209105809994499)
    ·
      refine ⟨61636687671313658714991749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41091125114209105809994499 61636687671313658714991749)
      ·
        refine ⟨11556878938371311009060953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61636687671313658714991749 11556878938371311009060953)
        ·
          refine ⟨8667659203778483256795715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11556878938371311009060953 8667659203778483256795715)
          ·
            refine ⟨13001488805667724885193573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8667659203778483256795715 13001488805667724885193573)
            ·
              refine ⟨2437779151062698415973795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13001488805667724885193573 2437779151062698415973795)
              ·
                refine ⟨3656668726594047623960693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437779151062698415973795 3656668726594047623960693)
                ·
                  refine ⟨342812693118191964746315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3656668726594047623960693 342812693118191964746315)
                  ·
                    rfl

theorem cell22_3004314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_3004314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004314 prefixEnd_3004314 := by exact prefixLift 3004314
  have htrace : WordTrace (prefixWord ++ tailWord_3004314) baseStart_3004314 baseEnd_3004314 := by
    simpa [prefixWord, tailWord_3004314, baseEnd_3004314] using wordTrace_append hprefix tailTrace_3004314
  have hstable : (prefixWord ++ tailWord_3004314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004314).length < 2 ^ (prefixWord ++ tailWord_3004314).sum := by decide
  have hdescent : baseEnd_3004314 < baseStart_3004314 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004325 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 6]
def baseStart_3004325 : Nat := 118140960795 + 3004325 * 2 ^ 59
def prefixEnd_3004325 : Nat := 4983230072969 + 3 ^ 40 * 3004325 * 2
def baseEnd_3004325 : Nat := 342813948293125177404637

theorem tailTrace_3004325 : CollatzResearch.WordTrace tailWord_3004325 prefixEnd_3004325 342813948293125177404637 := by
  unfold tailWord_3004325
  simp only [CollatzResearch.WordTrace]
  refine ⟨109576734840851097705302429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73051156560567398470201619 109576734840851097705302429)
  ·
    refine ⟨41091275565319161639488411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109576734840851097705302429 41091275565319161639488411)
    ·
      refine ⟨61636913347978742459232617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41091275565319161639488411 61636913347978742459232617)
      ·
        refine ⟨46227685010984056844424463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61636913347978742459232617 46227685010984056844424463)
        ·
          refine ⟨69341527516476085266636695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46227685010984056844424463 69341527516476085266636695)
          ·
            refine ⟨104012291274714127899955043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69341527516476085266636695 104012291274714127899955043)
            ·
              refine ⟨156018436912071191849932565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104012291274714127899955043 156018436912071191849932565)
              ·
                refine ⟨7313364230253337117965589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156018436912071191849932565 7313364230253337117965589)
                ·
                  refine ⟨342813948293125177404637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7313364230253337117965589 342813948293125177404637)
                  ·
                    rfl

theorem cell22_3004325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 6].length) (baseStart_3004325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004325 prefixEnd_3004325 := by exact prefixLift 3004325
  have htrace : WordTrace (prefixWord ++ tailWord_3004325) baseStart_3004325 baseEnd_3004325 := by
    simpa [prefixWord, tailWord_3004325, baseEnd_3004325] using wordTrace_append hprefix tailTrace_3004325
  have hstable : (prefixWord ++ tailWord_3004325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004325).length < 2 ^ (prefixWord ++ tailWord_3004325).sum := by decide
  have hdescent : baseEnd_3004325 < baseStart_3004325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004344 : List Nat := [2, 1, 2, 1, 2, 3, 5, 1, 1, 4]
def baseStart_3004344 : Nat := 118140960795 + 3004344 * 2 ^ 59
def prefixEnd_3004344 : Nat := 4983230072969 + 3 ^ 40 * 3004344 * 2
def baseEnd_3004344 : Nat := 1028448348967665815988853

theorem tailTrace_3004344 : CollatzResearch.WordTrace tailWord_3004344 prefixEnd_3004344 1028448348967665815988853 := by
  unfold tailWord_3004344
  simp only [CollatzResearch.WordTrace]
  refine ⟨54788713913891131975122043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73051618551854842633496057 54788713913891131975122043)
  ·
    refine ⟨82183070870836697962683065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54788713913891131975122043 82183070870836697962683065)
    ·
      refine ⟨61637303153127523472012299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82183070870836697962683065 61637303153127523472012299)
      ·
        refine ⟨92455954729691285208018449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61637303153127523472012299 92455954729691285208018449)
        ·
          refine ⟨69341966047268463906013837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92455954729691285208018449 69341966047268463906013837)
          ·
            refine ⟨26003237267725673964755189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69341966047268463906013837 26003237267725673964755189)
            ·
              refine ⟨2437803493849281934195799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26003237267725673964755189 2437803493849281934195799)
              ·
                refine ⟨3656705240773922901293699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2437803493849281934195799 3656705240773922901293699)
                ·
                  refine ⟨5485057861160884351940549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3656705240773922901293699 5485057861160884351940549)
                  ·
                    refine ⟨1028448348967665815988853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5485057861160884351940549 1028448348967665815988853)
                    ·
                      rfl

theorem cell22_3004344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_3004344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004344 prefixEnd_3004344 := by exact prefixLift 3004344
  have htrace : WordTrace (prefixWord ++ tailWord_3004344) baseStart_3004344 baseEnd_3004344 := by
    simpa [prefixWord, tailWord_3004344, baseEnd_3004344] using wordTrace_append hprefix tailTrace_3004344
  have hstable : (prefixWord ++ tailWord_3004344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004344).length < 2 ^ (prefixWord ++ tailWord_3004344).sum := by decide
  have hdescent : baseEnd_3004344 < baseStart_3004344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004372 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_3004372 : Nat := 118140960795 + 3004372 * 2 ^ 59
def prefixEnd_3004372 : Nat := 4983230072969 + 3 ^ 40 * 3004372 * 2
def baseEnd_3004372 : Nat := 1028457933939883076288767

theorem tailTrace_3004372 : CollatzResearch.WordTrace tailWord_3004372 prefixEnd_3004372 1028457933939883076288767 := by
  unfold tailWord_3004372
  simp only [CollatzResearch.WordTrace]
  refine ⟨54789224535840412366131685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73052299381120549821508913 54789224535840412366131685)
  ·
    refine ⟨10272979600470077318649691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54789224535840412366131685 10272979600470077318649691)
    ·
      refine ⟨15409469400705115977974537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10272979600470077318649691 15409469400705115977974537)
      ·
        refine ⟨11557102050528836983480903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15409469400705115977974537 11557102050528836983480903)
        ·
          refine ⟨17335653075793255475221355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11557102050528836983480903 17335653075793255475221355)
          ·
            refine ⟨26003479613689883212832033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17335653075793255475221355 26003479613689883212832033)
            ·
              refine ⟨19502609710267412409624025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26003479613689883212832033 19502609710267412409624025)
              ·
                refine ⟨14626957282700559307218019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19502609710267412409624025 14626957282700559307218019)
                ·
                  refine ⟨21940435924050838960827029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14626957282700559307218019 21940435924050838960827029)
                  ·
                    refine ⟨1028457933939883076288767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21940435924050838960827029 1028457933939883076288767)
                    ·
                      rfl

theorem cell22_3004372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_3004372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004372 prefixEnd_3004372 := by exact prefixLift 3004372
  have htrace : WordTrace (prefixWord ++ tailWord_3004372) baseStart_3004372 baseEnd_3004372 := by
    simpa [prefixWord, tailWord_3004372, baseEnd_3004372] using wordTrace_append hprefix tailTrace_3004372
  have hstable : (prefixWord ++ tailWord_3004372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004372).length < 2 ^ (prefixWord ++ tailWord_3004372).sum := by decide
  have hdescent : baseEnd_3004372 < baseStart_3004372 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004453 : List Nat := [1, 3, 1, 2, 2, 5, 1, 3, 1, 3]
def baseStart_3004453 : Nat := 118140960795 + 3004453 * 2 ^ 59
def prefixEnd_3004453 : Nat := 4983230072969 + 3 ^ 40 * 3004453 * 2
def baseEnd_3004453 : Nat := 1028485661895225865013519

theorem tailTrace_3004453 : CollatzResearch.WordTrace tailWord_3004453 prefixEnd_3004453 1028485661895225865013519 := by
  unfold tailWord_3004453
  simp only [CollatzResearch.WordTrace]
  refine ⟨109581403384387375565962013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73054268922924917043974675 109581403384387375565962013)
  ·
    refine ⟨41093026269145265837235755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109581403384387375565962013 41093026269145265837235755)
    ·
      refine ⟨61639539403717898755853633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41093026269145265837235755 61639539403717898755853633)
      ·
        refine ⟨46229654552788424066890225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61639539403717898755853633 46229654552788424066890225)
        ·
          refine ⟨34672240914591318050167669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46229654552788424066890225 34672240914591318050167669)
          ·
            refine ⟨3250522585742936067203219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34672240914591318050167669 3250522585742936067203219)
            ·
              refine ⟨4875783878614404100804829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250522585742936067203219 4875783878614404100804829)
              ·
                refine ⟨1828418954480401537801811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4875783878614404100804829 1828418954480401537801811)
                ·
                  refine ⟨2742628431720602306702717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828418954480401537801811 2742628431720602306702717)
                  ·
                    refine ⟨1028485661895225865013519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2742628431720602306702717 1028485661895225865013519)
                    ·
                      rfl

theorem cell22_3004453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 3, 1, 3].length) (baseStart_3004453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004453 prefixEnd_3004453 := by exact prefixLift 3004453
  have htrace : WordTrace (prefixWord ++ tailWord_3004453) baseStart_3004453 baseEnd_3004453 := by
    simpa [prefixWord, tailWord_3004453, baseEnd_3004453] using wordTrace_append hprefix tailTrace_3004453
  have hstable : (prefixWord ++ tailWord_3004453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004453).length < 2 ^ (prefixWord ++ tailWord_3004453).sum := by decide
  have hdescent : baseEnd_3004453 < baseStart_3004453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004470 : List Nat := [5, 1, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_3004470 : Nat := 118140960795 + 3004470 * 2 ^ 59
def prefixEnd_3004470 : Nat := 4983230072969 + 3 ^ 40 * 3004470 * 2
def baseEnd_3004470 : Nat := 1028491481342643487338467

theorem tailTrace_3004470 : CollatzResearch.WordTrace tailWord_3004470 prefixEnd_3004470 1028491481342643487338467 := by
  unfold tailWord_3004470
  simp only [CollatzResearch.WordTrace]
  refine ⟨6848876464082861716833179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73054682283550524979553909 6848876464082861716833179)
  ·
    refine ⟨10273314696124292575249769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6848876464082861716833179 10273314696124292575249769)
    ·
      refine ⟨7704986022093219431437327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10273314696124292575249769 7704986022093219431437327)
      ·
        refine ⟨11557479033139829147155991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7704986022093219431437327 11557479033139829147155991)
        ·
          refine ⟨17336218549709743720733987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11557479033139829147155991 17336218549709743720733987)
          ·
            refine ⟨26004327824564615581100981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17336218549709743720733987 26004327824564615581100981)
            ·
              refine ⟨2437905733552932710728217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26004327824564615581100981 2437905733552932710728217)
              ·
                refine ⟨1828429300164699533046163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2437905733552932710728217 1828429300164699533046163)
                ·
                  refine ⟨2742643950247049299569245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828429300164699533046163 2742643950247049299569245)
                  ·
                    refine ⟨1028491481342643487338467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2742643950247049299569245 1028491481342643487338467)
                    ·
                      rfl

theorem cell22_3004470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_3004470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004470 prefixEnd_3004470 := by exact prefixLift 3004470
  have htrace : WordTrace (prefixWord ++ tailWord_3004470) baseStart_3004470 baseEnd_3004470 := by
    simpa [prefixWord, tailWord_3004470, baseEnd_3004470] using wordTrace_append hprefix tailTrace_3004470
  have hstable : (prefixWord ++ tailWord_3004470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004470).length < 2 ^ (prefixWord ++ tailWord_3004470).sum := by decide
  have hdescent : baseEnd_3004470 < baseStart_3004470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004522 : List Nat := [3, 1, 3, 2, 13]
def baseStart_3004522 : Nat := 118140960795 + 3004522 * 2 ^ 59
def prefixEnd_3004522 : Nat := 4983230072969 + 3 ^ 40 * 3004522 * 2
def baseEnd_3004522 : Nat := 4232548485618653024849

theorem tailTrace_3004522 : CollatzResearch.WordTrace tailWord_3004522 prefixEnd_3004522 4232548485618653024849 := by
  unfold tailWord_3004522
  simp only [CollatzResearch.WordTrace]
  refine ⟨27395980005284350087555955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73055946680758266900149213 27395980005284350087555955)
  ·
    refine ⟨41093970007926525131333933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27395980005284350087555955 41093970007926525131333933)
    ·
      refine ⟨15410238752972446924250225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41093970007926525131333933 15410238752972446924250225)
      ·
        refine ⟨11557679064729335193187669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15410238752972446924250225 11557679064729335193187669)
        ·
          refine ⟨4232548485618653024849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 11557679064729335193187669 4232548485618653024849)
          ·
            rfl

theorem cell22_3004522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 13].length) (baseStart_3004522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004522 prefixEnd_3004522 := by exact prefixLift 3004522
  have htrace : WordTrace (prefixWord ++ tailWord_3004522) baseStart_3004522 baseEnd_3004522 := by
    simpa [prefixWord, tailWord_3004522, baseEnd_3004522] using wordTrace_append hprefix tailTrace_3004522
  have hstable : (prefixWord ++ tailWord_3004522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004522).length < 2 ^ (prefixWord ++ tailWord_3004522).sum := by decide
  have hdescent : baseEnd_3004522 < baseStart_3004522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004524 : List Nat := [2, 2, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_3004524 : Nat := 118140960795 + 3004524 * 2 ^ 59
def prefixEnd_3004524 : Nat := 4983230072969 + 3 ^ 40 * 3004524 * 2
def baseEnd_3004524 : Nat := 1028509966646205346488301

theorem tailTrace_3004524 : CollatzResearch.WordTrace tailWord_3004524 prefixEnd_3004524 1028509966646205346488301 := by
  unfold tailWord_3004524
  simp only [CollatzResearch.WordTrace]
  refine ⟨54791996483565077345898313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73055995311420103127864417 54791996483565077345898313)
  ·
    refine ⟨41093997362673808009423735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54791996483565077345898313 41093997362673808009423735)
    ·
      refine ⟨61640996044010712014135603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41093997362673808009423735 61640996044010712014135603)
      ·
        refine ⟨92461494066016068021203405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61640996044010712014135603 92461494066016068021203405)
        ·
          refine ⟨34673060274756025507951277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92461494066016068021203405 34673060274756025507951277)
          ·
            refine ⟨13002397603033509565481729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34673060274756025507951277 13002397603033509565481729)
            ·
              refine ⟨9751798202275132174111297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13002397603033509565481729 9751798202275132174111297)
              ·
                refine ⟨7313848651706349130583473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9751798202275132174111297 7313848651706349130583473)
                ·
                  refine ⟨5485386488779761847937605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7313848651706349130583473 5485386488779761847937605)
                  ·
                    refine ⟨1028509966646205346488301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5485386488779761847937605 1028509966646205346488301)
                    ·
                      rfl

theorem cell22_3004524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_3004524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004524 prefixEnd_3004524 := by exact prefixLift 3004524
  have htrace : WordTrace (prefixWord ++ tailWord_3004524) baseStart_3004524 baseEnd_3004524 := by
    simpa [prefixWord, tailWord_3004524, baseEnd_3004524] using wordTrace_append hprefix tailTrace_3004524
  have hstable : (prefixWord ++ tailWord_3004524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004524).length < 2 ^ (prefixWord ++ tailWord_3004524).sum := by decide
  have hdescent : baseEnd_3004524 < baseStart_3004524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004528 : List Nat := [2, 1, 1, 1, 5, 4, 2, 2, 4]
def baseStart_3004528 : Nat := 118140960795 + 3004528 * 2 ^ 59
def prefixEnd_3004528 : Nat := 4983230072969 + 3 ^ 40 * 3004528 * 2
def baseEnd_3004528 : Nat := 342837111975983556462763

theorem tailTrace_3004528 : CollatzResearch.WordTrace tailWord_3004528 prefixEnd_3004528 342837111975983556462763 := by
  unfold tailWord_3004528
  simp only [CollatzResearch.WordTrace]
  refine ⟨54792069429557831687471119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73056092572743775583294825 54792069429557831687471119)
  ·
    refine ⟨82188104144336747531206679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54792069429557831687471119 82188104144336747531206679)
    ·
      refine ⟨123282156216505121296810019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82188104144336747531206679 123282156216505121296810019)
      ·
        refine ⟨184923234324757681945215029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123282156216505121296810019 184923234324757681945215029)
        ·
          refine ⟨17336553217946032682363909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 184923234324757681945215029 17336553217946032682363909)
          ·
            refine ⟨3250603728364881127943233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17336553217946032682363909 3250603728364881127943233)
            ·
              refine ⟨2437952796273660845957425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3250603728364881127943233 2437952796273660845957425)
              ·
                refine ⟨1828464597205245634468069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2437952796273660845957425 1828464597205245634468069)
                ·
                  refine ⟨342837111975983556462763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1828464597205245634468069 342837111975983556462763)
                  ·
                    rfl

theorem cell22_3004528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 2, 4].length) (baseStart_3004528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004528 prefixEnd_3004528 := by exact prefixLift 3004528
  have htrace : WordTrace (prefixWord ++ tailWord_3004528) baseStart_3004528 baseEnd_3004528 := by
    simpa [prefixWord, tailWord_3004528, baseEnd_3004528] using wordTrace_append hprefix tailTrace_3004528
  have hstable : (prefixWord ++ tailWord_3004528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004528).length < 2 ^ (prefixWord ++ tailWord_3004528).sum := by decide
  have hdescent : baseEnd_3004528 < baseStart_3004528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004558 : List Nat := [4, 1, 1, 3, 3, 2, 1, 1, 2, 4]
def baseStart_3004558 : Nat := 118140960795 + 3004558 * 2 ^ 59
def prefixEnd_3004558 : Nat := 4983230072969 + 3 ^ 40 * 3004558 * 2
def baseEnd_3004558 : Nat := 1028521605541040591138197

theorem tailTrace_3004558 : CollatzResearch.WordTrace tailWord_3004558 prefixEnd_3004558 1028521605541040591138197 := by
  unfold tailWord_3004558
  simp only [CollatzResearch.WordTrace]
  refine ⟨13698154131125872312316791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73056822032671318999022885 13698154131125872312316791)
  ·
    refine ⟨20547231196688808468475187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13698154131125872312316791 20547231196688808468475187)
    ·
      refine ⟨30820846795033212702712781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20547231196688808468475187 30820846795033212702712781)
      ·
        refine ⟨11557817548137454763517293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30820846795033212702712781 11557817548137454763517293)
        ·
          refine ⟨4334181580551545536318985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11557817548137454763517293 4334181580551545536318985)
          ·
            refine ⟨3250636185413659152239239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4334181580551545536318985 3250636185413659152239239)
            ·
              refine ⟨4875954278120488728358859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250636185413659152239239 4875954278120488728358859)
              ·
                refine ⟨7313931417180733092538289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4875954278120488728358859 7313931417180733092538289)
                ·
                  refine ⟨5485448562885549819403717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7313931417180733092538289 5485448562885549819403717)
                  ·
                    refine ⟨1028521605541040591138197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5485448562885549819403717 1028521605541040591138197)
                    ·
                      rfl

theorem cell22_3004558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 1, 2, 4].length) (baseStart_3004558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004558 prefixEnd_3004558 := by exact prefixLift 3004558
  have htrace : WordTrace (prefixWord ++ tailWord_3004558) baseStart_3004558 baseEnd_3004558 := by
    simpa [prefixWord, tailWord_3004558, baseEnd_3004558] using wordTrace_append hprefix tailTrace_3004558
  have hstable : (prefixWord ++ tailWord_3004558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004558).length < 2 ^ (prefixWord ++ tailWord_3004558).sum := by decide
  have hdescent : baseEnd_3004558 < baseStart_3004558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004599 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 2, 5]
def baseStart_3004599 : Nat := 118140960795 + 3004599 * 2 ^ 59
def prefixEnd_3004599 : Nat := 4983230072969 + 3 ^ 40 * 3004599 * 2
def baseEnd_3004599 : Nat := 1028535640678930150863071

theorem tailTrace_3004599 : CollatzResearch.WordTrace tailWord_3004599 prefixEnd_3004599 1028535640678930150863071 := by
  unfold tailWord_3004599
  simp only [CollatzResearch.WordTrace]
  refine ⟨109586728441858442500776851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73057818961238961667184567 109586728441858442500776851)
  ·
    refine ⟨164380092662787663751165277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109586728441858442500776851 164380092662787663751165277)
    ·
      refine ⟨61642534748545373906686979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164380092662787663751165277 61642534748545373906686979)
      ·
        refine ⟨92463802122818060860030469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61642534748545373906686979 92463802122818060860030469)
        ·
          refine ⟨17336962898028386411255713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92463802122818060860030469 17336962898028386411255713)
          ·
            refine ⟨13002722173521289808441785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17336962898028386411255713 13002722173521289808441785)
            ·
              refine ⟨9752041630140967356331339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13002722173521289808441785 9752041630140967356331339)
              ·
                refine ⟨14628062445211451034497009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9752041630140967356331339 14628062445211451034497009)
                ·
                  refine ⟨10971046833908588275872757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14628062445211451034497009 10971046833908588275872757)
                  ·
                    refine ⟨1028535640678930150863071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10971046833908588275872757 1028535640678930150863071)
                    ·
                      rfl

theorem cell22_3004599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_3004599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004599 prefixEnd_3004599 := by exact prefixLift 3004599
  have htrace : WordTrace (prefixWord ++ tailWord_3004599) baseStart_3004599 baseEnd_3004599 := by
    simpa [prefixWord, tailWord_3004599, baseEnd_3004599] using wordTrace_append hprefix tailTrace_3004599
  have hstable : (prefixWord ++ tailWord_3004599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004599).length < 2 ^ (prefixWord ++ tailWord_3004599).sum := by decide
  have hdescent : baseEnd_3004599 < baseStart_3004599 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004601 : List Nat := [1, 2, 1, 4, 1, 2, 5, 1, 5]
def baseStart_3004601 : Nat := 118140960795 + 3004601 * 2 ^ 59
def prefixEnd_3004601 : Nat := 4983230072969 + 3 ^ 40 * 3004601 * 2
def baseEnd_3004601 : Nat := 342845441773267604104355

theorem tailTrace_3004601 : CollatzResearch.WordTrace tailWord_3004601 prefixEnd_3004601 342845441773267604104355 := by
  unfold tailWord_3004601
  simp only [CollatzResearch.WordTrace]
  refine ⟨109586801387851196842349657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73057867591900797894899771 109586801387851196842349657)
  ·
    refine ⟨82190101040888397631762243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109586801387851196842349657 82190101040888397631762243)
    ·
      refine ⟨123285151561332596447643365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82190101040888397631762243 123285151561332596447643365)
      ·
        refine ⟨23115965917749861833933131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123285151561332596447643365 23115965917749861833933131)
        ·
          refine ⟨34673948876624792750899697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23115965917749861833933131 34673948876624792750899697)
          ·
            refine ⟨26005461657468594563174773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34673948876624792750899697 26005461657468594563174773)
            ·
              refine ⟨2438012030387680740297635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 26005461657468594563174773 2438012030387680740297635)
              ·
                refine ⟨3657018045581521110446453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438012030387680740297635 3657018045581521110446453)
                ·
                  refine ⟨342845441773267604104355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3657018045581521110446453 342845441773267604104355)
                  ·
                    rfl

theorem cell22_3004601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 5, 1, 5].length) (baseStart_3004601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004601 prefixEnd_3004601 := by exact prefixLift 3004601
  have htrace : WordTrace (prefixWord ++ tailWord_3004601) baseStart_3004601 baseEnd_3004601 := by
    simpa [prefixWord, tailWord_3004601, baseEnd_3004601] using wordTrace_append hprefix tailTrace_3004601
  have hstable : (prefixWord ++ tailWord_3004601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004601).length < 2 ^ (prefixWord ++ tailWord_3004601).sum := by decide
  have hdescent : baseEnd_3004601 < baseStart_3004601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004659 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 4, 4]
def baseStart_3004659 : Nat := 118140960795 + 3004659 * 2 ^ 59
def prefixEnd_3004659 : Nat := 4983230072969 + 3 ^ 40 * 3004659 * 2
def baseEnd_3004659 : Nat := 1028556179905109994362887

theorem tailTrace_3004659 : CollatzResearch.WordTrace tailWord_3004659 prefixEnd_3004659 1028556179905109994362887 := by
  unfold tailWord_3004659
  simp only [CollatzResearch.WordTrace]
  refine ⟨109588916821641072747961031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73059277881094048498640687 109588916821641072747961031)
  ·
    refine ⟨164383375232461609121941547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109588916821641072747961031 164383375232461609121941547)
    ·
      refine ⟨246575062848692413682912321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164383375232461609121941547 246575062848692413682912321)
      ·
        refine ⟨184931297136519310262184241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 246575062848692413682912321 184931297136519310262184241)
        ·
          refine ⟨138698472852389482696638181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 184931297136519310262184241 138698472852389482696638181)
          ·
            refine ⟨26005963659823028005619659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 138698472852389482696638181 26005963659823028005619659)
            ·
              refine ⟨39008945489734542008429489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26005963659823028005619659 39008945489734542008429489)
              ·
                refine ⟨29256709117300906506322117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39008945489734542008429489 29256709117300906506322117)
                ·
                  refine ⟨5485632959493919969935397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29256709117300906506322117 5485632959493919969935397)
                  ·
                    refine ⟨1028556179905109994362887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5485632959493919969935397 1028556179905109994362887)
                    ·
                      rfl

theorem cell22_3004659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 4].length) (baseStart_3004659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004659 prefixEnd_3004659 := by exact prefixLift 3004659
  have htrace : WordTrace (prefixWord ++ tailWord_3004659) baseStart_3004659 baseEnd_3004659 := by
    simpa [prefixWord, tailWord_3004659, baseEnd_3004659] using wordTrace_append hprefix tailTrace_3004659
  have hstable : (prefixWord ++ tailWord_3004659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004659).length < 2 ^ (prefixWord ++ tailWord_3004659).sum := by decide
  have hdescent : baseEnd_3004659 < baseStart_3004659 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004753 : List Nat := [1, 2, 2, 1, 4, 4, 1, 2, 5]
def baseStart_3004753 : Nat := 118140960795 + 3004753 * 2 ^ 59
def prefixEnd_3004753 : Nat := 4983230072969 + 3 ^ 40 * 3004753 * 2
def baseEnd_3004753 : Nat := 342862786008708360837533

theorem tailTrace_3004753 : CollatzResearch.WordTrace tailWord_3004753 prefixEnd_3004753 342862786008708360837533 := by
  unfold tailWord_3004753
  simp only [CollatzResearch.WordTrace]
  refine ⟨109592345283300526801882913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73061563522200351201255275 109592345283300526801882913)
  ·
    refine ⟨82194258962475395101412185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109592345283300526801882913 82194258962475395101412185)
    ·
      refine ⟨61645694221856546326059139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82194258962475395101412185 61645694221856546326059139)
      ·
        refine ⟨92468541332784819489088709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61645694221856546326059139 92468541332784819489088709)
        ·
          refine ⟨17337851499897153654204133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92468541332784819489088709 17337851499897153654204133)
          ·
            refine ⟨3250847156230716310163275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17337851499897153654204133 3250847156230716310163275)
            ·
              refine ⟨4876270734346074465244913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3250847156230716310163275 4876270734346074465244913)
              ·
                refine ⟨3657203050759555848933685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4876270734346074465244913 3657203050759555848933685)
                ·
                  refine ⟨342862786008708360837533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3657203050759555848933685 342862786008708360837533)
                  ·
                    rfl

theorem cell22_3004753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 2, 5].length) (baseStart_3004753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004753 prefixEnd_3004753 := by exact prefixLift 3004753
  have htrace : WordTrace (prefixWord ++ tailWord_3004753) baseStart_3004753 baseEnd_3004753 := by
    simpa [prefixWord, tailWord_3004753, baseEnd_3004753] using wordTrace_append hprefix tailTrace_3004753
  have hstable : (prefixWord ++ tailWord_3004753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004753).length < 2 ^ (prefixWord ++ tailWord_3004753).sum := by decide
  have hdescent : baseEnd_3004753 < baseStart_3004753 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004770 : List Nat := [3, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_3004770 : Nat := 118140960795 + 3004770 * 2 ^ 59
def prefixEnd_3004770 : Nat := 4983230072969 + 3 ^ 40 * 3004770 * 2
def baseEnd_3004770 : Nat := 342864725824514234945849

theorem tailTrace_3004770 : CollatzResearch.WordTrace tailWord_3004770 prefixEnd_3004770 342864725824514234945849 := by
  unfold tailWord_3004770
  simp only [CollatzResearch.WordTrace]
  refine ⟨27398241331059734676312941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73061976882825959136834509 27398241331059734676312941)
  ·
    refine ⟨10274340499147400503617353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27398241331059734676312941 10274340499147400503617353)
    ·
      refine ⟨7705755374360550377713015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10274340499147400503617353 7705755374360550377713015)
      ·
        refine ⟨11558633061540825566569523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7705755374360550377713015 11558633061540825566569523)
        ·
          refine ⟨17337949592311238349854285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11558633061540825566569523 17337949592311238349854285)
          ·
            refine ⟨6501731097116714381195357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17337949592311238349854285 6501731097116714381195357)
            ·
              refine ⟨2438149161418767892948259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6501731097116714381195357 2438149161418767892948259)
              ·
                refine ⟨3657223742128151839422389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438149161418767892948259 3657223742128151839422389)
                ·
                  refine ⟨342864725824514234945849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3657223742128151839422389 342864725824514234945849)
                  ·
                    rfl

theorem cell22_3004770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_3004770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004770 prefixEnd_3004770 := by exact prefixLift 3004770
  have htrace : WordTrace (prefixWord ++ tailWord_3004770) baseStart_3004770 baseEnd_3004770 := by
    simpa [prefixWord, tailWord_3004770, baseEnd_3004770] using wordTrace_append hprefix tailTrace_3004770
  have hstable : (prefixWord ++ tailWord_3004770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004770).length < 2 ^ (prefixWord ++ tailWord_3004770).sum := by decide
  have hdescent : baseEnd_3004770 < baseStart_3004770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004781 : List Nat := [1, 5, 1, 1, 1, 2, 1, 4, 6]
def baseStart_3004781 : Nat := 118140960795 + 3004781 * 2 ^ 59
def prefixEnd_3004781 : Nat := 4983230072969 + 3 ^ 40 * 3004781 * 2
def baseEnd_3004781 : Nat := 342865980999447447604171

theorem tailTrace_3004781 : CollatzResearch.WordTrace tailWord_3004781 prefixEnd_3004781 342865980999447447604171 := by
  unfold tailWord_3004781
  simp only [CollatzResearch.WordTrace]
  refine ⟨109593366527199087583902197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73062244351466058389268131 109593366527199087583902197)
  ·
    refine ⟨10274378111924914460990831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109593366527199087583902197 10274378111924914460990831)
    ·
      refine ⟨15411567167887371691486247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10274378111924914460990831 15411567167887371691486247)
      ·
        refine ⟨23117350751831057537229371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15411567167887371691486247 23117350751831057537229371)
        ·
          refine ⟨34676026127746586305844057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23117350751831057537229371 34676026127746586305844057)
          ·
            refine ⟨26007019595809939729383043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34676026127746586305844057 26007019595809939729383043)
            ·
              refine ⟨39010529393714909594074565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26007019595809939729383043 39010529393714909594074565)
              ·
                refine ⟨7314474261321545548888981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39010529393714909594074565 7314474261321545548888981)
                ·
                  refine ⟨342865980999447447604171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7314474261321545548888981 342865980999447447604171)
                  ·
                    rfl

theorem cell22_3004781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_3004781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004781 prefixEnd_3004781 := by exact prefixLift 3004781
  have htrace : WordTrace (prefixWord ++ tailWord_3004781) baseStart_3004781 baseEnd_3004781 := by
    simpa [prefixWord, tailWord_3004781, baseEnd_3004781] using wordTrace_append hprefix tailTrace_3004781
  have hstable : (prefixWord ++ tailWord_3004781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004781).length < 2 ^ (prefixWord ++ tailWord_3004781).sum := by decide
  have hdescent : baseEnd_3004781 < baseStart_3004781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004811 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 4, 4]
def baseStart_3004811 : Nat := 118140960795 + 3004811 * 2 ^ 59
def prefixEnd_3004811 : Nat := 4983230072969 + 3 ^ 40 * 3004811 * 2
def baseEnd_3004811 : Nat := 1028608212611432264562421

theorem tailTrace_3004811 : CollatzResearch.WordTrace tailWord_3004811 prefixEnd_3004811 1028608212611432264562421 := by
  unfold tailWord_3004811
  simp only [CollatzResearch.WordTrace]
  refine ⟨109594460717090402707494287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73062973811393601804996191 109594460717090402707494287)
  ·
    refine ⟨164391691075635604061241431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109594460717090402707494287 164391691075635604061241431)
    ·
      refine ⟨246587536613453406091862147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164391691075635604061241431 246587536613453406091862147)
      ·
        refine ⟨369881304920180109137793221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 246587536613453406091862147 369881304920180109137793221)
        ·
          refine ⟨69352744672533770463336229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 369881304920180109137793221 69352744672533770463336229)
          ·
            refine ⟨13003639626100081961875543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69352744672533770463336229 13003639626100081961875543)
            ·
              refine ⟨19505459439150122942813315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13003639626100081961875543 19505459439150122942813315)
              ·
                refine ⟨29258189158725184414219973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19505459439150122942813315 29258189158725184414219973)
                ·
                  refine ⟨5485910467260972077666245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29258189158725184414219973 5485910467260972077666245)
                  ·
                    refine ⟨1028608212611432264562421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5485910467260972077666245 1028608212611432264562421)
                    ·
                      rfl

theorem cell22_3004811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 4].length) (baseStart_3004811 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004811 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004811 prefixEnd_3004811 := by exact prefixLift 3004811
  have htrace : WordTrace (prefixWord ++ tailWord_3004811) baseStart_3004811 baseEnd_3004811 := by
    simpa [prefixWord, tailWord_3004811, baseEnd_3004811] using wordTrace_append hprefix tailTrace_3004811
  have hstable : (prefixWord ++ tailWord_3004811).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004811).length < 2 ^ (prefixWord ++ tailWord_3004811).sum := by decide
  have hdescent : baseEnd_3004811 < baseStart_3004811 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004826 : List Nat := [3, 1, 1, 4, 1, 2, 1, 9]
def baseStart_3004826 : Nat := 118140960795 + 3004826 * 2 ^ 59
def prefixEnd_3004826 : Nat := 4983230072969 + 3 ^ 40 * 3004826 * 2
def baseEnd_3004826 : Nat := 114290371935330802826375

theorem tailTrace_3004826 : CollatzResearch.WordTrace tailWord_3004826 prefixEnd_3004826 114290371935330802826375 := by
  unfold tailWord_3004826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27398751953009015067322583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73063338541357373512860221 27398751953009015067322583)
  ·
    refine ⟨41098127929513522600983875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27398751953009015067322583 41098127929513522600983875)
    ·
      refine ⟨61647191894270283901475813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41098127929513522600983875 61647191894270283901475813)
      ·
        refine ⟨11558848480175678231526715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61647191894270283901475813 11558848480175678231526715)
        ·
          refine ⟨17338272720263517347290073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11558848480175678231526715 17338272720263517347290073)
          ·
            refine ⟨13003704540197638010467555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17338272720263517347290073 13003704540197638010467555)
            ·
              refine ⟨19505556810296457015701333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13003704540197638010467555 19505556810296457015701333)
              ·
                refine ⟨114290371935330802826375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19505556810296457015701333 114290371935330802826375)
                ·
                  rfl

theorem cell22_3004826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 9].length) (baseStart_3004826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004826 prefixEnd_3004826 := by exact prefixLift 3004826
  have htrace : WordTrace (prefixWord ++ tailWord_3004826) baseStart_3004826 baseEnd_3004826 := by
    simpa [prefixWord, tailWord_3004826, baseEnd_3004826] using wordTrace_append hprefix tailTrace_3004826
  have hstable : (prefixWord ++ tailWord_3004826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004826).length < 2 ^ (prefixWord ++ tailWord_3004826).sum := by decide
  have hdescent : baseEnd_3004826 < baseStart_3004826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004909 : List Nat := [1, 5, 1, 3, 1, 2, 2, 3, 1, 3]
def baseStart_3004909 : Nat := 118140960795 + 3004909 * 2 ^ 59
def prefixEnd_3004909 : Nat := 4983230072969 + 3 ^ 40 * 3004909 * 2
def baseEnd_3004909 : Nat := 1028641760014192675612121

theorem tailTrace_3004909 : CollatzResearch.WordTrace tailWord_3004909 prefixEnd_3004909 1028641760014192675612121 := by
  unfold tailWord_3004909
  simp only [CollatzResearch.WordTrace]
  refine ⟨109598035070735365444561781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73065356713823576963041187 109598035070735365444561781)
  ·
    refine ⟨10274815787881440510427667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 109598035070735365444561781 10274815787881440510427667)
    ·
      refine ⟨15412223681822160765641501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10274815787881440510427667 15412223681822160765641501)
      ·
        refine ⟨5779583880683310287115563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15412223681822160765641501 5779583880683310287115563)
        ·
          refine ⟨8669375821024965430673345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5779583880683310287115563 8669375821024965430673345)
          ·
            refine ⟨6502031865768724073005009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8669375821024965430673345 6502031865768724073005009)
            ·
              refine ⟨4876523899326543054753757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6502031865768724073005009 4876523899326543054753757)
              ·
                refine ⟨1828696462247453645532659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4876523899326543054753757 1828696462247453645532659)
                ·
                  refine ⟨2743044693371180468298989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828696462247453645532659 2743044693371180468298989)
                  ·
                    refine ⟨1028641760014192675612121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743044693371180468298989 1028641760014192675612121)
                    ·
                      rfl

theorem cell22_3004909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_3004909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004909 prefixEnd_3004909 := by exact prefixLift 3004909
  have htrace : WordTrace (prefixWord ++ tailWord_3004909) baseStart_3004909 baseEnd_3004909 := by
    simpa [prefixWord, tailWord_3004909, baseEnd_3004909] using wordTrace_append hprefix tailTrace_3004909
  have hstable : (prefixWord ++ tailWord_3004909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004909).length < 2 ^ (prefixWord ++ tailWord_3004909).sum := by decide
  have hdescent : baseEnd_3004909 < baseStart_3004909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004963 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 1, 6]
def baseStart_3004963 : Nat := 118140960795 + 3004963 * 2 ^ 59
def prefixEnd_3004963 : Nat := 4983230072969 + 3 ^ 40 * 3004963 * 2
def baseEnd_3004963 : Nat := 1028660245317754534761955

theorem tailTrace_3004963 : CollatzResearch.WordTrace tailWord_3004963 prefixEnd_3004963 1028660245317754534761955 := by
  unfold tailWord_3004963
  simp only [CollatzResearch.WordTrace]
  refine ⟨109600004612539732667027543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73066669741693155111351695 109600004612539732667027543)
  ·
    refine ⟨164400006918809599000541315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109600004612539732667027543 164400006918809599000541315)
    ·
      refine ⟨246600010378214398500811973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164400006918809599000541315 246600010378214398500811973)
      ·
        refine ⟨46237501945915199718902245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 246600010378214398500811973 46237501945915199718902245)
        ·
          refine ⟨8669531614859099947294171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46237501945915199718902245 8669531614859099947294171)
          ·
            refine ⟨13004297422288649920941257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8669531614859099947294171 13004297422288649920941257)
            ·
              refine ⟨9753223066716487440705943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13004297422288649920941257 9753223066716487440705943)
              ·
                refine ⟨14629834600074731161058915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9753223066716487440705943 14629834600074731161058915)
                ·
                  refine ⟨21944751900112096741588373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14629834600074731161058915 21944751900112096741588373)
                  ·
                    refine ⟨1028660245317754534761955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21944751900112096741588373 1028660245317754534761955)
                    ·
                      rfl

theorem cell22_3004963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 6].length) (baseStart_3004963 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004963 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004963 prefixEnd_3004963 := by exact prefixLift 3004963
  have htrace : WordTrace (prefixWord ++ tailWord_3004963) baseStart_3004963 baseEnd_3004963 := by
    simpa [prefixWord, tailWord_3004963, baseEnd_3004963] using wordTrace_append hprefix tailTrace_3004963
  have hstable : (prefixWord ++ tailWord_3004963).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004963).length < 2 ^ (prefixWord ++ tailWord_3004963).sum := by decide
  have hdescent : baseEnd_3004963 < baseStart_3004963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004982 : List Nat := [5, 1, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_3004982 : Nat := 118140960795 + 3004982 * 2 ^ 59
def prefixEnd_3004982 : Nat := 4983230072969 + 3 ^ 40 * 3004982 * 2
def baseEnd_3004982 : Nat := 1028666749406044818536897

theorem tailTrace_3004982 : CollatzResearch.WordTrace tailWord_3004982 prefixEnd_3004982 1028666749406044818536897 := by
  unfold tailWord_3004982
  simp only [CollatzResearch.WordTrace]
  refine ⟨6850043599966931181998075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73067131732980599274646133 6850043599966931181998075)
  ·
    refine ⟨10275065399950396772997113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6850043599966931181998075 10275065399950396772997113)
    ·
      refine ⟨7706299049962797579747835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10275065399950396772997113 7706299049962797579747835)
      ·
        refine ⟨11559448574944196369621753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7706299049962797579747835 11559448574944196369621753)
        ·
          refine ⟨8669586431208147277216315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11559448574944196369621753 8669586431208147277216315)
          ·
            refine ⟨13004379646812220915824473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8669586431208147277216315 13004379646812220915824473)
            ·
              refine ⟨9753284735109165686868355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13004379646812220915824473 9753284735109165686868355)
              ·
                refine ⟨14629927102663748530302533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9753284735109165686868355 14629927102663748530302533)
                ·
                  refine ⟨2743111331749452849431725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14629927102663748530302533 2743111331749452849431725)
                  ·
                    refine ⟨1028666749406044818536897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743111331749452849431725 1028666749406044818536897)
                    ·
                      rfl

theorem cell22_3004982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_3004982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004982 prefixEnd_3004982 := by exact prefixLift 3004982
  have htrace : WordTrace (prefixWord ++ tailWord_3004982) baseStart_3004982 baseEnd_3004982 := by
    simpa [prefixWord, tailWord_3004982, baseEnd_3004982] using wordTrace_append hprefix tailTrace_3004982
  have hstable : (prefixWord ++ tailWord_3004982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004982).length < 2 ^ (prefixWord ++ tailWord_3004982).sum := by decide
  have hdescent : baseEnd_3004982 < baseStart_3004982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3004999 : List Nat := [1, 1, 4, 1, 4, 3, 2, 1, 2, 3]
def baseStart_3004999 : Nat := 118140960795 + 3004999 * 2 ^ 59
def prefixEnd_3004999 : Nat := 4983230072969 + 3 ^ 40 * 3004999 * 2
def baseEnd_3004999 : Nat := 1028672568853462440861845

theorem tailTrace_3004999 : CollatzResearch.WordTrace tailWord_3004999 prefixEnd_3004999 1028672568853462440861845 := by
  unfold tailWord_3004999
  simp only [CollatzResearch.WordTrace]
  refine ⟨109601317640409310815338051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73067545093606207210225367 109601317640409310815338051)
  ·
    refine ⟨164401976460613966223007077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109601317640409310815338051 164401976460613966223007077)
    ·
      refine ⟨30825370586365118666813827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 164401976460613966223007077 30825370586365118666813827)
      ·
        refine ⟨46238055879547678000220741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30825370586365118666813827 46238055879547678000220741)
        ·
          refine ⟨8669635477415189625041389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46238055879547678000220741 8669635477415189625041389)
          ·
            refine ⟨3251113304030696109390521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8669635477415189625041389 3251113304030696109390521)
            ·
              refine ⟨2438334978023022082042891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3251113304030696109390521 2438334978023022082042891)
              ·
                refine ⟨3657502467034533123064337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438334978023022082042891 3657502467034533123064337)
                ·
                  refine ⟨2743126850275899842298253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3657502467034533123064337 2743126850275899842298253)
                  ·
                    refine ⟨1028672568853462440861845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743126850275899842298253 1028672568853462440861845)
                    ·
                      rfl

theorem cell22_3004999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_3004999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3004999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3004999 prefixEnd_3004999 := by exact prefixLift 3004999
  have htrace : WordTrace (prefixWord ++ tailWord_3004999) baseStart_3004999 baseEnd_3004999 := by
    simpa [prefixWord, tailWord_3004999, baseEnd_3004999] using wordTrace_append hprefix tailTrace_3004999
  have hstable : (prefixWord ++ tailWord_3004999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3004999).length < 2 ^ (prefixWord ++ tailWord_3004999).sum := by decide
  have hdescent : baseEnd_3004999 < baseStart_3004999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3004999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005010 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_3005010 : Nat := 118140960795 + 3005010 * 2 ^ 59
def prefixEnd_3005010 : Nat := 4983230072969 + 3 ^ 40 * 3005010 * 2
def baseEnd_3005010 : Nat := 1028676334378262078836811

theorem tailTrace_3005010 : CollatzResearch.WordTrace tailWord_3005010 prefixEnd_3005010 1028676334378262078836811 := by
  unfold tailWord_3005010
  simp only [CollatzResearch.WordTrace]
  refine ⟨27400429710842364923497121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73067812562246306462658989 27400429710842364923497121)
  ·
    refine ⟨20550322283131773692622841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27400429710842364923497121 20550322283131773692622841)
    ·
      refine ⟨15412741712348830269467131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20550322283131773692622841 15412741712348830269467131)
      ·
        refine ⟨23119112568523245404200697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15412741712348830269467131 23119112568523245404200697)
        ·
          refine ⟨17339334426392434053150523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23119112568523245404200697 17339334426392434053150523)
          ·
            refine ⟨26009001639588651079725785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17339334426392434053150523 26009001639588651079725785)
            ·
              refine ⟨19506751229691488309794339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26009001639588651079725785 19506751229691488309794339)
              ·
                refine ⟨29260126844537232464691509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19506751229691488309794339 29260126844537232464691509)
                ·
                  refine ⟨2743136891675365543564829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29260126844537232464691509 2743136891675365543564829)
                  ·
                    refine ⟨1028676334378262078836811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743136891675365543564829 1028676334378262078836811)
                    ·
                      rfl

theorem cell22_3005010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_3005010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005010 prefixEnd_3005010 := by exact prefixLift 3005010
  have htrace : WordTrace (prefixWord ++ tailWord_3005010) baseStart_3005010 baseEnd_3005010 := by
    simpa [prefixWord, tailWord_3005010, baseEnd_3005010] using wordTrace_append hprefix tailTrace_3005010
  have hstable : (prefixWord ++ tailWord_3005010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005010).length < 2 ^ (prefixWord ++ tailWord_3005010).sum := by decide
  have hdescent : baseEnd_3005010 < baseStart_3005010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005027 : List Nat := [1, 1, 1, 5, 1, 2, 2, 5, 1, 3]
def baseStart_3005027 : Nat := 118140960795 + 3005027 * 2 ^ 59
def prefixEnd_3005027 : Nat := 4983230072969 + 3 ^ 40 * 3005027 * 2
def baseEnd_3005027 : Nat := 1028682153825679701161759

theorem tailTrace_3005027 : CollatzResearch.WordTrace tailWord_3005027 prefixEnd_3005027 1028682153825679701161759 := by
  unfold tailWord_3005027
  simp only [CollatzResearch.WordTrace]
  refine ⟨109602338884307871597357335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73068225922871914398238223 109602338884307871597357335)
  ·
    refine ⟨164403508326461807396036003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109602338884307871597357335 164403508326461807396036003)
    ·
      refine ⟨246605262489692711094054005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 164403508326461807396036003 246605262489692711094054005)
      ·
        refine ⟨23119243358408691665067563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 246605262489692711094054005 23119243358408691665067563)
        ·
          refine ⟨34678865037613037497601345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23119243358408691665067563 34678865037613037497601345)
          ·
            refine ⟨26009148778209778123201009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34678865037613037497601345 26009148778209778123201009)
            ·
              refine ⟨19506861583657333592400757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26009148778209778123201009 19506861583657333592400757)
              ·
                refine ⟨1828768273467875024287571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19506861583657333592400757 1828768273467875024287571)
                ·
                  refine ⟨2743152410201812536431357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828768273467875024287571 2743152410201812536431357)
                  ·
                    refine ⟨1028682153825679701161759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743152410201812536431357 1028682153825679701161759)
                    ·
                      rfl

theorem cell22_3005027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 5, 1, 3].length) (baseStart_3005027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005027 prefixEnd_3005027 := by exact prefixLift 3005027
  have htrace : WordTrace (prefixWord ++ tailWord_3005027) baseStart_3005027 baseEnd_3005027 := by
    simpa [prefixWord, tailWord_3005027, baseEnd_3005027] using wordTrace_append hprefix tailTrace_3005027
  have hstable : (prefixWord ++ tailWord_3005027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005027).length < 2 ^ (prefixWord ++ tailWord_3005027).sum := by decide
  have hdescent : baseEnd_3005027 < baseStart_3005027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005070 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_3005070 : Nat := 118140960795 + 3005070 * 2 ^ 59
def prefixEnd_3005070 : Nat := 4983230072969 + 3 ^ 40 * 3005070 * 2
def baseEnd_3005070 : Nat := 1028696873604441922336627

theorem tailTrace_3005070 : CollatzResearch.WordTrace tailWord_3005070 prefixEnd_3005070 1028696873604441922336627 := by
  unfold tailWord_3005070
  simp only [CollatzResearch.WordTrace]
  refine ⟨13700488402894011242646583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73069271482101393294115109 13700488402894011242646583)
  ·
    refine ⟨20550732604341016863969875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13700488402894011242646583 20550732604341016863969875)
    ·
      refine ⟨30826098906511525295954813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20550732604341016863969875 30826098906511525295954813)
      ·
        refine ⟨11559787089941821985983055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30826098906511525295954813 11559787089941821985983055)
        ·
          refine ⟨17339680634912732978974583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11559787089941821985983055 17339680634912732978974583)
          ·
            refine ⟨26009520952369099468461875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17339680634912732978974583 26009520952369099468461875)
            ·
              refine ⟨39014281428553649202692813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26009520952369099468461875 39014281428553649202692813)
              ·
                refine ⟨14630355535707618451009805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39014281428553649202692813 14630355535707618451009805)
                ·
                  refine ⟨5486383325890356919128677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14630355535707618451009805 5486383325890356919128677)
                  ·
                    refine ⟨1028696873604441922336627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5486383325890356919128677 1028696873604441922336627)
                    ·
                      rfl

theorem cell22_3005070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_3005070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005070 prefixEnd_3005070 := by exact prefixLift 3005070
  have htrace : WordTrace (prefixWord ++ tailWord_3005070) baseStart_3005070 baseEnd_3005070 := by
    simpa [prefixWord, tailWord_3005070, baseEnd_3005070] using wordTrace_append hprefix tailTrace_3005070
  have hstable : (prefixWord ++ tailWord_3005070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005070).length < 2 ^ (prefixWord ++ tailWord_3005070).sum := by decide
  have hdescent : baseEnd_3005070 < baseStart_3005070 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005102 : List Nat := [4, 1, 4, 1, 1, 1, 1, 3, 6]
def baseStart_3005102 : Nat := 118140960795 + 3005102 * 2 ^ 59
def prefixEnd_3005102 : Nat := 4983230072969 + 3 ^ 40 * 3005102 * 2
def baseEnd_3005102 : Nat := 342902609286134835178843

theorem tailTrace_3005102 : CollatzResearch.WordTrace tailWord_3005102 prefixEnd_3005102 342902609286134835178843 := by
  unfold tailWord_3005102
  simp only [CollatzResearch.WordTrace]
  refine ⟨13700634294879519925792195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73070049572690772937558373 13700634294879519925792195)
  ·
    refine ⟨20550951442319279888688293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13700634294879519925792195 20550951442319279888688293)
    ·
      refine ⟨3853303395434864979129055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20550951442319279888688293 3853303395434864979129055)
      ·
        refine ⟨5779955093152297468693583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3853303395434864979129055 5779955093152297468693583)
        ·
          refine ⟨8669932639728446203040375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5779955093152297468693583 8669932639728446203040375)
          ·
            refine ⟨13004898959592669304560563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8669932639728446203040375 13004898959592669304560563)
            ·
              refine ⟨19507348439389003956840845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13004898959592669304560563 19507348439389003956840845)
              ·
                refine ⟨7315255664770876483815317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19507348439389003956840845 7315255664770876483815317)
                ·
                  refine ⟨342902609286134835178843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7315255664770876483815317 342902609286134835178843)
                  ·
                    rfl

theorem cell22_3005102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 3, 6].length) (baseStart_3005102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005102 prefixEnd_3005102 := by exact prefixLift 3005102
  have htrace : WordTrace (prefixWord ++ tailWord_3005102) baseStart_3005102 baseEnd_3005102 := by
    simpa [prefixWord, tailWord_3005102, baseEnd_3005102] using wordTrace_append hprefix tailTrace_3005102
  have hstable : (prefixWord ++ tailWord_3005102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005102).length < 2 ^ (prefixWord ++ tailWord_3005102).sum := by decide
  have hdescent : baseEnd_3005102 < baseStart_3005102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005113 : List Nat := [1, 2, 1, 4, 1, 1, 1, 11]
def baseStart_3005113 : Nat := 118140960795 + 3005113 * 2 ^ 59
def prefixEnd_3005113 : Nat := 4983230072969 + 3 ^ 40 * 3005113 * 2
def baseEnd_3005113 : Nat := 114301288153689349279055

theorem tailTrace_3005113 : CollatzResearch.WordTrace tailWord_3005113 prefixEnd_3005113 114301288153689349279055 := by
  unfold tailWord_3005113
  simp only [CollatzResearch.WordTrace]
  refine ⟨109605475561996308284987993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73070317041330872189991995 109605475561996308284987993)
  ·
    refine ⟨82204106671497231213740995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109605475561996308284987993 82204106671497231213740995)
    ·
      refine ⟨123306160007245846820611493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82204106671497231213740995 123306160007245846820611493)
      ·
        refine ⟨23119905001358596278864655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123306160007245846820611493 23119905001358596278864655)
        ·
          refine ⟨34679857502037894418296983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23119905001358596278864655 34679857502037894418296983)
          ·
            refine ⟨52019786253056841627445475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34679857502037894418296983 52019786253056841627445475)
            ·
              refine ⟨78029679379585262441168213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52019786253056841627445475 78029679379585262441168213)
              ·
                refine ⟨114301288153689349279055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 78029679379585262441168213 114301288153689349279055)
                ·
                  rfl

theorem cell22_3005113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 11].length) (baseStart_3005113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005113 prefixEnd_3005113 := by exact prefixLift 3005113
  have htrace : WordTrace (prefixWord ++ tailWord_3005113) baseStart_3005113 baseEnd_3005113 := by
    simpa [prefixWord, tailWord_3005113, baseEnd_3005113] using wordTrace_append hprefix tailTrace_3005113
  have hstable : (prefixWord ++ tailWord_3005113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005113).length < 2 ^ (prefixWord ++ tailWord_3005113).sum := by decide
  have hdescent : baseEnd_3005113 < baseStart_3005113 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005117 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 1, 5]
def baseStart_3005117 : Nat := 118140960795 + 3005117 * 2 ^ 59
def prefixEnd_3005117 : Nat := 4983230072969 + 3 ^ 40 * 3005117 * 2
def baseEnd_3005117 : Nat := 1028712962664949466411483

theorem tailTrace_3005117 : CollatzResearch.WordTrace tailWord_3005117 prefixEnd_3005117 1028712962664949466411483 := by
  unfold tailWord_3005117
  simp only [CollatzResearch.WordTrace]
  refine ⟨109605621453981816968133605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73070414302654544645422403 109605621453981816968133605)
  ·
    refine ⟨20551054022621590681525051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109605621453981816968133605 20551054022621590681525051)
    ·
      refine ⟨30826581033932386022287577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20551054022621590681525051 30826581033932386022287577)
      ·
        refine ⟨23119935775449289516715683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30826581033932386022287577 23119935775449289516715683)
        ·
          refine ⟨34679903663173934275073525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23119935775449289516715683 34679903663173934275073525)
          ·
            refine ⟨3251240968422556338288143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34679903663173934275073525 3251240968422556338288143)
            ·
              refine ⟨4876861452633834507432215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251240968422556338288143 4876861452633834507432215)
              ·
                refine ⟨7315292178950751761148323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4876861452633834507432215 7315292178950751761148323)
                ·
                  refine ⟨10972938268426127641722485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7315292178950751761148323 10972938268426127641722485)
                  ·
                    refine ⟨1028712962664949466411483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10972938268426127641722485 1028712962664949466411483)
                    ·
                      rfl

theorem cell22_3005117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_3005117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005117 prefixEnd_3005117 := by exact prefixLift 3005117
  have htrace : WordTrace (prefixWord ++ tailWord_3005117) baseStart_3005117 baseEnd_3005117 := by
    simpa [prefixWord, tailWord_3005117, baseEnd_3005117] using wordTrace_append hprefix tailTrace_3005117
  have hstable : (prefixWord ++ tailWord_3005117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005117).length < 2 ^ (prefixWord ++ tailWord_3005117).sum := by decide
  have hdescent : baseEnd_3005117 < baseStart_3005117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005121 : List Nat := [1, 2, 6, 2, 1, 1, 2, 2, 1, 4]
def baseStart_3005121 : Nat := 118140960795 + 3005121 * 2 ^ 59
def prefixEnd_3005121 : Nat := 4983230072969 + 3 ^ 40 * 3005121 * 2
def baseEnd_3005121 : Nat := 1028714331946694789311471

theorem tailTrace_3005121 : CollatzResearch.WordTrace tailWord_3005121 prefixEnd_3005121 1028714331946694789311471 := by
  unfold tailWord_3005121
  simp only [CollatzResearch.WordTrace]
  refine ⟨109605767345967325651279217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73070511563978217100852811 109605767345967325651279217)
  ·
    refine ⟨82204325509475494238459413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109605767345967325651279217 82204325509475494238459413)
    ·
      refine ⟨3853327758256663792427785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82204325509475494238459413 3853327758256663792427785)
      ·
        refine ⟨2889995818692497844320839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3853327758256663792427785 2889995818692497844320839)
        ·
          refine ⟨4334993728038746766481259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2889995818692497844320839 4334993728038746766481259)
          ·
            refine ⟨6502490592058120149721889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4334993728038746766481259 6502490592058120149721889)
            ·
              refine ⟨4876867944043590112291417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6502490592058120149721889 4876867944043590112291417)
              ·
                refine ⟨3657650958032692584218563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4876867944043590112291417 3657650958032692584218563)
                ·
                  refine ⟨5486476437049038876327845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3657650958032692584218563 5486476437049038876327845)
                  ·
                    refine ⟨1028714331946694789311471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5486476437049038876327845 1028714331946694789311471)
                    ·
                      rfl

theorem cell22_3005121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_3005121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005121 prefixEnd_3005121 := by exact prefixLift 3005121
  have htrace : WordTrace (prefixWord ++ tailWord_3005121) baseStart_3005121 baseEnd_3005121 := by
    simpa [prefixWord, tailWord_3005121, baseEnd_3005121] using wordTrace_append hprefix tailTrace_3005121
  have hstable : (prefixWord ++ tailWord_3005121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005121).length < 2 ^ (prefixWord ++ tailWord_3005121).sum := by decide
  have hdescent : baseEnd_3005121 < baseStart_3005121 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005130 : List Nat := [3, 1, 2, 1, 4, 2, 1, 8]
def baseStart_3005130 : Nat := 118140960795 + 3005130 * 2 ^ 59
def prefixEnd_3005130 : Nat := 4983230072969 + 3 ^ 40 * 3005130 * 2
def baseEnd_3005130 : Nat := 114301934758957973981827

theorem tailTrace_3005130 : CollatzResearch.WordTrace tailWord_3005130 prefixEnd_3005130 114301934758957973981827 := by
  unfold tailWord_3005130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27401523900733680047089211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73070730401956480125571229 27401523900733680047089211)
  ·
    refine ⟨41102285851100520070633817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27401523900733680047089211 41102285851100520070633817)
    ·
      refine ⟨30826714388325390052975363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41102285851100520070633817 30826714388325390052975363)
      ·
        refine ⟨46240071582488085079463045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30826714388325390052975363 46240071582488085079463045)
        ·
          refine ⟨8670013421716515952399321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46240071582488085079463045 8670013421716515952399321)
          ·
            refine ⟨6502510066287386964299491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8670013421716515952399321 6502510066287386964299491)
            ·
              refine ⟨9753765099431080446449237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6502510066287386964299491 9753765099431080446449237)
              ·
                refine ⟨114301934758957973981827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9753765099431080446449237 114301934758957973981827)
                ·
                  rfl

theorem cell22_3005130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_3005130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005130 prefixEnd_3005130 := by exact prefixLift 3005130
  have htrace : WordTrace (prefixWord ++ tailWord_3005130) baseStart_3005130 baseEnd_3005130 := by
    simpa [prefixWord, tailWord_3005130, baseEnd_3005130] using wordTrace_append hprefix tailTrace_3005130
  have hstable : (prefixWord ++ tailWord_3005130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005130).length < 2 ^ (prefixWord ++ tailWord_3005130).sum := by decide
  have hdescent : baseEnd_3005130 < baseStart_3005130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005213 : List Nat := [1, 4, 2, 4, 1, 1, 1, 4, 1, 3]
def baseStart_3005213 : Nat := 118140960795 + 3005213 * 2 ^ 59
def prefixEnd_3005213 : Nat := 4983230072969 + 3 ^ 40 * 3005213 * 2
def baseEnd_3005213 : Nat := 1028745825426837216011189

theorem tailTrace_3005213 : CollatzResearch.WordTrace tailWord_3005213 prefixEnd_3005213 1028745825426837216011189 := by
  unfold tailWord_3005213
  simp only [CollatzResearch.WordTrace]
  refine ⟨109609122861634025363628293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73072748574422683575752195 109609122861634025363628293)
  ·
    refine ⟨20551710536556379755680305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109609122861634025363628293 20551710536556379755680305)
    ·
      refine ⟨15413782902417284816760229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20551710536556379755680305 15413782902417284816760229)
      ·
        refine ⟨2890084294203240903142543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15413782902417284816760229 2890084294203240903142543)
        ·
          refine ⟨4335126441304861354713815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2890084294203240903142543 4335126441304861354713815)
          ·
            refine ⟨6502689661957292032070723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335126441304861354713815 6502689661957292032070723)
            ·
              refine ⟨9754034492935938048106085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6502689661957292032070723 9754034492935938048106085)
              ·
                refine ⟨1828881467425488384019891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9754034492935938048106085 1828881467425488384019891)
                ·
                  refine ⟨2743322201138232576029837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1828881467425488384019891 2743322201138232576029837)
                  ·
                    refine ⟨1028745825426837216011189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743322201138232576029837 1028745825426837216011189)
                    ·
                      rfl

theorem cell22_3005213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_3005213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005213 prefixEnd_3005213 := by exact prefixLift 3005213
  have htrace : WordTrace (prefixWord ++ tailWord_3005213) baseStart_3005213 baseEnd_3005213 := by
    simpa [prefixWord, tailWord_3005213, baseEnd_3005213] using wordTrace_append hprefix tailTrace_3005213
  have hstable : (prefixWord ++ tailWord_3005213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005213).length < 2 ^ (prefixWord ++ tailWord_3005213).sum := by decide
  have hdescent : baseEnd_3005213 < baseStart_3005213 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005237 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 6]
def baseStart_3005237 : Nat := 118140960795 + 3005237 * 2 ^ 59
def prefixEnd_3005237 : Nat := 4983230072969 + 3 ^ 40 * 3005237 * 2
def baseEnd_3005237 : Nat := 342918013705769717803705

theorem tailTrace_3005237 : CollatzResearch.WordTrace tailWord_3005237 prefixEnd_3005237 342918013705769717803705 := by
  unfold tailWord_3005237
  simp only [CollatzResearch.WordTrace]
  refine ⟨109609998213547077462501965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73073332142364718308334643 109609998213547077462501965)
  ·
    refine ⟨41103749330080154048438237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109609998213547077462501965 41103749330080154048438237)
    ·
      refine ⟨15413905998780057768164339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41103749330080154048438237 15413905998780057768164339)
      ·
        refine ⟨23120858998170086652246509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15413905998780057768164339 23120858998170086652246509)
        ·
          refine ⟨8670322124313782494592441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23120858998170086652246509 8670322124313782494592441)
          ·
            refine ⟨6502741593235336870944331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8670322124313782494592441 6502741593235336870944331)
            ·
              refine ⟨9754112389853005306416497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6502741593235336870944331 9754112389853005306416497)
              ·
                refine ⟨7315584292389753979812373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9754112389853005306416497 7315584292389753979812373)
                ·
                  refine ⟨342918013705769717803705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7315584292389753979812373 342918013705769717803705)
                  ·
                    rfl

theorem cell22_3005237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 6].length) (baseStart_3005237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005237 prefixEnd_3005237 := by exact prefixLift 3005237
  have htrace : WordTrace (prefixWord ++ tailWord_3005237) baseStart_3005237 baseEnd_3005237 := by
    simpa [prefixWord, tailWord_3005237, baseEnd_3005237] using wordTrace_append hprefix tailTrace_3005237
  have hstable : (prefixWord ++ tailWord_3005237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005237).length < 2 ^ (prefixWord ++ tailWord_3005237).sum := by decide
  have hdescent : baseEnd_3005237 < baseStart_3005237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005295 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 2, 6]
def baseStart_3005295 : Nat := 118140960795 + 3005295 * 2 ^ 59
def prefixEnd_3005295 : Nat := 4983230072969 + 3 ^ 40 * 3005295 * 2
def baseEnd_3005295 : Nat := 1028773895702616335460937

theorem tailTrace_3005295 : CollatzResearch.WordTrace tailWord_3005295 prefixEnd_3005295 1028773895702616335460937 := by
  unfold tailWord_3005295
  simp only [CollatzResearch.WordTrace]
  refine ⟨109612113647336953368113339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73074742431557968912075559 109612113647336953368113339)
  ·
    refine ⟨164418170471005430052170009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109612113647336953368113339 164418170471005430052170009)
    ·
      refine ⟨123313627853254072539127507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164418170471005430052170009 123313627853254072539127507)
      ·
        refine ⟨184970441779881108808691261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123313627853254072539127507 184970441779881108808691261)
        ·
          refine ⟨69363915667455415803259223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 184970441779881108808691261 69363915667455415803259223)
          ·
            refine ⟨104045873501183123704888835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69363915667455415803259223 104045873501183123704888835)
            ·
              refine ⟨156068810251774685557333253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104045873501183123704888835 156068810251774685557333253)
              ·
                refine ⟨29262901922207753541999985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156068810251774685557333253 29262901922207753541999985)
                ·
                  refine ⟨21947176441655815156499989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29262901922207753541999985 21947176441655815156499989)
                  ·
                    refine ⟨1028773895702616335460937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21947176441655815156499989 1028773895702616335460937)
                    ·
                      rfl

theorem cell22_3005295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_3005295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005295 prefixEnd_3005295 := by exact prefixLift 3005295
  have htrace : WordTrace (prefixWord ++ tailWord_3005295) baseStart_3005295 baseEnd_3005295 := by
    simpa [prefixWord, tailWord_3005295, baseEnd_3005295] using wordTrace_append hprefix tailTrace_3005295
  have hstable : (prefixWord ++ tailWord_3005295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005295).length < 2 ^ (prefixWord ++ tailWord_3005295).sum := by decide
  have hdescent : baseEnd_3005295 < baseStart_3005295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005344 : List Nat := [2, 1, 1, 4, 1, 1, 6, 1, 5]
def baseStart_3005344 : Nat := 118140960795 + 3005344 * 2 ^ 59
def prefixEnd_3005344 : Nat := 4983230072969 + 3 ^ 40 * 3005344 * 2
def baseEnd_3005344 : Nat := 342930223134665513661929

theorem tailTrace_3005344 : CollatzResearch.WordTrace tailWord_3005344 prefixEnd_3005344 342930223134665513661929 := by
  unfold tailWord_3005344
  simp only [CollatzResearch.WordTrace]
  refine ⟨54806950412079717368323543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73075933882772956491098057 54806950412079717368323543)
  ·
    refine ⟨82210425618119576052485315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54806950412079717368323543 82210425618119576052485315)
    ·
      refine ⟨123315638427179364078727973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82210425618119576052485315 123315638427179364078727973)
      ·
        refine ⟨23121682205096130764761495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123315638427179364078727973 23121682205096130764761495)
        ·
          refine ⟨34682523307644196147142243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23121682205096130764761495 34682523307644196147142243)
          ·
            refine ⟨52023784961466294220713365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34682523307644196147142243 52023784961466294220713365)
            ·
              refine ⟨2438614920068732541595939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 52023784961466294220713365 2438614920068732541595939)
              ·
                refine ⟨3657922380103098812393909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438614920068732541595939 3657922380103098812393909)
                ·
                  refine ⟨342930223134665513661929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3657922380103098812393909 342930223134665513661929)
                  ·
                    rfl

theorem cell22_3005344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 1, 5].length) (baseStart_3005344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005344 prefixEnd_3005344 := by exact prefixLift 3005344
  have htrace : WordTrace (prefixWord ++ tailWord_3005344) baseStart_3005344 baseEnd_3005344 := by
    simpa [prefixWord, tailWord_3005344, baseEnd_3005344] using wordTrace_append hprefix tailTrace_3005344
  have hstable : (prefixWord ++ tailWord_3005344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005344).length < 2 ^ (prefixWord ++ tailWord_3005344).sum := by decide
  have hdescent : baseEnd_3005344 < baseStart_3005344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005438 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3005438 : Nat := 118140960795 + 3005438 * 2 ^ 59
def prefixEnd_3005438 : Nat := 4983230072969 + 3 ^ 40 * 3005438 * 2
def baseEnd_3005438 : Nat := 1028822847525011629135499

theorem tailTrace_3005438 : CollatzResearch.WordTrace tailWord_3005438 prefixEnd_3005438 1028822847525011629135499 := by
  unfold tailWord_3005438
  simp only [CollatzResearch.WordTrace]
  refine ⟨13702166160727361098821121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 73078219523879259193712645 13702166160727361098821121)
  ·
    refine ⟨10276624620545520824115841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13702166160727361098821121 10276624620545520824115841)
    ·
      refine ⟨7707468465409140618086881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10276624620545520824115841 7707468465409140618086881)
      ·
        refine ⟨5780601349056855463565161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7707468465409140618086881 5780601349056855463565161)
        ·
          refine ⟨4335451011792641597673871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5780601349056855463565161 4335451011792641597673871)
          ·
            refine ⟨6503176517688962396510807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4335451011792641597673871 6503176517688962396510807)
            ·
              refine ⟨9754764776533443594766211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6503176517688962396510807 9754764776533443594766211)
              ·
                refine ⟨14632147164800165392149317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9754764776533443594766211 14632147164800165392149317)
                ·
                  refine ⟨2743527593400031011027997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14632147164800165392149317 2743527593400031011027997)
                  ·
                    refine ⟨1028822847525011629135499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743527593400031011027997 1028822847525011629135499)
                    ·
                      rfl

theorem cell22_3005438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3005438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005438 prefixEnd_3005438 := by exact prefixLift 3005438
  have htrace : WordTrace (prefixWord ++ tailWord_3005438) baseStart_3005438 baseEnd_3005438 := by
    simpa [prefixWord, tailWord_3005438, baseEnd_3005438] using wordTrace_append hprefix tailTrace_3005438
  have hstable : (prefixWord ++ tailWord_3005438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005438).length < 2 ^ (prefixWord ++ tailWord_3005438).sum := by decide
  have hdescent : baseEnd_3005438 < baseStart_3005438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005468 : List Nat := [2, 2, 3, 1, 5, 1, 2, 6]
def baseStart_3005468 : Nat := 118140960795 + 3005468 * 2 ^ 59
def prefixEnd_3005468 : Nat := 4983230072969 + 3 ^ 40 * 3005468 * 2
def baseEnd_3005468 : Nat := 114314790793122394542823

theorem tailTrace_3005468 : CollatzResearch.WordTrace tailWord_3005468 prefixEnd_3005468 114314790793122394542823 := by
  unfold tailWord_3005468
  simp only [CollatzResearch.WordTrace]
  refine ⟨54809211737855101957080529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73078948983806802609440705 54809211737855101957080529)
  ·
    refine ⟨41106908803391326467810397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54809211737855101957080529 41106908803391326467810397)
    ·
      refine ⟨15415090801271747425428899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41106908803391326467810397 15415090801271747425428899)
      ·
        refine ⟨23122636201907621138143349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15415090801271747425428899 23122636201907621138143349)
        ·
          refine ⟨2167747143928839481700939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 23122636201907621138143349 2167747143928839481700939)
          ·
            refine ⟨3251620715893259222551409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167747143928839481700939 3251620715893259222551409)
            ·
              refine ⟨2438715536919944416913557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3251620715893259222551409 2438715536919944416913557)
              ·
                refine ⟨114314790793122394542823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2438715536919944416913557 114314790793122394542823)
                ·
                  rfl

theorem cell22_3005468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 6].length) (baseStart_3005468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005468 prefixEnd_3005468 := by exact prefixLift 3005468
  have htrace : WordTrace (prefixWord ++ tailWord_3005468) baseStart_3005468 baseEnd_3005468 := by
    simpa [prefixWord, tailWord_3005468, baseEnd_3005468] using wordTrace_append hprefix tailTrace_3005468
  have hstable : (prefixWord ++ tailWord_3005468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005468).length < 2 ^ (prefixWord ++ tailWord_3005468).sum := by decide
  have hdescent : baseEnd_3005468 < baseStart_3005468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005500 : List Nat := [2, 2, 2, 2, 2, 3, 3, 2, 1, 3]
def baseStart_3005500 : Nat := 118140960795 + 3005500 * 2 ^ 59
def prefixEnd_3005500 : Nat := 4983230072969 + 3 ^ 40 * 3005500 * 2
def baseEnd_3005500 : Nat := 1028844071392064134085309

theorem tailTrace_3005500 : CollatzResearch.WordTrace tailWord_3005500 prefixEnd_3005500 1028844071392064134085309 := by
  unfold tailWord_3005500
  simp only [CollatzResearch.WordTrace]
  refine ⟨54809795305797136689662977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73079727074396182252883969 54809795305797136689662977)
  ·
    refine ⟨41107346479347852517247233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54809795305797136689662977 41107346479347852517247233)
    ·
      refine ⟨30830509859510889387935425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41107346479347852517247233 30830509859510889387935425)
      ·
        refine ⟨23122882394633167040951569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30830509859510889387935425 23122882394633167040951569)
        ·
          refine ⟨17342161795974875280713677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23122882394633167040951569 17342161795974875280713677)
          ·
            refine ⟨6503310673490578230267629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17342161795974875280713677 6503310673490578230267629)
            ·
              refine ⟨2438741502558966836350361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6503310673490578230267629 2438741502558966836350361)
              ·
                refine ⟨1829056126919225127262771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438741502558966836350361 1829056126919225127262771)
                ·
                  refine ⟨2743584190378837690894157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1829056126919225127262771 2743584190378837690894157)
                  ·
                    refine ⟨1028844071392064134085309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743584190378837690894157 1028844071392064134085309)
                    ·
                      rfl

theorem cell22_3005500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_3005500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005500 prefixEnd_3005500 := by exact prefixLift 3005500
  have htrace : WordTrace (prefixWord ++ tailWord_3005500) baseStart_3005500 baseEnd_3005500 := by
    simpa [prefixWord, tailWord_3005500, baseEnd_3005500] using wordTrace_append hprefix tailTrace_3005500
  have hstable : (prefixWord ++ tailWord_3005500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005500).length < 2 ^ (prefixWord ++ tailWord_3005500).sum := by decide
  have hdescent : baseEnd_3005500 < baseStart_3005500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005524 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 6]
def baseStart_3005524 : Nat := 118140960795 + 3005524 * 2 ^ 59
def prefixEnd_3005524 : Nat := 4983230072969 + 3 ^ 40 * 3005524 * 2
def baseEnd_3005524 : Nat := 342950762360845357161745

theorem tailTrace_3005524 : CollatzResearch.WordTrace tailWord_3005524 prefixEnd_3005524 342950762360845357161745 := by
  unfold tailWord_3005524
  simp only [CollatzResearch.WordTrace]
  refine ⟨54810232981753662739099813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73080310642338216985466417 54810232981753662739099813)
  ·
    refine ⟨10276918684078811763581215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54810232981753662739099813 10276918684078811763581215)
    ·
      refine ⟨15415378026118217645371823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10276918684078811763581215 15415378026118217645371823)
      ·
        refine ⟨23123067039177326468057735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15415378026118217645371823 23123067039177326468057735)
        ·
          refine ⟨34684600558765989702086603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23123067039177326468057735 34684600558765989702086603)
          ·
            refine ⟨52026900838148984553129905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34684600558765989702086603 52026900838148984553129905)
            ·
              refine ⟨39020175628611738414847429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52026900838148984553129905 39020175628611738414847429)
              ·
                refine ⟨7316282930364700952783893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39020175628611738414847429 7316282930364700952783893)
                ·
                  refine ⟨342950762360845357161745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7316282930364700952783893 342950762360845357161745)
                  ·
                    rfl

theorem cell22_3005524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_3005524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005524 prefixEnd_3005524 := by exact prefixLift 3005524
  have htrace : WordTrace (prefixWord ++ tailWord_3005524) baseStart_3005524 baseEnd_3005524 := by
    simpa [prefixWord, tailWord_3005524, baseEnd_3005524] using wordTrace_append hprefix tailTrace_3005524
  have hstable : (prefixWord ++ tailWord_3005524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005524).length < 2 ^ (prefixWord ++ tailWord_3005524).sum := by decide
  have hdescent : baseEnd_3005524 < baseStart_3005524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005541 : List Nat := [1, 3, 1, 3, 2, 1, 2, 5, 4]
def baseStart_3005541 : Nat := 118140960795 + 3005541 * 2 ^ 59
def prefixEnd_3005541 : Nat := 4983230072969 + 3 ^ 40 * 3005541 * 2
def baseEnd_3005541 : Nat := 342952702176651231270061

theorem tailTrace_3005541 : CollatzResearch.WordTrace tailWord_3005541 prefixEnd_3005541 342952702176651231270061 := by
  unfold tailWord_3005541
  simp only [CollatzResearch.WordTrace]
  refine ⟨109621086004445737381568477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73080724002963824921045651 109621086004445737381568477)
  ·
    refine ⟨41107907251667151518088179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109621086004445737381568477 41107907251667151518088179)
    ·
      refine ⟨61661860877500727277132269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41107907251667151518088179 61661860877500727277132269)
      ·
        refine ⟨23123197829062772728924601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61661860877500727277132269 23123197829062772728924601)
        ·
          refine ⟨17342398371797079546693451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23123197829062772728924601 17342398371797079546693451)
          ·
            refine ⟨26013597557695619320040177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17342398371797079546693451 26013597557695619320040177)
            ·
              refine ⟨19510198168271714490030133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26013597557695619320040177 19510198168271714490030133)
              ·
                refine ⟨1829081078275473233440325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19510198168271714490030133 1829081078275473233440325)
                ·
                  refine ⟨342952702176651231270061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829081078275473233440325 342952702176651231270061)
                  ·
                    rfl

theorem cell22_3005541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_3005541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005541 prefixEnd_3005541 := by exact prefixLift 3005541
  have htrace : WordTrace (prefixWord ++ tailWord_3005541) baseStart_3005541 baseEnd_3005541 := by
    simpa [prefixWord, tailWord_3005541, baseEnd_3005541] using wordTrace_append hprefix tailTrace_3005541
  have hstable : (prefixWord ++ tailWord_3005541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005541).length < 2 ^ (prefixWord ++ tailWord_3005541).sum := by decide
  have hdescent : baseEnd_3005541 < baseStart_3005541 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005543 : List Nat := [1, 1, 5, 1, 1, 4, 3, 1, 1, 4]
def baseStart_3005543 : Nat := 118140960795 + 3005543 * 2 ^ 59
def prefixEnd_3005543 : Nat := 4983230072969 + 3 ^ 40 * 3005543 * 2
def baseEnd_3005543 : Nat := 1028858791170826355260177

theorem tailTrace_3005543 : CollatzResearch.WordTrace tailWord_3005543 prefixEnd_3005543 1028858791170826355260177 := by
  unfold tailWord_3005543
  simp only [CollatzResearch.WordTrace]
  refine ⟨109621158950438491723141283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73080772633625661148760855 109621158950438491723141283)
  ·
    refine ⟨164431738425657737584711925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109621158950438491723141283 164431738425657737584711925)
    ·
      refine ⟨15415475477405412898566743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 164431738425657737584711925 15415475477405412898566743)
      ·
        refine ⟨23123213216108119347850115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15415475477405412898566743 23123213216108119347850115)
        ·
          refine ⟨34684819824162179021775173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23123213216108119347850115 34684819824162179021775173)
          ·
            refine ⟨6503403717030408566582845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34684819824162179021775173 6503403717030408566582845)
            ·
              refine ⟨2438776393886403212468567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6503403717030408566582845 2438776393886403212468567)
              ·
                refine ⟨3658164590829604818702851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438776393886403212468567 3658164590829604818702851)
                ·
                  refine ⟨5487246886244407228054277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658164590829604818702851 5487246886244407228054277)
                  ·
                    refine ⟨1028858791170826355260177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5487246886244407228054277 1028858791170826355260177)
                    ·
                      rfl

theorem cell22_3005543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_3005543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005543 prefixEnd_3005543 := by exact prefixLift 3005543
  have htrace : WordTrace (prefixWord ++ tailWord_3005543) baseStart_3005543 baseEnd_3005543 := by
    simpa [prefixWord, tailWord_3005543, baseEnd_3005543] using wordTrace_append hprefix tailTrace_3005543
  have hstable : (prefixWord ++ tailWord_3005543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005543).length < 2 ^ (prefixWord ++ tailWord_3005543).sum := by decide
  have hdescent : baseEnd_3005543 < baseStart_3005543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005558 : List Nat := [5, 1, 1, 2, 1, 1, 3, 4, 4]
def baseStart_3005558 : Nat := 118140960795 + 3005558 * 2 ^ 59
def prefixEnd_3005558 : Nat := 4983230072969 + 3 ^ 40 * 3005558 * 2
def baseEnd_3005558 : Nat := 342954641992457105378377

theorem tailTrace_3005558 : CollatzResearch.WordTrace tailWord_3005558 prefixEnd_3005558 342954641992457105378377 := by
  unfold tailWord_3005558
  simp only [CollatzResearch.WordTrace]
  refine ⟨6851356627836509330308583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 73081137363589432856624885 6851356627836509330308583)
  ·
    refine ⟨10277034941754763995462875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6851356627836509330308583 10277034941754763995462875)
    ·
      refine ⟨15415552412632145993194313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10277034941754763995462875 15415552412632145993194313)
      ·
        refine ⟨11561664309474109494895735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15415552412632145993194313 11561664309474109494895735)
        ·
          refine ⟨17342496464211164242343603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11561664309474109494895735 17342496464211164242343603)
          ·
            refine ⟨26013744696316746363515405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17342496464211164242343603 26013744696316746363515405)
            ·
              refine ⟨9755154261118779886318277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26013744696316746363515405 9755154261118779886318277)
              ·
                refine ⟨1829091423959771228684677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9755154261118779886318277 1829091423959771228684677)
                ·
                  refine ⟨342954641992457105378377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829091423959771228684677 342954641992457105378377)
                  ·
                    rfl

theorem cell22_3005558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_3005558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005558 prefixEnd_3005558 := by exact prefixLift 3005558
  have htrace : WordTrace (prefixWord ++ tailWord_3005558) baseStart_3005558 baseEnd_3005558 := by
    simpa [prefixWord, tailWord_3005558, baseEnd_3005558] using wordTrace_append hprefix tailTrace_3005558
  have hstable : (prefixWord ++ tailWord_3005558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005558).length < 2 ^ (prefixWord ++ tailWord_3005558).sum := by decide
  have hdescent : baseEnd_3005558 < baseStart_3005558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005601 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 5, 3]
def baseStart_3005601 : Nat := 118140960795 + 3005601 * 2 ^ 59
def prefixEnd_3005601 : Nat := 4983230072969 + 3 ^ 40 * 3005601 * 2
def baseEnd_3005601 : Nat := 1028878645756133537309999

theorem tailTrace_3005601 : CollatzResearch.WordTrace tailWord_3005601 prefixEnd_3005601 1028878645756133537309999 := by
  unfold tailWord_3005601
  simp only [CollatzResearch.WordTrace]
  refine ⟨109623274384228367628752657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73082182922818911752501771 109623274384228367628752657)
  ·
    refine ⟨82217455788171275721564493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 109623274384228367628752657 82217455788171275721564493)
    ·
      refine ⟨30831545920564228395586685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82217455788171275721564493 30831545920564228395586685)
      ·
        refine ⟨11561829720211585648345007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30831545920564228395586685 11561829720211585648345007)
        ·
          refine ⟨17342744580317378472517511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11561829720211585648345007 17342744580317378472517511)
          ·
            refine ⟨26014116870476067708776267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17342744580317378472517511 26014116870476067708776267)
            ·
              refine ⟨39021175305714101563164401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26014116870476067708776267 39021175305714101563164401)
              ·
                refine ⟨29265881479285576172373301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39021175305714101563164401 29265881479285576172373301)
                ·
                  refine ⟨2743676388683022766159997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29265881479285576172373301 2743676388683022766159997)
                  ·
                    refine ⟨1028878645756133537309999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743676388683022766159997 1028878645756133537309999)
                    ·
                      rfl

theorem cell22_3005601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_3005601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005601 prefixEnd_3005601 := by exact prefixLift 3005601
  have htrace : WordTrace (prefixWord ++ tailWord_3005601) baseStart_3005601 baseEnd_3005601 := by
    simpa [prefixWord, tailWord_3005601, baseEnd_3005601] using wordTrace_append hprefix tailTrace_3005601
  have hstable : (prefixWord ++ tailWord_3005601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005601).length < 2 ^ (prefixWord ++ tailWord_3005601).sum := by decide
  have hdescent : baseEnd_3005601 < baseStart_3005601 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005618 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_3005618 : Nat := 118140960795 + 3005618 * 2 ^ 59
def prefixEnd_3005618 : Nat := 4983230072969 + 3 ^ 40 * 3005618 * 2
def baseEnd_3005618 : Nat := 1028884465203551159634947

theorem tailTrace_3005618 : CollatzResearch.WordTrace tailWord_3005618 prefixEnd_3005618 1028884465203551159634947 := by
  unfold tailWord_3005618
  simp only [CollatzResearch.WordTrace]
  refine ⟨27405973606291694883030377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73082596283444519688081005 27405973606291694883030377)
  ·
    refine ⟨20554480204718771162272783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27405973606291694883030377 20554480204718771162272783)
    ·
      refine ⟨30831720307078156743409175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20554480204718771162272783 30831720307078156743409175)
      ·
        refine ⟨46247580460617235115113763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30831720307078156743409175 46247580460617235115113763)
        ·
          refine ⟨69371370690925852672670645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46247580460617235115113763 69371370690925852672670645)
          ·
            refine ⟨6503566002274298688062873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 69371370690925852672670645 6503566002274298688062873)
            ·
              refine ⟨4877674501705724016047155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6503566002274298688062873 4877674501705724016047155)
              ·
                refine ⟨7316511752558586024070733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877674501705724016047155 7316511752558586024070733)
                ·
                  refine ⟨2743691907209469759026525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7316511752558586024070733 2743691907209469759026525)
                  ·
                    refine ⟨1028884465203551159634947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743691907209469759026525 1028884465203551159634947)
                    ·
                      rfl

theorem cell22_3005618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_3005618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005618 prefixEnd_3005618 := by exact prefixLift 3005618
  have htrace : WordTrace (prefixWord ++ tailWord_3005618) baseStart_3005618 baseEnd_3005618 := by
    simpa [prefixWord, tailWord_3005618, baseEnd_3005618] using wordTrace_append hprefix tailTrace_3005618
  have hstable : (prefixWord ++ tailWord_3005618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005618).length < 2 ^ (prefixWord ++ tailWord_3005618).sum := by decide
  have hdescent : baseEnd_3005618 < baseStart_3005618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005676 : List Nat := [2, 2, 1, 1, 2, 4, 3, 1, 6]
def baseStart_3005676 : Nat := 118140960795 + 3005676 * 2 ^ 59
def prefixEnd_3005676 : Nat := 4983230072969 + 3 ^ 40 * 3005676 * 2
def baseEnd_3005676 : Nat := 342968106596286113894923

theorem tailTrace_3005676 : CollatzResearch.WordTrace tailWord_3005676 prefixEnd_3005676 342968106596286113894923 := by
  unfold tailWord_3005676
  simp only [CollatzResearch.WordTrace]
  refine ⟨54813004929478327718866441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73084006572637770291821921 54813004929478327718866441)
  ·
    refine ⟨41109753697108745789149831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54813004929478327718866441 41109753697108745789149831)
    ·
      refine ⟨61664630545663118683724747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41109753697108745789149831 61664630545663118683724747)
      ·
        refine ⟨92496945818494678025587121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61664630545663118683724747 92496945818494678025587121)
        ·
          refine ⟨69372709363871008519190341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92496945818494678025587121 69372709363871008519190341)
          ·
            refine ⟨13007383005725814097348189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69372709363871008519190341 13007383005725814097348189)
            ·
              refine ⟨4877768627147180286505571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13007383005725814097348189 4877768627147180286505571)
              ·
                refine ⟨7316652940720770429758357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877768627147180286505571 7316652940720770429758357)
                ·
                  refine ⟨342968106596286113894923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7316652940720770429758357 342968106596286113894923)
                  ·
                    rfl

theorem cell22_3005676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_3005676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005676 prefixEnd_3005676 := by exact prefixLift 3005676
  have htrace : WordTrace (prefixWord ++ tailWord_3005676) baseStart_3005676 baseEnd_3005676 := by
    simpa [prefixWord, tailWord_3005676, baseEnd_3005676] using wordTrace_append hprefix tailTrace_3005676
  have hstable : (prefixWord ++ tailWord_3005676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005676).length < 2 ^ (prefixWord ++ tailWord_3005676).sum := by decide
  have hdescent : baseEnd_3005676 < baseStart_3005676 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005682 : List Nat := [3, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_3005682 : Nat := 118140960795 + 3005682 * 2 ^ 59
def prefixEnd_3005682 : Nat := 4983230072969 + 3 ^ 40 * 3005682 * 2
def baseEnd_3005682 : Nat := 342968791237158775344917

theorem tailTrace_3005682 : CollatzResearch.WordTrace tailWord_3005682 prefixEnd_3005682 342968791237158775344917 := by
  unfold tailWord_3005682
  simp only [CollatzResearch.WordTrace]
  refine ⟨27406557174233729615612825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73084152464623278974967533 27406557174233729615612825)
  ·
    refine ⟨20554917880675297211709619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27406557174233729615612825 20554917880675297211709619)
    ·
      refine ⟨30832376821012945817564429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20554917880675297211709619 30832376821012945817564429)
      ·
        refine ⟨11562141307879854681586661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30832376821012945817564429 11562141307879854681586661)
        ·
          refine ⟨2167901495227472752797499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11562141307879854681586661 2167901495227472752797499)
          ·
            refine ⟨3251852242841209129196249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2167901495227472752797499 3251852242841209129196249)
            ·
              refine ⟨2438889182130906846897187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3251852242841209129196249 2438889182130906846897187)
              ·
                refine ⟨3658333773196360270345781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2438889182130906846897187 3658333773196360270345781)
                ·
                  refine ⟨342968791237158775344917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3658333773196360270345781 342968791237158775344917)
                  ·
                    rfl

theorem cell22_3005682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_3005682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005682 prefixEnd_3005682 := by exact prefixLift 3005682
  have htrace : WordTrace (prefixWord ++ tailWord_3005682) baseStart_3005682 baseEnd_3005682 := by
    simpa [prefixWord, tailWord_3005682, baseEnd_3005682] using wordTrace_append hprefix tailTrace_3005682
  have hstable : (prefixWord ++ tailWord_3005682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005682).length < 2 ^ (prefixWord ++ tailWord_3005682).sum := by decide
  have hdescent : baseEnd_3005682 < baseStart_3005682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005725 : List Nat := [1, 4, 2, 3, 1, 1, 1, 4, 2, 3]
def baseStart_3005725 : Nat := 118140960795 + 3005725 * 2 ^ 59
def prefixEnd_3005725 : Nat := 4983230072969 + 3 ^ 40 * 3005725 * 2
def baseEnd_3005725 : Nat := 1028921093490238547209619

theorem tailTrace_3005725 : CollatzResearch.WordTrace tailWord_3005725 prefixEnd_3005725 1028921093490238547209619 := by
  unfold tailWord_3005725
  simp only [CollatzResearch.WordTrace]
  refine ⟨109627797035779136806266629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73085198023852757870844419 109627797035779136806266629)
  ·
    refine ⟨20555211944208588151174993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109627797035779136806266629 20555211944208588151174993)
    ·
      refine ⟨15416408958156441113381245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20555211944208588151174993 15416408958156441113381245)
      ·
        refine ⟨5781153359308665417517967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15416408958156441113381245 5781153359308665417517967)
        ·
          refine ⟨8671730038962998126276951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5781153359308665417517967 8671730038962998126276951)
          ·
            refine ⟨13007595058444497189415427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671730038962998126276951 13007595058444497189415427)
            ·
              refine ⟨19511392587666745784123141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13007595058444497189415427 19511392587666745784123141)
              ·
                refine ⟨3658386110187514834523089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19511392587666745784123141 3658386110187514834523089)
                ·
                  refine ⟨2743789582640636125892317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3658386110187514834523089 2743789582640636125892317)
                  ·
                    refine ⟨1028921093490238547209619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2743789582640636125892317 1028921093490238547209619)
                    ·
                      rfl

theorem cell22_3005725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_3005725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005725 prefixEnd_3005725 := by exact prefixLift 3005725
  have htrace : WordTrace (prefixWord ++ tailWord_3005725) baseStart_3005725 baseEnd_3005725 := by
    simpa [prefixWord, tailWord_3005725, baseEnd_3005725] using wordTrace_append hprefix tailTrace_3005725
  have hstable : (prefixWord ++ tailWord_3005725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005725).length < 2 ^ (prefixWord ++ tailWord_3005725).sum := by decide
  have hdescent : baseEnd_3005725 < baseStart_3005725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005727 : List Nat := [1, 1, 2, 4, 4, 2, 2, 2, 4]
def baseStart_3005727 : Nat := 118140960795 + 3005727 * 2 ^ 59
def prefixEnd_3005727 : Nat := 4983230072969 + 3 ^ 40 * 3005727 * 2
def baseEnd_3005727 : Nat := 342973926043703736219871

theorem tailTrace_3005727 : CollatzResearch.WordTrace tailWord_3005727 prefixEnd_3005727 342973926043703736219871 := by
  unfold tailWord_3005727
  simp only [CollatzResearch.WordTrace]
  refine ⟨109627869981771891147839435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73085246654514594098559623 109627869981771891147839435)
  ·
    refine ⟨164441804972657836721759153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109627869981771891147839435 164441804972657836721759153)
    ·
      refine ⟨123331353729493377541319365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164441804972657836721759153 123331353729493377541319365)
      ·
        refine ⟨23124628824280008288997381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123331353729493377541319365 23124628824280008288997381)
        ·
          refine ⟨4335867904552501554187009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23124628824280008288997381 4335867904552501554187009)
          ·
            refine ⟨3251900928414376165640257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4335867904552501554187009 3251900928414376165640257)
            ·
              refine ⟨2438925696310782124230193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3251900928414376165640257 2438925696310782124230193)
              ·
                refine ⟨1829194272233086593172645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2438925696310782124230193 1829194272233086593172645)
                ·
                  refine ⟨342973926043703736219871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1829194272233086593172645 342973926043703736219871)
                  ·
                    rfl

theorem cell22_3005727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 4].length) (baseStart_3005727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005727 prefixEnd_3005727 := by exact prefixLift 3005727
  have htrace : WordTrace (prefixWord ++ tailWord_3005727) baseStart_3005727 baseEnd_3005727 := by
    simpa [prefixWord, tailWord_3005727, baseEnd_3005727] using wordTrace_append hprefix tailTrace_3005727
  have hstable : (prefixWord ++ tailWord_3005727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005727).length < 2 ^ (prefixWord ++ tailWord_3005727).sum := by decide
  have hdescent : baseEnd_3005727 < baseStart_3005727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005738 : List Nat := [3, 1, 4, 2, 1, 1, 3, 7]
def baseStart_3005738 : Nat := 118140960795 + 3005738 * 2 ^ 59
def prefixEnd_3005738 : Nat := 4983230072969 + 3 ^ 40 * 3005738 * 2
def baseEnd_3005738 : Nat := 114325060406212316292731

theorem tailTrace_3005738 : CollatzResearch.WordTrace tailWord_3005738 prefixEnd_3005738 114325060406212316292731 := by
  unfold tailWord_3005738
  simp only [CollatzResearch.WordTrace]
  refine ⟨27407067796183010006622467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73085514123154693350993245 27407067796183010006622467)
  ·
    refine ⟨41110601694274515009933701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27407067796183010006622467 41110601694274515009933701)
    ·
      refine ⟨7708237817676471564362569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41110601694274515009933701 7708237817676471564362569)
      ·
        refine ⟨5781178363257353673271927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7708237817676471564362569 5781178363257353673271927)
        ·
          refine ⟨8671767544886030509907891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5781178363257353673271927 8671767544886030509907891)
          ·
            refine ⟨13007651317329045764861837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8671767544886030509907891 13007651317329045764861837)
            ·
              refine ⟨4877869243998392161823189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13007651317329045764861837 4877869243998392161823189)
              ·
                refine ⟨114325060406212316292731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4877869243998392161823189 114325060406212316292731)
                ·
                  rfl

theorem cell22_3005738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 7].length) (baseStart_3005738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005738 prefixEnd_3005738 := by exact prefixLift 3005738
  have htrace : WordTrace (prefixWord ++ tailWord_3005738) baseStart_3005738 baseEnd_3005738 := by
    simpa [prefixWord, tailWord_3005738, baseEnd_3005738] using wordTrace_append hprefix tailTrace_3005738
  have hstable : (prefixWord ++ tailWord_3005738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005738).length < 2 ^ (prefixWord ++ tailWord_3005738).sum := by decide
  have hdescent : baseEnd_3005738 < baseStart_3005738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005757 : List Nat := [1, 4, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_3005757 : Nat := 118140960795 + 3005757 * 2 ^ 59
def prefixEnd_3005757 : Nat := 4983230072969 + 3 ^ 40 * 3005757 * 2
def baseEnd_3005757 : Nat := 1028932047744201130409521

theorem tailTrace_3005757 : CollatzResearch.WordTrace tailWord_3005757 prefixEnd_3005757 1028932047744201130409521 := by
  unfold tailWord_3005757
  simp only [CollatzResearch.WordTrace]
  refine ⟨109628964171663206271431525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73085976114442137514287683 109628964171663206271431525)
  ·
    refine ⟨20555430782186851175893411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 109628964171663206271431525 20555430782186851175893411)
    ·
      refine ⟨30833146173280276763840117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20555430782186851175893411 30833146173280276763840117)
      ·
        refine ⟨2890607453745025946610011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 30833146173280276763840117 2890607453745025946610011)
        ·
          refine ⟨4335911180617538919915017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2890607453745025946610011 4335911180617538919915017)
          ·
            refine ⟨3251933385463154189936263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4335911180617538919915017 3251933385463154189936263)
            ·
              refine ⟨4877900078194731284904395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3251933385463154189936263 4877900078194731284904395)
              ·
                refine ⟨7316850117292096927356593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4877900078194731284904395 7316850117292096927356593)
                ·
                  refine ⟨5487637587969072695517445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7316850117292096927356593 5487637587969072695517445)
                  ·
                    refine ⟨1028932047744201130409521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5487637587969072695517445 1028932047744201130409521)
                    ·
                      rfl

theorem cell22_3005757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_3005757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005757 prefixEnd_3005757 := by exact prefixLift 3005757
  have htrace : WordTrace (prefixWord ++ tailWord_3005757) baseStart_3005757 baseEnd_3005757 := by
    simpa [prefixWord, tailWord_3005757, baseEnd_3005757] using wordTrace_append hprefix tailTrace_3005757
  have hstable : (prefixWord ++ tailWord_3005757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005757).length < 2 ^ (prefixWord ++ tailWord_3005757).sum := by decide
  have hdescent : baseEnd_3005757 < baseStart_3005757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005783 : List Nat := [1, 1, 3, 2, 3, 2, 3, 2, 5]
def baseStart_3005783 : Nat := 118140960795 + 3005783 * 2 ^ 59
def prefixEnd_3005783 : Nat := 4983230072969 + 3 ^ 40 * 3005783 * 2
def baseEnd_3005783 : Nat := 342980316025181909753147

theorem tailTrace_3005783 : CollatzResearch.WordTrace tailWord_3005783 prefixEnd_3005783 342980316025181909753147 := by
  unfold tailWord_3005783
  simp only [CollatzResearch.WordTrace]
  refine ⟨109629912469569012711878003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73086608313046008474585335 109629912469569012711878003)
  ·
    refine ⟨164444868704353519067817005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109629912469569012711878003 164444868704353519067817005)
    ·
      refine ⟨61666825764132569650431377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 164444868704353519067817005 61666825764132569650431377)
      ·
        refine ⟨46250119323099427237823533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61666825764132569650431377 46250119323099427237823533)
        ·
          refine ⟨17343794746162285214183825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46250119323099427237823533 17343794746162285214183825)
          ·
            refine ⟨13007846059621713910637869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17343794746162285214183825 13007846059621713910637869)
            ·
              refine ⟨4877942272358142716489201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13007846059621713910637869 4877942272358142716489201)
              ·
                refine ⟨3658456704268607037366901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4877942272358142716489201 3658456704268607037366901)
                ·
                  refine ⟨342980316025181909753147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3658456704268607037366901 342980316025181909753147)
                  ·
                    rfl

theorem cell22_3005783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 3, 2, 5].length) (baseStart_3005783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005783 prefixEnd_3005783 := by exact prefixLift 3005783
  have htrace : WordTrace (prefixWord ++ tailWord_3005783) baseStart_3005783 baseEnd_3005783 := by
    simpa [prefixWord, tailWord_3005783, baseEnd_3005783] using wordTrace_append hprefix tailTrace_3005783
  have hstable : (prefixWord ++ tailWord_3005783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005783).length < 2 ^ (prefixWord ++ tailWord_3005783).sum := by decide
  have hdescent : baseEnd_3005783 < baseStart_3005783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005864 : List Nat := [2, 1, 6, 1, 2, 2, 1, 2, 1, 4]
def baseStart_3005864 : Nat := 118140960795 + 3005864 * 2 ^ 59
def prefixEnd_3005864 : Nat := 4983230072969 + 3 ^ 40 * 3005864 * 2
def baseEnd_3005864 : Nat := 1028968676030888517984193

theorem tailTrace_3005864 : CollatzResearch.WordTrace tailWord_3005864 prefixEnd_3005864 1028968676030888517984193 := by
  unfold tailWord_3005864
  simp only [CollatzResearch.WordTrace]
  refine ⟨54816433391137781772788323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73088577854850375697051097 54816433391137781772788323)
  ·
    refine ⟨82224650086706672659182485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54816433391137781772788323 82224650086706672659182485)
    ·
      refine ⟨3854280472814375280899179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 82224650086706672659182485 3854280472814375280899179)
      ·
        refine ⟨5781420709221562921348769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3854280472814375280899179 5781420709221562921348769)
        ·
          refine ⟨4336065531916172191011577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5781420709221562921348769 4336065531916172191011577)
          ·
            refine ⟨3252049148937129143258683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4336065531916172191011577 3252049148937129143258683)
            ·
              refine ⟨4878073723405693714888025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3252049148937129143258683 4878073723405693714888025)
              ·
                refine ⟨3658555292554270286166019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4878073723405693714888025 3658555292554270286166019)
                ·
                  refine ⟨5487832938831405429249029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3658555292554270286166019 5487832938831405429249029)
                  ·
                    refine ⟨1028968676030888517984193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5487832938831405429249029 1028968676030888517984193)
                    ·
                      rfl

theorem cell22_3005864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 2, 1, 4].length) (baseStart_3005864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005864 prefixEnd_3005864 := by exact prefixLift 3005864
  have htrace : WordTrace (prefixWord ++ tailWord_3005864) baseStart_3005864 baseEnd_3005864 := by
    simpa [prefixWord, tailWord_3005864, baseEnd_3005864] using wordTrace_append hprefix tailTrace_3005864
  have hstable : (prefixWord ++ tailWord_3005864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005864).length < 2 ^ (prefixWord ++ tailWord_3005864).sum := by decide
  have hdescent : baseEnd_3005864 < baseStart_3005864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3005871 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 2, 7]
def baseStart_3005871 : Nat := 118140960795 + 3005871 * 2 ^ 59
def prefixEnd_3005871 : Nat := 4983230072969 + 3 ^ 40 * 3005871 * 2
def baseEnd_3005871 : Nat := 1028971072273942833059171

theorem tailTrace_3005871 : CollatzResearch.WordTrace tailWord_3005871 prefixEnd_3005871 1028971072273942833059171 := by
  unfold tailWord_3005871
  simp only [CollatzResearch.WordTrace]
  refine ⟨109633122093250203741081467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73088748062166802494054311 109633122093250203741081467)
  ·
    refine ⟨164449683139875305611622201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 109633122093250203741081467 164449683139875305611622201)
    ·
      refine ⟨123337262354906479208716651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 164449683139875305611622201 123337262354906479208716651)
      ·
        refine ⟨185005893532359718813074977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123337262354906479208716651 185005893532359718813074977)
        ·
          refine ⟨138754420149269789109806233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185005893532359718813074977 138754420149269789109806233)
          ·
            refine ⟨104065815111952341832354675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 138754420149269789109806233 104065815111952341832354675)
            ·
              refine ⟨156098722667928512748532013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104065815111952341832354675 156098722667928512748532013)
              ·
                refine ⟨58537021000473192280699505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156098722667928512748532013 58537021000473192280699505)
                ·
                  refine ⟨43902765750354894210524629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58537021000473192280699505 43902765750354894210524629)
                  ·
                    refine ⟨1028971072273942833059171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 43902765750354894210524629 1028971072273942833059171)
                    ·
                      rfl

theorem cell22_3005871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_3005871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3005871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3005871 prefixEnd_3005871 := by exact prefixLift 3005871
  have htrace : WordTrace (prefixWord ++ tailWord_3005871) baseStart_3005871 baseEnd_3005871 := by
    simpa [prefixWord, tailWord_3005871, baseEnd_3005871] using wordTrace_append hprefix tailTrace_3005871
  have hstable : (prefixWord ++ tailWord_3005871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3005871).length < 2 ^ (prefixWord ++ tailWord_3005871).sum := by decide
  have hdescent : baseEnd_3005871 < baseStart_3005871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3005871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006008 : List Nat := [2, 1, 2, 1, 4, 2, 10]
def baseStart_3006008 : Nat := 118140960795 + 3006008 * 2 ^ 59
def prefixEnd_3006008 : Nat := 4983230072969 + 3 ^ 40 * 3006008 * 2
def baseEnd_3006008 : Nat := 38111776673100746014213

theorem tailTrace_3006008 : CollatzResearch.WordTrace tailWord_3006008 prefixEnd_3006008 38111776673100746014213 := by
  unfold tailWord_3006008
  simp only [CollatzResearch.WordTrace]
  refine ⟨54819059446876938069409339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73092079262502584092545785 54819059446876938069409339)
  ·
    refine ⟨82228589170315407104114009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54819059446876938069409339 82228589170315407104114009)
    ·
      refine ⟨61671441877736555328085507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82228589170315407104114009 61671441877736555328085507)
      ·
        refine ⟨92507162816604832992128261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61671441877736555328085507 92507162816604832992128261)
        ·
          refine ⟨17345093028113406186024049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92507162816604832992128261 17345093028113406186024049)
          ·
            refine ⟨13008819771085054639518037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17345093028113406186024049 13008819771085054639518037)
            ·
              refine ⟨38111776673100746014213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 13008819771085054639518037 38111776673100746014213)
              ·
                rfl

theorem cell22_3006008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 10].length) (baseStart_3006008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006008 prefixEnd_3006008 := by exact prefixLift 3006008
  have htrace : WordTrace (prefixWord ++ tailWord_3006008) baseStart_3006008 baseEnd_3006008 := by
    simpa [prefixWord, tailWord_3006008, baseEnd_3006008] using wordTrace_append hprefix tailTrace_3006008
  have hstable : (prefixWord ++ tailWord_3006008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006008).length < 2 ^ (prefixWord ++ tailWord_3006008).sum := by decide
  have hdescent : baseEnd_3006008 < baseStart_3006008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006010 : List Nat := [3, 1, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_3006010 : Nat := 118140960795 + 3006010 * 2 ^ 59
def prefixEnd_3006010 : Nat := 4983230072969 + 3 ^ 40 * 3006010 * 2
def baseEnd_3006010 : Nat := 1029018654814592803833745

theorem tailTrace_3006010 : CollatzResearch.WordTrace tailWord_3006010 prefixEnd_3006010 1029018654814592803833745 := by
  unfold tailWord_3006010
  simp only [CollatzResearch.WordTrace]
  refine ⟨27409547959936657620097871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73092127893164420320260989 27409547959936657620097871)
  ·
    refine ⟨41114321939904986430146807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27409547959936657620097871 41114321939904986430146807)
    ·
      refine ⟨61671482909857479645220211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41114321939904986430146807 61671482909857479645220211)
      ·
        refine ⟨92507224364786219467830317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61671482909857479645220211 92507224364786219467830317)
        ·
          refine ⟨34690209136794832300436369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92507224364786219467830317 34690209136794832300436369)
          ·
            refine ⟨26017656852596124225327277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34690209136794832300436369 26017656852596124225327277)
            ·
              refine ⟨9756621319723546584497729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26017656852596124225327277 9756621319723546584497729)
              ·
                refine ⟨7317465989792659938373297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9756621319723546584497729 7317465989792659938373297)
                ·
                  refine ⟨5488099492344494953779973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7317465989792659938373297 5488099492344494953779973)
                  ·
                    refine ⟨1029018654814592803833745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5488099492344494953779973 1029018654814592803833745)
                    ·
                      rfl

theorem cell22_3006010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_3006010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006010 prefixEnd_3006010 := by exact prefixLift 3006010
  have htrace : WordTrace (prefixWord ++ tailWord_3006010) baseStart_3006010 baseEnd_3006010 := by
    simpa [prefixWord, tailWord_3006010, baseEnd_3006010] using wordTrace_append hprefix tailTrace_3006010
  have hstable : (prefixWord ++ tailWord_3006010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006010).length < 2 ^ (prefixWord ++ tailWord_3006010).sum := by decide
  have hdescent : baseEnd_3006010 < baseStart_3006010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006040 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 5, 3]
def baseStart_3006040 : Nat := 118140960795 + 3006040 * 2 ^ 59
def prefixEnd_3006040 : Nat := 4983230072969 + 3 ^ 40 * 3006040 * 2
def baseEnd_3006040 : Nat := 1029028924427682725583653

theorem tailTrace_3006040 : CollatzResearch.WordTrace tailWord_3006040 prefixEnd_3006040 1029028924427682725583653 := by
  unfold tailWord_3006040
  simp only [CollatzResearch.WordTrace]
  refine ⟨54819643014818972801991787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 73092857353091963735989049 54819643014818972801991787)
  ·
    refine ⟨82229464522228459202987681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54819643014818972801991787 82229464522228459202987681)
    ·
      refine ⟨61672098391671344402240761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82229464522228459202987681 61672098391671344402240761)
      ·
        refine ⟨46254073793753508301680571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61672098391671344402240761 46254073793753508301680571)
        ·
          refine ⟨69381110690630262452520857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46254073793753508301680571 69381110690630262452520857)
          ·
            refine ⟨52035833017972696839390643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69381110690630262452520857 52035833017972696839390643)
            ·
              refine ⟨78053749526959045259085965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52035833017972696839390643 78053749526959045259085965)
              ·
                refine ⟨29270156072609641972157237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78053749526959045259085965 29270156072609641972157237)
                ·
                  refine ⟨2744077131807153934889741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 29270156072609641972157237 2744077131807153934889741)
                  ·
                    refine ⟨1029028924427682725583653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2744077131807153934889741 1029028924427682725583653)
                    ·
                      rfl

theorem cell22_3006040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 5, 3].length) (baseStart_3006040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006040 prefixEnd_3006040 := by exact prefixLift 3006040
  have htrace : WordTrace (prefixWord ++ tailWord_3006040) baseStart_3006040 baseEnd_3006040 := by
    simpa [prefixWord, tailWord_3006040, baseEnd_3006040] using wordTrace_append hprefix tailTrace_3006040
  have hstable : (prefixWord ++ tailWord_3006040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006040).length < 2 ^ (prefixWord ++ tailWord_3006040).sum := by decide
  have hdescent : baseEnd_3006040 < baseStart_3006040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006085 : List Nat := [1, 3, 1, 1, 4, 1, 3, 1, 2, 5]
def baseStart_3006085 : Nat := 118140960795 + 3006085 * 2 ^ 59
def prefixEnd_3006085 : Nat := 4983230072969 + 3 ^ 40 * 3006085 * 2
def baseEnd_3006085 : Nat := 1029044328847317608208515

theorem tailTrace_3006085 : CollatzResearch.WordTrace tailWord_3006085 prefixEnd_3006085 1029044328847317608208515 := by
  unfold tailWord_3006085
  simp only [CollatzResearch.WordTrace]
  refine ⟨109640927314474918289371709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 73093951542983278859581139 109640927314474918289371709)
  ·
    refine ⟨41115347742928094358514391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 109640927314474918289371709 41115347742928094358514391)
    ·
      refine ⟨61673021614392141537771587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41115347742928094358514391 61673021614392141537771587)
      ·
        refine ⟨92509532421588212306657381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61673021614392141537771587 92509532421588212306657381)
        ·
          refine ⟨17345537329047789807498259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92509532421588212306657381 17345537329047789807498259)
          ·
            refine ⟨26018305993571684711247389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17345537329047789807498259 26018305993571684711247389)
            ·
              refine ⟨9756864747589381766717771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26018305993571684711247389 9756864747589381766717771)
              ·
                refine ⟨14635297121384072650076657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9756864747589381766717771 14635297121384072650076657)
                ·
                  refine ⟨10976472841038054487557493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14635297121384072650076657 10976472841038054487557493)
                  ·
                    refine ⟨1029044328847317608208515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10976472841038054487557493 1029044328847317608208515)
                    ·
                      rfl

theorem cell22_3006085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_3006085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006085 prefixEnd_3006085 := by exact prefixLift 3006085
  have htrace : WordTrace (prefixWord ++ tailWord_3006085) baseStart_3006085 baseEnd_3006085 := by
    simpa [prefixWord, tailWord_3006085, baseEnd_3006085] using wordTrace_append hprefix tailTrace_3006085
  have hstable : (prefixWord ++ tailWord_3006085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006085).length < 2 ^ (prefixWord ++ tailWord_3006085).sum := by decide
  have hdescent : baseEnd_3006085 < baseStart_3006085 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3006130 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3006130 : Nat := 118140960795 + 3006130 * 2 ^ 59
def prefixEnd_3006130 : Nat := 4983230072969 + 3 ^ 40 * 3006130 * 2
def baseEnd_3006130 : Nat := 1029059733266952490833377

theorem tailTrace_3006130 : CollatzResearch.WordTrace tailWord_3006130 prefixEnd_3006130 1029059733266952490833377 := by
  unfold tailWord_3006130
  simp only [CollatzResearch.WordTrace]
  refine ⟨27410642149827972743689961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 73095045732874593983173229 27410642149827972743689961)
  ·
    refine ⟨20557981612370979557767471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27410642149827972743689961 20557981612370979557767471)
    ·
      refine ⟨30836972418556469336651207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20557981612370979557767471 30836972418556469336651207)
      ·
        refine ⟨46255458627834704004976811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30836972418556469336651207 46255458627834704004976811)
        ·
          refine ⟨69383187941752056007465217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46255458627834704004976811 69383187941752056007465217)
          ·
            refine ⟨52037390956314042005598913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69383187941752056007465217 52037390956314042005598913)
            ·
              refine ⟨39028043217235531504199185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52037390956314042005598913 39028043217235531504199185)
              ·
                refine ⟨29271032412926648628149389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39028043217235531504199185 29271032412926648628149389)
                ·
                  refine ⟨10976637154847493235556021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29271032412926648628149389 10976637154847493235556021)
                  ·
                    refine ⟨1029059733266952490833377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10976637154847493235556021 1029059733266952490833377)
                    ·
                      rfl

theorem cell22_3006130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3006130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3006130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3006130 prefixEnd_3006130 := by exact prefixLift 3006130
  have htrace : WordTrace (prefixWord ++ tailWord_3006130) baseStart_3006130 baseEnd_3006130 := by
    simpa [prefixWord, tailWord_3006130, baseEnd_3006130] using wordTrace_append hprefix tailTrace_3006130
  have hstable : (prefixWord ++ tailWord_3006130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3006130).length < 2 ^ (prefixWord ++ tailWord_3006130).sum := by decide
  have hdescent : baseEnd_3006130 < baseStart_3006130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3006130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
